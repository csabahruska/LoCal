module Dynamic

import LoCal
import Data.Maybe
import Data.SortedMap
import Data.SortedSet
import Data.String
import Control.Monad.State
import Data.Primitives.Interpolation
import Control.ANSI
import System.File
import System
import Decidable.Equality

export
Injective MkRegion where
  injective Refl = Refl

public export
DecEq Region where
  decEq (MkRegion x) (MkRegion y) = decEqCong $ decEq x y

showRegion : Region -> String
showRegion (MkRegion i) = "MkRegion \{i}"

Show Region where show = showRegion
Interpolation Region where interpolate = show

showTy : Ty -> String
showTy t = case t of
  T0          => "T0"
  Pair a b    => "Pair (\{showTy a}) (\{showTy b})"
  Either a b  => "Either (\{showTy a}) (\{showTy b})"
  I64         => "I64"
  Offset a    => "Offset (\{showTy a})"
  Ptr a       => "Ptr (\{showTy a})"
  Box i       => "Box"

Show Ty where show = showTy
Interpolation Ty where interpolate = showTy

showLoc : Loc r -> String
showLoc loc = case loc of
  LocStart t r => "LocStart (\{show t}) (\{show r})"
  LocAfter t l => "LocAfter (\{show t})\n (\{showLoc l})"
  LocAfterTag s t l => "LocAfterTag \{s} (\{show t})\n (\{showLoc l})"

Show (Loc r) where show = showLoc
Interpolation (Loc r) where interpolate = show

genCmpOp : CmpOp -> String
genCmpOp = \case
  EQ => "=="
  GE => ">="
  GT => ">"
  LE => "<="
  LT => "<"
  NE => "!="

genIntOp2 : IntOp2 -> String
genIntOp2 = \case
  Plus  => "+"
  Sub   => "-"
  Times => "*"
  Quot  => "/"
  Rem   => "%"

Interpolation IntOp2 where interpolate = genIntOp2
Interpolation CmpOp where interpolate = genCmpOp

{-
  TODO:
    done - fully dynamic cursor passing and size calculation
    - interpreter based static improvements
-}

-- DONE: dynamic fill ; in a separate function
{-
  + the location expression tells how to serialize cursor passing
  TODO:
    done - use monad stack to store region/cursor environment
-}

getLocTy : Loc r -> Ty
getLocTy (LocStart t _) = t
getLocTy (LocAfter t _) = t
getLocTy (LocAfterTag _ t _) = t

getLocRegion : {r : _} -> Loc r -> Region
getLocRegion {r} _ = r

-- TODO: return: relative base value and static offset, and the required runtime end witnesses
getStaticIndex : Loc r -> Maybe Int
getStaticIndex = \case
  LocStart _ _ => Just 0
  LocAfter _ l => do
    i <- getStaticIndex l
    s <- getStaticSize (getLocTy l)
    Just (i + s)
  LocAfterTag "Pair" _ l => do
    getStaticIndex l
  LocAfterTag _ _ l => do
    i <- getStaticIndex l
    Just (1 + i)

-- codegen monad

record CG
M = StateT CG IO

record CGLocal where
  constructor MkCGLocal
  locations     : SortedMap String String
  endwitness    : SortedMap String String
  allocActions  : SortedMap String $ List $ M ()
  writeActions  : SortedMap String $ List $ M ()
  funName       : String
  indentLevel   : Nat
  -- assertions
  read          : SortedSet String
  write         : SortedSet String

record CG where
  constructor MkCG
  -- global
  counter     : Int
  decls       : List String
  code        : SortedMap String (List String)
  local       : CGLocal

emptyCGLocal : CGLocal
emptyCGLocal = MkCGLocal
  { locations     = empty
  , endwitness    = empty
  , allocActions  = empty
  , writeActions  = empty
  , funName       = ""
  , indentLevel   = 0
  , read          = empty
  , write         = empty
  }

emptyCG : CG
emptyCG = MkCG
  { counter     = 0
  , decls       = []
  , code        = empty
  , local       = emptyCGLocal
  }

-- actions

addAllocAction : Loc r -> M () -> M ()
addAllocAction loc act = modify {local.allocActions $= insertWith (++) (show loc) [act]}

addWriteAction : Loc r -> M () -> M ()
addWriteAction loc act = modify {local.writeActions $= insertWith (++) (show loc) [act]}

runActions : (CG -> SortedMap String (List (M ()))) -> Loc r -> M ()
runActions f loc = case lookup (show loc) !(gets f) of
  Nothing   => pure ()
  Just acts => sequence_ acts

runAllocActions : Loc r -> M ()
runAllocActions = runActions (.local.allocActions)

runWriteActions : Loc r -> M ()
runWriteActions = runActions (.local.writeActions)

-- assetions

assertRead : Loc r -> M ()
assertRead loc = do
  w <- gets (.local.write)
  let key = show loc
  -- check if it is already written
  unless (contains key w) $ do
    assert_total $ idris_crash $ "INTERNAL ERROR: read before write on: \{loc}"
  modify {local.read $= insert key}

assertWrite : Loc r -> M ()
assertWrite loc = do
  w <- gets (.local.write)
  let key = show loc
  when (contains key w) $ do
    assert_total $ idris_crash $ "INTERNAL ERROR: multiple writes on \{loc}"
    --putStrLn $ "INTERNAL ERROR: multiple writes on \{loc}"
  modify {local.write $= insert key}

markAlreadyWritten : Loc r -> M a -> M a
markAlreadyWritten = ?markAlreadyWritten1

markWrite : Loc r -> M a -> M a
markWrite loc action = ?markWrite1
{-
  assertWrite loc
  -- TODO: execute write actions
-}

markAlloc : Loc r -> M a -> M a
markAlloc loc action = ?markAlloc1
{-
  -- TODO: assert it is not allocated yet
  -- execute alloc actions
  runAllocActions loc
  -- HINT: run future code actions, or should this run after the first write? t depends, the actions could be tied for allocation or for writes
  --        this is action running after allocation
-}


newId : M Int
newId = state (\m => ({counter $= (+ 1)} m, m.counter))

newCursorName : M String
newCursorName = pure "cur\{!newId}"

indent : M a -> M a
indent m = do
  l <- gets (.local.indentLevel)
  modify {local.indentLevel $= (+ 1)}
  res <- m
  modify {local.indentLevel := l}
  pure res

-- TODO: what about alloc actions?
localScope : M a -> M a
localScope m = do
  locs <- gets (.local.locations)
  endws <- gets (.local.endwitness)
  reads <- gets (.local.read)
  writes <- gets (.local.write)
  res <- m
  modify { local.locations  := locs
         , local.endwitness := endws
         , local.read       := reads
         , local.write      := writes
         }
  pure res

emit : String -> M ()
emit s = do
  cg <- get
  putStrLn "[\{cg.local.funName}] \{s}"
  modify {code $= insertWith (++) cg.local.funName [indent (cg.local.indentLevel * 2) s]}

emitDecl : String -> M ()
emitDecl s = do
  cg <- get
  putStrLn "[\{cg.local.funName}] \{s}"
  modify {decls $= (::) s}

genFunction : String -> M a -> M a
genFunction fun_name action = do
  l <- gets (.local)
  modify {local := emptyCGLocal}
  modify {local.funName := fun_name}
  modify {code $= insert fun_name []}
  result <- action
  modify {local := l}
  pure result

isNewFunction : String -> M Bool
isNewFunction funName = pure $ isNothing (lookup funName !(gets code))

getTy : {t : _} -> {0 l : Loc r} -> (Exp t l _) -> Ty
getTy {t} _ = t

getLoc : {t : _} -> {l : Loc r} -> (Exp t l _) -> Loc r
getLoc {l} _ = l

addCur : String -> Loc r -> M ()
addCur c l = modify {local.locations $= insert (show l) c}

-- IDEA: use Loc values in Map as keys via its show function

lookupEndWitness : (loc : Loc r) -> M (Maybe String)
lookupEndWitness loc = do
  locs <- gets (.local.endwitness)
  pure $ lookup (show loc) locs

getEndWitness : (loc : Loc r) -> M String
getEndWitness loc = do
  Just ew <- lookupEndWitness loc
    | Nothing => assert_total $ idris_crash $ "INTERNAL ERROR: missing loc endwitness for \{loc}\n endwitness map: \{show !(gets (.local.endwitness))}"
  pure ew

lookupCursor : (loc : Loc r) -> M (Maybe String)
lookupCursor loc = do
  locs <- gets (.local.locations)
  pure $ lookup (show loc) locs

getCursor : (loc : Loc r) -> M String
getCursor loc = do
  locs <- gets (.local.locations)
  let Just cur = lookup (show loc) locs
        | Nothing => assert_total $ idris_crash $ "INTERNAL ERROR: missing loc cursor for \{loc}\n locations map: \{show locs}"
  pure cur

getAllocatedCursor : Loc r -> (String -> M ()) -> M ()
getAllocatedCursor loc action = case !(lookupCursor loc) of
  Just cur => action cur
  Nothing  => addAllocAction loc $ getCursor loc >>= action

getWrittenCursor : Loc r -> (String -> M ()) -> M ()
getWrittenCursor loc action = ?getWrittenCursor1 -- case !(lookupCursor loc) of

-- TODO: check that it is written only once ; use an effect map for LocVals
allocCursor : (loc : Loc r) -> M String
allocCursor loc = do
  -- putStrLn " !! gen cursor for \{loc}"
  let locKey = show loc
  {-
    gen new if does not exist
    return exisiting when available
  -}
  locs <- gets (.local.locations)
  let newCur = do
        c <- newCursorName
        print $ colored BrightRed " !! add cursor \{c} :=\n \{loc}\n\n"
        print $ colored BrightMagenta " !! static index \{c} := \{show (getStaticIndex loc)}\n\n"
        addCur c loc
        emit "/* \{c} = \{loc} */"
        pure c
  case lookup locKey !(gets (.local.locations)) of
    Just v  => assert_total $ idris_crash $ "cursor '\{v}' is already generated for \{loc}" -- Q: idk if this is right, because reads can reuse cursors
    Nothing => do
      case loc of
        LocStart _ _ => assert_total $ idris_crash $ "can not allocate LocStart"
        LocAfter _ l => do
          c <- newCur
          markAlloc loc $ emit "char* \{c} = \{!(getEndWitness l)};"
          pure c
        LocAfterTag s fstTy l => do
          let tagSize : Int = case s of
                "Pair"  => 0
                _       => 1
          c <- newCur
          markAlloc loc $ emit "char* \{c} = \{!(getCursor l)} + \{tagSize};"
          pure c


hasEndWitness : Loc r -> M Bool
hasEndWitness loc = do
  ends <- gets (.local.endwitness)
  pure $ isJust $ lookup (show loc) ends

defineEndWitness : (loc : Loc r) -> String -> M ()
defineEndWitness loc value = unless !(hasEndWitness loc) $ do
  cur <- getCursor loc
  let ew = "\{cur}_end"
  modify {local.endwitness $= insert (show loc) ew}
  emit "char* \{ew} = \{value};"

updateEndWitnessTo : {loc2 : _} -> (loc : Loc r) -> Exp _ loc2 _ -> M ()
updateEndWitnessTo {loc2} loc e = do
  ew <- getEndWitness loc2
  modify {local.endwitness $= insert (show loc) ew}
  print $ colored BrightBlue " update endwitness to \{ew} for\n \{loc}\n\n"

inheritEndWitness : {ew : _} -> {loc2 : Loc r2} -> (loc : Loc r) -> Exp _ loc2 ew -> M ()
inheritEndWitness loc e = case ew of
  NoEW => pure ()
  EW   => updateEndWitnessTo loc e

addStaticSizeEndWitness : (loc : Loc r) -> String -> M ()
addStaticSizeEndWitness l msg = do
  let t = getLocTy l
      Just bytes = getStaticSize t
        | Nothing => assert_total $ idris_crash $ "INTERNAL ERROR: missing static size for: \{l}"
  unless !(hasEndWitness l) $ do
    cur <- getCursor l
    let ew = "\{cur}_end"
    modify {local.endwitness $= insert (show l) ew}
    emit "char* \{ew} = \{cur} + \{bytes}; // \{msg}"
    print $ colored BrightCyan " add endwitness to \{ew} for\n \{l}\n\n"

{-
  TODO: rewrite to continuation passig style EDSL to avoid duplicated codegen, i.e. 'let i = MkI64 1 in MkRTup i (MkPtr i)' will set the value of i to 1 twice
  PROBLEM: this is a wrong example because Ptr should not implicate codegen for its argument because it is contained by some other structure
  REQUIREMENT/GOAL:
    the IR and codegen must be a direct representation of the instruction ordering of the final program
    this rules out CPS style IR
    it requires non CPS normal value focused IR with direct codegen
  Q: what creates the cursors for arguments?
  A: structure eliminators and function body
-}

partial fillDyn : {ew : _} -> {loc : _} -> Exp t loc ew -> M ()
partial readDyn : {ew : _} -> {loc : _} -> Exp t loc ew -> M ()

-- ?? read or write
fillDyn (MkBox v) = do
  putStrLn " ++ MkBox"
  fillDyn v

-- ?? read or write
fillDyn (UnBox v) = do
  putStrLn " ++ UnBox"
  fillDyn v

fillDyn MkT0 = do
  putStrLn " ++ MkT0"
  _ <- allocCursor loc
  addStaticSizeEndWitness loc "MkT0"
  markWrite loc $ pure ()

fillDyn (MkI64 i) = do
  putStrLn " ++ MkI64 \{i}"
  cur <- allocCursor loc
  addStaticSizeEndWitness loc "MkI64"
  markWrite loc $ emit "*(int*) \{cur} = \{i}; // MkI64"

fillDyn (MkPair va vb) = do
  putStrLn " ++ MkPair"
  _ <- allocCursor loc
  fillDyn va
  fillDyn vb
  inheritEndWitness loc vb
  markWrite loc $ pure ()

fillDyn (MkPtr {loc_in} v) = do
  putStrLn " ++ MkPtr"
  readDyn v
  cur <- allocCursor loc
  addStaticSizeEndWitness loc "MkPtr"
  -- HINT: it is required that the target to be written, it will make the dereferenced value valid
  getWrittenCursor loc_in $ \cur_in => do
    markWrite loc $ emit "*(char**) \{cur} = \{cur_in};"

fillDyn (MkOffset {loc_in} v) = do
  putStrLn " ++ MkOffset"
  readDyn v
  cur <- allocCursor loc
  addStaticSizeEndWitness loc "MkOffset"
  -- HINT: it is required that the target to be written, it will make the dereferenced value valid
  getWrittenCursor loc_in $ \cur_in => do
    markWrite loc $ emit "*(int*) \{cur} = \{cur_in} - \{cur};"

fillDyn (DeRefPtr {x, r_in, loc_in} v cont) = do
  putStrLn " ++ DeRefPtr"
  readDyn v
  getWrittenCursor loc_in $ \cur_in => do
    -- generate new cursor name for loc_val
    cur <- newCursorName
    let r_val = MkRegion !newId
        loc_val = LocStart x r_val
    addCur cur loc_val
    emit "/* \{cur} = \{loc_val} */"
    markAlloc loc $ emit "char* \{cur} = *(char**)\{cur_in}; // DeRefPtr"
    markWrite loc $ pure ()
    fillDyn (cont {r_val} Var)
{-
  TODO:
    - add assertions when alloc and actions were not run in the end of codegen
-}
fillDyn (DeRefOffset {x, r_in, loc_in} v cont) = do
  putStrLn " ++ DeRefPtr"
  readDyn v
  getWrittenCursor loc_in $ \cur_in => do
    -- generate new cursor name for loc_val
    cur <- newCursorName
    let r_val = MkRegion !newId
        loc_val = LocStart x r_val
    addCur cur loc_val
    emit "/* \{cur} = \{loc_val} */"
    markAlloc loc $ emit "char* \{cur} = \{cur_in} + *(int*)\{cur_in}; // DeRefOffset"
    markWrite loc $ pure ()
    fillDyn (cont {r_val} Var)

fillDyn (MkLeft arg) = do
  putStrLn " ++ MkLeft"
  cur <- allocCursor loc
  emit "*(char*) \{cur} = 0; // LEFT_TAG"
  fillDyn arg
  inheritEndWitness loc arg
  markWrite loc $ pure ()

fillDyn (MkRight arg) = do
  putStrLn " ++ MkRight"
  cur <- allocCursor loc
  emit "*(char*) \{cur} = 1; // RIGHT_TAG"
  fillDyn arg
  inheritEndWitness loc arg
  markWrite loc $ pure ()

-- primops
fillDyn (I64Op2CE op {loc_in2} argC1 arg2) = do
  putStrLn " ++ I64Op2CE"
  readDyn arg2
  cur <- allocCursor loc
  addStaticSizeEndWitness loc "I64Op2CE - result"
  getWrittenCursor loc_in2 $ \cur_in2 => do
    markWrite loc $ emit "*(int*) \{cur} = \{argC1} \{op} *(int*) \{cur_in2};"

fillDyn (I64Op2EC op {loc_in1} arg1 argC2) = do
  putStrLn " ++ I64Op2EC"
  readDyn arg1
  cur <- allocCursor loc
  addStaticSizeEndWitness loc "I64Op2EC - result"
  getWrittenCursor loc_in1 $ \cur_in1 => do
    markWrite loc $ emit "*(int*) \{cur} = *(int*) \{cur_in1} \{op} \{argC2};"

fillDyn (I64Op2 op {loc_in1, loc_in2} arg1 arg2) = do
  putStrLn " ++ I64Op2"
  readDyn arg1
  readDyn arg2
  cur <- allocCursor loc
  addStaticSizeEndWitness loc "I64Op2 - result"
  getWrittenCursor loc_in1 $ \cur_in1 => do
    getWrittenCursor loc_in2 $ \cur_in2 => do
      markWrite loc $ emit "*(int*) \{cur} = *(int*) \{cur_in1} \{op} *(int*) \{cur_in2};"

fillDyn (I64Cmp op {loc_in1, loc_in2} arg1 arg2) = do
  putStrLn " ++ I64Cmp"
  readDyn arg1
  readDyn arg2
  cur <- allocCursor loc
  addStaticSizeEndWitness loc "I64Cmp - result"
  getWrittenCursor loc_in1 $ \cur_in1 => do
    getWrittenCursor loc_in2 $ \cur_in2 => do
      markWrite loc $ emit "*(char*) \{cur} = (*(int*) \{cur_in1} \{op} *(int*) \{cur_in2}) ? 1 /*RIGHT_TAG*/ : 0 /*LEFT_TAG*/;"

fillDyn (I64CmpC op argC1 {loc_in2} arg2) = do
  putStrLn " ++ I64CmpC"
  readDyn arg2
  cur <- allocCursor loc
  addStaticSizeEndWitness loc "I64CmpC - result"
  getWrittenCursor loc_in2 $ \cur_in2 => do
    markWrite loc $ emit "*(char*) \{cur} = (\{argC1} \{op} *(int*) \{cur_in2}) ? 1 /*RIGHT_TAG*/ : 0 /*LEFT_TAG*/;"

fillDyn (PrintI64 {loc_in} v cont) = do
  putStrLn " ++ PrintI64"
  readDyn v
  getWrittenCursor loc_in $ \cur_in => do
    emit "printf(\"%d\\n\", *(int*) \{cur_in});"
    fillDyn $ cont ()

fillDyn (PrintValue {loc_in} v cont) = do
  putStrLn " ++ PrintValue"
  readDyn v
  getWrittenCursor loc_in $ \cur_in => do
    cur_end <- getEndWitness loc_in
    emit "print_hex(\{cur_in}, \{cur_end} - \{cur_in});"
    fillDyn $ cont ()

fillDyn (LetRegion cont) = do
  putStrLn " ++ LetRegion"
  let r = MkRegion !newId
  fillDyn (cont r)

fillDyn (LetRegionValue {t_val} r v cont) = do
  putStrLn " ++ LetRegionValue"
  c <- newCursorName
  let loc_start = LocStart t_val r
  addCur c loc_start
  markAlloc loc_start $ emit "char *\{c} = newRegion();"
  fillDyn v
  fillDyn (cont Var)

fillDyn (CasePair {a, loc_tup} tup cont) = do
  putStrLn " ++ CasePair"
  readDyn tup
  getWrittenCursor loc_tup $ \_ => do -- Q: should we require allocation only?
    let locFst = LocAfterTag "Pair" a loc_tup
    _ <- allocCursor locFst
    markAlreadyWritten locFst $ pure ()
    fillDyn $ cont Var AddLocAfter {tup_ew_fun = InheritEW}

fillDyn (CaseEither {a, b, loc_scrut} scrut cont_left cont_right) = do
  lift $ putStrLn " ++ CaseEither"
  readDyn scrut
  getWrittenCursor loc_scrut $ \cur_tag => do
    let locL = LocAfterTag "Left"  a loc_scrut
        locR = LocAfterTag "Right" b loc_scrut

    let cur_end_tmp     = "\{!(newCursorName)}_end_tmp"
        cur_tag_end_tmp = "\{cur_tag}_end_tmp"
    emit "char* \{cur_end_tmp} = 0; // uninitalized"
    emit "char* \{cur_tag_end_tmp} = 0; // uninitalized"

    let writeScrutEW = do
          Just ew <- lookupEndWitness loc_scrut
            | Nothing => pure False
          emit "\{cur_tag_end_tmp} = \{ew};"
          pure True

    emit "if (*(char*) \{cur_tag} == 0) { // LEFT"
    (scrut_ew_left, left_cglocal) <- indent $ localScope $ do
      _ <- markAlreadyWritten locL $ allocCursor locL
      let expL = cont_left Var {either_ew_fun = InheritEW}
      fillDyn expL
      emit "\{cur_end_tmp} = \{!(getEndWitness $ getLoc expL)};"
      pure (!writeScrutEW, !(gets (.local)))

    emit "} else { // RIGHT"
    (scrut_ew_right, right_cglocal) <- indent $ localScope $ do
      _ <- markAlreadyWritten locR $ allocCursor locR
      let expR = cont_right Var {either_ew_fun = InheritEW}
      fillDyn expR
      emit "\{cur_end_tmp} = \{!(getEndWitness $ getLoc expR)};"
      pure (!writeScrutEW, !(gets (.local)))
    emit "}"

    modify { local.read   $= union (intersection left_cglocal.read  right_cglocal.read)
           , local.write  $= union (intersection left_cglocal.write right_cglocal.write)
           }
    defineEndWitness loc cur_end_tmp
    -- add end-witness for loc_scrut ; this can be done when both left and right eliminator has it
    when (scrut_ew_left && scrut_ew_right) $ do
      defineEndWitness loc_scrut cur_tag_end_tmp

fillDyn (Copy {loc_in} v) = do
  putStrLn " ++ Copy"
  readDyn v
  cur_dst <- allocCursor loc
  getWrittenCursor loc_in $ \cur_src => do
    cur_src_end <- getEndWitness loc_in
    defineEndWitness loc "\{cur_dst} + (\{cur_src_end} - \{cur_src})"
    markWrite loc $ emit "memcpy(\{cur_dst}, \{cur_src}, \{cur_src_end} - \{cur_src});"

-- TODO: input end-witness passing and return
fillDyn (FunApp2 {loc_arg, loc_res} fun_name fun arg) = do
  putStrLn " ++ FunApp2 \{fun_name}"
  readDyn arg
  cur_out <- allocCursor loc_res
  getWrittenCursor loc_arg $ \cur_in => do
    -- HINT: fun may or may not need arg end witness
    --    Q: how to handle this?
    --    A: arg end-witness is not needed

    -- TODO: omit end-witness for static sized outputs
    markWrite loc_res $ defineEndWitness loc_res "\{fun_name}(\{cur_in}, \{cur_out})"

  -- codegen function if needed
  when !(isNewFunction fun_name) $ do
    genFunction fun_name $ do
      -- TODO: support multi parameter functions
      -- TODO: pass arg's pointers entry if any
      cur_arg <- newCursorName
      cur_out <- newCursorName
      markAlreadyWritten loc_arg $ markAlloc loc_arg $ addCur cur_arg loc_arg
      markAlloc loc_res $ addCur cur_out loc_res
      emitDecl "char* \{fun_name}(char* \{cur_arg}, char* \{cur_out});"
      emit "char* \{fun_name}(char* \{cur_arg}, char* \{cur_out}) {"
      indent $ do
        emit "/* \{cur_arg} = \{loc_arg} */"
        emit "/* \{cur_out} = \{loc_res} */"
        let (res) = fun Var
        fillDyn res
        emit "return \{!(getEndWitness loc_res)};"
      emit "}"

fillDyn e = readDyn e

{-
  TODO:
  - clarify the relation and semantics between fillDyn and evalEff
-}

readDyn (MkStaticEW v) = do
  putStrLn " ++ MkStaticEW"
  readDyn v
  addStaticSizeEndWitness loc  "MkStaticEW"

readDyn (AddLocAfter {b, locFst} v) = do
  putStrLn " ++ AddLocAfter"
  readDyn v
  let locSnd = LocAfter b locFst
  _ <- allocCursor locSnd
  markAlreadyWritten locSnd $ pure ()

readDyn (InheritEW v) = do
  putStrLn " ++ InheritEW"
  readDyn v
  inheritEndWitness loc v

readDyn Var = do
  putStrLn " ++ Var"
  getWrittenCursor loc $ \cur => do
    emit "/* \{cur} = \{loc} */"
    emit "// Var \{getLocTy loc}" -- assert_total $ idris_crash $ "Var"



c_header : String
c_header = """
  #include <stdio.h>
  #include <stdlib.h>
  #include <string.h>

  char* newRegion() {
    return malloc(1024);
  }

  void print_hex(const unsigned char *buf, size_t len) {
    printf("%ld bytes\\n", len);
    for (size_t i = 0; i < len; i++) {
        // %02x: 0-padded, 2-character minimum, lowercase hex
        printf("%02x ", buf[i]);

        // Optional: add a newline every 16 bytes for readability
        if ((i + 1) % 16 == 0) printf("\\n");
    }
    printf("\\n");
  }

  """

partial public export
toBufferDyn : {t : _} -> Exp t (LocStart t (MkRegion (-1))) EW -> IO String
toBufferDyn {t} e = do
  print $ background Yellow " ---- CODEGEN ----\n"
  putStrLn ""
  s <- execStateT emptyCG $ do
    genFunction "main" $ do
      emit "void main() {"
      indent $ fillDyn $ LetRegionValue (MkRegion (-1)) e id
      emit "}"
  putStrLn " ---- CODE OUTPUT ----"
  pure $ unlines $ c_header :: [unlines (reverse funLines) | funLines <- s.decls :: values s.code]

partial public export
compileProgram : String -> Program -> IO String
compileProgram name (Main e) = do
  let fname = name ++ ".c"
  print $ background BrightRed " ---- CODEGEN \{fname} ----\n"
  src <- toBufferDyn e
  Right _ <- writeFile fname src
    | Left err => idris_crash (show err)
  (c_msg, 0) <- run "gcc \{fname} -o \{name}"
    | err => idris_crash (show err)
  putStrLn c_msg
  pure src

{-
  INSIGHTS:
    - read: values can be bring to scope sequentially, but only when they are written
        + requirement: written value
        + position:
          * depends on previus values (needs end witness computed at runtime, by traversing previous structures or using offset info)
          * does not depend on previous values (static offset can be computed at compile time)
    - write:
        + unordered write: if the value is not read and if the position does not depend on previous values
        + ordered write: value position depends on previous values
    - write first / read second barrier: all reads must come after writes
  TODO:
    - learn about read and write cursors
    - write function to compute the static offset of a location in this form: static offset + list of location runtime sizes
    - write location ord comparison function, to check before after relation
    - write isNextLoc function
    - add effect tracking to locations: ALLOC, WRITE, READ
    - check the required effects during codegen
    - support forward pointers
    done - separate offsets and pointers
    done - add functions
    SKIP - write full value traversal checker function, which would tell the unaccessed locations ; not possible in LoCal RTup2/STup2 is to make this explicit
    - add high level language and map it to local
      + for first use fully pointer based approach with a bump allocator region allocator
    done - support dec/def types, used Box instead

  Q: would it be enough in practice if only backward pointers would be supported?
  Q: how is atomicity and value sharing is related? (value representation and value indirection)
      can an indirection be created where the actual value is not created yet?
      the indirection must not be read before it is written, but this is true for every value

  IDEA:
    transform the code into sequential composition of dynamic and static sized allocated and filled blocks
    the indices would be statically known within each static block where the base pointer would be the input of the static block
    and the base pointer would be produced at runtime and it would represent the end witness for a dynamically sized value
    Q: is this cursor calculus?
    - think about compressed regions, static sized region chunks could fetch or push data to/from compression

  INSIGHTS:
    - LoCal type system nuresry has the same role as the ALLOC/READ/WRITE effect system
    - offset and indirection is an endwitness problem which is a cursor language related issue, more specifically it is related to the dynamic sized block
      LoCal does not have the concept of endwitness
      for efficiency the endwitness must be computed in constant time O(1) via offset or pointer or size
    - imlicit sharing support = LoCal + interpreter
      parallelism support     = LoCal + interpreter
      where the interpreter handles the indirection resolution
  Q: is endwitness type (static, indirection, or traversal-where the program consumes it-) a property of each location?
  A: i think so
    - cursor calculus can include endwitnesses for dynamically sized values,
      this should be reflected in the cursor calculus type system,
      function applications must be well typed in cursor calculus
  - the L location's endwitness is an indirection to the value comes after L
    INSIGHT:
      this is a misconception because end witness is a cursor calculus level concept, although technically it is a pointer also
      the lowest level of calculus must be the cursor calculus that will set the location and endwitness semantics along with the final layout

  TODO: for high level Exp
    - implement traversal effect calculation
    - insert explicit endwitness computation method to locations which will set the semantics and layout

  Q: could the endwitness strategy be included as an Exp or location index?
     with this LoCal would describe the exact layout and cursor calculus would not be needed
  A: YES with RTup2 and STup2 the endwittness computation becomes explicit in LoCal

  Q: should require full traverse effect in LoCal? could it be modeled with endwitness strategy encoding?
  A: YES RTup2/STup2 solves this also.

  IDEA:
    enforce full structure traversal by construction, with Tup2 eliminator in LoCal

  Q: which design is better?
    a) linear cursor passing
    b) sequence of statically indexed blocks with dynamic base index

  IDEA:
    done - add two kind of tules: SerialTup2 (STup2) and RandomAccessTup2 (RTup2)
  TODO:
    done - allocate RTup2 snd indirection only when fst size is not statically known
    - finish LoCal:
      + effect tracking during codegen
      done + add function support
    - add high level Exp
      + adt support
      + no locations
      + implicit sharing support
      + translate to LoCal
    - think about how end-witnesses are created with reading data
-}
