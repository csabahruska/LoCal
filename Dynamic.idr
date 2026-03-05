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

Interpolation Region where interpolate = show
Interpolation Ty where interpolate = showTy
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
  preallocs     : SortedMap String String
  locations     : SortedMap String String
  endwitness    : SortedMap String String
  writeActions  : SortedMap String $ List $ M ()
  genFunActions : List $ M ()
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
  { preallocs     = empty
  , locations     = empty
  , endwitness    = empty
  , writeActions  = empty
  , genFunActions = []
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

debug : M () -> M ()
--debug a = a
debug _ = pure ()

-- actions

addWriteAction : Loc r -> M () -> M ()
addWriteAction loc act = modify {local.writeActions $= insertWith (++) (show loc) [act]}

runActions : (CG -> SortedMap String (List (M ()))) -> Loc r -> M ()
runActions f loc = case lookup (show loc) !(gets f) of
  Nothing   => pure ()
  Just acts => sequence_ acts

runWriteActions : Loc r -> M ()
runWriteActions loc = do
  runActions (.local.writeActions) loc
  -- clear actions
  modify {local.writeActions $= delete (show loc)}

-- assetions

assertNoActionsLeft : M ()
assertNoActionsLeft = do
  wActs <- gets (.local.writeActions)
  unless (null wActs) $ do
    assert_total $ idris_crash $ "pending write actions for: \{unlines (keys wActs)}"

listPendingActions : M ()
listPendingActions = do
  wActs <- gets (.local.writeActions)
  unless (null wActs) $ do
    putStrLn $ "pending write actions for: \{unlines (keys wActs)}"

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

-- PURPOSE: get access to a sub value of an existing written value
markAlreadyWritten : Loc r -> M a -> M a
markAlreadyWritten loc action = do
  modify {local.write $= insert (show loc)}
  action

markWrite : Loc r -> M a -> M a
markWrite loc action = do
  -- NOTE: check if loc is written only once
  assertWrite loc
  res <- action
  runWriteActions loc
  pure res

markAlloc : Loc r -> M a -> M a
{-
  PURPOSE: check if a location is allocated only once
  DESIGN: allocations can not be postponed
          reads always come after writes
-}
markAlloc loc action = case lookup (show loc) !(gets (.local.locations)) of
  Just c  => assert_total $ idris_crash $ "\{c} is already allocated for \{loc}"
  Nothing => action

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

-- TODO: what about alloc and read actions?
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

runAfterGenFunction : M () -> M ()
runAfterGenFunction act = modify {local.genFunActions $= (::) act}

genFunction : String -> M a -> M a
genFunction fun_name action = do
  l <- gets (.local)
  modify {local := emptyCGLocal}
  modify {local.funName := fun_name}
  modify {code $= insert fun_name []}
  result <- action
  -- run post gen fun actions
  gets (.local.genFunActions) >>= sequence_

  modify {local := l}
  pure result

isNewFunction : String -> M Bool
isNewFunction funName = pure $ isNothing (lookup funName !(gets code))

getTy : {t : _} -> {0 l : Loc r} -> (Exp t l _ _) -> Ty
getTy {t} _ = t

getLoc : {t : _} -> {l : Loc r} -> (Exp t l _ _) -> Loc r
getLoc {l} _ = l

addCur : String -> Loc r -> M ()
addCur c l = modify {local.locations $= insert (show l) c}

preallocCursor : String -> Loc r -> M ()
preallocCursor c l = modify {local.preallocs $= insert (show l) c}

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
        | Nothing => assert_total $ idris_crash $ "INTERNAL ERROR: missing loc cursor for:\n \{loc}\n\n locations map: \{show locs}"
  pure cur

getWrittenCursor : Loc r -> (String -> M ()) -> M ()
getWrittenCursor loc action = do
  let act = getCursor loc >>= action
  if contains (show loc) !(gets (.local.write))
    then act
    else addWriteAction loc act

-- TODO: check that it is written only once ; use an effect map for LocVals
-- TODO: make this continuation based, which can pospone action until the location could be generated, i.e. end-witness is added
-- DESIGN: allocations must not block, but writes can be postponed, but not allocations
--         this mean that fillDyn always progress, and it creates cursors, but not necessary writes the content
--         in case of reads the cursor allocation must progress also, because the EDSL API guarantees ???? IDK, what does it guarantee?
allocCursor : (loc : Loc r) -> M String
allocCursor loc = markAlloc loc $ case lookup (show loc) !(gets (.local.preallocs)) of
  Just c  => addCur c loc >> pure c
  Nothing => do
    -- putStrLn " !! gen cursor for \{loc}"
    let newCur = do
          c <- newCursorName
          print $ colored BrightRed " !! add cursor \{c} :=\n \{loc}\n\n"
          print $ colored BrightMagenta " !! static index \{c} := \{show (getStaticIndex loc)}\n\n"
          addCur c loc
          debug $ emit "/* \{c} = \{loc} */"
          pure c
    case loc of
      LocStart _ _ => do
        c <- newCur
        emit "char* \{c} = newRegion();"
        pure c
      LocAfter _ l => do
        c <- newCur
        emit "char* \{c} = \{!(getEndWitness l)};"
        pure c
      LocAfterTag s fstTy l => do
        let tagSize : Int = case s of
              "Pair"  => 0
              _       => 1
        c <- newCur
        emit "char* \{c} = \{!(getCursor l)} + \{tagSize};"
        pure c

allocCursorIfNeeded : (loc : Loc r) -> M String
allocCursorIfNeeded loc = do
  Just cur <- lookupCursor loc
    | Nothing => allocCursor loc
  pure cur

hasEndWitness : Loc r -> M Bool
hasEndWitness loc = do
  ends <- gets (.local.endwitness)
  pure $ isJust $ lookup (show loc) ends

defineEndWitness : (loc : Loc r) -> String -> M ()
defineEndWitness loc value = unless !(hasEndWitness loc) $ do
  ew <- case !(lookupCursor loc) of
    Nothing   => newCursorName
    Just cur  => pure "\{cur}_end"
  modify {local.endwitness $= insert (show loc) ew}
  emit "char* \{ew} = \{value};"

updateEndWitnessTo : {loc2 : _} -> (loc : Loc r) -> Exp _ loc2 _ _ -> M ()
updateEndWitnessTo {loc2} loc e = do
  ew <- getEndWitness loc2
  modify {local.endwitness $= insert (show loc) ew}
  print $ colored BrightBlue " update endwitness to \{ew} for\n \{loc}\n\n"

inheritEndWitness : {ew : _} -> {loc2 : Loc r2} -> (loc : Loc r) -> Exp _ loc2 ew _ -> M ()
inheritEndWitness loc e = case ew of
  NoEW => pure ()
  EW   => updateEndWitnessTo loc e

addStaticSizeEndWitness : (loc : Loc r) -> String -> M ()
addStaticSizeEndWitness l msg = do
  let t = getLocTy l
      Just bytes = getStaticSize t
        | Nothing => assert_total $ idris_crash $ "INTERNAL ERROR: \{msg} missing static size for: \{l}"
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

ensureWritten : Loc r -> M ()
ensureWritten loc = getWrittenCursor loc $ \_ => pure () -- this action will be consumed at write, or will make assertNoActionsLeft fail

data CGMode = FillDyn | ReadDyn

fillDyn : {ew : _} -> {loc : _} -> Exp t loc ew _ -> M ()
readDyn : {ew : _} -> {loc : _} -> Exp t loc ew _ -> M ()
evalCont : {ew : _} -> {loc : _} -> Exp t loc ew _ -> CGMode -> M ()

evalCGMode : CGMode -> {ew : _} -> {loc : _} -> Exp t loc ew _ -> M ()
evalCGMode FillDyn = fillDyn
evalCGMode ReadDyn = readDyn

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
  getWrittenCursor (getLoc va) $ \_ => do
    getWrittenCursor (getLoc vb) $ \_ => do
      markWrite loc $ pure ()

fillDyn (MkPtr {loc_in} v) = do
  putStrLn " ++ MkPtr"
  readDyn v
  cur <- allocCursor loc
  addStaticSizeEndWitness loc "MkPtr"
  -- HINT: it is required that the target to be written, it will make the dereferenced value valid
  getWrittenCursor loc_in $ \cur_in => do
    markWrite loc $ emit "*(char**) \{cur} = \{cur_in}; // MkPtr"

fillDyn (MkOffset {loc_in} v) = do
  putStrLn " ++ MkOffset"
  readDyn v
  cur <- allocCursor loc
  addStaticSizeEndWitness loc "MkOffset"
  -- HINT: it is required that the target to be written, it will make the dereferenced value valid
  getWrittenCursor loc_in $ \cur_in => do
    markWrite loc $ emit "*(int*) \{cur} = \{cur_in} - \{cur}; // MkOffset"

{-
  done - add assertions when alloc and actions were not run in the end of codegen
-}

fillDyn (MkLeft arg) = do
  putStrLn " ++ MkLeft"
  cur <- allocCursor loc
  emit "*(char*) \{cur} = 0; // LEFT_TAG"
  fillDyn arg
  inheritEndWitness loc arg
  getWrittenCursor (getLoc arg) $ \_ => do
    markWrite loc $ pure ()

fillDyn (MkRight arg) = do
  putStrLn " ++ MkRight"
  cur <- allocCursor loc
  emit "*(char*) \{cur} = 1; // RIGHT_TAG"
  fillDyn arg
  inheritEndWitness loc arg
  getWrittenCursor (getLoc arg) $ \_ => do
    markWrite loc $ pure ()

-- primops
{-
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
-}
fillDyn (I64Op2 op {loc_in1, loc_in2} arg1 arg2) = do
  putStrLn " ++ I64Op2"
  readDyn arg1
  readDyn arg2
  cur <- allocCursor loc
  addStaticSizeEndWitness loc "I64Op2 - result"
  getWrittenCursor loc_in1 $ \cur_in1 => do
    getWrittenCursor loc_in2 $ \cur_in2 => do
      markWrite loc $ emit "*(int*) \{cur} = *(int*) \{cur_in1} \{op} *(int*) \{cur_in2}; // I64Op2"

fillDyn (I64Cmp op {loc_in1, loc_in2} arg1 arg2) = do
  putStrLn " ++ I64Cmp"
  readDyn arg1
  readDyn arg2
  cur <- allocCursor loc
  addStaticSizeEndWitness loc "I64Cmp - result"
  getWrittenCursor loc_in1 $ \cur_in1 => do
    getWrittenCursor loc_in2 $ \cur_in2 => do
      markWrite loc $ emit "*(char*) \{cur} = (*(int*) \{cur_in1} \{op} *(int*) \{cur_in2}) ? 1 /*RIGHT_TAG*/ : 0 /*LEFT_TAG*/;"
{-
fillDyn (I64CmpC op argC1 {loc_in2} arg2) = do
  putStrLn " ++ I64CmpC"
  readDyn arg2
  cur <- allocCursor loc
  addStaticSizeEndWitness loc "I64CmpC - result"
  getWrittenCursor loc_in2 $ \cur_in2 => do
    markWrite loc $ emit "*(char*) \{cur} = (\{argC1} \{op} *(int*) \{cur_in2}) ? 1 /*RIGHT_TAG*/ : 0 /*LEFT_TAG*/;"
-}

fillDyn (Copy {loc_in} v) = do
  putStrLn " ++ Copy"
  readDyn v
  cur_dst <- allocCursor loc
  getWrittenCursor loc_in $ \cur_src => do
    cur_src_end <- getEndWitness loc_in
    defineEndWitness loc "\{cur_dst} + (\{cur_src_end} - \{cur_src})"
    markWrite loc $ emit "memcpy(\{cur_dst}, \{cur_src}, \{cur_src_end} - \{cur_src}); // Copy"

fillDyn (FunApp {fun_ews, loc_res} fun_name args) = do
  putStrLn " ++ FunApp \{fun_name}"
  let readArgs : Arg _ -> M ()
      readArgs (Arg0) = pure ()
      readArgs (ArgN e a) = readDyn e >> readArgs a
  readArgs args
  -- TODO: handle returning ews
  unless (null fun_ews) $ assert_total $ idris_crash $ "TODO - handle FunApp fun_ews"
  cur_out <- allocCursor loc_res
  let buildCall : List String -> Arg _ -> M ()
      buildCall curs (ArgN {loc=loc_arg} _ a) = getWrittenCursor loc_arg $ \cur_in => buildCall (cur_in :: curs) a
      buildCall curs Arg0 = markWrite loc_res $ defineEndWitness loc_res "\{fun_name}(\{joinBy ", " $ reverse curs}, \{cur_out})"
  buildCall [] args

-- TODO: input end-witness passing and return
fillDyn (FunAppDef {res, fun_ews, loc_res} fun_name fun args) = do
  putStrLn " ++ FunAppDef \{fun_name}"
  -- 1. gen function call
  fillDyn $ FunApp {res, fun_ews, loc_res} fun_name args
  runAfterGenFunction $ when !(isNewFunction fun_name) $ do
    -- 2. codegen function if needed
    genFunction fun_name $ do
      -- TODO: pass arg's pointers entry if any -- what is this???
      cur_out <- newCursorName
      preallocCursor cur_out loc_res

      let buildParams : M () -> List String -> List String -> Arg _ -> M (M (), List String, List String)
          buildParams act params paramDocs Arg0 = pure (act, params, paramDocs)
          buildParams act params paramDocs (ArgN {loc=loc_arg} e a) = do
            cur_arg <- newCursorName
            markAlreadyWritten loc_arg $ markAlloc loc_arg $ addCur cur_arg loc_arg

            putStrLn " ++ FunAppDef \{fun_name} - arg - add end-witness \{loc_arg}"
            -- TODO: design proper arg end-witness handling
            let act2 = when (isJust $ getStaticSize $ getTy e) $ do
                        addStaticSizeEndWitness loc_arg "FunAppDef - arg"

            buildParams (act >> act2) ("char* \{cur_arg}" :: params) ("/* \{cur_arg} = \{loc_arg} */" :: paramDocs) a

      (act, params, paramDocs) <- buildParams (pure ()) [] [] args

      let toParams : Arg a -> Arg a
          toParams Arg0 = Arg0
          toParams (ArgN e a) = ArgN Var $ toParams a

          paramDecls = joinBy ", " $ reverse params

      emitDecl "char* \{fun_name}(\{paramDecls}, char* \{cur_out});"
      emit "char* \{fun_name}(\{paramDecls}, char* \{cur_out}) {"
      indent $ do
        debug $ for_ paramDocs emit
        debug $ emit "/* \{cur_out} = \{loc_res} */"
        act -- TODO: design proper arg end-witness handling
        fillDyn {loc=loc_res} $ fun $ toParams args
        assertNoActionsLeft
        emit "return \{!(getEndWitness loc_res)};"
      emit "}"

fillDyn e@(LetRegionValue{}) = evalCont e FillDyn
fillDyn e@(LetRegion{}) = evalCont e FillDyn
fillDyn e@(PrintI64{}) = evalCont e FillDyn
fillDyn e@(PrintValue{}) = evalCont e FillDyn
fillDyn e@(DeRefOffset{}) = evalCont e FillDyn
fillDyn e@(DeRefPtr{}) = evalCont e FillDyn
fillDyn e@(CaseEither{}) = evalCont e FillDyn

fillDyn (AddEW{}) = assert_total $ idris_crash $ "fillDyn - AddEW"
fillDyn (GetEWS{}) = assert_total $ idris_crash $ "fillDyn - GetEWS"
--fillDyn (Var{}) = ensureWritten loc -- this is needed for NewFunApp result, is this ok?? 
fillDyn (Var{}) = assert_total $ idris_crash $ "fillDyn - Var"
fillDyn (GetFst{}) = assert_total $ idris_crash $ "fillDyn - GetFst"
fillDyn (GetSnd{}) = assert_total $ idris_crash $ "fillDyn - GetSnd"
fillDyn (StaticEW{}) = assert_total $ idris_crash $ "fillDyn - StaticEW"
fillDyn (GenEW{}) = assert_total $ idris_crash $ "fillDyn - GenEW"
fillDyn (PairEW{}) = assert_total $ idris_crash $ "fillDyn - PairEW"
fillDyn (LeftEW{}) = assert_total $ idris_crash $ "fillDyn - LeftEW"
fillDyn (RightEW{}) = assert_total $ idris_crash $ "fillDyn - RightEW"
{-
  done - clarify the relation and semantics between fillDyn and readDyn
-}

-----------------
evalCont (LetRegionValue r v cont) mode = do
  putStrLn " ++ LetRegionValue \{show r}"
  fillDyn v
  evalCGMode mode (cont Var)

evalCont (LetRegion cont) mode = do
  putStrLn " ++ LetRegion"
  let r = MkRegion !newId
  evalCGMode mode (cont r)

evalCont (PrintI64 {loc_in} v cont) mode = do
  putStrLn " ++ PrintI64 (read)"
  readDyn v
  getWrittenCursor loc_in $ \cur_in => do
    emit "printf(\"%d\\n\", *(int*) \{cur_in});"
  evalCGMode mode $ cont ()

evalCont (PrintValue {loc_in} v cont) mode = do
  putStrLn " ++ PrintValue (read)"
  readDyn v
  getWrittenCursor loc_in $ \cur_in => do
    cur_end <- getEndWitness loc_in
    emit "print_hex(\{cur_in}, \{cur_end} - \{cur_in});"
  evalCGMode mode $ cont ()

evalCont (DeRefOffset {x, r_in, loc_in} v cont) mode = do
  putStrLn " ++ DeRefPtr (read)"
  readDyn v
  getWrittenCursor loc_in $ \cur_in => do
    -- generate new cursor name for loc_val
    cur <- newCursorName
    let r_val = MkRegion !newId
        loc_val = LocStart x r_val
    debug $ emit "/* \{cur} = \{loc_val} */"
    markAlloc loc_val $ do
      addCur cur loc_val
      emit "char* \{cur} = \{cur_in} + *(int*)\{cur_in}; // DeRefOffset"
    markWrite loc_val $ pure ()
    evalCGMode mode (cont {r_val} Var)

evalCont (DeRefPtr {x, r_in, loc_in} v cont) mode = do
  putStrLn " ++ DeRefPtr"
  readDyn v
  getWrittenCursor loc_in $ \cur_in => do
    -- generate new cursor name for loc_val
    cur <- newCursorName
    let r_val = MkRegion !newId
        loc_val = LocStart x r_val
    debug $ emit "/* \{cur} = \{loc_val} */"
    markAlloc loc_val $ do
      addCur cur loc_val
      emit "char* \{cur} = *(char**)\{cur_in}; // DeRefPtr"
    markWrite loc_val $ pure ()
    evalCGMode mode (cont {r_val} Var)

evalCont (CaseEither {a, b, loc_scrut} scrut cont_left cont_right) mode = do
  lift $ putStrLn " ++ CaseEither \{loc_scrut}"
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
      let expL = cont_left Var
      evalCGMode mode expL
      emit "\{cur_end_tmp} = \{!(getEndWitness $ getLoc expL)};"
      pure (!writeScrutEW, !(gets (.local)))

    emit "} else { // RIGHT"
    (scrut_ew_right, right_cglocal) <- indent $ localScope $ do
      _ <- markAlreadyWritten locR $ allocCursor locR
      let expR = cont_right Var
      evalCGMode mode expR
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

evalCont _ _ = assert_total $ idris_crash $ "evalCont TODO"
-----------------

readDyn (StaticEW v) = do
  putStrLn " ++ StaticEW"
  readDyn v
  addStaticSizeEndWitness loc  "StaticEW"

{-
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
-}

{-
  LetRegion       wdone rdone                           cont
  LetRegionValue  wdone rdone                           cont
  Copy            wdone rdone   rsem = ensure written
  MkBox           wdone rdone   rsem = traverse
  UnBox           wdone rdone   rsem = traverse
  MkPair          wdone rdone   rsem = ensure written
  MkLeft          wdone rdone   rsem = ensure written
  MkRight         wdone rdone   rsem = ensure written
  GetFst                rdone
  GetSnd                rdone
  CaseEither      wdone rdone                           cont
  AddEW           TODO  ??
  FunAppDef       wdone rdone   rsem = traverse         cont
  MkOffset        wdone rdone   rsem = ensure written
  DeRefOffset     wdone rdone   rsem = traverse         cont
  MkPtr           wdone rdone   rsem = ensure written
  DeRefPtr        wdone rdone   rsem = traverse         cont
  MkT0            wdone rdone   rsem = ensure written
  MkI64           wdone rdone   rsem = ensure written
  I64Op2          wdone rdone   rsem = ensure written
  I64Cmp          wdone rdone   rsem = ensure written
  PrintI64        wdone rdone   rsem = traverse         cont
  PrintValue      wdone rdone   rsem = traverse         cont
  Var                   rdone   rsem = ensure written
  StaticEW              rdone
  GenEW                 TODO
  PairEW                TODO
  LeftEW                TODO
  RightEW               TODO
-}

readDyn (I64Cmp{})    = ensureWritten loc
readDyn (I64Op2{})    = ensureWritten loc
readDyn (MkI64{})     = ensureWritten loc
readDyn (MkT0{})      = ensureWritten loc
readDyn (MkPtr{})     = ensureWritten loc
readDyn (MkOffset{})  = ensureWritten loc
readDyn (MkRight{})   = ensureWritten loc
readDyn (MkLeft{})    = ensureWritten loc
readDyn (MkPair{})    = ensureWritten loc
readDyn (Copy{})      = ensureWritten loc
readDyn (Var{})       = ensureWritten loc
readDyn (FunAppDef{}) = ensureWritten loc
readDyn (FunApp{})    = ensureWritten loc

readDyn (MkBox v) = readDyn v
readDyn (UnBox v) = readDyn v

readDyn e@(LetRegionValue{}) = evalCont e ReadDyn
readDyn e@(LetRegion{}) = evalCont e ReadDyn
readDyn e@(PrintI64{}) = evalCont e ReadDyn
readDyn e@(PrintValue{}) = evalCont e ReadDyn
readDyn e@(DeRefOffset{}) = evalCont e ReadDyn
readDyn e@(DeRefPtr{}) = evalCont e ReadDyn
readDyn e@(CaseEither{}) = evalCont e ReadDyn

readDyn (GetFst {a, loc_tup} tup) = do
  readDyn tup
  getWrittenCursor loc_tup $ \_ => do
    let locFst = LocAfterTag "Pair" a loc_tup
    _ <- allocCursorIfNeeded locFst
    markAlreadyWritten locFst $ pure ()

readDyn (GetSnd {a, b, loc_tup} tup fst) = do
  readDyn tup
  readDyn fst
  getWrittenCursor (getLoc fst) $ \_ => do
    let locFst = LocAfterTag "Pair" a loc_tup
        locSnd = LocAfter b locFst
    _ <- allocCursorIfNeeded locSnd
    markAlreadyWritten locSnd $ pure ()

readDyn (AddEW{}) = assert_total $ idris_crash $ "readDyn - AddEW"

readDyn (GenEW a) = do
  readDyn a
  --assert_total $ idris_crash $ "readDyn - GenEW type: \{getLocTy loc}"
  defineEndWitness loc "0 /*GenEW - TODO*/"

readDyn (GetEWS{}) = assert_total $ idris_crash $ "readDyn - GetEWS"
readDyn (LeftEW{}) = assert_total $ idris_crash $ "readDyn - LeftEW"
readDyn (PairEW{}) = assert_total $ idris_crash $ "readDyn - PairEW"
readDyn (RightEW{}) = assert_total $ idris_crash $ "readDyn - RightEW"

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

public export
toBufferDyn : {t : _} -> Exp t (LocStart t (MkRegion (-1))) EW [] -> IO String
toBufferDyn {t} e = do
  print $ background Yellow " ---- CODEGEN ----\n"
  putStrLn ""
  s <- execStateT emptyCG $ do
    genFunction "main" $ do
      emit "void main() {"
      indent $ readDyn $ LetRegionValue (MkRegion (-1)) e id
      assertNoActionsLeft
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
