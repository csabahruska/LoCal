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
  counter       : Int
  decls         : List String
  code          : SortedMap String (List String)
  traverseFuns  : SortedMap String String -- Ty -> function name
  local         : CGLocal

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
  { counter       = 0
  , decls         = []
  , code          = empty
  , traverseFuns  = empty
  , local         = emptyCGLocal
  }

debug : M () -> M ()
--debug a = a
debug _ = pure ()

printSrc : M ()
printSrc = do
  cg <- get
  Just funLines <- pure $ lookup cg.local.funName cg.code
    | Nothing => assert_total $ idris_crash "unknown function: \{cg.local.funName}"
  putStrLn . unlines . reverse $ funLines


-- actions

addWriteAction : Loc r -> M () -> M ()
addWriteAction loc act = modify {local.writeActions $= insertWith (++) (show loc) [act]}

runActions : (CG -> SortedMap String (List (M ()))) -> Loc r -> M ()
runActions f loc = case lookup (show loc) !(gets f) of
  Nothing   => pure ()
  Just acts => do
    putStrLn "RUN ACTIONS \{loc}"
    sequence_ $ reverse acts

runWriteActions : Loc r -> M ()
runWriteActions loc = do
  runActions (.local.writeActions) loc
  -- clear actions
  modify {local.writeActions $= delete (show loc)}

-- assetions

assertNoActionsLeft : M ()
assertNoActionsLeft = do
  cg <- get
  unless (null cg.local.writeActions) $ do
    printSrc
    assert_total $ idris_crash $ "pending write actions for locations:\n\{unlines (keys cg.local.writeActions)}\nwritten locations:\n\{unlines (Prelude.toList cg.local.write)}"

listPendingActions : M ()
listPendingActions = do
  cg <- get
  unless (null cg.local.writeActions) $ do
    putStrLn $ "pending write actions for locations:\n\{unlines (keys cg.local.writeActions)}\nwritten locations:\n\{unlines (Prelude.toList cg.local.write)}"

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

markAlloc2 : Loc r -> M String -> M String
markAlloc2 loc action = case lookup (show loc) !(gets (.local.locations)) of
  Just c  => pure c -- assert_total $ idris_crash $ "\{c} is already allocated for \{loc}"
  Nothing => action

markAlloc : Loc r -> M a -> M a
{-
  PURPOSE: check if a location is allocated only once
  DESIGN: allocations can not be postponed
          reads always come after writes
-}
markAlloc loc action = case lookup (show loc) !(gets (.local.locations)) of
  Just c  => printSrc >> assert_total (idris_crash $ "\{c} is already allocated for \{loc}")
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

showLocs : SortedMap String String -> String
showLocs locs = unlines $ map show $ Data.SortedMap.toList locs

getEndWitness : (loc : Loc r) -> M String
getEndWitness loc = do
  Just ew <- lookupEndWitness loc
    | Nothing => printSrc >> assert_total (idris_crash $ "INTERNAL ERROR: missing loc endwitness for \{loc}\n endwitness map:\n\{showLocs !(gets (.local.endwitness))}")
  pure ew

lookupCursor : (loc : Loc r) -> M (Maybe String)
lookupCursor loc = do
  locs <- gets (.local.locations)
  pure $ lookup (show loc) locs

getCursor : (loc : Loc r) -> M String
getCursor loc = do
  locs <- gets (.local.locations)
  Just cur <- pure $ lookup (show loc) locs
        | Nothing => printSrc >> assert_total (idris_crash $ "INTERNAL ERROR: missing loc cursor for:\n \{loc}\n\n locations map:\n\{showLocs locs}")
  pure cur

whenWritten : Loc r -> (M ()) -> M ()
whenWritten loc action = when (contains (show loc) !(gets (.local.write))) action

getWrittenCursor : Loc r -> (String -> M ()) -> M ()
getWrittenCursor loc action = do
  let act = getCursor loc >>= action
  if contains (show loc) !(gets (.local.write))
    then act
    else do
      -- HINT: needed for offset
      putStrLn "SUSPEND \{loc}"
      addWriteAction loc act

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

setEndWitness : (loc : Loc r) -> String -> M ()
setEndWitness loc ew = modify {local.endwitness $= insert (show loc) ew}

defineEndWitness : (loc : Loc r) -> String -> String -> M ()
defineEndWitness loc value msg = unless !(hasEndWitness loc) $ do
  ew <- case !(lookupCursor loc) of
    Nothing   => newCursorName
    Just cur  => pure "\{cur}_end"
  modify {local.endwitness $= insert (show loc) ew}
  emit "char* \{ew} = \{value}; //\{msg}"

updateEndWitnessTo : {loc2 : _} -> (loc : Loc r) -> Exp _ loc2 _ _ -> M ()
updateEndWitnessTo {loc2} loc e = do
  ew <- getEndWitness loc2
  modify {local.endwitness $= insert (show loc) ew}
  print $ colored BrightBlue " update endwitness to \{ew} for\n \{loc}\n\n"

updateEndWitnessTo' : (loc : Loc r) -> (loc2 : Loc r2) -> M ()
updateEndWitnessTo' loc loc2 = do
  ew <- getEndWitness loc2
  modify {local.endwitness $= insert (show loc) ew}
  print $ colored BrightBlue " update endwitness to \{ew} for\n \{loc}\n\n"

inheritEndWitness : {rw : _} -> {loc2 : Loc r2} -> (loc : Loc r) -> Exp _ loc2 rw _ -> M ()
inheritEndWitness loc e = case rw of
  R NoEW  => pure ()
  _       => updateEndWitnessTo loc e

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

Show CGMode where
  show FillDyn = "FillDyn"
  show ReadDyn = "ReadDyn"
Interpolation CGMode where interpolate = show

Show EndWitness where
  show EW = "EW"
  show NoEW = "NoEW"
Interpolation EndWitness where interpolate = show

Show RWMode where
  show (R ew) = "(R \{ew})"
  show W = "W"
Interpolation RWMode where interpolate = show

partial fillDyn  : {rw : _} -> {loc : _} -> Exp t loc rw _ -> M ()
partial readDyn  : {rw : _} -> {loc : _} -> Exp t loc rw _ -> M ()
partial evalCont : {rw : _} -> {loc : _} -> Exp t loc rw _ -> CGMode -> M ()

partial evalCGMode : CGMode -> {rw : _} -> {loc : Loc r} -> Exp t loc rw _ -> M ()
evalCGMode FillDyn = fillDyn
evalCGMode ReadDyn = readDyn

-- traversal

genEW : {r : _} -> {loc : Loc r} -> {t : _} -> {ew : _} -> Exp t loc (R ew) [] -> Exp t loc REW []
genEW {ew=EW} e = e
genEW {ew=NoEW} e with (decEq True $ isStaticSize t)
  genEW e | Yes p                   = StaticEW {prf = p} e
  genEW e | _ with (t)
    genEW e | _ | Either _ _        = CaseEither e (LeftEW e . genEW) (RightEW e . genEW)
    genEW e | _ | Pair _ _          = PairEW e $ genEW $ GetSnd e $ genEW $ GetFst e
    genEW e | _ | Box n (Delay tbx) = MkBox $ GenEW $ UnBox e
    genEW _ | _ | t2                = assert_total $ idris_crash $ "genEW for type \{t} - sub type: \{t2}"

genTraversalEW : {r : _} -> {loc : Loc r} -> {t : _} -> {ew : _} -> Exp t loc (R ew) [] -> M String
genTraversalEW e = do
  let key = show t
  when (isJust $ getStaticSize t) $ assert_total $ idris_crash $ "traverseLoc for static size: \{t}"
  fun_name <- case lookup key !(gets (.traverseFuns)) of
    Nothing => do
      let fun_name = "traverseFun\{!newId}"
      modify {traverseFuns $= insert key fun_name}
      runAfterGenFunction $ genFunction fun_name $ do
        cur <- newCursorName
        markAlreadyWritten loc $ markAlloc loc $ addCur cur loc
        emitDecl "char* \{fun_name}(char* \{cur}); /* \{key} */"
        emit "char* \{fun_name}(char* \{cur}) { /* \{key} */"
        indent $ do
          debug $ emit "/* \{cur} = \{loc} */"
          readDyn $ genEW e
          --assertNoActionsLeft -- TODO: fix CaseEither read/write assertion handling
          --listPendingActions
          emit "return \{!(getEndWitness loc)};"
        emit "}"
      pure fun_name
    Just fun_name => pure fun_name
  cur <- getCursor loc
  pure "\{fun_name}(\{cur})"

readArgs : Arg _ -> M ()
readArgs Arg0 = pure ()
readArgs (ArgN {t, fun, n} e a) = do
  --let loc = LocStart t $ MkArgRegion fun n
  readDyn e
  readArgs a

-- buffer codegen
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
    putStrLn " ++ MkPair - 1"
    getWrittenCursor (getLoc vb) $ \_ => do
      putStrLn " ++ MkPair - 2"
      markWrite loc $ pure ()

fillDyn (MkPtr {loc_in} v) = do
  putStrLn " ++ MkPtr"
  readDyn v
  cur <- allocCursor loc
  addStaticSizeEndWitness loc "MkPtr"
  -- HINT: it is required that the target to be written, it will make the dereferenced value valid
  getWrittenCursor loc_in $ \cur_in => do
    putStrLn " ++ MkPtr - 1"
    markWrite loc $ emit "*(char**) \{cur} = \{cur_in}; // MkPtr"

fillDyn (MkOffset {loc_in} v) = do
  putStrLn " ++ MkOffset"
  readDyn v
  cur <- allocCursor loc
  addStaticSizeEndWitness loc "MkOffset"
  -- HINT: it is required that the target to be written, it will make the dereferenced value valid
  getWrittenCursor loc_in $ \cur_in => do
    putStrLn " ++ MkOffset - 1"
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
    putStrLn " ++ MkLeft - 1 - markWrite \{loc}"
    markWrite loc $ pure ()

fillDyn (MkRight arg) = do
  putStrLn " ++ MkRight"
  cur <- allocCursor loc
  emit "*(char*) \{cur} = 1; // RIGHT_TAG"
  fillDyn arg
  inheritEndWitness loc arg
  getWrittenCursor (getLoc arg) $ \_ => do
    putStrLn " ++ MkRight - 1 - markWrite \{loc}"
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
    putStrLn " ++ I64Op2 - 1"
    getWrittenCursor loc_in2 $ \cur_in2 => do
      putStrLn " ++ I64Op2 - 2"
      markWrite loc $ emit "*(int*) \{cur} = *(int*) \{cur_in1} \{op} *(int*) \{cur_in2}; // I64Op2"

fillDyn (I64Cmp op {loc_in1, loc_in2} arg1 arg2) = do
  putStrLn " ++ I64Cmp"
  readDyn arg1
  readDyn arg2
  cur <- allocCursor loc
  addStaticSizeEndWitness loc "I64Cmp - result"
  getWrittenCursor loc_in1 $ \cur_in1 => do
    putStrLn " ++ I64Cmp - 1"
    getWrittenCursor loc_in2 $ \cur_in2 => do
      putStrLn " ++ I64Cmp - 2"
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
    putStrLn " ++ Copy - 2"
    cur_src_end <- getEndWitness loc_in
    defineEndWitness loc "\{cur_dst} + (\{cur_src_end} - \{cur_src})" "Copy"
    markWrite loc $ emit "memcpy(\{cur_dst}, \{cur_src}, \{cur_src_end} - \{cur_src}); // Copy"

fillDyn (FunApp {fun_ews, loc_res} fun_name args) = do
  putStrLn " ++ FunApp \{fun_name}"
  readArgs args
  -- TODO: handle returning ews
  unless (null fun_ews) $ assert_total $ idris_crash $ "TODO - handle FunApp fun_ews"
  putStrLn " ++ FunApp \{fun_name} - 1"
  cur_out <- allocCursor loc_res
  let buildCall : List String -> Arg _ -> M ()
      buildCall curs (ArgN {loc_arg} _ a) = getWrittenCursor loc_arg $ \cur_in => putStrLn "FunApp \{fun_name} - arg - \{cur_in}" >> buildCall (cur_in :: curs) a
      buildCall curs Arg0 = markWrite loc_res $ defineEndWitness loc_res "\{fun_name}(\{joinBy ", " $ reverse curs}, \{cur_out})" "FunApp"
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
          buildParams act params paramDocs (ArgN {t, fun, n, loc_arg} e a) = do
            let loc_param = LocStart t $ MkArgRegion fun n
            cur_param <- newCursorName
            markAlreadyWritten loc_param $ markAlloc loc_param $ addCur cur_param loc_param

            putStrLn " ++ FunAppDef \{fun_name} - arg - add end-witness \{loc_param}"
            -- TODO: design proper arg end-witness handling
            let act2 = when (isJust $ getStaticSize $ getTy e) $ do
                        addStaticSizeEndWitness loc_param "FunAppDef - arg"

            buildParams (act >> act2) ("char* \{cur_param}" :: params) ("/* \{cur_param} = \{loc_param} */" :: paramDocs) a

      (act, params, paramDocs) <- buildParams (pure ()) [] [] args

      let toParams : {fun : _} -> Arg {fun} {n} a -> Arg {fun} {n} a
          toParams (Arg0) = Arg0
          toParams (ArgN {fun, t, n} e a) = ArgN {n, loc_arg=LocStart t $ MkArgRegion fun n} Var $ toParams {n} a

          paramDecls = joinBy ", " $ reverse params

      emitDecl "char* \{fun_name}(\{paramDecls}, char* \{cur_out});"
      emit "char* \{fun_name}(\{paramDecls}, char* \{cur_out}) {"
      indent $ do
        debug $ for_ paramDocs emit
        debug $ emit "/* \{cur_out} = \{loc_res} */"
        act -- TODO: design proper arg end-witness handling
        fillDyn {loc=loc_res} $ fun $ toParams {fun=fun_name} args
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
    putStrLn " ++ PrintI64 (read) - 1"
    emit "printf(\"%d\\n\", *(int*) \{cur_in});"
    evalCGMode mode $ cont ()

evalCont (PrintValue {loc_in} v cont) mode = do
  putStrLn " ++ PrintValue (read) - \{showLoExpTag v} loc: \{loc_in}"
  readDyn v
  putStrLn " ++ PrintValue (read) - 0"
  getWrittenCursor loc_in $ \cur_in => do
    putStrLn " ++ PrintValue (read) - 1"
    cur_end <- getEndWitness loc_in
    emit "print_hex(\{cur_in}, \{cur_end} - \{cur_in});"
    putStrLn " ++ PrintValue (read) - 0 - 1"
    evalCGMode mode $ cont ()

evalCont (DeRefOffset {x, r_in, loc_in} v cont) mode = do
  putStrLn " ++ DeRefPtr (read)"
  readDyn v
  getWrittenCursor loc_in $ \cur_in => do
    putStrLn " ++ DeRefPtr (read) - 1"
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
    putStrLn " ++ DeRefPtr - 1"
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

evalCont (CaseEither {a, b, loc_scrut, ew_scrut} scrut cont_left cont_right) mode = do
  lift $ putStrLn " ++ CaseEither scrut: \{loc_scrut} \{ew_scrut} \{mode} loc: \{loc} \{rw}"
  readDyn scrut
  getWrittenCursor loc_scrut $ \cur_tag => do
    lift $ putStrLn " ++ CaseEither \{loc_scrut} - 1  \{mode}"
    let locL = LocAfterTag "Left"  a loc_scrut
        locR = LocAfterTag "Right" b loc_scrut

    let cur_res_tmp     = "\{!(newCursorName)}_res_tmp"
        cur_end_tmp     = "\{cur_res_tmp}_end_tmp"
        cur_tag_end_tmp = "\{!(newCursorName)}_end_tmp"
    emit "char* \{cur_res_tmp} = 0; // uninitalized CaseEither result"
    emit "char* \{cur_end_tmp} = 0; // uninitalized CaseEither result end-witness"
    emit "char* \{cur_tag_end_tmp} = 0; // uninitalized CaseEither scrutinee end-witness"
{-
    cur20_res_tmp_end_tmp = cur25_end; // FIX
-}
    cg <- get
    emit "if (*(char*) \{cur_tag} == 0) { // LEFT"
    ({-(has_res_cur_left, scrut_ew_left), -}left_cglocal) <- indent $ localScope $ do
      _ <- markAlreadyWritten locL $ allocCursorIfNeeded locL
      let expL = cont_left Var
      evalCGMode mode expL
      putStrLn " LEFT finished - 1 \{mode}"
      -- Q: is this always needed or it depends on the mode?
      whenWritten loc $ do
        emit "\{cur_res_tmp} = \{!(getCursor loc)};"
        case rw of
          R NoEW => pure ()
          _      => emit "\{cur_end_tmp} = \{!(getEndWitness loc)};"
      {-
      case ew_scrut of
        EW    => emit "\{cur_tag_end_tmp} = \{!(getEndWitness locL)};"
        NoEW  => pure ()
      -}
      --case mode of
      --  FillDyn => emit "\{cur_end_tmp} = \{!(getEndWitness $ getLoc expL)};"
      --  ReadDyn => pure () -- TODO: what to do when it has end-witness?
      putStrLn " LEFT finished - 2"
      --getWrittenCursor (getLoc expL) $ \_ => do
      pure ({-!writeResAndScrutEW,-} !(gets (.local)))

    emit "} else { // RIGHT"
    ({-(has_res_cur_right, scrut_ew_right),-} right_cglocal) <- indent $ localScope $ do
      putStrLn " RIGHT finished - 1 \{mode}"
      _ <- markAlreadyWritten locR $ allocCursorIfNeeded locR
      --allocCursorIfNeeded
      putStrLn " RIGHT finished - 2 \{mode}"
      let expR = cont_right Var
      putStrLn " RIGHT finished - 3 \{mode}"
      evalCGMode mode expR
      putStrLn " RIGHT finished - 4 \{mode}"
      -- Q: is this always needed or it depends on the mode?
      whenWritten loc $ do
        emit "\{cur_res_tmp} = \{!(getCursor loc)};"
        case rw of
          R NoEW => pure ()
          _      => emit "\{cur_end_tmp} = \{!(getEndWitness loc)};"
      {-
      case ew_scrut of
        EW    => emit "\{cur_tag_end_tmp} = \{!(getEndWitness locR)};"
        NoEW  => pure ()
      -}


      --case ew_scrut of
      --  EW    => emit "\{cur_end_tmp} = \{!(getEndWitness $ getLoc expR)};"
      --  NoEW  => pure ()
      --case mode of
      --  FillDyn => emit "\{cur_end_tmp} = \{!(getEndWitness $ getLoc expR)};"
      --  ReadDyn => pure () -- TODO: what to do when it has end-witness?
      putStrLn " RIGHT finished - 2"
      pure ({-!writeResAndScrutEW,-} !(gets (.local)))
    emit "}"
    case mode of
      FillDyn => markWrite loc $ pure ()
      ReadDyn => pure ()

    --modify { local.read   $= union (intersection left_cglocal.read  right_cglocal.read)
    --       , local.write  $= union (intersection left_cglocal.write right_cglocal.write)
     --      }
    modify { local.read   $= union (intersection left_cglocal.read  right_cglocal.read)
           , local.write  $= union (union left_cglocal.write right_cglocal.write)
           }
    putStrLn "CaseEither - new locations left:\n\{ unlines . map show . Data.SortedSet.toList $ difference (fromList . keys $ left_cglocal.locations)  (fromList . keys $ cg.local.locations)}"
    putStrLn "CaseEither - new locations right:\n\{unlines . map show . Data.SortedSet.toList $ difference (fromList . keys $ right_cglocal.locations) (fromList . keys $ cg.local.locations)}"
    putStrLn "CaseEither - 1"

    {-
    lookupCursor loc >>= \case
      Just _  => do
        addCur cur_res_tmp loc
        setEndWitness loc cur_end_tmp -- TODO: is this mode dependent? or is it also ew dependent? figure this out
      Nothing => emit "/* CaseEither - TODO: missing cursor for \{loc}*/"
    -}
    --when (has_res_cur_left && has_res_cur_right) $ do
    --  addCur cur_res_tmp loc
    whenWritten loc $ do
      addCur cur_res_tmp loc
      case rw of
        R NoEW => pure ()
        _     => setEndWitness loc cur_end_tmp -- TODO: is this mode dependent? or is it also ew dependent? figure this out
    {-
    case ew_scrut of
      EW    => setEndWitness loc_scrut cur_tag_end_tmp
      NoEW  => pure ()
    -}
    putStrLn "CaseEither - 2"
    -- add end-witness for loc_scrut ; this can be done when both left and right eliminator has it
    --when (scrut_ew_left && scrut_ew_right) $ do
    --  defineEndWitness loc_scrut cur_tag_end_tmp "CaseEither - scrut"
    putStrLn "CaseEither - 3"

evalCont _ _ = assert_total $ idris_crash $ "evalCont TODO"

-----------------

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
  GenEW                 rdone
  PairEW                rdone
  LeftEW                rdone
  RightEW               rdone
-}

-- Q: should we traverse this? maybe yes, probably yes, because read arguments may contain LetRegionValues
readDyn (I64Cmp _ a b)= putStrLn " ++ I64Cmp (read)" >> readDyn a >> readDyn b
readDyn (I64Op2 _ a b)= putStrLn " ++ I64Op2 (read)" >> readDyn a >> readDyn b
readDyn (MkI64{})     = putStrLn " ++ MkI64 (read)"
readDyn (MkT0{})      = putStrLn " ++ MkT0 (read)"
readDyn (MkPtr a)     = putStrLn " ++ MkPtr (read)" >> readDyn a
readDyn (MkOffset a)  = putStrLn " ++ MkOffset (read)" >> readDyn a
readDyn (MkRight a)   = putStrLn " ++ MkRight (read)" >> readDyn a
readDyn (MkLeft a)    = putStrLn " ++ MkLeft (read)" >> readDyn a
readDyn (MkPair a b)  = putStrLn " ++ MkPair (read)" >> readDyn a >> readDyn b
readDyn (Copy v)      = putStrLn " ++ Copy (read)" >> readDyn v
readDyn (Var{})       = putStrLn " ++ Var (read)"
readDyn (FunAppDef _ _ a) = putStrLn " ++ FunAppDef (read)" >> readArgs a
readDyn (FunApp _ a)      = putStrLn " ++ FunApp (read)" >> readArgs a

readDyn (MkBox v) = putStrLn " ++ MkBox (read)" >> readDyn v
readDyn (UnBox v) = putStrLn " ++ UnBox (read)" >> readDyn v

readDyn e@(LetRegionValue{}) = evalCont e ReadDyn
readDyn e@(LetRegion{}) = evalCont e ReadDyn
readDyn e@(PrintI64{}) = evalCont e ReadDyn
readDyn e@(PrintValue{}) = evalCont e ReadDyn
readDyn e@(DeRefOffset{}) = evalCont e ReadDyn
readDyn e@(DeRefPtr{}) = evalCont e ReadDyn
readDyn e@(CaseEither{}) = evalCont e ReadDyn

readDyn (GetFst {a, loc_tup} tup) = do
  putStrLn " ++ GetFst (read)"
  readDyn tup
  getWrittenCursor loc_tup $ \_ => do
    putStrLn " ++ GetFst (read) - 1"
    let locFst = LocAfterTag "Pair" a loc_tup
    _ <- allocCursorIfNeeded locFst
    markAlreadyWritten locFst $ pure ()

readDyn (GetSnd {a, b, loc_tup} tup fst) = do
  putStrLn " ++ GetSnd (read)"
  readDyn tup
  readDyn fst
  getWrittenCursor (getLoc fst) $ \_ => do
    putStrLn " ++ GetSnd (read) - 1"
    let locFst = LocAfterTag "Pair" a loc_tup
        locSnd = LocAfter b locFst
    _ <- allocCursorIfNeeded locSnd
    markAlreadyWritten locSnd $ pure ()

readDyn (AddEW{}) = assert_total $ idris_crash $ "readDyn - AddEW"
readDyn (GetEWS{}) = assert_total $ idris_crash $ "readDyn - GetEWS"

readDyn (StaticEW v) = do
  putStrLn " ++ StaticEW (read)"
  readDyn v
  addStaticSizeEndWitness loc  "StaticEW"

readDyn (GenEW a) = do
  putStrLn " ++ GenEW (read)"
  readDyn a
  let t = getLocTy loc
  case getStaticSize t of
    Just _  => addStaticSizeEndWitness loc  "GenEW - StaticEW"
    Nothing => defineEndWitness loc "\{!(genTraversalEW a)}" "GenEW - \{show t}"
  case loc of
    -- snd
    LocAfter _ (LocAfterTag "Pair" _ loc_pair) => updateEndWitnessTo' loc_pair loc
    LocAfterTag "Left"  _ loc_scrut => updateEndWitnessTo' loc_scrut loc
    LocAfterTag "Right" _ loc_scrut => updateEndWitnessTo' loc_scrut loc
    _ => pure ()

readDyn (PairEW {loc_tup} _ snd) = putStrLn " ++ PairEW (read)" >> readDyn snd >> updateEndWitnessTo loc_tup snd
readDyn (LeftEW  {loc_scrut} _ a) = putStrLn " ++ LeftEW (read)" >> readDyn a >> updateEndWitnessTo loc_scrut a
readDyn (RightEW {loc_scrut} _ a) = putStrLn " ++ RightEW (read)" >> readDyn a >> updateEndWitnessTo loc_scrut a

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

public export partial
toBufferDyn : {t : _} -> Exp t (LocStart t (MkRegion (-1))) REW [] -> IO String
toBufferDyn {t} e = do
  print $ background Yellow " ---- CODEGEN ----\n"
  putStrLn ""
  s <- execStateT emptyCG $ do
    genFunction "main" $ do
      emit "void main() {"
      indent $ readDyn e
      assertNoActionsLeft
      emit "}"
  putStrLn " ---- CODE OUTPUT ----"
  pure $ unlines $ c_header :: [unlines (reverse funLines) | funLines <- s.decls :: values s.code]


partial public export
compileProgram : String -> Program -> IO String
compileProgram name (Main e) = do
  let fname = "test/\{name}.c"
  print $ background BrightRed " ---- CODEGEN \{fname} ----\n"
  src <- toBufferDyn e
  Right _ <- writeFile fname src
    | Left err => idris_crash (show err)
  (c_msg, 0) <- run "gcc -O3 \{fname} -o test/\{name}"
    | err => idris_crash (show err)
  putStrLn c_msg
  pure src
