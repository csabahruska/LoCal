module Dynamic

import LoCal
import Data.Maybe
import Data.SortedMap
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
  STup2 a b   => "STup2 (\{showTy a}) (\{showTy b})"
  RTup2 a b   => "RTup2 (\{showTy a}) (\{showTy b})"
  Either a b  => "Either (\{showTy a}) (\{showTy b})"
  I64         => "I64"
  Offset a    => "Offset (\{showTy a})"
  Ptr a       => "Ptr (\{showTy a})"
  Box i       => "Box"

Show Ty where show = showTy
Interpolation Ty where interpolate = show

showLoc : Loc r -> String
showLoc loc = case loc of
  LocStart t r => "LocStart (\{show t}) (\{show r})"
  LocAfter t l => "LocAfter (\{show t})\n (\{showLoc l})"
  LocAfterTag s t l => "LocAfterTag \{s} (\{show t})\n (\{showLoc l})"

Show (Loc r) where show = showLoc
Interpolation (Loc r) where interpolate = show

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

-- static index calculator

getStaticSize : Ty -> Maybe Int
getStaticSize = \case
  T0    => Just 0
  I64   => pure 8
  Offset _ => pure 8
  Ptr _ => pure 8
  STup2 a b => do
    sa <- getStaticSize a
    sb <- getStaticSize b
    pure (sa + sb)
  RTup2 a b => do
    sa <- getStaticSize a
    sb <- getStaticSize b
    pure (sa + sb) -- HINT: no indirection is needed when fst static size is known
  Either a b => do
    sa <- getStaticSize a
    sb <- getStaticSize b
    if sa == sb -- special case, when the left and right size matches and statically known
      then Just (1 + sa)
      else Nothing
  Box _ => Nothing

getLocTy : Loc r -> Ty
getLocTy (LocStart t _) = t
getLocTy (LocAfter t _) = t
getLocTy (LocAfterTag _ t _) = t

getLocRegion : {r : _} -> Loc r -> Region
getLocRegion {r} _ = r

isStaticSize : Ty -> Bool
isStaticSize t = isJust $ getStaticSize t

getRTupTagSize : Ty -> Int
getRTupTagSize fstTy = if isStaticSize fstTy then 0 else 8 -- no indirection to snd is needed when the static size of fst is known

-- TODO: return: relative base value and static offset, and the required runtime end witnesses
getStaticIndex : Loc r -> Maybe Int
getStaticIndex = \case
  LocStart _ _ => Just 0
  LocAfter _ l => do
    i <- getStaticIndex l
    s <- getStaticSize (getLocTy l)
    Just (i + s)
  LocAfterTag "STup2" _ l => do
    getStaticIndex l
  LocAfterTag "RTup2" fstTy l => do
    i <- getStaticIndex l
    Just (getRTupTagSize fstTy + i)
  LocAfterTag _ _ l => do
    i <- getStaticIndex l
    Just (1 + i)

data LocVal : Type where
  MkLocVal : {r : Region} -> (loc : Loc r) -> LocVal

-- codegen monad

record CGLocal where
  constructor MkCGLocal
  locations   : SortedMap String String
  endwitness  : SortedMap String String
  pointers    : SortedMap String LocVal
  funName     : String
  indentLevel : Nat

record CG where
  constructor MkCG
  -- global
  counter     : Int
  decls       : List String
  code        : SortedMap String (List String)
  local       : CGLocal

emptyCGLocal : CGLocal
emptyCGLocal = MkCGLocal
  { locations   = empty
  , endwitness  = empty
  , pointers    = empty
  , funName     = ""
  , indentLevel = 0
  }

emptyCG : CG
emptyCG = MkCG
  { counter     = 0
  , decls       = []
  , code        = empty
  , local       = emptyCGLocal
  }

M = StateT CG IO

{-
  IDEA:
    do not use the Size argument of the LocAfter constructor,
    instead every value should know it's size and provide it somehow to the locations that come after that
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

localScope : M a -> M a
localScope m = do
  locs <- gets (.local.locations)
  endws <- gets (.local.endwitness)
  res <- m
  modify {local.locations := locs, local.endwitness := endws}
  pure res

emit : String -> M ()
emit s = do
  cg <- get
  lift $ putStrLn "[\{cg.local.funName}] \{s}"
  modify {code $= insertWith (++) cg.local.funName [indent (cg.local.indentLevel * 2) s]}

emitDecl : String -> M ()
emitDecl s = do
  cg <- get
  lift $ putStrLn "[\{cg.local.funName}] \{s}"
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

getTy : {t : _} -> {0 l : Loc r} -> (Exp t l) -> Ty
getTy {t} _ = t

getLoc : {t : _} -> {l : Loc r} -> (Exp t l) -> Loc r
getLoc {l} _ = l

addCur : String -> Loc r -> M ()
addCur c l = modify {local.locations $= insert (show l) c}

addPointer : LocVal -> Loc r -> M ()
addPointer lv l = modify {local.pointers $= insert (show l) lv}

getPointer : (loc : Loc r) -> M LocVal
getPointer loc = do
  ptrs <- gets (.local.pointers)
  let Just lv = lookup (show loc) ptrs
        | Nothing => assert_total $ idris_crash $ "INTERNAL ERROR: missing LocVal for \{loc}"
  pure lv

-- IDEA: use Loc values in Map as keys via its show function

lookupEndWitness : (loc : Loc r) -> M (Maybe String)
lookupEndWitness loc = do
  ends <- gets (.local.endwitness)
  pure $ lookup (show loc) ends

getEndWitness : (loc : Loc r) -> M String
getEndWitness loc = do
  ends <- gets (.local.endwitness)
  let Just ew = lookup (show loc) ends
        | Nothing => assert_total $ idris_crash $ "INTERNAL ERROR: missing loc endwitness for \{loc}\n endwitness map: \{show ends}"
  pure ew

getCursor : (loc : Loc r) -> M String
getCursor loc = do
  locs <- gets (.local.locations)
  let Just cur = lookup (show loc) locs
        | Nothing => assert_total $ idris_crash $ "INTERNAL ERROR: missing loc cursor for \{loc}\n locations map: \{show locs}"
  pure cur

-- TODO: check that it is written only once ; use an effect map for LocVals
genCursor : {r :_ } -> (loc : Loc r) -> M String
genCursor {r} loc = do
  --lift $ putStrLn " !! gen cursor for \{loc}"
  let locKey = show loc
  {-
    gen new if does not exist
    return exisiting when available
  -}
  locs <- gets (.local.locations)
  let newCur = do
        c <- newCursorName
        lift $ print $ colored BrightRed " !! add cursor \{c} :=\n \{loc}\n\n"
        lift $ print $ colored BrightMagenta " !! static index \{c} := \{show (getStaticIndex loc)}\n\n"
        addCur c loc
        emit "/* \{c} = \{loc} */"
        pure c
  case lookup locKey !(gets (.local.locations)) of
    Just v  => do
      lift $ print $ colored BrightGreen " !! has cursor \{v} :=\n \{loc}\n\n"
      pure v
    Nothing => do
      case loc of
        LocStart _ (MkRegion ri) => assert_total $ idris_crash $ "INTERNAL ERROR: missing LocStart for region \{ri} locations: \{show locs}"
        LocAfter _ l => do
          c <- newCur
          emit "char* \{c} = \{!(getEndWitness l)}; // STATIC INDEX \{show (getStaticIndex loc)} in \{show (getLocRegion loc)}"
          pure c
        LocAfterTag s fstTy l => do
          let tagSize : Int = case s of
                "STup2" => 0
                "RTup2" => getRTupTagSize fstTy -- maybe an indirection for snd
                _       => 1
          c <- newCur
          emit "char* \{c} = \{!(getCursor l)} + \{tagSize}; // STATIC INDEX \{show (getStaticIndex loc)} in \{show (getLocRegion loc)}"
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

updateEndWitnessTo : {loc2 : _} -> (loc : Loc r) -> Exp _ loc2 -> M ()
updateEndWitnessTo {loc2} loc e = do
  ew <- getEndWitness loc2
  modify {local.endwitness $= insert (show loc) ew}
  lift $ print $ colored BrightBlue " update endwitness to \{ew} for\n \{loc}\n\n"

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
    lift $ print $ colored BrightCyan " add endwitness to \{ew} for\n \{l}\n\n"

tryAddStaticSizeEndWitness : Loc r -> String -> M ()
tryAddStaticSizeEndWitness loc msg = do
  when (isStaticSize (getLocTy loc)) $ do
    addStaticSizeEndWitness loc "Var"

defineRTup2FstEndWitness : {r : _} -> Loc r -> Ty -> M ()
defineRTup2FstEndWitness loc_tup a = do
  cur_tup <- genCursor loc_tup
  let locFst = LocAfterTag "RTup2" a loc_tup
  _ <- genCursor locFst
  case getStaticSize a of
    Just _  => do
      emit "// getStaticSize - true"
      addStaticSizeEndWitness locFst "RTup2 - static sized fst"
    Nothing => do
      emit "// getStaticSize - false"
      defineEndWitness locFst "\{cur_tup} + *(int*)\{cur_tup}; // get Snd cursor from RTup2" -- get random access pointer to snd

maybeSetEndWitness : Loc r -> Loc r -> M ()
maybeSetEndWitness loc value = do
  ends <- gets (.local.endwitness)
  case lookup (show value) ends of
    Nothing => pure () -- todo
    Just ew => modify {local.endwitness $= insert (show loc) ew}

-- TODO: rewrite to continuation passig style EDSL to avoid duplicated codegen, i.e. 'let i = MkI64 1 in MkRTup i (MkPtr i)' will set the value of i to 1 twice

partial fillDyn : {r : _ } -> {t : _ } -> {loc : Loc r} -> Exp t loc -> M ()

-- HINT: no end-witness definition is needed for static sized types

fillDyn (MkBox v) = do
  lift $ putStrLn " ++ MkBox"
  fillDyn v
  -- inherits end-witness

fillDyn (UnBox v) = do
  lift $ putStrLn " ++ UnBox"
  fillDyn v
  -- inherits end-witness

fillDyn MkT0 = do
  lift $ putStrLn " ++ MkT0"
  _ <- genCursor loc
  addStaticSizeEndWitness loc "MkT0"

fillDyn (MkI64 i) = do
  lift $ putStrLn " ++ MkI64 \{i}"
  cur <- genCursor loc
  emit "*(int*) \{cur} = \{i}; // MkI64"
  addStaticSizeEndWitness loc "MkI64"

fillDyn (MkSTup2 a b) = do
  lift $ putStrLn " ++ MkSTup2"
  cur <- genCursor loc
  fillDyn a
  fillDyn b
  updateEndWitnessTo loc b -- error if missing

fillDyn (MkRTup2 a b) = do
  lift $ putStrLn " ++ MkRTup2"
  cur <- genCursor loc -- cursor for RTup2, which is: indirection-to-snd/fst-endwitness + fst + snd
  fillDyn a
  unless (isStaticSize (getTy a)) $ do
    emit "*(int*) \{cur} = \{!(getEndWitness $ getLoc a)} - \{cur}; // RTup2 fst size in bytes"
  fillDyn b
  updateEndWitnessTo loc b -- error if missing

{-
  NOTES:
    effects:
      alloc - gen cursor + end witness
      write
      read

  TODO: track effects for locations
-}

fillDyn (MkPtr {loc_in} v) = do
  lift $ putStrLn " ++ MkPtr"
  --fillDyn v -- v is already generated, the CPS EDSL will fix this proper
  cur <- genCursor loc
  cur_in <- getCursor loc_in
  -- TODO: support forward pointers
  -- Q: how to decide if a location is after or before of another?
  -- A: it is possible to compute that from loctions
  --  TODO: write such a function
  emit "*(char**) \{cur} = \{cur_in};"
  addPointer (MkLocVal loc_in) loc
  addStaticSizeEndWitness loc "MkPtr"

fillDyn (MkOffset {loc_in} v) = do
  lift $ putStrLn " ++ MkOffset"
  --fillDyn v -- v is already generated, the CPS EDSL will fix this proper
  cur <- genCursor loc
  cur_in <- getCursor loc_in
  emit "*(int*) \{cur} = \{cur_in} - \{cur};"
  addPointer (MkLocVal loc_in) loc
  addStaticSizeEndWitness loc "MkOffset"

fillDyn (DeRef {r_in, loc_in} v cont) = do
  lift $ putStrLn " ++ DeRef"
  fillDyn v
  cur_in <- getCursor loc_in
  MkLocVal {r=r_val} loc_val <- getPointer loc_in
  cur <- genCursor loc_val
  emit "\{cur} = *(char**)\{cur_in}; // DeRef"
  fillDyn (cont r_val loc_val Var)

fillDyn (DeRefOffset {r_in, loc_in} v cont) = do
  lift $ putStrLn " ++ DeRefOffset"
  fillDyn v
  cur_in <- getCursor loc_in
  MkLocVal {r=r_val} loc_val <- getPointer loc_in
  case decEq r_val r_in of
    No _ => assert_total $ idris_crash $ "INTERNAL ERROR: DeRefOffset region mismatch \{r_val} should be \{r_in}"
    Yes Refl => do
      cur <- genCursor loc_val
      emit "\{cur} = \{cur_in} + *(int*)\{cur_in}; // DeRefOffset"
      fillDyn (cont loc_val Var)

fillDyn (MkLeft a) = do
  lift $ putStrLn " ++ MkLeft"
  cur <- genCursor loc
  emit "*(char*) \{cur} = 0; // LEFT_TAG"
  fillDyn a
  updateEndWitnessTo loc a -- error if missing

fillDyn (MkRight b) = do
  lift $ putStrLn " ++ MkRight"
  cur <- genCursor loc
  emit "*(char*) \{cur} = 1; // RIGHT_TAG"
  fillDyn b
  updateEndWitnessTo loc b -- error if missing
{-
  TODO: implement effect tracking and cursor and end-witness generation
  Q: should we get rid off LocBoxCorcion with removing Ty from Loc type?
      maybe i should try this out in a branch?
      what would i lose if only Exp would track types and not locations?
  A: yes, it makes the system simpler
-}

fillDyn (PrjFst {a, loc_tup} tup cont) = do
  lift $ putStrLn " ++ PrjFst"
  fillDyn tup
  defineRTup2FstEndWitness loc_tup a
  fillDyn (cont Var) -- Q: is Var unused? why? is the location that track values instead of binder names? A: YES

fillDyn (PrjSnd {a, b, loc_tup} tup cont) = do
  lift $ putStrLn " ++ PrjSnd"
  fillDyn tup
  defineRTup2FstEndWitness loc_tup a
  let locFst = LocAfterTag "RTup2" a loc_tup
      locSnd = LocAfter b locFst
  _ <- genCursor locSnd
  fillDyn (cont Var) -- Q: is Var unused? why? is the location that track values instead of binder names? A: YES
  -- try to set end-witness for RTup2 if snd was traversed
  maybeSetEndWitness loc_tup locSnd

fillDyn (AddI64 {loc_in, loc_in2} a b) = do
  lift $ putStrLn " ++ AddI64"
  fillDyn a
  fillDyn b
  cur <- genCursor loc
  cur_in <- getCursor loc_in
  cur_in2 <- getCursor loc_in2
  emit "*(int*) \{cur} = *(int*) \{cur_in} + *(int*) \{cur_in2};"
  addStaticSizeEndWitness loc_in  "AddI64 - arg1"
  addStaticSizeEndWitness loc_in2 "AddI64 - arg2"
  addStaticSizeEndWitness loc     "AddI64 - result"

fillDyn (EqI64 {loc_in, loc_in2} a b) = do
  lift $ putStrLn " ++ EqI64"
  fillDyn a
  fillDyn b
  cur <- genCursor loc
  cur_in <- getCursor loc_in
  cur_in2 <- getCursor loc_in2
  emit "if (*(int*) \{cur_in} == *(int*) \{cur_in2}) { // true"
  indent $ emit "*(char*) \{cur} = 1; // RIGHT_TAG"
  emit "} else { // false"
  indent $ emit "*(char*) \{cur} = 0; // LEFT_TAG"
  emit "}"
  addStaticSizeEndWitness loc_in  "EqI64 - arg1"
  addStaticSizeEndWitness loc_in2 "EqI64 - arg2"
  addStaticSizeEndWitness loc     "EqI64 - result"

fillDyn (PrintI64 {loc_in} a) = do
  lift $ putStrLn " ++ PrintI64"
  fillDyn a
  cur <- genCursor loc
  cur_in <- getCursor loc_in
  emit "printf(\"%d\\n\", *(int*) \{cur_in});"
  addStaticSizeEndWitness loc_in  "PrintI64 - arg1"
  addStaticSizeEndWitness loc     "PrintI64 - result"

fillDyn (PrintValue {loc_in} a) = do
  lift $ putStrLn " ++ PrintValue"
  fillDyn a
  cur <- genCursor loc
  cur_in <- getCursor loc_in
  cur_end <- getEndWitness loc_in
  emit "print_hex(\{cur_in}, \{cur_end} - \{cur_in});"
  addStaticSizeEndWitness loc "PrintValue - result"

fillDyn (LetRegion cont) = do
  lift $ putStrLn " ++ LetRegion"
  let r = MkRegion !newId
  fillDyn (cont r)

fillDyn (LetRegionValue {a,t} r v cont) = do
  lift $ putStrLn " ++ LetRegionValue"
  c <- newCursorName
  emit "char *\{c} = newRegion();"
  let loc_start = LocStart t r
  addCur c loc_start
  fillDyn {t=t} v
  tryAddStaticSizeEndWitness loc_start "LetRegionValue"
  fillDyn {t=a} (cont Var)

fillDyn (CaseSTup2 {a, b, loc_tup} tup cont) = do
  lift $ putStrLn " ++ CaseSTup2"
  fillDyn tup
  fillDyn (cont Var Var)
  -- create tup end-witness
  let locFst = LocAfterTag "STup2" a loc_tup
      locSnd = LocAfter b locFst
  _ <- genCursor locSnd
  -- try to set end-witness for STup2 if snd was traversed
  maybeSetEndWitness loc_tup locSnd

--TODO: example for stup2 where an int pair is created and passed to a function that prints the fst and snd ; also create an error case that prints only the snd or snd then fst

fillDyn (CaseEither {scrut_loc} scrut cont_left cont_right) = do
  lift $ putStrLn " ++ CaseEither"
  fillDyn scrut
  cur <- genCursor loc
  let cur_end_tmp = "\{!(newCursorName)}_end_tmp"
  emit "char* \{cur_end_tmp} = 0; // uninitalized"
  cur_tag <- getCursor scrut_loc

  let cur_tag_end_tmp = "\{cur_tag}_end_tmp"
  emit "char* \{cur_tag_end_tmp} = 0; // uninitalized"

  emit "if (*(char*) \{cur_tag} == 0) { // LEFT"
  scrut_ew_left <- indent $ localScope $ do
    let expL = cont_left Var
    fillDyn expL
    emit "\{cur_end_tmp} = \{!(getEndWitness $ getLoc expL)};"
    scrut_ew <- lookupEndWitness scrut_loc
    case scrut_ew of
      Nothing => pure ()
      Just ew => emit "\{cur_tag_end_tmp} = \{ew};"
    pure $ isJust scrut_ew
  emit "} else { // RIGHT"
  scrut_ew_right <- indent $ localScope $ do
    let expR = cont_right Var
    fillDyn expR
    emit "\{cur_end_tmp} = \{!(getEndWitness $ getLoc expR)};"
    scrut_ew <- lookupEndWitness scrut_loc
    case scrut_ew of
      Nothing => pure ()
      Just ew => emit "\{cur_tag_end_tmp} = \{ew};"
    pure $ isJust scrut_ew
  emit "}"
  defineEndWitness loc cur_end_tmp
  -- add end-witness for scrut_loc ; this can be done when both left and right eliminator has it
  when (scrut_ew_left && scrut_ew_right) $ do
    defineEndWitness scrut_loc cur_tag_end_tmp

fillDyn (Copy {r_in, loc_in} _) = do
  lift $ putStrLn " ++ Copy"
  cur_src <- getCursor loc_in
  cur_dst <- genCursor loc
  cur_src_end <- getEndWitness loc_in
  emit "memcpy(\{cur_dst}, \{cur_src}, \{cur_src_end} - \{cur_src});"
  defineEndWitness loc "\{cur_dst} + (\{cur_src_end} - \{cur_src})"

fillDyn Var = do
  cur <- genCursor loc
  emit "/* \{cur} = \{loc} */"
  emit "// Var \{t}" -- assert_total $ idris_crash $ "Var"
  tryAddStaticSizeEndWitness loc "Var"

fillDyn (FunApp {loc_in} fun_name fun arg) = do
  lift $ putStrLn " ++ FunApp \{fun_name}"
  fillDyn arg
  cur_out <- genCursor loc
  cur_in <- getCursor loc_in
  -- HINT: fun may or may not need arg end witness
  --    Q: how to handle this?
  --    A: arg end-witness is not needed

  -- TODO: omit end-witness for static sized outputs
  defineEndWitness loc "\{fun_name}(\{cur_in}, \{cur_out})"
  -- codegen function if needed
  when !(isNewFunction fun_name) $ do
    genFunction fun_name $ do
      -- TODO: support multi parameter functions
      -- TODO: pass arg's pointers entry if any
      cur_arg <- newCursorName
      addCur cur_arg loc_in
      cur_out <- newCursorName
      addCur cur_out loc
      emitDecl "char* \{fun_name}(char* \{cur_arg}, char* \{cur_out});"
      emit "char* \{fun_name}(char* \{cur_arg}, char* \{cur_out}) {"
      indent $ do
        emit "/* \{cur_arg} = \{loc_in} */"
        emit "/* \{cur_out} = \{loc} */"
        tryAddStaticSizeEndWitness loc_in "fun arg"
        fillDyn (fun Var)
        emit "return \{!(getEndWitness loc)};"
      emit "}"

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
toBufferDyn : {t : _} -> Exp t (LocStart t (MkRegion (-1))) -> IO String
toBufferDyn {t} e = do
  print $ background Yellow " ---- CODEGEN ----"
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
  src <- toBufferDyn e
  let fname = name ++ ".c"
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
