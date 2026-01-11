module Dynamic

import LoCal
--import Instances
import Data.List.Elem
import Data.Maybe
import Data.SortedMap
import Data.SortedSet
import Data.String
import Control.Monad.State
import Data.Primitives.Interpolation
import Control.ANSI

data Effect = Read | Write | Allocated | Traversed

ordTagEffect : Effect -> Int
ordTagEffect Read       = 0
ordTagEffect Write      = 1
ordTagEffect Allocated  = 2
ordTagEffect Traversed  = 3

Eq Effect where a == b = ordTagEffect a == ordTagEffect b
Ord Effect where compare a b = compare (ordTagEffect a) (ordTagEffect b)

showEffect : Effect -> String
showEffect = \case
  Read      => "Read"
  Write     => "Write"
  Allocated => "Allocated"
  Traversed => "Traversed"

Show Effect where show = showEffect
Interpolation Effect where interpolate = show

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
  Ind a       => "Ind (\{showTy a})"
  BoxTy i     => "BoxTy \{elemToNat i}"

Show Ty where show = showTy
Interpolation Ty where interpolate = show

showLoc : Loc r t -> String
showLoc loc = case loc of
  LocStart t r => "LocStart (\{show t}) (\{show r})"
  LocAfter t l => "LocAfter (\{show t})\n (\{showLoc l})"
  LocAfterTag s t l => "LocAfterTag \{s} (\{show t})\n (\{showLoc l})"
  LocBoxCoerce t l => "LocBoxCoerce (\{show t})\n (\{showLoc l})"

Show (Loc r t) where show = showLoc
Interpolation (Loc r t) where interpolate = show

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
  Ind _ => pure 8
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
  BoxTy _ => Nothing

{-
data LocItem : Type where
  MkLocItem : Loc r t -> LocItem

RevLoc = List LocItem
--RevLoc2 = List (r : Region ** (t : Ty ** Loc r t))

mkRevLoc : Loc r t -> RevLoc
mkRevLoc loc = case loc of
  LocStart _ _ => [MkLocItem loc]
  LocAfter _ l => mkRevLoc l ++ [MkLocItem loc]
  LocAfterTag _ _ l => mkRevLoc l ++ [MkLocItem loc]
-}
getLocTy : Loc r t -> Ty
getLocTy (LocStart t _) = t
getLocTy (LocAfter t _) = t
getLocTy (LocAfterTag _ t _) = t
getLocTy (LocBoxCoerce t _) = t

getLocRegion : {r : _} -> Loc r t -> Region
getLocRegion {r} _ = r

isStaticSize : Ty -> Bool
isStaticSize t = isJust $ getStaticSize t

getRTupTagSize : Ty -> Int
getRTupTagSize fstTy = if isStaticSize fstTy then 0 else 8 -- no indirection to snd is needed when the static size of fst is known

-- TODO: return: relative base value and static offset, and the required runtime end witnesses
getStaticIndex : Loc r t -> Maybe Int
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
  LocBoxCoerce _ _ => Nothing

-- codegen monad

record CGLocal where
  constructor MkCGLocal
  locations   : SortedMap String String
  endwitness  : SortedMap String String
  effects     : SortedMap String (SortedSet Effect)
  funName     : String
  indentLevel : Nat

record CG where
  constructor MkCG
  -- global
  counter     : Int
  code        : SortedMap String (List String)
  local       : CGLocal

emptyCGLocal : CGLocal
emptyCGLocal = MkCGLocal
  { locations   = empty
  , endwitness  = empty
  , effects     = empty
  , funName     = ""
  , indentLevel = 0
  }

emptyCG : CG
emptyCG = MkCG
  { counter     = 0
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

getTy : {t : _} -> {0 l : Loc r t} -> (Exp t l) -> Ty
getTy {t} _ = t

getLoc : {t : _} -> {l : Loc r t} -> (Exp t l) -> Loc r t
getLoc {l} _ = l

addCur : String -> Loc r t -> M ()
addCur c l = modify {local.locations $= insert (show l) c}

-- effect handling
addEffect : (loc : Loc r t) -> Effect -> M ()
addEffect _ _ = pure () -- TODO

reqEffect : (loc : Loc r t) -> Effect -> M ()
reqEffect _ _ = pure () -- TODO

getEffect : (loc : Loc r t) -> M (SortedSet Effect)
getEffect loc = do
  effs <- gets (.local.effects)
  let Just eff = lookup (show loc) effs
        | Nothing => assert_total $ idris_crash $ "INTERNAL ERROR: missing loc cursor for \{loc}\n effect map: \{show effs}"
  pure eff


-- IDEA: use Loc values in Map as keys via its show function

getEndWitness : (loc : Loc r t) -> M String
getEndWitness loc = do
  ends <- gets (.local.endwitness)
  let Just ew = lookup (show loc) ends
        | Nothing => assert_total $ idris_crash $ "INTERNAL ERROR: missing loc endwitness for \{loc}\n endwitness map: \{show ends}"
  pure ew

getCursor : (loc : Loc r t) -> M String
getCursor loc = do
  locs <- gets (.local.locations)
  let Just cur = lookup (show loc) locs
        | Nothing => assert_total $ idris_crash $ "INTERNAL ERROR: missing loc cursor for \{loc}\n locations map: \{show locs}"
  pure cur

-- TODO: check that it is written only once ; use an effect map for LocVals
genCursor : {r :_ } -> (loc : Loc r t) -> M String
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
        LocBoxCoerce _ l => genCursor l

defineEndWitness : (loc : Loc r t) -> String -> M ()
defineEndWitness loc value = do
  cur <- getCursor loc
  let ew = "\{cur}_end"
  modify {local.endwitness $= insert (show loc) ew}
  emit "char* \{ew} = \{value};"

updateEndWitnessTo : {loc2 : _} -> (loc : Loc r t) -> Exp _ loc2 -> M ()
updateEndWitnessTo {loc2} loc e = do
  ew <- getEndWitness loc2
  modify {local.endwitness $= insert (show loc) ew}
  lift $ print $ colored BrightBlue " update endwitness to \{ew} for\n \{loc}\n\n"

addStaticSizeEndWitness : {t : _} -> (loc : Loc r t) -> String -> M ()
addStaticSizeEndWitness {t} l msg = do
  let Just bytes = getStaticSize t
        | Nothing => assert_total $ idris_crash $ "INTERNAL ERROR: missing statis size for: \{l}"
  cur <- getCursor l
  let ew = "\{cur}_end"
  modify {local.endwitness $= insert (show l) ew}
  emit "char* \{ew} = \{cur} + \{bytes}; // \{msg}"
  lift $ print $ colored BrightCyan " add endwitness to \{ew} for\n \{l}\n\n"

partial fillDyn : {r : _ } -> {t : _ } -> {loc : Loc r t} -> Exp t loc -> M ()
fillDyn (Box {i} v) = do
  lift $ putStrLn " ++ Box \{elemToNat i}"
  addCur !(genCursor loc) (getLoc v)
  fillDyn v
  updateEndWitnessTo loc v

fillDyn (UnBox {i} v) = do
  lift $ putStrLn " ++ UnBox \{elemToNat i}"
  addCur !(genCursor loc) (getLoc v)
  fillDyn v
  updateEndWitnessTo loc v

fillDyn MkT0 = do
  lift $ putStrLn " ++ MkT0"
  cur <- genCursor loc
  addStaticSizeEndWitness loc "T0"

fillDyn (MkI64 i) = do
  lift $ putStrLn " ++ MkI64 \{i}"
  cur <- genCursor loc
  addStaticSizeEndWitness loc "I64"
  emit "*(int*) \{cur} = \{i};"

fillDyn (MkSTup2 a b) = do
  lift $ putStrLn " ++ MkSTup2"
  cur <- genCursor loc
  fillDyn a
  fillDyn b
  updateEndWitnessTo loc b

fillDyn (MkRTup2 a b) = do
  lift $ putStrLn " ++ MkRTup2"
  cur <- genCursor loc -- cursor for RTup2, which is: indirection-to-snd/fst-endwitness + fst + snd
  fillDyn a
  unless (isStaticSize (getTy a)) $ do
    emit "*(char**) \{cur} = \{!(getEndWitness $ getLoc a)};"
  fillDyn b
  updateEndWitnessTo loc b

{-
  NOTES:
    effects:
      alloc - gen cursor + end witness
      write
      read

  TODO: track effects for locations
-}

fillDyn (MkInd {loc_in} _) = do
  lift $ putStrLn " ++ MkInd"
  cur <- genCursor loc
  addStaticSizeEndWitness loc "Ind" -- 64 bit pointer
  cur_in <- getCursor loc_in
  -- TODO: support forward pointers
  -- Q: how to decide if a location is after or before of another?
  -- A: it is possible to compute that from loctions
  --  TODO: write such a function
  emit "*(char**) \{cur} = \{cur_in};"

fillDyn (MkIndLong {loc_in} _) = do
  lift $ putStrLn " ++ MkIndLong"
  cur <- genCursor loc
  addStaticSizeEndWitness loc "IndLong" -- 64 bit pointer
  cur_in <- getCursor loc_in
  emit "*(char**) \{cur} = \{cur_in};"

fillDyn (MkLeft a) = do
  lift $ putStrLn " ++ MkLeft"
  cur <- genCursor loc
  emit "*(char*) \{cur} = 0; // LEFT_TAG"
  fillDyn a
  updateEndWitnessTo loc a

fillDyn (MkRight b) = do
  lift $ putStrLn " ++ MkRight"
  cur <- genCursor loc
  emit "*(char*) \{cur} = 1; // RIGHT_TAG"
  fillDyn b
  updateEndWitnessTo loc b

fillDyn (PrjFst a cont) = do
  lift $ putStrLn " ++ PrjFst"
  fillDyn a
  fillDyn (cont Var) -- Q: is Var unused? why? is the location that track values instead of binder names? A: YES
  -- Q: is endwintness needed for fst?
fillDyn (PrjSnd {a, loc_tup} tup cont) = do
  lift $ putStrLn " ++ PrjSnd"
  fillDyn tup
  let locFst = LocAfterTag "RTup2" a loc_tup
  case getStaticSize a of
    Just _  => addStaticSizeEndWitness locFst "static index for RTup2Snd"
    Nothing => defineEndWitness locFst "*(char**)\{!(getCursor loc)}; // get Snd cursor from RTup2" -- get random access pointer to snd
  fillDyn (cont Var) -- Q: is Var unused? why? is the location that track values instead of binder names? A: YES
  -- Q: is endwintness needed for snd?

fillDyn (AddI64 {loc_in, loc_in2} a b) = do
  lift $ putStrLn " ++ AddI64"
  fillDyn a
  fillDyn b
  cur <- genCursor loc
  addStaticSizeEndWitness loc "I64"
  cur_in <- getCursor loc_in
  cur_in2 <- getCursor loc_in2
  emit "*(int*) \{cur} = *(int*) \{cur_in} + *(int*) \{cur_in2};"

fillDyn (EqI64 {loc_in, loc_in2} a b) = do
  lift $ putStrLn " ++ EqI64"
  fillDyn a
  fillDyn b
  cur <- genCursor loc
  addStaticSizeEndWitness loc "Either T0 T0 (alias Bool)"
  cur_in <- getCursor loc_in
  cur_in2 <- getCursor loc_in2
  emit "if (*(int*) \{cur_in} == *(int*) \{cur_in2}) { // true"
  indent $ emit "*(char*) \{cur} = 1; // RIGHT_TAG"
  emit "} else { // false"
  indent $ emit "*(char*) \{cur} = 0; // LEFT_TAG"
  emit "}"

fillDyn (PrintI64 {loc_in} a) = do
  lift $ putStrLn " ++ PrintI64"
  fillDyn a
  cur <- genCursor loc
  addStaticSizeEndWitness loc "T0"
  cur_in <- getCursor loc_in
  emit "printf(\"%ld\\n\", *(int*) \{cur_in});"

fillDyn (LetRegion cont) = do
  lift $ putStrLn " ++ LetRegion"
  let r = MkRegion !newId
  fillDyn (cont r)

fillDyn (LetRegionValue {a,t} r v cont) = do
  lift $ putStrLn " ++ LetRegionValue"
  c <- newCursorName
  emit "char *\{c} = newRegion();"
  addCur c (LocStart t r)
  fillDyn {t=t} v
  fillDyn {t=a} (cont Var)

--  LetRegionValue : (r : Region) -> Exp t (LocStart t r) -> (Exp t (LocStart t r) -> Exp a loc) -> Exp a loc
{-
fillDyn (Let {r_in} {loc_in} a cont) = fillDyn {r=r_in} {loc=loc_in} a >> fillDyn (cont a)
-}
fillDyn (CaseEither {scrut_loc} scrut cont_left cont_right) = do
  lift $ putStrLn " ++ CaseEither"
  fillDyn scrut
  cur <- genCursor loc
  let cur_end_tmp = "\{!(newCursorName)}_end_tmp"
  emit "char* \{cur_end_tmp} = 0; // uninitalized"
  cur_tag <- getCursor scrut_loc
  emit "if (*(char*) \{cur_tag} == 0) { // LEFT"
  indent $ localScope $ do
    let expL = cont_left Var
    fillDyn expL
    emit "\{cur_end_tmp} = \{!(getEndWitness $ getLoc expL)};"
  emit "} else { // RIGHT"
  indent $ localScope $ do
    let expR = cont_right Var
    fillDyn expR
    emit "\{cur_end_tmp} = \{!(getEndWitness $ getLoc expR)};"
  emit "}"
  defineEndWitness loc cur_end_tmp

fillDyn (Copy {r_in, loc_in} _) = do
  lift $ putStrLn " ++ Copy"
  cur_src <- getCursor loc_in
  cur_dst <- genCursor loc
  cur_src_end <- getEndWitness loc_in
  emit "memcpy(\{cur_dst}, \{cur_src}, \{cur_src_end} - \{cur_src});"
  defineEndWitness loc "\{cur_dst} + (\{cur_src_end} - \{cur_src})"

fillDyn Var = emit "// Var \{t}" -- assert_total $ idris_crash $ "Var"

fillDyn (FunApp2 {loc_in} fun_name fun arg) = do
  lift $ putStrLn " ++ FunApp2 \{fun_name}"
  fillDyn arg
  cur_out <- genCursor loc
  cur_in <- getCursor loc_in
  -- TODO: omit end-witness for static sized outputs
  -- TODO: addStaticSizeEndWitness loc "T0"
  defineEndWitness loc "\{fun_name}(\{cur_in}, \{cur_out})"
  -- codegen function if needed
  when !(isNewFunction fun_name) $ do
    genFunction fun_name $ do
      cur_arg <- newCursorName
      addCur cur_arg loc_in
      cur_out <- newCursorName
      addCur cur_out loc
      emit "char* \{fun_name}(char* \{cur_arg}, char* \{cur_out}) {"
      indent $ do
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
  pure $ unlines $ c_header :: [unlines (reverse funLines) | funLines <- values s.code]

partial public export
compileProgram : Program -> IO String
compileProgram (Main3 e) = toBufferDyn e
--  Main3  : {res : Ty} -> Exp res (LocStart res (MkRegion (-4))) -> Program

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
    - separate offsets and pointers
    - add functions
    SKIP - write full value traversal checker function, which would tell the unaccessed locations ; not possible in LoCal RTup2/STup2 is to make this explicit
    - add high level language and map it to local
      + for first use fully pointer based approach with a bump allocator region allocator
    - support dec/def types

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
-}
