module Dynamic

import LoCal
--import Instances
import Data.Maybe
import Data.SortedMap
import Data.String
import Control.Monad.State
import Data.Primitives.Interpolation
import Control.ANSI


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
  DecTy n     => "DecTy \{n}"
  DefTy a b c => "DefTy (\{showTy a}) (\{showTy b}) (\{showTy c})"

Show Ty where show = showTy
Interpolation Ty where interpolate = show

showLoc : Loc r t -> String
showLoc loc = case loc of
  LocStart t r => "LocStart (\{show t}) (\{show r})"
  LocAfter t l => "LocAfter (\{show t})\n (\{showLoc l})"
  LocAfterTag s t l => "LocAfterTag \{s} (\{show t})\n (\{showLoc l})"

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
  DecTy _ => Nothing
  DefTy _ _ a => getStaticSize a
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

-- codegen monad

record CG where
  constructor MkCG
  counter     : Int
  locations   : SortedMap String String
  endwitness  : SortedMap String String
  code        : List String
  indentLevel : Nat

emptyCG : CG
emptyCG = MkCG
  { counter     = 0
  , locations   = empty
  , endwitness  = empty
  , code        = []
  , indentLevel = 0
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
  l <- gets (.indentLevel)
  modify {indentLevel $= (+ 1)}
  res <- m
  modify {indentLevel := l}
  pure res

localScope : M a -> M a
localScope m = do
  locs <- gets (.locations)
  endws <- gets (.endwitness)
  res <- m
  modify {locations := locs, endwitness := endws}
  pure res

emit : String -> M ()
emit s = do
  cg <- get
  lift $ putStrLn s
  modify {code $= (::) (indent (cg.indentLevel * 2) s)}

getTy : {t : _} -> {0 l : Loc r t} -> (Exp t l) -> Ty
getTy {t} _ = t

getLoc : {t : _} -> {l : Loc r t} -> (Exp t l) -> Loc r t
getLoc {l} _ = l

addCur : String -> Loc r t -> M ()
addCur c l = modify {locations $= insert (show l) c}

-- IDEA: use Loc values in Map as keys via its show function

getEndWitness : (loc : Loc r t) -> M String
getEndWitness loc = do
  ends <- gets endwitness
  let Just ew = lookup (show loc) ends
        | Nothing => assert_total $ idris_crash $ "INTERNAL ERROR: missing loc endwitness for \{loc}\n endwitness map: \{show ends}"
  pure ew

getCursor : (loc : Loc r t) -> M String
getCursor loc = do
  locs <- gets locations
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
  locs <- gets locations
  let newCur = do
        c <- newCursorName
        lift $ print $ colored BrightRed " !! add cursor \{c} :=\n \{loc}\n\n"
        lift $ print $ colored BrightMagenta " !! static index \{c} := \{show (getStaticIndex loc)}\n\n"
        addCur c loc
        pure c
  case lookup locKey !(gets locations) of
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

defineEndWitness : (loc : Loc r t) -> String -> M ()
defineEndWitness loc value = do
  cur <- getCursor loc
  let ew = "\{cur}_end"
  modify {endwitness $= insert (show loc) ew}
  emit "char* \{ew} = \{value};"

declareEndWitness : (loc : Loc r t) -> M String
declareEndWitness loc = do
  cur <- getCursor loc
  let ew = "\{cur}_end"
  modify {endwitness $= insert (show loc) ew}
  emit "char* \{ew} = 0; // uninitialized"
  pure ew

setEndWitnessTo : {loc2 : _} -> String -> Exp _ loc2 -> M ()
setEndWitnessTo {loc2} ew _ = do
  ew2 <- getEndWitness loc2
  emit "\{ew} = \{ew2};"

updateEndWitnessTo : {loc2 : _} -> (loc : Loc r t) -> Exp _ loc2 -> M ()
updateEndWitnessTo {loc2} loc e = do
  ew <- getEndWitness loc2
  modify {endwitness $= insert (show loc) ew}
  lift $ print $ colored BrightBlue " update endwitness to \{ew} for\n \{loc}\n\n"

addStaticSizeEndWitness : (loc : Loc r t) -> Int -> String -> M ()
addStaticSizeEndWitness l bytes msg = do
  cur <- getCursor l
  let ew = "\{cur}_end"
  modify {endwitness $= insert (show l) ew}
  emit "char* \{ew} = \{cur} + \{bytes}; // \{msg}"
  lift $ print $ colored BrightCyan " add endwitness to \{ew} for\n \{l}\n\n"

partial fillDyn : {r : _ } -> {t : _ } -> {loc : Loc r t} -> Exp t loc -> M ()
fillDyn {r} {loc} (MkI64 i) = do
  lift $ putStrLn " ++ MkI64 \{i}"
  cur <- genCursor loc
  addStaticSizeEndWitness loc 8 "I64"
  emit "*(int*) \{cur} = \{i};"

fillDyn {loc} (MkSTup2 a b) = do
  lift $ putStrLn " ++ MkSTup2"
  cur <- genCursor loc
  fillDyn a
  fillDyn b
  updateEndWitnessTo loc b

fillDyn {loc} (MkRTup2 a b) = do
  lift $ putStrLn " ++ MkRTup2"
  cur <- genCursor loc -- cursor for RTup2, which is: indirection-to-snd/fst-endwitness + fst + snd
  fillDyn a
  when (isStaticSize (getTy a)) $ do
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

fillDyn {loc} (MkInd {loc_in} _) = do
  lift $ putStrLn " ++ MkInd"
  cur <- genCursor loc
  addStaticSizeEndWitness loc 8 "Ind" -- 64 bit pointer
  cur_in <- getCursor loc_in
  -- TODO: support forward pointers
  -- Q: how to decide if a location is after or before of another?
  -- A: it is possible to compute that from loctions
  --  TODO: write such a function
  emit "*(char**) \{cur} = \{cur_in};"

fillDyn {loc} (MkIndLong {loc_in} _) = do
  lift $ putStrLn " ++ MkIndLong"
  cur <- genCursor loc
  addStaticSizeEndWitness loc 8 "IndLong" -- 64 bit pointer
  cur_in <- getCursor loc_in
  emit "*(char**) \{cur} = \{cur_in};"

fillDyn {loc} (MkLeft a) = do
  lift $ putStrLn " ++ MkLeft"
  cur <- genCursor loc
  emit "*(char*) \{cur} = 0; // LEFT_TAG"
  fillDyn a
  updateEndWitnessTo loc a

fillDyn {loc} (MkRight b) = do
  lift $ putStrLn " ++ MkRight"
  cur <- genCursor loc
  emit "*(char*) \{cur} = 1; // RIGHT_TAG"
  fillDyn b
  updateEndWitnessTo loc b

fillDyn (PrjFst {r} a cont) = do
  lift $ putStrLn " ++ PrjFst"
  fillDyn a
  fillDyn (cont Var) -- Q: is Var unused? why? is the location that track values instead of binder names? A: YES
fillDyn (PrjSnd {a, loc} tup cont) = do
  lift $ putStrLn " ++ PrjSnd"
  fillDyn tup
  let locFst = LocAfterTag "RTup2" a loc
  case getStaticSize a of
    Just s  => addStaticSizeEndWitness locFst s "static index for RTup2Snd"
    Nothing => defineEndWitness locFst "*(char**)\{!(getCursor loc)}; // get Snd cursor from RTup2" -- get random access pointer to snd
  fillDyn (cont Var) -- Q: is Var unused? why? is the location that track values instead of binder names? A: YES

fillDyn {loc} (PrintI64 {loc_in} a) = do
  lift $ putStrLn " ++ PrintI64"
  fillDyn a
  cur <- genCursor loc
  addStaticSizeEndWitness loc 0 "T0"
  cur_in <- getCursor loc_in
  emit "printf(\"%ld\\n\", *(int*) \{cur_in});"

fillDyn {t} (LetRegion cont) = do
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
fillDyn {loc} (CaseEither {scrut_loc} scrut cont_left cont_right) = do
  lift $ putStrLn " ++ CaseEither"
  fillDyn scrut
  cur <- genCursor loc
  cur_end <- declareEndWitness loc
  cur_tag <- getCursor scrut_loc
  emit "if (*(char*) \{cur_tag} == 0) { // LEFT"
  indent $ localScope $ do
    let expL = cont_left Var
    fillDyn expL
    setEndWitnessTo cur_end expL
  emit "} else { // RIGHT"
  indent $ localScope $ do
    let expR = cont_right Var
    fillDyn expR
    setEndWitnessTo cur_end expR
  emit "}"

fillDyn {loc} (Copy {r_in, loc_in} _) = do
  lift $ putStrLn " ++ Copy"
  cur_src <- getCursor loc_in
  cur_dst <- genCursor loc
  cur_src_end <- getEndWitness loc_in
  emit "memcpy(\{cur_dst}, \{cur_src}, \{cur_src_end} - \{cur_src});"

fillDyn {t} Var = emit "// Var \{t}" -- assert_total $ idris_crash $ "Var"

partial public export
toBufferDyn : {t : _} -> Exp t (LocStart t (MkRegion (-1))) -> IO String
toBufferDyn {t} e = do
  print $ background Yellow " ---- CODEGEN ----"
  putStrLn ""
  s <- execStateT emptyCG $ do
    fillDyn $ LetRegionValue (MkRegion (-1)) e id
  putStrLn " ---- CODE OUTPUT ----"
  pure $ unlines $ reverse s.code

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
    - write full value traversal checker function, which would tell the unaccessed locations
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
    - LoCal nuresry has the same role as the ALLOC/READ/WRITE effect system
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

  TODO:
    - implement traversal effect calculation
    - insert explicit endwitness computation method to locations which will set the semantics and layout

  Q: could the endwitness strategy be included as an Exp or location index?
     with this LoCal would describe the exact layout and cursor calculus would not be needed
  Q: should require full traverse effect in LoCal? could it be modeled with endwitness strategy encoding?

  IDEA:
    enforce full structure traversal by construction, with Tup2 eliminator in LoCal

  Q: which design is better?
    a) linear cursor passing
    b) sequence of statically indexed blocks with dynamic base index

  IDEA:
    done - add two kind of tules: SerialTup2 (STup2) and RandomAccessTup2 (RTup2)
  TODO:
    done - allocate RTup2 snd indirection only when fst size is not statically known
-}
