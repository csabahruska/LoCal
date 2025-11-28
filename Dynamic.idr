module Dynamic

import LoCal
--import Instances
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
  Tup2 a b    => "Tup2 (\{showTy a}) (\{showTy b})"
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
    - fully dynamic cursor passing and size calculation
    - interpreter based static improvements
-}

-- TODO: dynamic fill ; in a separate function
{-
  + the location expression tells how to serialize cursor passing
  TODO:
    - use monad stack to store region/cursor environment
-}

record CG where
  constructor MkCG
  counter     : Int
  locations   : SortedMap String String
  endwitness  : SortedMap String String
  locSize     : SortedMap String Int
  code        : List String
  indentLevel : Nat

emptyCG : CG
emptyCG = MkCG
  { counter     = 0
  , locations   = empty
  , endwitness  = empty
  , locSize     = empty
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

emit : String -> M ()
emit s = do
  cg <- get
  lift $ putStrLn s
  modify {code $= (::) (indent (cg.indentLevel * 2) s)}

getTy : {t : _} -> {0 l : Loc r t} -> (Exp t l) -> Ty
getTy {t} _ = t

addCur : String -> Loc r t -> M ()
addCur c l = modify {locations $= insert (show l) c}

-- IDEA: use Loc values in Map as keys via its show function

{-
data Loc : (r : Region) -> (t : Ty) -> Type where
  LocStart    : (t : Ty) -> (r : Region) -> Loc r t
  LocAfter    : (t : Ty) -> Loc r t_prev -> Loc r t   -- Q: dynamically/runtime known? maybe a better name is RuntimeAfter ; A: NO!
                -- INSIGHT: if we would put Ty to this (instead of static size that would provide enough information to generate runtime function to calculate an endwitness
                -- IDEA: location is not the right thing that descibes the next location
                --        instead it would be the end witness of some value!
                --        location + size-witness = end-witness
          --    ^ this should be a value variable instead of Ty, that would solve the sizeof problem with either's left/right
          --    Q: what problem would it cause?
  LocAfterTag : (t : Ty) -> Loc r t_prev -> Loc r t         -- statically known ; used for jump over the tag
  LocTup2Fst  : (t : Ty) -> Loc r t_prev -> Loc r t
-}

-- TODO: check that it is written only once ; use an effect map for LocVals
genCursor : (loc : Loc r t) -> M String
genCursor loc = do
  --lift $ putStrLn " !! gen cursor for \{loc}"
  let locKey = show loc
  {-
    gen new if does not exist
    return exisiting when available
  -}
  locs <- gets locations
  --sizes <- gets locSize
  ends <- gets endwitness
  let newCur = do
        c <- newCursorName
        lift $ print $ colored BrightRed " !! add cursor \{c} :=\n \{loc}\n\n"
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
          let Just ew = lookup (show l) ends
                | Nothing => assert_total $ idris_crash $ "INTERNAL ERROR: missing loc endwitness for \{l} endwitness map: \{show ends}"
          c <- newCur
          emit "char* \{c} = \{ew};"
          pure c
        LocAfterTag _ _ l => do
          let Just ew = lookup (show l) ends
                | Nothing => assert_total $ idris_crash $ "INTERNAL ERROR: missing loc endwitness for \{l} endwitness map: \{show ends}"
          c <- newCur
          emit "char* \{c} = \{ew};"
          pure c
{-
getLocTy
getLocOffset : Loc r t -> Int
getLocOffset (LocStart _ _) = 0
getLocOffset (LocAfterTag _ l) = getLocOffset l
-}
{-
  LocAfter (I64)
 (LocAfterTag (I64)
 (LocAfter (Tup2 (I64) (I64))
 (LocAfterTag (Tup2 (I64) (I64))
 (LocStart (Tup2 (Tup2 (I64) (I64)) (Tup2 (I64) (I64))) MkRegion -1))))

-}

updateEndWitnessTo : {loc2 : _} -> (loc : Loc r t) -> Exp _ loc2 -> M ()
updateEndWitnessTo {loc2} loc e = do
  ends <- gets endwitness
  let Just ew = lookup (show loc2) ends
        | Nothing => assert_total $ idris_crash $ "INTERNAL ERROR: missing loc endwitness for \{loc2} endwitness map: \{show ends}"
  modify {endwitness $= insert (show loc) ew}

addStaticSizeEndWitness : (loc : Loc r t) -> Int -> String -> M ()
addStaticSizeEndWitness l bytes msg = do
  locs <- gets locations
  let Just cur = lookup (show l) locs
        | Nothing => assert_total $ idris_crash $ "INTERNAL ERROR: missing cursor for \{l}, locations map: \{show locs}"
  let ew = "\{cur}_end"
  modify {endwitness $= insert (show l) ew}
  emit "char* \{ew} = \{cur} + \{bytes}; // \{msg}"

partial fillDyn : {r : _ } -> {t : _ } -> {loc : Loc r t} -> Exp t loc -> M ()
fillDyn {r} {loc} (MkI64 i) = do
  lift $ putStrLn " ++ MkI64 \{i}"
  {-
    TODO:
      - gen location and store it on cg env
      get cursor for the location
      store
  -}
  cur <- genCursor loc
  addStaticSizeEndWitness loc 8 "I64" -- TODO: which do we want?
  emit "*(int*) \{cur} = \{i};"

fillDyn {loc} (MkTup2 a b) = do
  lift $ putStrLn " ++ MkTup2"
  cur <- genCursor loc
  addStaticSizeEndWitness loc 0 "Tup2Tag" -- TODO: which do we want?
  fillDyn a
  fillDyn b
  updateEndWitnessTo loc b
  -- TODO: make it better!!

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
  cur_in <- genCursor loc_in
  emit "*(char**) \{cur} = \{cur_in};"

fillDyn {loc} (MkIndLong {loc_in} _) = do
  lift $ putStrLn " ++ MkIndLong"
  cur <- genCursor loc
  addStaticSizeEndWitness loc 8 "IndLong" -- 64 bit pointer
  cur_in <- genCursor loc_in
  emit "*(char**) \{cur} = \{cur_in};"

fillDyn {loc} (MkLeft a) = do
  lift $ putStrLn " ++ MkLeft"
  cur <- genCursor loc
  addStaticSizeEndWitness loc 1 "LeftTag" -- 64 bit pointer
  emit "*(char*) \{cur} = 0; // LEFT_TAG"
  fillDyn a
  updateEndWitnessTo loc a -- TODO: write cursor

fillDyn {loc} (MkRight b) = do
  lift $ putStrLn " ++ MkRight"
  cur <- genCursor loc
  addStaticSizeEndWitness loc 1 "RightTag" -- 64 bit pointer
  emit "*(char*) \{cur} = 1; // RIGHT_TAG"
  fillDyn b
  updateEndWitnessTo loc b

fillDyn (PrjFst {r} a cont) = do
  fillDyn a
  lift $ putStrLn " ++ PrjFst"
  fillDyn (cont Var) -- Q: is Var unused? why? is the location that track values instead of binder names? A: YES
fillDyn (PrjSnd a cont) = do
  fillDyn a
  lift $ putStrLn " ++ PrjSnd"
  fillDyn (cont Var) -- Q: is Var unused? why? is the location that track values instead of binder names? A: YES

fillDyn {loc} (PrintI64 {loc_in} a) = do
  lift $ putStrLn " ++ PrintI64"
  fillDyn a
  cur_in <- genCursor loc_in
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
fillDyn (CaseEither {loc} scrut cont_left cont_right) = do
  lift $ putStrLn " ++ CaseEither"
  fillDyn scrut
  cur_tag <- genCursor loc
  emit "if (*(char*) \{cur_tag} == 0) { // LEFT"
  indent $ fillDyn (cont_left Var)
  emit "} else { // RIGHT"
  indent $ fillDyn (cont_right Var)
  emit "}"

fillDyn {loc} (Copy {r_in, loc_in} src) = do
  lift $ putStrLn " ++ Copy"
  let bytes = 0 --sizeToInt s
  cur_src <- genCursor loc_in
  cur_dst <- genCursor loc
  emit "memcpy(\{cur_dst}, \{cur_src}, \{bytes});"

fillDyn Var = emit "// Var" -- assert_total $ idris_crash $ "Var"

{-
allocRegion : M LocVal
allocRegion = do
  let r = MkRegion !newId
  let lv = MkLocVal r (MkLE (LocStart r))
  c <- newCursorName
  emit "char *\{c} = newRegion();"
  addCur c lv
  pure lv
-}

partial public export
toBufferDyn : {t : _} -> Exp t (LocStart t (MkRegion (-1))) -> IO String
--public export partial toBufferDyn : Exp a (LocStart a (MkRegion (-1))) -> IO String
toBufferDyn {t} e = do
  print $ background Yellow " ---- CODEGEN ----"
  putStrLn ""
  s <- execStateT emptyCG $ do
    c <- newCursorName
    -- alloc main region
    emit "char *\{c} = newRegion();"
    let r   = MkRegion (-1)
    let loc = LocStart t r
    addCur c (LocStart t (MkRegion (-1)))
    --fillDyn {r=MkRegion (-1)} {loc=MkLE (LocStart (MkRegion (-1)))} e
    fillDyn $ LetRegionValue (MkRegion (-1)) e id
  putStrLn " ---- CODE OUTPUT ----"
  pure $ unlines $ reverse s.code


{-
  TODO:
    - remove usage of Size in dynamic cursor backend,
      instead add Ty to LocAfter and generate runtime endwitness calculator code
    done - complete codegen to handle all Exp constructors
-}
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
-}
