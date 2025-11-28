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
    done - fully dynamic cursor passing and size calculation
    - interpreter based static improvements
-}

-- DONE: dynamic fill ; in a separate function
{-
  + the location expression tells how to serialize cursor passing
  TODO:
    done - use monad stack to store region/cursor environment
-}

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
genCursor : (loc : Loc r t) -> M String
genCursor loc = do
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
          emit "char* \{c} = \{!(getEndWitness l)};"
          pure c
        LocAfterTag s _ l => do
          let tagSize = case s of
                "Tup2" => 0
                _      => 1
          c <- newCur
          emit "char* \{c} = \{!(getCursor l)} + \{tagSize};"
          pure c

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

fillDyn {loc} (MkTup2 a b) = do
  lift $ putStrLn " ++ MkTup2"
  cur <- genCursor loc
  fillDyn a
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
fillDyn (PrjSnd a cont) = do
  lift $ putStrLn " ++ PrjSnd"
  fillDyn a
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
-}
