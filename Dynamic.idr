module Dynamic

import LoCal
import Instances
import Data.SortedMap
import Data.String
import Control.Monad.State
import Data.Primitives.Interpolation

-- TODO: remove
partial sizeToInt : Size -> Int
sizeToInt (STup2 a b) = sizeToInt a + sizeToInt b
sizeToInt (STag a) = 1 + sizeToInt a
sizeToInt (SInt a) = a
{-
  MkTup2
  MkLeft
  MkRight
  CaseEither
  Copy
-}
{-
  TODO:
    change C cursor representation to
      typedef struct {char* begin; char* end;} cursor_t;
-}


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
  locations   : SortedMap LocVal String
  endwitness  : SortedMap LocVal String
  locSize     : SortedMap LocVal Int
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

addCur : String -> LocVal -> M ()
addCur c lv = modify {locations $= insert lv c}

showLoc : Loc r -> String
showLoc loc = case loc of
  MkLE (LocStart (MkRegion ri)) => "LocStart \{ri}"
  MkLE (LocAfter _ _ l ) => "LocAfter (\{showLoc l})"
  MkLE (LocAfterTag l ) => "LocAfterTag (\{showLoc l})"
  MkLE (LocTup2Fst l ) => "LocTup2Fst (\{showLoc l})"
  MkLoc i => "MkLoc \{i}"

Show (Loc r) where show = showLoc

showRegion : Region -> String
showRegion (MkRegion i) = "MkRegion \{i}"

Show Region where show = showRegion

showLocVal : LocVal -> String
showLocVal (MkLocVal r l) = "MkLocVal (\{show r}) (\{show l})"

Show LocVal where show = showLocVal

-- TODO: check that it is written only once ; use an effect map for LocVals
genCursor : {r : _} -> (loc : Loc r) -> M String
genCursor {r} loc = do
  lift $ putStrLn " !! gen cursor for \{showLoc loc}"
  let lv  = MkLocVal r loc
  {-
    gen new if does not exist
    return exisiting when available
  -}
  locs <- gets locations
  sizes <- gets locSize
  let newCur = do
        c <- newCursorName
        lift $ putStrLn " !! add cursor \{showLoc loc} => \{c}"
        addCur c lv
        pure c
  case lookup lv !(gets locations) of
    Just v  => pure v
    Nothing => do
      case loc of
        MkLE (LocStart (MkRegion ri)) => assert_total $ idris_crash $ "INTERNAL ERROR: missing LocStart for region \{ri} locations: \{show locs}"
        MkLE (LocAfter _ _ l ) => do
          {-
          let lv = MkLocVal r l
              Just size = lookup lv sizes
                | Nothing => assert_total $ idris_crash $ "INTERNAL ERROR: missing loc size for \{show lv} locSize: \{show sizes}"
          -}
          c <- newCur
          emit "cursor_t \{c} = {.begin = \{!(genCursor l)}.end};"
          pure c
        MkLE (LocAfterTag l) => do
          c <- newCur
          emit "cursor_t \{c} = {.begin = \{!(genCursor l)}.end};"
          pure c
        MkLE (LocTup2Fst l) => do
          genCursor l
        MkLoc _ => assert_total $ idris_crash $ "INTERNAL ERROR: MkLoc is not supported"

--addStaticEndWitness : (loc : _) -> Int -> M ()
--addStaticEndWitness _ _ = pure ()

addStaticSize : {r : _} -> (loc : Loc r) -> Int -> M ()
addStaticSize {r} l s = do
  lift $ putStrLn " !! set size for \{showLoc l} = \{s}"
  modify {locSize $= insert (MkLocVal r l) s}

partial fillDyn : {r : _ } -> {loc : Loc r} -> Exp a loc s -> M ()
fillDyn {r} {loc} (MkI64 i) = do
  lift $ putStrLn " ++ MkI64 \{i}"
  {-
    TODO:
      - gen location and store it on cg env
      get cursor for the location
      store
  -}
  --addStaticSize loc 8       -- TODO: size or end witness?
  cur <- genCursor loc
  --addStaticEndWitness loc 8 -- TODO: which do we want?
  emit "*(int*) \{cur}.begin = \{i};"
  emit "\{cur}.end = \{cur}.begin + 8;"
  pure ()
{-
  char *cur0 = ...;
  *(int*)cur0 = i;

    GibCursor after_tag_521 = loc_302 + 1;
    *(GibInt *) after_tag_521 = 123;
-}
fillDyn {loc} (MkTup2 {a_s, b_s} a b) = do
  lift $ putStrLn " ++ MkTup2"
  --addStaticSize loc $ sizeToInt a_s + sizeToInt b_s
  fillDyn a
  fillDyn b
  -- TODO: make it better!!

fillDyn {r} (MkInd {loc_in, loc_ind} i) = do
  lift $ putStrLn " ++ MkInd"
  addStaticSize loc_ind 8 -- 64 bit pointer
  cur_in <- genCursor loc_in
  cur_ind <- genCursor loc_ind
  emit "*(char*) \{cur_ind} = \{cur_in};"

fillDyn {r} (MkIndLong {r_in, loc_in, loc_ind} i) = do
  lift $ putStrLn " ++ MkIndLong"
  addStaticSize loc_ind 8 -- 64 bit pointer
  cur_in <- genCursor {r=r_in} loc_in
  cur_ind <- genCursor loc_ind
  emit "*(char*) \{cur_ind} = \{cur_in};"

fillDyn {loc} (MkLeft {s_a} a) = do
  lift $ putStrLn " ++ MkLeft"
  emit "*(char*) \{!(genCursor loc)} = 0; // LEFT_TAG"
  addStaticSize loc $ 1 + sizeToInt s_a
  fillDyn a

fillDyn {loc} (MkRight {s_b} b) = do
  lift $ putStrLn " ++ MkRight"
  emit "*(char*) \{!(genCursor loc)} = 1; // RIGHT_TAG"
  addStaticSize loc $ 1 + sizeToInt s_b
  fillDyn b

fillDyn (PrjFst _ cont) = fillDyn (cont Var) -- Q: is Var unused? why? is the location that track values instead of binder names? A: YES
fillDyn (PrjSnd _ cont) = fillDyn (cont Var) -- Q: is Var unused? why? is the location that track values instead of binder names? A: YES

fillDyn {loc} (PrintI64 {r_in, loc_in} _) = do
  lift $ putStrLn " ++ PrintI64"
  addStaticSize loc 0
  cur_in <- genCursor {r=r_in} loc_in
  emit "printf(\"%ld\\n\", *(int*) \{cur_in});"

fillDyn (LetRegion cont) = do
  c <- newCursorName
  emit "char *\{c} = newRegion();"
  let r   = MkRegion !newId
      loc = MkLE (LocStart r)
  addCur c (MkLocVal r loc)
  fillDyn (cont r)

fillDyn (Let {r_in} {loc_in} a cont) = fillDyn {r=r_in} {loc=loc_in} a >> fillDyn (cont a)

fillDyn {loc, s} (CaseEither scrut cont_left cont_right) = do
  lift $ putStrLn " ++ CaseEither"
  addStaticSize loc $ 1 + sizeToInt s
  cur_tag <- genCursor loc
  emit "if (*(char*) \{cur_tag} == 0) { // LEFT"
  indent $ fillDyn (cont_left Var)
  emit "} else { // RIGHT"
  indent $ fillDyn (cont_right Var)
  emit "}"

fillDyn {loc, s} (Copy {r_in, loc_in} src) = do
  lift $ putStrLn " ++ Copy"
  let bytes = sizeToInt s
  addStaticSize loc bytes
  addStaticSize loc_in bytes
  cur_src <- genCursor loc_in
  cur_dst <- genCursor loc
  emit "memcpy(\{cur_dst}, \{cur_src}, \{bytes});"

fillDyn Var = assert_total $ idris_crash $ "Var"

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

public export partial toBufferDyn : Exp a (MkLE (LocStart (MkRegion (-1)))) s -> IO String
toBufferDyn e = do
  putStrLn " ---- CODEGEN ----"
  s <- execStateT emptyCG $ do
            -- alloc main region
            c <- newCursorName
            emit "char *\{c} = newRegion();"
            --let r   = MkRegion (-1)
            --    loc = MkLE (LocStart (MkRegion (-1)))
            addCur c (MkLocVal (MkRegion (-1)) (MkLE (LocStart (MkRegion (-1)))))
            fillDyn {r=MkRegion (-1)} {loc=MkLE (LocStart (MkRegion (-1)))} e
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
-}
