import LoCal
import Instances
import Data.SortedMap
import Data.String
import Control.Monad.State
import Data.Primitives.Interpolation

-- data IntList = Cons Int IntList
--              | Nil

i64ListTy : Ty
i64ListTy =
  DecBox $ \t =>
  DefBox t (Either (Tup2 I64 t) T0) t
{-
test_ : Program
test_ =
  MkDec $ \myFun1 =>
  MkDef {arg = T0} myFun1 (\a => a) $
  Main myFun1

f : (1 _ : Int) -> Int -> Int
f = \a, b => a
--f a b = a
-}
{-
  DONE: modify all examples so that the last expression of a bind chain sould be a Ret with variable
-}
{-
-- put all values into variables
myFun000_ok_reverse_sharing : Exp (Tup2 I64 I64)
myFun000_ok_reverse_sharing =
  LetRegion $ \r =>
  LetLoc (LocStart r) $ \l1, sl1 =>
  -- create i64 values
  Let l1 (MkI64 101) $ \i1 =>
  LetLoc (LocAfter I64 sl1) $ \l2, sl2 =>
  Let l2 (MkTup2 i1 i1) $ \t1 =>
  Ret sl2 t1
-}

i64 : {loc : _} -> Exp I64 loc ?
i64 = MkI64 1

sample_tup2_01 : {loc : _} -> Exp (Tup2 I64 I64) loc ?
sample_tup2_01 =
  -- create i64 values
  let i1 = MkI64 101 in
  let i2 = MkI64 201 in
  let l3 = MkTup2 i1 i2 in
  l3

sample_tup2_01_sharing : {loc : _} -> Exp (Tup2 I64 (Ind I64)) loc ?
sample_tup2_01_sharing =
  -- create i64 values
  let i1 = MkI64 101 in
  let l3 = MkTup2 i1 (MkInd i1) in
  l3

sample_tup2_01_sharing2 : {loc : _} -> Exp (Tup2 (Ind I64) I64) loc ?
sample_tup2_01_sharing2 =
  -- create i64 values
  let i1 = MkI64 101 in
  let l3 = MkTup2 (MkInd i1) i1  in
  l3

sample_tup2_02 : {loc : _} -> Exp (Tup2 (Tup2 I64 I64) (Tup2 I64 I64)) loc ?
sample_tup2_02 = MkTup2 sample_tup2_01 sample_tup2_01

--sample_tup2_03 = sample_tup2_02 {loc = MkLE (LocStart (MkRegion 0))}
{-
sample_print_snd : {loc_in : Loc _} -> {loc_out : _} -> Exp T0 loc_out
sample_print_snd =
  let t = sample_tup2_01_sharing in
  PrjSnd {loc=loc_in }{loc_out} t $ \i =>
  PrintI64 i
-}


newRegion : ((r : Region) -> Loc r -> Exp t l s) -> Exp t l s
newRegion f = LetRegion $ \r => f r (MkLE (LocStart r))

--newValue : Exp t l1 s -> (Exp t l1 s -> Exp t2 l2 s2) -> Exp t2 l2 s2
--newValue e f = newRegion (\_, loc => Let {loc_in=loc} e $ \e2 => f e2)

sample_print_snd_fst : {loc_out : _} -> Exp T0 loc_out ?
sample_print_snd_fst =
  --LetRegion $ \r =>
  --Let (sample_tup2_02 {loc = MkLE (LocStart r)}) $ \t1 =>

  newRegion $ \r, loc_in =>
  Let {loc_in} sample_tup2_02 $ \t1 =>

  --newValue sample_tup2_02 $ \t1 =>

  PrjSnd t1 $ \t2 =>
  PrjFst t2 $ \i =>
  PrintI64 i

{-
  TODO:
    done - sample for either
    done - sample for decomposition and reuse substructure in a new tuple
-}

sample_new_tup_ind : {loc_out : _} -> Exp (Tup2 (Ind (Tup2 I64 I64)) (Ind (Tup2 I64 I64))) loc_out ?
sample_new_tup_ind =
  LetRegion $ \r =>
  Let (sample_tup2_02 {loc = MkLE (LocStart r)}) $ \t1 =>
  PrjSnd t1 $ \t2 =>
  MkTup2 (MkIndLong t2) (MkIndLong t2)


sample_new_tup_copy : {loc_out : _} -> Exp (Tup2 I64 I64) loc_out ?
sample_new_tup_copy =
  LetRegion $ \r =>
  Let (sample_tup2_02 {loc = MkLE (LocStart r)}) $ \t1 =>
  PrjSnd t1 $ \t2 =>
  Copy t2

sample_left_01 : {loc : _} -> Exp (Either (Tup2 I64 I64) I64) loc ?
sample_left_01 = MkLeft sample_tup2_01

sample_tup_either_01 : {loc : _} -> Exp (Tup2 (Either (Tup2 I64 I64) I64) I64) loc ?
sample_tup_either_01 = MkTup2 (MkRight (MkI64 11)) (MkI64 222)


{-
  TODO: either eliminator sample
-}
sample_print_either_elim : {loc_out : _} -> Exp T0 loc_out ?
sample_print_either_elim =
  newRegion $ \r, loc_in =>
  Let {loc_in} sample_left_01 $ \e1 =>
  -- INSIGHT: the size of the left side of the tuple {s_l} is unknown, it can be anything
  -- PROBLEM: well, it is wrong! the left tup2 is prefrectly constructed, but the size information comes only from the deconstruction side
  -- Q: how to fill it automatically?
  -- basically it is unused part of the type, no constructor belongs to it
  -- IDEA: with coercive subtyping we could implement lattice operations, so the type elaborator unification could calculate the lattice values also
  CaseEither {s_l = STup2 (SInt 0) ?} e1
    (\l => PrintI64 (PrjSnd l id))
    (\r => PrintI64 r)

-- ----------------------------------------------

partial sizeOf : Ty -> Int
sizeOf I64 = 1
sizeOf (Tup2 a b) = sizeOf a + sizeOf b -- no tag for tup2
sizeOf (Either a b) = 1 + max (sizeOf a) (sizeOf b) -- HACK, because it compiles to tagged union

partial sizeToInt : Size -> Int
sizeToInt (STup2 a b) = sizeToInt a + sizeToInt b
sizeToInt (STag a) = 1 + sizeToInt a
sizeToInt (SInt a) = a

partial locToIndex : Loc r -> Int
locToIndex (MkLE (LocStart _)) = 0
locToIndex (MkLE (LocAfterTag l)) = 1 + locToIndex l
locToIndex (MkLE (LocAfter s l)) = sizeToInt s + locToIndex l
locToIndex (MkLE (LocTup2Fst l)) = 0 + locToIndex l

{-
  MkLE  : LocExp r -> Loc r

public export
data LocExp : (1 r : Region) -> Type where
  LocStart    : (1 r : Region) -> LocExp r
  LocAfter    : Ty -> (1 _ : Loc r) -> LocExp r   -- Q: dynamically/runtime known? maybe a better name is RuntimeAfter ; A: NO!
          --    ^ this should be a value variable instead of Ty, that would solve the sizeof problem with either's left/right
          --    Q: what problem would it cause?
  LocAfterTag : (1 _ : Loc r) -> LocExp r         -- statically known ; used for jump over the tag
-}

-- static fill ; compiler
partial fill : {r : _} -> {loc : Loc r} -> Exp a loc s -> String
fill {loc} (MkI64 i) = "write " ++ show i ++ " to " ++ show (locToIndex loc) ++ " ; "
fill {loc} (MkTup2 a b) = fill a ++ fill b
fill {loc} (MkInd {loc_in} _) = "write IND " ++ show (locToIndex loc_in) ++ " to " ++ show (locToIndex loc) ++ " ; "
fill (PrjFst _ cont) = fill (cont (Var 0))
fill (PrjSnd _ cont) = fill (cont (Var 0))
fill (PrintI64 {loc_in} _) = "read " ++ show (locToIndex loc_in) ++ " and PrintI64 ; "
fill (LetRegion cont) = fill (cont (MkRegion 0)) -- TODO
fill (Let {r_in} {loc_in} a cont) = fill {r=r_in} {loc=loc_in} a ++ fill (cont a)
fill {loc} (MkLeft a) = "write Left tag to " ++ show (locToIndex loc) ++ " ; " ++ fill a
fill {loc} (MkRight a) = "write Right tag to " ++ show (locToIndex loc) ++ " ; " ++ fill a

partial toBuffer : Exp a (MkLE (LocStart (MkRegion 0))) s -> String
toBuffer e = fill e

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

emptyCG : CG
emptyCG = MkCG
  { counter     = 0
  , locations   = empty
  , endwitness  = empty
  , locSize     = empty
  , code        = []
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

emit : String -> M ()
emit s = do
  lift $ putStrLn s
  modify {code $= (::) s}

addCur : String -> LocVal -> M ()
addCur c lv = modify {locations $= insert lv c}

showLoc : Loc r -> String
showLoc loc = case loc of
  MkLE (LocStart (MkRegion ri)) => "LocStart \{ri}"
  MkLE (LocAfter _ l ) => "LocAfter (\{showLoc l})"
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
        MkLE (LocAfter _ l ) => do
          let lv = MkLocVal r l
              Just size = lookup lv sizes
                | Nothing => assert_total $ idris_crash $ "INTERNAL ERROR: missing loc size for \{show lv} locSize: \{show sizes}"
          c <- newCur
          emit "int *\{c} = (char*)\{!(genCursor l)} + \{size};"
          pure c
        MkLE (LocAfterTag l) => do
          c <- newCur
          emit "int *\{c} = (char*)\{!(genCursor l)} + 1;"
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
  addStaticSize loc 8       -- TODO: size or end witness?
  cur <- genCursor loc
  --addStaticEndWitness loc 8 -- TODO: which do we want?
  emit "*(int*) \{cur} = \{i};"
  pure ()
{-
  char *cur0 = ...;
  *(int*)cur0 = i;

    GibCursor after_tag_521 = loc_302 + 1;
    *(GibInt *) after_tag_521 = 123;
-}
fillDyn {loc} (MkTup2 {a_s, b_s} a b) = do
  lift $ putStrLn " ++ MkTup2"
  addStaticSize loc $ sizeToInt a_s + sizeToInt b_s
  fillDyn a
  fillDyn b
  -- TODO: make it better!!

fillDyn {r} (MkInd {loc_in, loc_ind} i) = do
  lift $ putStrLn " ++ MkInd"
  addStaticSize loc_ind 8 -- 64 bit pointer
  cur_in <- genCursor loc_in
  cur_ind <- genCursor loc_ind
  emit "*(int*) \{cur_ind} = \{cur_in};"

fillDyn {loc} (MkLeft {s_a} a) = do
  lift $ putStrLn " ++ MkLeft"
  addStaticSize loc $ 1 + sizeToInt s_a
  fillDyn a

fillDyn {loc} (MkRight {s_b} b) = do
  lift $ putStrLn " ++ MkRight"
  addStaticSize loc $ 1 + sizeToInt s_b
  fillDyn b

fillDyn (PrjFst _ cont) = fillDyn (cont (Var 0)) -- Q: is Var unused? why? is the location that track values instead of binder names?
fillDyn (PrjSnd _ cont) = fillDyn (cont (Var 0)) -- Q: is Var unused? why? is the location that track values instead of binder names?

fillDyn {loc} (PrintI64 {r_in, loc_in} _) = do
  lift $ putStrLn " ++ PrintI64"
  addStaticSize loc 0
  cur_in <- genCursor {r=r_in} loc_in
  emit "printf(\"%ld\\n\", *(int*) \{cur_in});"

fillDyn (LetRegion cont) = do
  c <- newCursorName
  emit "int *\{c} = newRegion();"
  let r   = MkRegion !newId
      loc = MkLE (LocStart r)
  addCur c (MkLocVal r loc)
  fillDyn (cont r)

fillDyn (Let {r_in} {loc_in} a cont) = fillDyn {r=r_in} {loc=loc_in} a >> fillDyn (cont a)

-- TODO:
--  MkIndLong : Exp t loc_in s -> Exp (Ind t) loc_ind (SInt 8)                             -- cross region
--  Copy : Exp t loc_in s -> Exp t loc s
--  CaseEither : {a, b, c : Ty} -> {s, s_l, s_r, s_out : Size} -> {loc : Loc r} -> {loc_out : Loc r_out} -> Exp (Either a b) loc (STag s) {-(SEither s_l s_r)-} ->
--               let locArg = MkLE (LocAfterTag loc) in
--               (Exp a locArg s_l -> Exp c loc_out s_out) -> (Exp b locArg s_r -> Exp c loc_out s_out) -> Exp c loc_out s_out


{-
allocRegion : M LocVal
allocRegion = do
  let r = MkRegion !newId
  let lv = MkLocVal r (MkLE (LocStart r))
  c <- newCursorName
  emit "int *\{c} = newRegion();"
  addCur c lv
  pure lv
-}

partial toBufferDyn : Exp a (MkLE (LocStart (MkRegion (-1)))) s -> IO String
toBufferDyn e = do
  putStrLn " ---- CODEGEN ----"
  s <- execStateT emptyCG $ do
            -- alloc main region
            c <- newCursorName
            emit "int *\{c} = newRegion();"
            --let r   = MkRegion (-1)
            --    loc = MkLE (LocStart (MkRegion (-1)))
            addCur c (MkLocVal (MkRegion (-1)) (MkLE (LocStart (MkRegion (-1)))))
            fillDyn {r=MkRegion (-1)} {loc=MkLE (LocStart (MkRegion (-1)))} e
  putStrLn " ---- CODE OUTPUT ----"
  pure $ unlines $ reverse s.code

partial main : IO ()
{-
sample_new_tup_ind : {loc_out : _} -> Exp (Tup2 (Ind (Tup2 I64 I64)) (Ind (Tup2 I64 I64))) loc_out ?
sample_new_tup_copy : {loc_out : _} -> Exp (Tup2 I64 I64) loc_out ?
sample_print_either_elim : {loc_out : _} -> Exp T0 loc_out ?
-}

{-
  TODO:
    - remove usage of Size in dynamic cursor backend,
      instead add Ty to LocAfter and generate runtime endwitness calculator code
    - complete codegen to handle all Exp constructors
-}

main = do
  {-
  putStr !(toBufferDyn i64)
  putStr !(toBufferDyn sample_tup2_01)
  putStr !(toBufferDyn sample_tup2_01_sharing)
  putStr !(toBufferDyn sample_tup2_01_sharing2)
  putStr !(toBufferDyn sample_tup2_02)
  putStr !(toBufferDyn sample_left_01)
  putStr !(toBufferDyn sample_tup_either_01)
  putStr !(toBufferDyn sample_print_snd_fst)
  -}
  putStr !(toBufferDyn sample_print_snd_fst)
  --putStr !(toBufferDyn sample_new_tup_ind)
