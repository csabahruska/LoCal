import LoCal
import Instances
import Data.SortedMap
import Data.String
import Control.Monad.State
import Data.Primitives.Interpolation
import Static
import Dynamic

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
  MkTup2 i1 i2

sample_tup2_01_sharing : {loc : _} -> Exp (Tup2 I64 (Ind I64)) loc ?
sample_tup2_01_sharing =
  -- create i64 values
  let i1 = MkI64 101 in
  MkTup2 i1 (MkInd i1)

sample_tup2_01_sharing2 : {loc : _} -> Exp (Tup2 (Ind I64) I64) loc ?
sample_tup2_01_sharing2 =
  -- create i64 values
  let i1 = MkI64 101 in
  MkTup2 (MkInd i1) i1

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

-- test

partial main : IO ()
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
  putStr !(toBufferDyn sample_new_tup_ind)
  putStr !(toBufferDyn sample_new_tup_copy)
  -}
  putStr !(toBufferDyn sample_print_either_elim)
