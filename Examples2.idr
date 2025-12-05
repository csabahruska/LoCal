import LoCal
import Dynamic

-- data IntList = Cons Int IntList
--              | Nil

i64ListTy : Ty
i64ListTy =
  let t = "i64List" in
  DefTy t (Either (RTup2 I64 t) T0) t

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

i64 : {loc : _} -> Exp I64 loc
i64 = MkI64 1

sample_tup2_01 : {loc : _} -> Exp (RTup2 I64 I64) loc
sample_tup2_01 =
  -- create i64 values
  let i1 = MkI64 101 in
  let i2 = MkI64 201 in
  MkRTup2 i1 i2

sample_tup2_01_sharing : {loc : _} -> Exp (RTup2 I64 (Ind I64)) loc
sample_tup2_01_sharing =
  -- create i64 values
  let i1 = MkI64 101 in
  MkRTup2 i1 (MkInd i1)

sample_tup2_01_sharing2 : {loc : _} -> Exp (RTup2 (Ind I64) I64) loc
sample_tup2_01_sharing2 =
  -- create i64 values
  let i1 = MkI64 101 in
  MkRTup2 (MkInd i1) i1


--sample_tup2_03 = sample_tup2_02 {loc = MkLE (LocStart (MkRegion 0))}
{-
sample_print_snd : {loc_in : Loc _} -> {loc_out : _} -> Exp T0 loc_out
sample_print_snd =
  let t = sample_tup2_01_sharing in
  PrjSnd {loc=loc_in }{loc_out} t $ \i =>
  PrintI64 i
-}

sample_tup2_02 : {loc : _} -> Exp (RTup2 (RTup2 I64 I64) (RTup2 I64 I64)) loc
sample_tup2_02 = MkRTup2 sample_tup2_01 sample_tup2_01

sample_print_snd_fst : {loc_out : _} -> Exp T0 loc_out
sample_print_snd_fst =
  LetRegion $ \r =>
  LetRegionValue r sample_tup2_02 $ \t1 =>
  PrjSnd t1 $ \t2 =>
  PrjFst t2 $ \i =>
  PrintI64 i

sample_new_tup_ind : {loc_out : _} -> Exp (RTup2 (Ind (RTup2 I64 I64)) (Ind (RTup2 I64 I64))) loc_out
sample_new_tup_ind =
  LetRegion $ \r =>
  LetRegionValue r sample_tup2_02 $ \t1 =>
  PrjSnd t1 $ \t2 =>
  MkRTup2 (MkIndLong t2) (MkIndLong t2)


sample_new_tup_copy : {loc_out : _} -> Exp (RTup2 I64 I64) loc_out
sample_new_tup_copy =
  LetRegion $ \r =>
  LetRegionValue r sample_tup2_02 $ \t1 =>
  PrjSnd t1 $ \t2 =>
  Copy t2

sample_left_01 : {loc : _} -> Exp (Either (RTup2 I64 I64) I64) loc
sample_left_01 = MkLeft sample_tup2_01

sample_tup_either_01 : {loc : _} -> Exp (RTup2 (Either (RTup2 I64 I64) I64) I64) loc
sample_tup_either_01 = MkRTup2 (MkRight (MkI64 11)) (MkI64 222)


sample_print_either_elim : {loc_out : _} -> Exp T0 loc_out
sample_print_either_elim =
  -- allocate value into a new region
  LetRegion $ \r =>
  LetRegionValue r sample_left_01 $ \e1 =>

  -- INSIGHT: the size of the left side of the tuple {s_l} is unknown, it can be anything
  -- PROBLEM: well, it is wrong! the left tup2 is prefrectly constructed, but the size information comes only from the deconstruction side
  -- Q: how to fill it automatically?
  -- basically it is unused part of the type, no constructor belongs to it
  -- IDEA: with coercive subtyping we could implement lattice operations, so the type elaborator unification could calculate the lattice values also

  CaseEither e1
    (\l => PrintI64 (PrjSnd l id))
    (\r => PrintI64 r)

sample_print_either_elim2 : {loc_out : _} -> Exp (Either (RTup2 I64 I64) I64) loc_out
sample_print_either_elim2 =
  LetRegion $ \r =>
  LetRegionValue r sample_left_01 $ \e1 =>
  CaseEither e1
    (\l => Copy e1)
    (\r => Copy e1)

sample_print_either_elim3 : {loc_out : _} -> Exp (Ind (Either (RTup2 I64 I64) I64)) loc_out
sample_print_either_elim3 =
  LetRegion $ \r =>
  LetRegionValue r sample_left_01 $ \e1 =>
  CaseEither e1
    (\l => MkIndLong e1)
    (\r => MkIndLong e1)

sample_print_either_elim4 : {loc_out : _} -> Exp (RTup2 (Either (RTup2 I64 I64) I64) I64) loc_out
sample_print_either_elim4 =
  LetRegion $ \r =>
  LetRegionValue r sample_left_01 $ \e1 =>
  let v1 = CaseEither e1
        (\l => MkLeft (MkRTup2 (MkI64 11) (MkI64 22)))
        (\r => MkRight (MkI64 33))
  in MkRTup2 v1 (MkI64 44)

-- TODO: support forward pointers
sample_print_either_elim5_forward_ind : {loc_out : _} -> Exp (RTup2 (Ind I64) (RTup2 (Either (RTup2 I64 I64) I64) I64)) loc_out
sample_print_either_elim5_forward_ind =
  LetRegion $ \r =>
  LetRegionValue r sample_left_01 $ \e1 =>
  let v1 = CaseEither e1
        (\l => MkLeft (MkRTup2 (MkI64 11) (MkI64 22)))
        (\r => MkRight (MkI64 33)) in
  let i1 = MkI64 44 in
  MkRTup2 (MkInd i1) (MkRTup2 v1 i1)

sample_print_either_elim5_backward_ind : {loc_out : _} -> Exp (RTup2 (RTup2 I64 (Either (RTup2 I64 I64) I64)) (Ind I64)) loc_out
sample_print_either_elim5_backward_ind =
  LetRegion $ \r =>
  LetRegionValue r sample_left_01 $ \e1 =>
  let v1 = CaseEither e1
        (\l => MkLeft (MkRTup2 (MkI64 11) (MkI64 22)))
        (\r => MkRight (MkI64 33)) in
  let i1 = MkI64 44 in
  MkRTup2 (MkRTup2 i1 v1) (MkInd i1)

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
  putStr !(toBufferDyn sample_print_either_elim)
  -}
  --putStr !(toBufferDyn i64)
  --putStr !(toBufferDyn sample_tup2_02)
  --pure ()
  --putStr !(toBufferDyn sample_tup2_01)
  --putStr !(toBufferDyn sample_tup2_01_sharing)
  --putStr !(toBufferDyn sample_tup2_01_sharing2)
  --putStr !(toBufferDyn sample_left_01)
  --putStr !(toBufferDyn sample_tup_either_01)
  --putStr !(toBufferDyn sample_print_snd_fst)
  --putStr !(toBufferDyn sample_print_either_elim)
  --putStr !(toBufferDyn sample_print_either_elim4)
  --putStr !(toBufferDyn sample_print_either_elim2)
  --putStr !(toBufferDyn sample_print_either_elim5_forward_ind) -- TODO
  putStr !(toBufferDyn sample_print_either_elim5_backward_ind)
