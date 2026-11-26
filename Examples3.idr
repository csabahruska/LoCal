import LoCal

i64 : {loc : _} -> Exp I64 loc W []
i64 = MkI64 1

sample_tup2_01 : {r : _} -> {loc : Loc r} -> Exp (Pair I64 I64) loc W []
sample_tup2_01 =
  -- create i64 values
  let i1 = MkI64 101 in
  let i2 = MkI64 201 in
  MkPair i1 i2

sample_left_01 : {r : _} -> {loc : Loc r} -> Exp (Either (Pair I64 I64) I64) loc W []
sample_left_01 = MkLeft sample_tup2_01

sample_tup2_02 : {r : _} -> {loc : Loc r} -> Exp (Pair (Pair I64 I64) (Pair I64 I64)) loc W []
sample_tup2_02 = MkPair sample_tup2_01 sample_tup2_01

sample_print_snd_fst : {loc_out : _} -> Exp T0 loc_out W []
sample_print_snd_fst =
  LetRegion $ \r =>
  LetRegionValue r sample_tup2_02 $ \t1 =>
  let fst = GetFst $ GetSnd t1 (StaticEW $ GetFst t1) in
  PrintI64 fst $ \() => MkT0

{-
sample_tup2_sharing_01 : {loc : _} -> Exp (RTup2 (RTup2 (Ind I64) I64{-deref-}) I64{-literal-}) loc
sample_tup2_sharing_01 =
  -- create i64 values
  let i1 = MkI64 101 in
  let p1 = MkInd i1 in
  MkRTup2 (MkRTup2 p1 (DeRef p1)) i1
-}
{-
  MkInd : {loc_in : Loc r t} -> {loc_ind : Loc r (Ind t)} -> Exp t loc_in -> Exp (Ind t) loc_ind -- within the same region
  DeRef : {loc_in : Loc r t} -> {loc_ind : Loc r (Ind t)} -> Exp (Ind t) loc_ind -> Exp t loc_in -- within the same region
-}
{-
exp_i1 : {loc : _} -> Exp I64 loc
exp_p1 : {loc : _} -> Exp (Ind I64) loc
exp_i1 = DeRef exp_p1
exp_p1 = MkInd (exp_i1{loc_in=loc})

sample_tup2_sharing_02 : {loc : _} -> Exp (Tup2 I64 (Ind I64)) loc
sample_tup2_sharing_02 =
  -- create i64 values
    MkTup2 exp_i1 exp_p1
-}
{-
test3 : Program
test3 = Main $ let i = MkI64 1 in PrintI64 i $ \() => i

test4 : Program
test4 = Main $ let i = MkI64 1 in MkPair (I64Op2 Plus i i) i
-}
