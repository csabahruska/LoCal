import LoCal

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

sample_tup2_02 : {loc : _} -> Exp (Tup2 (Tup2 I64 I64) (Tup2 I64 I64)) loc ?
sample_tup2_02 = MkTup2 sample_tup2_01 sample_tup2_01

sample_tup2_03 = sample_tup2_02 {loc = MkLE (LocStart (MkRegion 0))}
{-
sample_print_snd : {loc_in : Loc _} -> {loc_out : _} -> Exp T0 loc_out
sample_print_snd =
  let t = sample_tup2_01_sharing in
  PrjSnd {loc=loc_in }{loc_out} t $ \i =>
  PrintI64 i
-}

sample_print_snd_fst : {loc_out : _} -> Exp T0 loc_out ?
sample_print_snd_fst =
  LetRegion $ \r =>
  Let (sample_tup2_02 {loc = MkLE (LocStart r)}) $ \t1 =>
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

partial fill : {loc : _} -> Exp a loc s -> String
fill {loc} (MkI64 i) = "write " ++ show i ++ " to " ++ show (locToIndex loc) ++ " ; "
fill {loc} (MkTup2 a b) = fill a ++ fill b
fill {loc} (MkInd {loc_arg} _) = "write IND " ++ show (locToIndex loc_arg) ++ " to " ++ show (locToIndex loc) ++ " ; "
fill (PrjFst _ cont) = fill (cont (Var 0))
fill (PrjSnd _ cont) = fill (cont (Var 0))
fill (PrintI64 {loc_arg} _) = "read " ++ show (locToIndex loc_arg) ++ " and PrintI64 ; "
fill (LetRegion cont) = fill (cont (MkRegion 0)) -- TODO
fill (Let {loc_in} a cont) = fill {loc=loc_in} a ++ fill (cont a)
fill {loc} (MkLeft a) = "write Left tag to " ++ show (locToIndex loc) ++ " ; " ++ fill a
fill {loc} (MkRight a) = "write Right tag to " ++ show (locToIndex loc) ++ " ; " ++ fill a

partial toBuffer : Exp a (MkLE (LocStart (MkRegion 0))) s -> String
toBuffer e = fill e
