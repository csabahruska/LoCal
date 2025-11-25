module Static

import LoCal

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
locToIndex (MkLE (LocAfter ty s l)) = sizeToInt s + locToIndex l
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
fill (PrjFst _ cont) = fill (cont Var)
fill (PrjSnd _ cont) = fill (cont Var)
fill (PrintI64 {loc_in} _) = "read " ++ show (locToIndex loc_in) ++ " and PrintI64 ; "
fill (LetRegion cont) = fill (cont (MkRegion 0)) -- TODO
fill (Let {r_in} {loc_in} a cont) = fill {r=r_in} {loc=loc_in} a ++ fill (cont a)
fill {loc} (MkLeft a) = "write Left tag to " ++ show (locToIndex loc) ++ " ; " ++ fill a
fill {loc} (MkRight a) = "write Right tag to " ++ show (locToIndex loc) ++ " ; " ++ fill a

partial toBuffer : Exp a (MkLE (LocStart (MkRegion 0))) s -> String
toBuffer e = fill e
