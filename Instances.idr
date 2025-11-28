module Instances
import LoCal

import Decidable.Equality

partial public export
Eq Ty where
  T0 == T0 = True
  (Tup2 a1 a2) == (Tup2 b1 b2) = a1 == b1 && a2 == b2
  (Either a1 a2) == (Either b1 b2) = a1 == b1 && a2 == b2
  I64 == I64 = True
  (Ind a) == (Ind b) = a == b
  (DecTy a) == (DecTy b) = a == b
  (DefTy _ _ a) == b = a == b
  a == (DefTy _ _ b) = a == b

DecEq Ty where
  decEq = decEq @{FromEq}


ordTagTy : Ty -> Int
ordTagTy T0             = 0
ordTagTy (Tup2 _ _)     = 1
ordTagTy (Either _ _)   = 2
ordTagTy I64            = 3
ordTagTy (Ind _)        = 4
ordTagTy (DecTy _)      = 5
ordTagTy (DefTy _ _ _)  = 6

partial public export
Ord Ty where
  compare T0 T0 = EQ
  compare (Tup2 a1 a2) (Tup2 b1 b2) = case compare a1 b1 of
    EQ => compare a2 b2
    GT => GT
    LT => LT
  compare (Either a1 a2) (Either b1 b2) = case compare a1 b1 of
    EQ => compare a2 b2
    GT => GT
    LT => LT
  compare I64 I64 = EQ
  compare (Ind a) (Ind b) = compare a b
  compare (DecTy a) (DecTy b) = compare a b
  compare (DefTy _ _ a) b = compare a b
  compare a (DefTy _ _ b) = compare a b
  compare a b = compare (ordTagTy a) (ordTagTy b)

-- instances
public export
Eq Region where
  (MkRegion a) == (MkRegion b) = a == b

public export
Ord Region where
  compare (MkRegion a) (MkRegion b) = compare a b

DecEq Region where
  decEq = decEq @{FromEq}

partial public export
Eq (Loc r t) where
  (LocStart t r) == (LocStart t r) = True
  (LocAfter {t_prev=p1} t a) == (LocAfter {t_prev=p2} t b) = case decEq p1 p2 of -- HINT: Ty does not matter
    Yes Refl => a == b
    No _     => False
  (LocAfterTag {t_prev=p1} t a) == (LocAfter {t_prev=p2} t b) = case decEq p1 p2 of -- HINT: Ty does not matter
    Yes Refl => a == b
    No _     => False
  (LocTup2Fst {t_prev=p1} t a) == (LocTup2Fst {t_prev=p2} t b) = case decEq p1 p2 of -- HINT: Ty does not matter
    Yes Refl => a == b
    No _     => False
  _ == _ = False


ordTagLocExp : Loc r t -> Int
ordTagLocExp (LocStart _ _)     = 0
ordTagLocExp (LocAfter _ _)     = 1
ordTagLocExp (LocAfterTag _ _)  = 2
ordTagLocExp (LocTup2Fst _ _)   = 3


partial public export
Ord (Loc r t) where
  compare (LocStart t a) (LocStart t a) = EQ
  compare (LocAfter {t_prev=p1} t a) (LocAfter {t_prev=p2} t b) = compare a b -- HINT: Ty and Size does not matter
  compare (LocAfterTag t a) (LocAfterTag t b) = compare a b
  compare (LocTup2Fst t a) (LocTup2Fst t b) = compare a b
  compare a b = compare (ordTagLocExp a) (ordTagLocExp b)

{-
public export
data LocVal : Type where
  MkLocVal : (r : Region) -> (t : Ty) -> Loc r t -> LocVal

partial public export
Eq LocVal where
  (MkLocVal a1 b1) == (MkLocVal a2 b2) = case decEq a1 a2 of
    Yes Refl => b1 == b2
    No _     => False

partial public export
Ord LocVal where
  compare (MkLocVal a1 a2) (MkLocVal b1 b2) =
    case compare a1 b1 of
      EQ => case decEq a1 b1 of
              Yes Refl => compare a2 b2
      GT => GT
      LT => LT
-}