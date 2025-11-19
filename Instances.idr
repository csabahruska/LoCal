module Instances
import LoCal

import Decidable.Equality

-- instances
public export
Eq Region where
  (MkRegion a) == (MkRegion b) = a == b

public export
Ord Region where
  compare (MkRegion a) (MkRegion b) = compare a b

DecEq Region where
  decEq = decEq @{FromEq}

public export
Eq Size where
  STup2 a1 a2 == STup2 b1 b2 = a1 == b1 && a2 == b2
  STag a == STag b = a == b
  SInt a == SInt b = a == b
  D == D = True
  _ == _ = False

ordTagSize : Size -> Int
ordTagSize (STup2 _ _)  = 0
ordTagSize (STag _)     = 1
ordTagSize (SInt _)     = 2
ordTagSize D            = 3

public export
Ord Size where
  compare (STup2 a1 a2) (STup2 b1 b2) =
    case compare a1 b1 of
      EQ => compare a2 b2
      GT => GT
      LT => LT
  compare (STag a) (STag b) = compare a b
  compare (SInt a) (SInt b) = compare a b
  compare D D = EQ
  compare a b = compare (ordTagSize a) (ordTagSize b)

mutual
  partial public export
  Eq (LocExp r) where
    (LocStart a) == (LocStart a) = True
    (LocAfter a1 b1) == (LocAfter a2 b2) = a1 == a2 && b1 == b2
    (LocAfterTag a) == (LocAfterTag b) = a == b
    _ == _ = False

  partial public export
  Eq (Loc r) where
    (MkLoc a) == (MkLoc b) = a == b
    (MkLE a) == (MkLE b) = a == b
    _ == _ = False

ordTagLoc : Loc r -> Int
ordTagLoc (MkLoc _) = 0
ordTagLoc (MkLE _)  = 1

ordTagLocExp : LocExp r -> Int
ordTagLocExp (LocStart _)     = 0
ordTagLocExp (LocAfter _ _)   = 1
ordTagLocExp (LocAfterTag _)  = 2

mutual
  partial public export
  Ord (LocExp r) where
    compare (LocStart a) (LocStart a) = EQ
    compare (LocAfter a1 b1) (LocAfter a2 b2) = case compare a1 a2 of
      EQ => compare b1 b2
      GT => GT
      LT => LT
    compare (LocAfterTag a) (LocAfterTag b) = compare a b
    compare _ _ = EQ

  partial public export
  Ord (Loc r) where
    compare (MkLoc a) (MkLoc b) = compare a b
    compare (MkLE a) (MkLE b) = compare a b
    compare a b = compare (ordTagLoc a) (ordTagLoc b)

public export
data LocVal : Type where
  MkLocVal : (r : Region) -> Loc r -> LocVal

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
