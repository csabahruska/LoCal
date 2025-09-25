data Ty
  = T0
  | Tup2 Ty Ty
  | Either Ty Ty
  | I64
  | DecBox (Ty -> Ty)
  | DefBox Ty Ty Ty

{-
  INSIGHT:
    control flow construct data
      if          -> + types
      basic block -> * types
    unconsrained recursion needs Box!!!
-}

{-
  REPRESENTATION:
    - no tag:   I64
    - has tag:  Tup2, Either

  FUTURE WORK:
    - no tag for Tup2 ; problem to solve is location aliasing
-}

i64ListTy : Ty
i64ListTy =
  DecBox $ \t =>
  DefBox t (Either (Tup2 I64 t) T0) t

data Region : Type where

data Loc : (1 r : Region) -> Type where

data LocExp : (1 r : Region) -> Type where
  LocStart    : (1 r : Region) -> LocExp r
  LocAfter    : Ty -> (1 l : Loc r) -> LocExp r   -- Q: dynamically/runtime known? maybe a better name is RuntimeAfter ; A: NO!
  LocAfterTag : (1 l : Loc r) -> LocExp r         -- statically known ; used for jump over the tag

data Def : (arg : Ty) -> (res : Ty) -> Type

{-
  Q:
    do we need locations for building only?
    do we need locations for deconstruction?

  - locations can be queried from variables
-}

{-
  mvp simplifications:
    - only tup2 and either ; product and sum type
    - only I64 interger primitive type
    - functions with only single argument

  Q: what about stack frames and stack based memory management?
  Q: what about returning values in registers?
  A: use special region for that, or use escape analysis on regions
-}

data Exp : (t : Ty) -> Type where
  TT : Exp I64

  -- primitive values
  MkI64 : Int -> Exp I64

  -- value shapes, ADT can be modeled with these
  MkTup2  : Exp a -> Exp b -> Exp (Tup2 a b)
  MkLeft  : Exp a -> Exp (Either a b)
  MkRight : Exp b -> Exp (Either a b)

  CaseFst     : Exp (Tup2 a b)   -> (Loc r -> Exp a -> Exp c) -> Exp c
  CaseSnd     : Exp (Tup2 a b)   -> (Loc r -> Exp b -> Exp c) -> Exp c
  CaseEither  : Exp (Either a b) -> (Loc r -> Exp a -> Exp c) -> (Loc r -> Exp b -> Exp c) -> Exp c

  -- location related
  LetRegion : (1 c : (1 r : Region) -> Exp a) -> Exp a
  LetLoc : (1 le : LocExp r) -> (1 c : (1 l : Loc r) -> Loc r -> Exp a) -> Exp a -- Q: is this needed? use loc expressions for construction?

  -- generic
  Let : (1 l : Loc r) -> Exp a -> (1 c : Exp a -> Exp b) -> Exp b

  AppDef : Def arg res -> Exp arg -> Exp res

data Def : (arg : Ty) -> (res : Ty) -> Type where
  MkDefId : Int -> Def arg res

data DefList : Type where
  NilDef  : DefList
  MkDec   : {arg : Ty} -> {res : Ty} -> (Def arg res -> DefList) -> DefList
  MkDef   : {arg : Ty} -> {res : Ty} -> Def arg res -> (Exp arg -> Exp res) -> DefList -> DefList

-- -------------------------------

test : Int -> DefList
test i =
  MkDec $ \myFun1 =>
  MkDef {arg = I64} myFun1 (\a => a) $
  NilDef
f : (1 t : Int) -> Int -> Int
f = \a, b => a
--f a b = a


-- put all values into variables
myFun000_ok : Exp (Tup2 I64 I64)
myFun000_ok =
  LetRegion $ \r =>
  LetLoc (LocStart r) $ \l1, sl1 =>
  -- create i64 values
  Let l1 (MkI64 101) $ \i1 =>
  MkTup2 i1 i1

myFun000_error : Exp (Tup2 I64 I64)
myFun000_error =
  LetRegion $ \r =>
  LetLoc (LocStart r) $ \l1, sl1 =>
  LetLoc (LocAfter I64 sl1) $ \l2, sl2 =>
  -- create i64 values
  Let l1 (MkI64 101) $ \i1 =>
  Let l2 (MkI64 101) $ \i2 =>
  MkTup2 i1 i2


myFun000_error_why_is_ok : Exp (Tup2 I64 I64)
myFun000_error_why_is_ok =
  LetRegion $ \r =>
  LetLoc (LocStart r) $ \l1, sl1 =>
  -- create i64 values
  Let l1 (MkI64 101) $ \i1 =>
  LetLoc (LocAfter I64 sl1) $ \l2, sl2 =>
  Let l2 (MkI64 101) $ \i2 =>
  MkTup2 i1 i2

myFun00 : Exp (Tup2 I64 I64)
myFun00 =
  LetRegion $ \r =>
  LetLoc (LocStart r) $ \l1, sl1 =>                  -- for the tag
  LetLoc (LocAfterTag sl1) $ \l2, sl2 =>             -- for the second i64
  LetLoc (LocAfter I64 sl2) $ \l3, sl3 =>            -- for the second i64
  -- create i64 values
  Let l2 (MkI64 101) $ \i1 =>
  Let l3 (MkI64 202) $ \i2 =>
  -- create structures
  Let l1 (MkTup2 i1 i2) $ \t1 =>
  t1

myFun00Err : Exp I64
myFun00Err =
  LetRegion $ \r =>
  LetLoc (LocStart r) $ \l1, sl1 =>                  -- for the first i64
  LetLoc (LocAfter I64 sl1) $ \l2, sl2 =>                  -- for the first i64
  -- create i64 values
  Let l1 (MkI64 101) $ \i1 =>
  Let l2 (MkI64 101) $ \i2 =>
  i1

{-
  Q: how to express location relations?
    a) flattened low level: sequence of prim types            ; locations are sequenced linearly           (list of locations) ; compatible with linear types
    b) high level:          sequence of high level structures ; locations can be referenced multiple times (tree of locations) ; needs multi modality

  NOTE:
    the problem of the list of locations approach is that it fixes the layout and we want to support filed reordering, so the location language must support that
-}
myFun01 : Exp (Tup2 (Tup2 I64 I64) I64)
myFun01 =
  LetRegion $ \r =>
  LetLoc (LocStart r) $ \l1, sl1 =>           -- for tup2 tag
  LetLoc (LocAfterTag sl1) $ \l2, sl2 =>      -- for the embedded tup2 tag
  LetLoc (LocAfterTag sl2) $ \l3, sl3 =>      -- for the first i64
  LetLoc (LocAfter I64 sl3) $ \l4, sl4 =>     -- for the middle i64
  LetLoc (LocAfter I64 sl4) $ \l5, sl5 =>     -- for the third i64
  -- create i64 values
  Let l3 (MkI64 101) $ \i1 =>
  Let l4 (MkI64 202) $ \i2 =>
  Let l5 (MkI64 303) $ \i3 =>
  -- create structures
  Let l1 (MkTup2 i1 i2) $ \t1 =>
  Let l2 (MkTup2 t1 i3) $ \t2 =>
  t2
  -- PROBLEM: location aliasing!!!!
  --          each location should be written only once
  --          if tup2 would have a runtime tag that would prevent location aliasing
  --          that means that tup2 tag is irrelevant at runtime
  --  SOLVED by requiring tag for Tup2

-- -------------------------------

-- multi arg modeling

data Arg : (sig : List Ty) -> Type where
  NilArg : Arg Nil
  MkArg : Exp t -> Arg s -> Arg (t :: s)

test2 : Arg [I64, I64]
test2 = MkArg TT $ MkArg TT $ NilArg

Fun : List Ty -> Ty -> Type
Fun [] r = Exp r
Fun (t::ts) r = Exp t -> Fun ts r

fn : Fun [I64, I64] I64
fn = \a => \b => b

{-
  ingredients
    App - function + one argument
    Tup2
    Either
    Top level functions:
      def + arr
    fst, snd
    either - control flow based eliminator
-}

{-
  NOTES:
    location is: staticly known or dynamicly/runtime known
-}

{-
  put either and tup2 and I64 into buffers
-}

myId : (1 x : a) -> a
myId x =
  let a = x in
  -- let b = x in
  a


v : Int
v = let i = 1 in
    let a = id i in
    let b = id i in
    b
