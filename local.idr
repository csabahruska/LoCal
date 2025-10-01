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


-- data IntList = Cons Int IntList
--              | Nil

i64ListTy : Ty
i64ListTy =
  DecBox $ \t =>
  DefBox t (Either (Tup2 I64 t) T0) t

data Region : Type where

data Loc : (_ : Ty) -> (1 _ : Region) -> Type where

data LocExp : (1 _ : Region) -> Type where
  LocStart    : (1 r : Region) -> LocExp r
  LocAfter    : Ty -> (1 _ : Loc _ r) -> LocExp r   -- Q: dynamically/runtime known? maybe a better name is RuntimeAfter ; A: NO!
  LocAfterTag : (1 _ : Loc _ r) -> LocExp r         -- statically known ; used for jump over the tag

data Fun : (arg : Ty) -> (res : Ty) -> Type

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
    - no sharing

  Q: what about stack frames and stack based memory management?
  Q: what about returning values in registers?
  A: use special region for that, or use escape analysis on regions

  mvp example:
    - program read user input N:int
    - creates a List of Int from 1 to N unpacked in a buffer

-}

{-
  currently sharing is not supported
  for support we need:
    + indirection value
    + location for indirection
    + linear value types ; in Let
    + dup hoas primitive
-}

{-
  TODO: refactor to
    - simple expression ; value definition
    - bind chain ; various lets, return value
-}
data Exp : (t : Ty) -> Type where
  TT : Exp I64

  -- primitive values
  MkI64 : Int -> Exp I64

  -- value shapes, ADT can be modeled with these
  MkTup2  : Exp a -> Exp b -> Exp (Tup2 a b)
  MkLeft  : Exp a -> Exp (Either a b)
  MkRight : Exp b -> Exp (Either a b)

  CaseFst     : Exp (Tup2 a b)   -> (Loc a r -> Exp a -> Exp c) -> Exp c
  CaseSnd     : Exp (Tup2 a b)   -> (Loc b r -> Exp b -> Exp c) -> Exp c
  CaseEither  : Exp (Either a b) -> (Loc a r -> Exp a -> Exp c) -> (Loc b r -> Exp b -> Exp c) -> Exp c

  -- location related
  LetRegion : (1 _ : (1 _ : Region) -> Exp a) -> Exp a
  LetLoc : {t : Ty} -> (1 _ : LocExp r) -> (1 _ : (1 _ : Loc t r) -> Loc t r -> Exp a) -> Exp a -- Q: is this needed? use loc expressions for construction?

  -- generic
  Let : (1 _ : Loc a _) -> Exp a -> (1 _ : Exp a -> Exp b) -> Exp b

  FunApp : Fun arg res -> Exp arg -> Exp res

data Fun : (arg : Ty) -> (res : Ty) -> Type where
  MkFunId : Int -> Fun arg res

data DefList : Type where
  NilDef  : DefList
  MkDec   : {arg : Ty} -> {res : Ty} -> (Fun arg res -> DefList) -> DefList
  MkDef   : {arg : Ty} -> {res : Ty} -> Fun arg res -> (Exp arg -> Exp res) -> DefList -> DefList

-- -------------------------------

test : Int -> DefList
test i =
  MkDec $ \myFun1 =>
  MkDef {arg = I64} myFun1 (\a => a) $
  NilDef

f : (1 _ : Int) -> Int -> Int
f = \a, b => a
--f a b = a

{-
  TODO:
    - separate expressions from value definitions
    - make all location variables linear, one for values one for locations
    - add function return (terminator expression)
      + that would take a location and a value
      + or it would take a variable
         * this would need a new location expression type: function return value ; NO - it should use the after location
-}

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

myFun000_error_sharing : Exp (Tup2 I64 I64)
myFun000_error_sharing =
  LetRegion $ \r =>
  LetLoc (LocStart r) $ \l1, sl1 =>
  LetLoc (LocAfterTag sl1) $ \l2, sl2 =>
  -- create i64 values
  Let l1 (MkI64 101) $ \i1 =>
  Let l2 (MkTup2 i1 i1) $ \t1 =>
  t1

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
  LetLoc (LocAfterTag sl1) $ \l2, sl2 =>             -- for the first i64
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


  PROBLEM:
    currently a tup2 I64 I64 representation can be arbitraty, but it will be written correctly due to locations,
      but the consumer (reader) side might use a different layout,
      for example the producer side could use a [TAG, trash, fst I64, trash, snd I64] layout
      and the consumer side just would expect a packed [TAG, fst I64, snd I64] layout,
      which would not work
    to solve it the type and layout must be attached
    Q: where to attach?
      a) Ty
      b) Exp  ; <=== I'd prefer this

    Q: what would be the layout language?

  LAYOUT MVP:
    - force to use packed ; left to right layout ordering
    - make it correct by construction
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

FunTy : List Ty -> Ty -> Type
FunTy [] r = Exp r
FunTy (t::ts) r = Exp t -> FunTy ts r

fn : FunTy [I64, I64] I64
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

myId : (1 _ : a) -> a
myId x =
  let a = x in
  -- let b = x in
  a


v : Int
v = let i = 1 in
    let a = id i in
    let b = id i in
    b
