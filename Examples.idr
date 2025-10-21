import LoCal
import CodeGen
import Eval

-- data IntList = Cons Int IntList
--              | Nil

i64ListTy : Ty
i64ListTy =
  DecBox $ \t =>
  DefBox t (Either (Tup2 I64 t) T0) t

test_ : Program
test_ =
  MkDec $ \myFun1 =>
  MkDef {arg = T0} myFun1 (\a => a) $
  Main myFun1

f : (1 _ : Int) -> Int -> Int
f = \a, b => a
--f a b = a

{-
  DONE: modify all examples so that the last expression of a bind chain sould be a Ret with variable
-}

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

myFun000_ok_reverse : Exp (Tup2 I64 I64)
myFun000_ok_reverse =
  LetRegion $ \r =>
  LetLoc (LocStart r) $ \l1, sl1 =>
  -- create i64 values
  Let l1 (MkI64 101) $ \i1 =>
  LetLoc (LocAfter I64 sl1) $ \l2, sl2 =>
  LetLoc (LocAfter I64 sl2) $ \l3, sl3 =>
  Let l2 (MkI64 201) $ \i2 =>
  Let l3 (MkTup2 i1 i2) $ \t1 =>
  Ret sl3 t1

myFun000_ok_in_order : Exp (Tup2 I64 I64)
myFun000_ok_in_order =
  LetRegion $ \r =>
  LetLoc (LocStart r) $ \l1, sl1 =>
  LetLoc (LocAfterTag sl1) $ \l2, sl2 =>
  LetLoc (LocAfter I64 sl2) $ \l3, sl3 =>
  -- create i64 values
  Let l3 (MkI64 201) $ \i2 =>
  Let l2 (MkI64 101) $ \i1 =>
  Let l1 (MkTup2 i1 i2) $ \t1 =>
  Ret sl3 t1

myFun000_error : Exp (Tup2 I64 I64)
myFun000_error =
  LetRegion $ \r =>
  LetLoc (LocStart r) $ \l1, sl1 =>
  LetLoc (LocAfter I64 sl1) $ \l2, sl2 =>
  -- create i64 values
  Let l1 (MkI64 101) $ \i1 =>
  Let l2 (MkI64 101) $ \i2 =>
  -- create tup
  LetLoc (LocAfter I64 sl2) $ \l3, sl3 =>
  Let l3 (MkTup2 i1 i2) $ \t1 =>
  Ret sl3 t1

myFun000_error_sharing : Exp (Tup2 I64 I64)
myFun000_error_sharing =
  LetRegion $ \r =>
  LetLoc (LocStart r) $ \l1, sl1 =>
  LetLoc (LocAfterTag sl1) $ \l2, sl2 =>
  -- create i64 values
  Let l1 (MkI64 101) $ \i1 =>
  Let l2 (MkTup2 i1 i1) $ \t1 =>
  Ret sl2 t1

myFun000_error_why_is_ok : Exp (Tup2 I64 I64)
myFun000_error_why_is_ok =
  LetRegion $ \r =>
  LetLoc (LocStart r) $ \l1, sl1 =>
  -- create i64 values
  Let l1 (MkI64 101) $ \i1 =>
  LetLoc (LocAfter I64 sl1) $ \l2, sl2 =>
  Let l2 (MkI64 101) $ \i2 =>
  -- create tup
  LetLoc (LocAfter I64 sl2) $ \l3, sl3 =>
  Let l3 (MkTup2 i1 i2) $ \t1 =>
  Ret sl3 t1

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
  Ret sl3 t1

myFun00_fst : Exp (Tup2 I64 I64) -> Exp I64
myFun00_fst t =
  LetRegion $ \r =>
  LetLoc (LocStart r) $ \l1, sl1 =>                  -- for the first i64
  CaseFst t $ \i1 =>
  Let l1 i1 $ \i2 => -- HINT: value copy between regions
  Ret sl1 i2

myFun00_snd : Exp (Tup2 I64 I64) -> Exp I64
myFun00_snd t =
  LetRegion $ \r =>
  LetLoc (LocStart r) $ \l1, sl1 =>                  -- for the first i64
  CaseSnd t $ \i1 =>
  Let l1 i1 $ \i2 => -- HINT: value copy between regions
  Ret sl1 i2

{-
  NOTE: currently locations are for output, such as value construction
  Q: what about input locations?
     what about function calls and location passing?
     what about static and dynamic input/output locations at function calls?
-}
myFun00_app : Fun (Tup2 I64 I64) I64 -> Exp (Tup2 I64 I64) -> Exp I64
myFun00_app f t =
  LetRegion $ \r =>
  LetLoc (LocStart r) $ \l1, sl1 =>                  -- for the first i64
  Let l1 (FunApp f t) $ \i1 => -- HINT: value copy between regions
  Ret sl1 i1

myFun00Err : Exp I64
myFun00Err =
  LetRegion $ \r =>
  LetLoc (LocStart r) $ \l1, sl1 =>                  -- for the first i64
  LetLoc (LocAfter I64 sl1) $ \l2, sl2 =>                  -- for the first i64
  -- create i64 values
  Let l1 (MkI64 101) $ \i1 =>
  Let l2 (MkI64 101) $ \i2 =>
  Ret sl2 i1

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
  Ret sl5 t2
  -- PROBLEM: location aliasing!!!!
  --          each location should be written only once
  --          if tup2 would have a runtime tag that would prevent location aliasing
  --          that means that tup2 tag is irrelevant at runtime
  --  SOLVED by requiring tag for Tup2

myFun02_right : Exp (Either I64 (Tup2 I64 I64))
myFun02_right =
  LetRegion $ \r =>
  LetLoc (LocStart r) $ \l1, sl1 =>                  -- for the tag
  LetLoc (LocAfterTag sl1) $ \l2, sl2 =>             -- for the tag
  LetLoc (LocAfterTag sl2) $ \l3, sl3 =>             -- for the first i64
  LetLoc (LocAfter I64 sl3) $ \l4, sl4 =>            -- for the second i64
  -- create i64 values
  Let l3 (MkI64 101) $ \i1 =>
  Let l4 (MkI64 202) $ \i2 =>
  -- create structures
  Let l2 (MkTup2 i1 i2) $ \t1 =>
  Let l1 (MkRight t1) $ \t2 =>
  Ret sl4 t2

myFun02_left : Exp (Either I64 (Tup2 I64 I64))
myFun02_left =
  LetRegion $ \r =>
  LetLoc (LocStart r) $ \l1, sl1 =>                  -- for the tag
  LetLoc (LocAfterTag sl1) $ \l2, sl2 =>             -- for the i64
  -- create i64 values
  Let l2 (MkI64 101) $ \i1 =>
  Let l1 (MkLeft i1) $ \t1 =>
  Ret sl2 t1

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

test : Program
test =
  MkDec $ \myFun01_ =>
  MkDef myFun01_ (\ _ => myFun01) $
  Main myFun01_
