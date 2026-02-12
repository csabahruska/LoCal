module HiCal

import Decidable.Equality

public export
data Ty : Type where
  T0      : Ty
  Pair    : Ty -> Ty -> Ty
  Either  : Ty -> Ty -> Ty
  I64     : Ty
  -- recursive type support
  Box     : String -> Lazy Ty -> Ty

public export
showTy : Ty -> String
showTy t = case t of
  T0          => "T0"
  Pair a b    => "Pair (\{showTy a}) (\{showTy b})"
  Either a b  => "Either (\{showTy a}) (\{showTy b})"
  I64         => "I64"
  Box n t     => "Box \{n}"

public export Show Ty  where show = showTy
public export Eq Ty    where a == b = showTy a == showTy b
public export DecEq Ty where decEq = decEq @{FromEq}

public export
data IntOp2 = Plus | Sub | Times | Quot | Rem

public export
data CmpOp = EQ | GE | GT | LE | LT | NE

public export
data Exp : (t : Ty) -> Type

public export
data Arg : (sig : List Type) -> Type where
  Arg0 : Arg []
  ArgN : {t : _} -> Exp t -> Arg s -> Arg (Exp t :: s)

data Exp where

  Let : {a: Ty} -> Exp a -> (Exp a -> Exp b) -> Exp b

  -- boxing
  MkBox : {n : String} -> Exp t -> Exp (Box n t)
  UnBox : Exp (Box _ t) -> Exp t

  -- value shapes, ADT can be modeled with these

  MkPair  : {a, b : Ty} -> Exp a -> Exp b -> Exp (Pair a b)
  MkLeft  : {a, b : Ty} -> Exp a -> Exp (Either a b)
  MkRight : {a, b : Ty} -> Exp b -> Exp (Either a b)

  CasePair   : {a, b, c : Ty} -> Exp (Pair a b) -> (Exp a -> Exp b -> Exp c) -> Exp c
  CaseEither : {a, b, c : Ty} -> Exp (Either a b) -> (Exp a -> Exp c) -> (Exp b -> Exp c) -> Exp c

  FunAppNew :
           String ->
           (fun_def  : Arg exps_in  -> Exp res) ->
           (fun_args : Arg exps_in) -> Exp res

  -- primitive values
  MkT0  : Exp T0
  MkI64 : Int -> Exp I64

  -- I64 primops
  I64Op2  : IntOp2 -> Exp I64 -> Exp I64 -> Exp I64
  I64Cmp  : CmpOp  -> Exp I64 -> Exp I64 -> Exp (Either T0 T0)

  -- IO primops
  PrintI64 : Exp I64 -> (() -> Exp t) -> Exp t

  -- prints the buffer content at the location in hexadecimal
  PrintValue : {t_in : _} -> Exp t_in -> (() -> Exp t) -> Exp t

  -- internal
  Var : {t : _} -> Int -> Exp t

public export
data Program : Type where
  Main  : {res : Ty} -> Exp res -> Program
