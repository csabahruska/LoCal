module HiCal

public export
data Ty : Type where
  T0      : Ty
  Pair    : Ty -> Ty -> Ty
  Either  : Ty -> Ty -> Ty
  I64     : Ty
  -- recursive type support
  Box     : Lazy Ty -> Ty

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

  Let : {a, b : Ty} -> Exp a -> (Exp a -> Exp b) -> Exp b

  -- boxing
  MkBox : Exp t -> Exp (Box t)
  UnBox : Exp (Box t) -> Exp t

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

  I64Op2CE : IntOp2 -> Int -> Exp I64 -> Exp I64
  I64Op2EC : IntOp2 -> Exp I64 -> Int -> Exp I64
  I64CmpC  : CmpOp  -> Int -> Exp I64 -> Exp (Either T0 T0)

  -- IO primops
  PrintI64 : Exp I64 -> (() -> Exp t) -> Exp t

  -- prints the buffer content at the location in hexadecimal
  PrintValue : Exp t_in -> (() -> Exp t) -> Exp t

  -- internal
  Var : Exp t

public export
data Program : Type where
  Main  : {res : Ty} -> Exp res -> Program
