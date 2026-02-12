module HiCalExamples

import HiCal

public export
AddI64C : Int -> Exp I64 -> Exp I64
AddI64C i = I64Op2 Plus (MkI64 i)

public export
EqI64C, LtI64C : Int -> Exp I64 -> Exp (Either T0 T0)
EqI64C i = I64Cmp EQ (MkI64 i)
LtI64C i = I64Cmp LT (MkI64 i)

Rev_my_ty : Ty
Rev_my_ty = Either (Pair (Box "Rev_my_ty" Rev_my_ty) I64) T0

test_12 : Program
test_12 =
  let genList : Arg [Exp I64] -> Exp Rev_my_ty
      genList (ArgN i Arg0) =
        CaseEither (EqI64C 10 i)
          (\f => MkLeft $ MkPair (MkBox $ FunAppNew "genList" genList (ArgN (AddI64C 1 i) Arg0)) i)
          (\t => MkRight MkT0)

      printList : Arg [Exp Rev_my_ty] -> Exp T0
      printList (ArgN a Arg0) =
        CaseEither a
          (\l =>
              CasePair l $ \lst, i =>
              PrintI64 i $ \_ =>
              FunAppNew "printList" printList (ArgN (UnBox lst) Arg0)
          )
          (\r => MkT0)

  in Main $
      let i = MkI64 1 in
      Let (FunAppNew "genList" genList (ArgN i Arg0)) $ \l =>
      PrintValue l $ \_ =>
      FunAppNew "printList" printList (ArgN l Arg0)
