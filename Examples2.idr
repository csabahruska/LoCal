module Examples2

import LoCal
import Dynamic

-------------------------------------------
-- Boxing experiment --------------
-------------------------------------------

-- data IntList = Cons Int IntList
--              | Nil

mutual
  my_ty : Ty
  my_ty = Either (RTup2 I64 my_ty_box) T0

  my_ty_box : Ty
  my_ty_box = Box my_ty

sample_box_03 : {loc : _} -> Exp Examples2.my_ty loc
sample_box_03 = MkRight MkT0

sample_box_04 : {r : _} -> {loc : Loc r} -> Exp Examples2.my_ty_box loc
sample_box_04 = MkBox sample_box_03

sample_box_05 : {r : _} -> {loc : Loc r} -> Exp Examples2.my_ty loc
sample_box_05 = UnBox sample_box_04

sample_box_06 : {r : _} -> {loc : Loc r} -> Exp Examples2.my_ty loc
sample_box_06 = MkLeft $ MkRTup2 (MkI64 1) sample_box_04

sample_box_07 : {r : _} -> {loc : Loc r} -> Exp Examples2.my_ty loc
sample_box_07 = MkLeft $ MkRTup2 (MkI64 2) $ MkBox sample_box_06


-- data IntList = Cons IntList Int
--              | Nil

mutual
  rev_my_ty : Ty
  rev_my_ty = Either (RTup2 rev_my_ty_box I64) T0

  rev_my_ty_box : Ty
  rev_my_ty_box = Box rev_my_ty

sample_box_13 : {loc : _} -> Exp Examples2.rev_my_ty loc
sample_box_13 = MkRight MkT0

sample_box_14 : {r : _} -> {loc : Loc r} -> Exp Examples2.rev_my_ty_box loc
sample_box_14 = MkBox sample_box_13

sample_box_15 : {r : _} -> {loc : Loc r} -> Exp Examples2.rev_my_ty loc
sample_box_15 = UnBox sample_box_14

sample_box_16 : {r : _} -> {loc : Loc r} -> Exp Examples2.rev_my_ty loc
sample_box_16 = MkLeft $ MkRTup2 sample_box_14 (MkI64 1)

sample_box_17 : {r : _} -> {loc : Loc r} -> Exp Examples2.rev_my_ty loc
sample_box_17 = MkLeft $ MkRTup2 (MkBox sample_box_16) (MkI64 2)

-------------------------------------------
-- END of boxing experiment
-------------------------------------------

i64 : {loc : _} -> Exp I64 loc
i64 = MkI64 1

sample_tup2_01 : {loc : _} -> Exp (RTup2 I64 I64) loc
sample_tup2_01 =
  -- create i64 values
  let i1 = MkI64 101 in
  let i2 = MkI64 201 in
  MkRTup2 i1 i2

sample_tup2_01_sharing : {loc : _} -> Exp (RTup2 I64 (Offset I64)) loc
sample_tup2_01_sharing =
  -- create i64 values
  let i1 = MkI64 101 in
  MkRTup2 i1 (MkOffset i1)

sample_tup2_01_sharing2 : {loc : _} -> Exp (RTup2 (Offset I64) I64) loc
sample_tup2_01_sharing2 =
  -- create i64 values
  let i1 = MkI64 101 in
  MkRTup2 (MkOffset i1) i1


--sample_tup2_03 = sample_tup2_02 {loc = MkLE (LocStart (MkRegion 0))}
{-
sample_print_snd : {loc_in : Loc _} -> {loc_out : _} -> Exp T0 loc_out
sample_print_snd =
  let t = sample_tup2_01_sharing in
  PrjSnd {loc=loc_in }{loc_out} t $ \i =>
  PrintI64 i
-}

sample_tup2_02 : {loc : _} -> Exp (RTup2 (RTup2 I64 I64) (RTup2 I64 I64)) loc
sample_tup2_02 = MkRTup2 sample_tup2_01 sample_tup2_01

sample_print_snd_fst : {loc_out : _} -> Exp T0 loc_out
sample_print_snd_fst =
  LetRegion $ \r =>
  LetRegionValue r sample_tup2_02 $ \t1 =>
  PrjSnd t1 $ \t2 =>
  PrjFst t2 $ \i =>
  PrintI64 i

sample_new_tup_ind : {r : _} -> {loc_out : Loc r} -> Exp (RTup2 (Ptr (RTup2 I64 I64)) (Ptr (RTup2 I64 I64))) loc_out
sample_new_tup_ind =
  LetRegion $ \r2 =>
  LetRegionValue r2 sample_tup2_02 $ \t1 =>
  PrjSnd t1 $ \t2 =>
  MkRTup2 (MkPtr t2) (MkPtr t2)

sample_new_tup_copy : {loc_out : _} -> Exp (RTup2 I64 I64) loc_out
sample_new_tup_copy =
  LetRegion $ \r =>
  LetRegionValue r sample_tup2_02 $ \t1 =>
  PrjSnd t1 $ \t2 =>
  Copy t2

sample_left_01 : {loc : _} -> Exp (Either (RTup2 I64 I64) I64) loc
sample_left_01 = MkLeft sample_tup2_01

sample_tup_either_01 : {loc : _} -> Exp (RTup2 (Either (RTup2 I64 I64) I64) I64) loc
sample_tup_either_01 = MkRTup2 (MkRight (MkI64 11)) (MkI64 222)


sample_print_either_elim : {loc_out : _} -> Exp T0 loc_out
sample_print_either_elim =
  -- allocate value into a new region
  LetRegion $ \r =>
  LetRegionValue r sample_left_01 $ \e1 =>

  -- INSIGHT: the size of the left side of the tuple {s_l} is unknown, it can be anything
  -- PROBLEM: well, it is wrong! the left tup2 is prefrectly constructed, but the size information comes only from the deconstruction side
  -- Q: how to fill it automatically?
  -- basically it is unused part of the type, no constructor belongs to it
  -- IDEA: with coercive subtyping we could implement lattice operations, so the type elaborator unification could calculate the lattice values also

  CaseEither e1
    (\l => PrintI64 (PrjSnd l id))
    (\r => PrintI64 r)

sample_print_either_elim2 : {loc_out : _} -> Exp (Either (RTup2 I64 I64) I64) loc_out
sample_print_either_elim2 =
  LetRegion $ \r =>
  LetRegionValue r sample_left_01 $ \e1 =>
  CaseEither e1
    (\l => Copy e1)
    (\r => Copy e1)

sample_print_either_elim3 : {loc_out : _} -> Exp (Ptr (Either (RTup2 I64 I64) I64)) loc_out
sample_print_either_elim3 =
  LetRegion $ \r =>
  LetRegionValue r sample_left_01 $ \e1 =>
  CaseEither e1
    (\l => MkPtr e1)
    (\r => MkPtr e1)

sample_print_either_elim4 : {loc_out : _} -> Exp (RTup2 (Either (RTup2 I64 I64) I64) I64) loc_out
sample_print_either_elim4 =
  LetRegion $ \r =>
  LetRegionValue r sample_left_01 $ \e1 =>
  let v1 = CaseEither e1
        (\l => MkLeft (MkRTup2 (MkI64 11) (MkI64 22)))
        (\r => MkRight (MkI64 33))
  in MkRTup2 v1 (MkI64 44)

-- TODO: support forward pointers
sample_print_either_elim5_forward_ind : {loc_out : _} -> Exp (RTup2 (Offset I64) (RTup2 (Either (RTup2 I64 I64) I64) I64)) loc_out
sample_print_either_elim5_forward_ind =
  LetRegion $ \r =>
  LetRegionValue r sample_left_01 $ \e1 =>
  let v1 = CaseEither e1
        (\l => MkLeft (MkRTup2 (MkI64 11) (MkI64 22)))
        (\r => MkRight (MkI64 33)) in
  let i1 = MkI64 44 in
  MkRTup2 (MkOffset i1) (MkRTup2 v1 i1)

sample_print_either_elim5_backward_ind : {loc_out : _} -> Exp (RTup2 (RTup2 I64 (Either (RTup2 I64 I64) I64)) (Offset I64)) loc_out
sample_print_either_elim5_backward_ind =
  LetRegion $ \r =>
  LetRegionValue r sample_left_01 $ \e1 =>
  let v1 = CaseEither e1
        (\l => MkLeft (MkRTup2 (MkI64 11) (MkI64 22)))
        (\r => MkRight (MkI64 33)) in
  let i1 = MkI64 44 in
  MkRTup2 (MkRTup2 i1 v1) (MkOffset i1)

test_1 : Program
test_1 =
  let mainFun : {loc_out : _} -> Exp T0 loc_out
      mainFun =
            LetRegion $ \r =>
            LetRegionValue r (MkI64 123) $ \e1 =>
            PrintI64 e1
  in Main mainFun

test_2 : Program
test_2 =
  Main $ LetRegion $ \r =>
         LetRegionValue r (MkI64 123) $ \e1 =>
         PrintI64 e1

test_3 : Program
test_3 =
  Main $ LetRegion $ \r =>
          LetRegionValue r (MkI64 123) $ \e1 =>
          PrintI64 e1

test_4 : Program
test_4 =
  let mainExp : {loc : _} -> Exp T0 loc
      mainExp =
          LetRegion $ \r =>
          LetRegionValue r (MkI64 123) $ \e1 =>
          PrintI64 e1
  in Main mainExp

test_5 : Program
test_5 =
  let myPrint : {r_in : _} -> {loc_in : Loc r_in} -> Exp I64 loc_in -> Exp T0 loc_out
      myPrint i = PrintI64 i
  in Main $
          LetRegion $ \r =>
          LetRegionValue r (MkI64 123) $ \i =>
          FunApp "myPrint" myPrint i

{-
  done:
    add Int primops
      - arithmetic: + - * /
      - comparison: eq lt gt le ge
      - if-then-else
        IDEA: model it with comaprison returning Bool that is modeled with Either T0 T0
              if-then-else is implemented with either eliminator

    write recursive example that creates linked list, i.e. enumerates numbers from 1 to 10
      - count from 1 to 10 and return 10
      - collect numbers from 1 to 10
-}

{-
  IDEA:
    would it be possible to add special region to model stack frame, a region that is local and tied to function scope?
    that would simplify writing programs
-}

test_6 : Program
test_6 =
  let genList : {r_in : _} -> {loc_in : Loc r_in} -> {r_out : _} -> {loc_out : Loc r_out} -> Exp I64 loc_in -> Exp I64 loc_out
      genList i =
        LetRegion $ \r =>
        LetRegionValue r (MkI64 10) $ \ten =>
        LetRegion $ \r =>
        LetRegionValue r (EqI64 ten i) $ \b =>
        CaseEither b
          (\f =>
              LetRegion $ \r =>
              LetRegionValue r (MkI64 1) $ \one =>
              LetRegion $ \r =>
              LetRegionValue r (AddI64 one i) $ \next =>
              FunApp "genList" genList next
          )
          (\t => Copy ten)
  in Main $
      LetRegion $ \r =>
      LetRegionValue r (MkI64 1) $ \i =>
      LetRegion $ \r =>
      LetRegionValue r (FunApp "genList" genList i) $ \i =>
      PrintI64 i

test_7 : Program
test_7 =
  let genList : {r_in : _} -> {loc_in : Loc r_in} -> {r_out : _} -> {loc_out : Loc r_out} -> Exp I64 loc_in -> Exp Examples2.my_ty loc_out
      genList i =
        LetRegion $ \r =>
        LetRegionValue r (MkI64 10) $ \ten =>
        LetRegion $ \r =>
        LetRegionValue r (EqI64 ten i) $ \b =>
        CaseEither b
          (\f =>
              LetRegion $ \r =>
              LetRegionValue r (MkI64 1) $ \one =>
              LetRegion $ \r =>
              LetRegionValue r (AddI64 one i) $ \next =>
              MkLeft $ MkRTup2 (Copy i) $ MkBox $ FunApp "genList" genList next
          )
          (\t => MkRight MkT0)
  in Main $
      LetRegion $ \r =>
      LetRegionValue r (MkI64 1) $ \i =>
      LetRegion $ \r =>
      LetRegionValue r (FunApp "genList" genList i) $ \l =>
      PrintValue l

test_8 : Program
test_8 =
  let genList : {r_in : _} -> {loc_in : Loc r_in} -> {r_out : _} -> {loc_out : Loc r_out} -> Exp I64 loc_in -> Exp Examples2.my_ty loc_out
      genList i =
        LetRegion $ \r =>
        LetRegionValue r (MkI64 10) $ \ten =>
        LetRegion $ \r =>
        LetRegionValue r (EqI64 ten i) $ \b =>
        CaseEither b
          (\f =>
              LetRegion $ \r =>
              LetRegionValue r (MkI64 1) $ \one =>
              LetRegion $ \r =>
              LetRegionValue r (AddI64 one i) $ \next =>
              -- !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
              -- TODO: what should create the end-witness for COPY?
              -- Q: what should be the rules for end-witness construction?
              -- TODO: design the end-witness construction for value consumption primitives
              -- IDEA/HACK: auto construct end-witness for static sized values/types
              -- TODO: design the end-witness creation for either and tup and box type consuming operations
              -- !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
              MkLeft $ MkRTup2 (Copy i) $ MkBox $ FunApp "genList" genList next
          )
          (\t => MkRight MkT0)

      printList : {r_in : _} -> {loc_in : Loc r_in} -> {r_out : _} -> {loc_out : Loc r_out} -> Exp Examples2.my_ty loc_in -> Exp T0 loc_out
      printList a =
        CaseEither a
          (\l =>
              PrjFst l $ \hd =>
              PrjSnd l $ \tl =>
              LetRegion $ \r =>
              LetRegionValue r (PrintI64 hd) $ \t0 =>
              FunApp "printList" printList $ UnBox tl
          )
          (\r => MkT0)
  in Main $
      LetRegion $ \r =>
      LetRegionValue r (MkI64 1) $ \i =>
      LetRegion $ \r =>
      LetRegionValue r (FunApp "genList" genList i) $ \l =>
      LetRegion $ \r =>
      LetRegionValue r (PrintValue l) $ \i =>
      FunApp "printList" printList l

test_9 : Program
test_9 =
  let printList : {r_in : _} -> {loc_in : Loc r_in} -> {r_out : _} -> {loc_out : Loc r_out} -> Exp Examples2.my_ty loc_in -> Exp T0 loc_out
      printList a =
        CaseEither a
          (\l =>
              PrjFst l $ \hd =>
              PrjSnd l $ \tl =>
              LetRegion $ \r =>
              LetRegionValue r (PrintI64 hd) $ \t0 =>
              FunApp "printList" printList $ UnBox tl
          )
          (\r => MkT0)
  in Main $
      LetRegion $ \r =>
      LetRegionValue r sample_box_07 $ \l =>
      FunApp "printList" printList l

test_10 : Program
test_10 =
  let printList : Nat -> {r_in : _} -> {loc_in : Loc r_in} -> {r_out : _} -> {loc_out : Loc r_out} -> Exp Examples2.my_ty loc_in -> Exp T0 loc_out
      printList unroll a =
        CaseEither a
          (\l =>
              PrjFst l $ \hd =>
              PrjSnd l $ \tl =>
              LetRegion $ \r =>
              LetRegionValue r (PrintI64 hd) $ \t0 =>
              case unroll of
                0   => FunApp "printList" (printList 0) $ UnBox tl
                S i => printList i $ UnBox tl
          )
          (\r => MkT0)
  in Main $
      LetRegion $ \r =>
      LetRegionValue r sample_box_07 $ \l =>
      FunApp "printList" (printList 2) l

test_11 : Program
test_11 =
  let printList : Nat -> {r_in : _} -> {loc_in : Loc r_in} -> {r_out : _} -> {loc_out : Loc r_out} -> Exp Examples2.rev_my_ty loc_in -> Exp T0 loc_out
      printList unroll a =
        CaseEither a
          (\l =>
              PrjFst l $ \hd =>
              PrjSnd l $ \tl =>
              LetRegion $ \r =>
              LetRegionValue r (PrintI64 tl) $ \t0 =>
              case unroll of
                0   => FunApp "printList" (printList 0) $ UnBox hd
                S i => printList i $ UnBox hd
          )
          (\r => MkT0)
  in Main $
      LetRegion $ \r =>
      LetRegionValue r sample_box_17 $ \l =>
      LetRegion $ \r =>
      LetRegionValue r (PrintValue l) $ \l2 =>
      FunApp "printList" (printList 2) l

test_12 : Program
test_12 =
  let genList : {r_in : _} -> {loc_in : Loc r_in} -> {r_out : _} -> {loc_out : Loc r_out} -> Exp I64 loc_in -> Exp Examples2.rev_my_ty loc_out
      genList i =
        LetRegion $ \r =>
        LetRegionValue r (MkI64 10) $ \ten =>
        LetRegion $ \r =>
        LetRegionValue r (EqI64 ten i) $ \b =>
        CaseEither b
          (\f =>
              LetRegion $ \r =>
              LetRegionValue r (MkI64 1) $ \one =>
              LetRegion $ \r =>
              LetRegionValue r (AddI64 one i) $ \next =>
              -- !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
              -- TODO: what should create the end-witness for COPY?
              -- Q: what should be the rules for end-witness construction?
              -- TODO: design the end-witness construction for value consumption primitives
              -- IDEA/HACK: auto construct end-witness for static sized values/types
              -- TODO: design the end-witness creation for either and tup and box type consuming operations
              -- !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
              MkLeft $ MkRTup2 (MkBox $ FunApp "genList" genList next) (Copy i)
          )
          (\t => MkRight MkT0)

      printList : {r_in : _} -> {loc_in : Loc r_in} -> {r_out : _} -> {loc_out : Loc r_out} -> Exp Examples2.rev_my_ty loc_in -> Exp T0 loc_out
      printList a =
        CaseEither a
          (\l =>
              PrjFst l $ \tl =>
              PrjSnd l $ \hd =>
              LetRegion $ \r =>
              LetRegionValue r (PrintI64 hd) $ \t0 =>
              FunApp "printList" printList $ UnBox tl
          )
          (\r => MkT0)
  in Main $
      LetRegion $ \r =>
      LetRegionValue r (MkI64 1) $ \i =>
      LetRegion $ \r =>
      LetRegionValue r (FunApp "genList" genList i) $ \l =>
      LetRegion $ \r =>
      LetRegionValue r (PrintValue l) $ \i =>
      FunApp "printList" printList l

test_13 : Program
test_13 = Main $
      LetRegion $ \r =>
      let i1 = MkI64 1 in
      LetRegionValue r (MkRTup2 i1 (MkOffset i1)) $ \v =>
      LetRegion $ \r =>
      LetRegionValue r (PrintValue v) $ \_ =>
      PrjFst v $ \i2 =>
      PrjSnd v $ \i3 =>
      DeRefOffset i3 $ \_,i4 =>
      PrintI64 i4

test_14 : Program
test_14 = Main $
      LetRegion $ \r =>
      let i1 = MkI64 1 in
      LetRegionValue r (MkRTup2 i1 (MkPtr i1)) $ \v =>
      LetRegion $ \r =>
      LetRegionValue r (PrintValue v) $ \_ =>
      PrjFst v $ \i2 =>
      PrjSnd v $ \i3 =>
      DeRefPtr i3 $ \_,_,i4 =>
      PrintI64 i4

test_15 : Program
test_15 =
  let printPair : {r_in : _} -> {loc_in : Loc r_in} -> {r_out : _} -> {loc_out : Loc r_out} -> Exp (STup2 I64 I64) loc_in -> Exp T0 loc_out
      printPair p =
        CaseSTup2 p $ \fst, snd =>
        PrintI64 fst
  in Main $
      LetRegion $ \r =>
      LetRegionValue r (MkSTup2 (MkI64 7) (MkI64 8)) $ \l =>
      FunApp "printPair" printPair l

test_16 : Program
test_16 =
  let printPair : {r_in : _} -> {loc_in : Loc r_in} -> {r_out : _} -> {loc_out : Loc r_out} -> Exp (STup2 I64 I64) loc_in -> Exp T0 loc_out
      printPair p =
        CaseSTup2 p $ \fst, snd =>
        LetRegion $ \r =>
        LetRegionValue r (PrintI64 fst) $ \_ =>
        PrintI64 snd
  in Main $
      LetRegion $ \r =>
      LetRegionValue r (MkSTup2 (MkI64 7) (MkI64 8)) $ \l =>
      FunApp "printPair" printPair l

test_17 : Program
test_17 =
  let printPair : {r_in : _} -> {loc_in : Loc r_in} -> {r_out : _} -> {loc_out : Loc r_out} -> Exp (STup2 I64 I64) loc_in -> Exp T0 loc_out
      printPair p =
        CaseSTup2 p $ \fst, snd =>
        LetRegion $ \r =>
        LetRegionValue r (PrintI64 snd) $ \_ =>
        PrintI64 fst
  in Main $
      LetRegion $ \r =>
      LetRegionValue r (MkSTup2 (MkI64 7) (MkI64 8)) $ \l =>
      FunApp "printPair" printPair l

-- test

partial main : IO ()
main = do
  --putStr !(toBufferDyn sample_box_03)
  --putStr !(toBufferDyn sample_box_04)
  --putStr !(toBufferDyn sample_box_05)
  --putStr !(toBufferDyn sample_box_06)
  --putStr !(toBufferDyn sample_box_07)
  {-
  putStr !(toBufferDyn i64)
  putStr !(toBufferDyn sample_tup2_01)
  putStr !(toBufferDyn sample_tup2_01_sharing)
  putStr !(toBufferDyn sample_tup2_01_sharing2)
  putStr !(toBufferDyn sample_tup2_02)
  putStr !(toBufferDyn sample_left_01)
  putStr !(toBufferDyn sample_tup_either_01)
  putStr !(toBufferDyn sample_print_snd_fst)
  putStr !(toBufferDyn sample_new_tup_ind)
  putStr !(toBufferDyn sample_new_tup_copy)
  putStr !(toBufferDyn sample_print_either_elim)
  -}
  --putStr !(toBufferDyn i64)
  --putStr !(toBufferDyn sample_tup2_02)
  --pure ()
  --putStr !(toBufferDyn sample_tup2_01)
  --putStr !(toBufferDyn sample_tup2_01_sharing)
  --putStr !(toBufferDyn sample_tup2_01_sharing2)
  --putStr !(toBufferDyn sample_left_01)
  --putStr !(toBufferDyn sample_tup_either_01)
  --putStr !(toBufferDyn sample_print_snd_fst)
  --putStr !(toBufferDyn sample_print_either_elim)
  --putStr !(toBufferDyn sample_print_either_elim4)
  --putStr !(toBufferDyn sample_print_either_elim2)
  --putStr !(toBufferDyn sample_print_either_elim5_forward_ind) -- TODO
  --putStr !(toBufferDyn sample_print_either_elim5_backward_ind)
  _ <- compileProgram "test11" test_11
  _ <- compileProgram "test8" test_8
  _ <- compileProgram "test12" test_12
  _ <- compileProgram "test13" test_13
  _ <- compileProgram "test14" test_14
  _ <- compileProgram "test15" test_15
  _ <- compileProgram "test16" test_16
  -- _ <- compileProgram "test17" test_17 -- this test should fail, because snd is used first in an STup2
  pure ()
{-
TODO:
  list:
    map (+1) list
    filter
    sum
    append

  tree
    build
    sum
-}
