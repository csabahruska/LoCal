module Examples2

import LoCal
import Dynamic

-------------------------------------------
-- Boxing experiment --------------
-------------------------------------------

-- data IntList = Cons Int IntList
--              | Nil

My_ty : Ty
My_ty = Either (Pair I64 $ Box My_ty) T0

sample_box_03 : {r : _} -> {loc : Loc r} -> Exp My_ty loc EW
sample_box_03 = MkRight MkT0

sample_box_04 : {r : _} -> {loc : Loc r} -> Exp (Box My_ty) loc EW
sample_box_04 = MkBox sample_box_03

sample_box_05 : {r : _} -> {loc : Loc r} -> Exp My_ty loc EW
sample_box_05 = UnBox sample_box_04

sample_box_06 : {r : _} -> {loc : Loc r} -> Exp My_ty loc EW
sample_box_06 = MkLeft $ MkPair (MkI64 1) sample_box_04

sample_box_07 : {r : _} -> {loc : Loc r} -> Exp My_ty loc EW
sample_box_07 = MkLeft $ MkPair (MkI64 2) $ MkBox sample_box_06

-- data IntList = Cons IntList Int
--              | Nil

Rev_my_ty : Ty
Rev_my_ty = Either (Pair (Offset I64) $ Pair (Box Rev_my_ty) I64) T0

sample_box_13 : {r : _} -> {loc : Loc r} -> Exp Rev_my_ty loc EW
sample_box_13 = MkRight MkT0

sample_box_14 : {r : _} -> {loc : Loc r} -> Exp (Box Rev_my_ty) loc EW
sample_box_14 = MkBox sample_box_13

sample_box_15 : {r : _} -> {loc : Loc r} -> Exp Rev_my_ty loc EW
sample_box_15 = UnBox sample_box_14

sample_box_16 : {r : _} -> {loc : Loc r} -> Exp Rev_my_ty loc EW
sample_box_16 = MkLeft $ let i = MkI64 1 in MkPair (MkOffset i) $ MkPair (MkBox sample_box_13) i

sample_box_17 : {r : _} -> {loc : Loc r} -> Exp Rev_my_ty loc EW
sample_box_17 = MkLeft $ let i = MkI64 2 in MkPair (MkOffset i) $ MkPair (MkBox sample_box_16) i

-------------------------------------------
-- END of boxing experiment
-------------------------------------------

i64 : {r : _} -> {loc : Loc r} -> Exp I64 loc EW
i64 = MkI64 1

sample_tup2_01 : {r : _} -> {loc : Loc r} -> Exp (Pair I64 I64) loc EW
sample_tup2_01 =
  -- create i64 values
  let i1 = MkI64 101 in
  let i2 = MkI64 102 in
  MkPair i1 i2

sample_tup2_01_sharing : {r : _} -> {loc : Loc r} -> Exp (Pair I64 (Offset I64)) loc EW
sample_tup2_01_sharing =
  -- create i64 values
  let i1 = MkI64 101 in
  MkPair i1 (MkOffset i1)

sample_tup2_01_sharing2 : {r : _} -> {loc : Loc r} -> Exp (Pair (Offset I64) I64) loc EW
sample_tup2_01_sharing2 =
  -- create i64 values
  let i1 = MkI64 101 in
  MkPair (MkOffset i1) i1

sample_tup2_02 : {r : _} -> {loc : Loc r} -> Exp (Pair (Pair I64 I64) (Pair I64 I64)) loc EW
sample_tup2_02 = MkPair sample_tup2_01 sample_tup2_01
{-
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
-}
{-
test_1 : Program
test_1 = Main $
  MkI64 123 $ \i =>
  PrintI64 i $ \i =>
  i

test_2 : Program
test_2 = Main $
  LetRegion $ \r =>
  LetRegionValue r (MkI64 123 id) $ \e1 =>
  PrintI64 e1 $ \e1 =>
  MkT0 id

test_5 : Program
test_5 =
  let myPrint : {r_out : _} -> {loc_out : Loc r_out} -> {r_in : _} -> {loc_in : Loc r_in} -> Exp I64 loc_in EW -> Exp T0 loc_out EW
      myPrint i = PrintI64 i $ \i => MkT0 id
  in Main $
      LetRegion $ \r =>
      LetRegionValue r (MkI64 123 id) $ \i =>
      FunApp "myPrint" myPrint i $ \r => r
-}
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
{-
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
  let genList : {r_in : _} -> {loc_in : Loc r_in} -> {r_out : _} -> {loc_out : Loc r_out} -> Exp I64 loc_in -> Exp My_ty loc_out
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
  let genList : {r_in : _} -> {loc_in : Loc r_in} -> {r_out : _} -> {loc_out : Loc r_out} -> Exp I64 loc_in -> Exp My_ty loc_out
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

      printList : {r_in : _} -> {loc_in : Loc r_in} -> {r_out : _} -> {loc_out : Loc r_out} -> Exp My_ty loc_in -> Exp T0 loc_out
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
  let printList : {r_in : _} -> {loc_in : Loc r_in} -> {r_out : _} -> {loc_out : Loc r_out} -> Exp My_ty loc_in -> Exp T0 loc_out
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
-}
{-
test_10 : Program
test_10 =
  let printList : Nat -> {ew : _} -> {r_in : _} -> {loc_in : Loc r_in} -> {r_out : _} -> {loc_out : Loc r_out} -> Exp My_ty loc_in ew -> Exp T0 loc_out EW
      printList unroll a =
        CaseEither a
          (\l =>
              PrjFst l $ \l, hd =>
              PrjSnd l $ \l, tl =>
              PrintI64 hd $ \hd =>
              UnBox tl $ \tl, utl =>
              case unroll of
                0   => FunApp "printList" (printList 0) utl id
                S i => printList i utl
          )
          (\r => MkT0 id)

  in Main $
      LetRegion $ \r =>
      LetRegionValue r sample_box_07 $ \l =>
      PrintValue l $ \l =>
      FunApp "printList" (printList 2) l $ \l =>
      l

test_11 : Program
test_11 =
  let printList : Nat -> {ew : _} -> {r_in : _} -> {loc_in : Loc r_in} -> {r_out : _} -> {loc_out : Loc r_out} -> Exp Rev_my_ty loc_in ew -> Exp T0 loc_out EW
      printList unroll a =
        CaseEither a
          (\l =>
              PrjFst l $ \l, hd =>
              PrjSnd l $ \l, tl =>
              PrintI64 tl $ \t0 =>
              UnBox hd $ \hd, uhd =>
              case unroll of
                0   => FunApp "printList" (printList 0) uhd id
                S i => printList i uhd
          )
          (\r => MkT0 id)

  in Main $
      LetRegion $ \r =>
      LetRegionValue r sample_box_17 $ \l =>
      PrintValue l $ \l =>
      FunApp "printList" (printList 2) l $ \l =>
      l
-}

test_12 : Program
test_12 =
  let genList : {r_in : _} -> {loc_in : Loc r_in} -> {r_out : _} -> {loc_out : Loc r_out} -> Exp I64 loc_in NoEW -> Exp Rev_my_ty loc_out EW
      genList i =
        LetRegion $ \r =>
        LetRegionValue r (EqI64C 10 i) $ \b =>
        CaseEither b
          (\f =>
              LetRegion $ \r =>
              LetRegionValue r (AddI64C 1 i) $ \next =>
              -- !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
              -- TODO: what should create the end-witness for COPY?
              -- Q: what should be the rules for end-witness construction?
              -- TODO: design the end-witness construction for value consumption primitives
              -- IDEA/HACK: auto construct end-witness for static sized values/types
              -- TODO: design the end-witness creation for either and tup and box type consuming operations
              -- !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
              ------------------------------------------
              -- BUG! how to handle this?
              {-
              -- failing -- Q: what is this situation?
              Copy i $ \i, i_copy =>
              FunApp "genList" genList next $ \res =>
              -}
              -- working
              let res = FunApp2 "genList" genList next in
              --FunApp "genList" genList next $ \res =>
              MkLeft $ let i = Copy $ MkStaticEW i in MkPair (MkOffset i) $ MkPair (MkBox res) i
          )
          (\t => MkRight MkT0)

      printList : {ew : _} -> {r_in : _} -> {loc_in : Loc r_in} -> {r_out : _} -> {loc_out : Loc r_out} -> Exp Rev_my_ty loc_in ew -> Exp T0 loc_out EW
      printList a =
        CaseEither a
          (\l =>
              CasePair l $ \ofs, list_fun =>
              let lst = list_fun $ MkStaticEW ofs in
              CasePair lst $ \lst, snd_fun =>
              DeRefOffset ofs $ \i =>
              PrintI64 i $ \_ =>
              FunApp2 "printList" printList (UnBox lst)
          )
          (\r => MkT0)

      mapSuccList : {ew : _} -> {r_in : _} -> {loc_in : Loc r_in} -> {r_out : _} -> {loc_out : Loc r_out} ->
                    Exp Rev_my_ty loc_in ew -> Exp Rev_my_ty loc_out EW
      mapSuccList a =
        CaseEither a
          (\l =>
              CasePair l $ \ofs, list_fun =>
              let lst = list_fun $ MkStaticEW ofs in
              CasePair lst $ \lst, snd_fun =>
              DeRefOffset ofs $ \i =>

              let res = FunApp2 "mapSuccList" mapSuccList (UnBox lst) in
              MkLeft $ let i = MkStaticEW $ AddI64C 1 i in MkPair (MkOffset i) $ MkPair (MkBox res) i
              -- TODO: return input end-witness
          )
          --(\r => MkRight $ Copy $ MkStaticEW r)
          (\r => MkRight MkT0)

      filterLt5List : {ew : _} -> {r_in : _} -> {loc_in : Loc r_in} -> {r_out : _} -> {loc_out : Loc r_out} ->
                    Exp Rev_my_ty loc_in ew -> Exp Rev_my_ty loc_out EW
      filterLt5List a =
        CaseEither a
          (\l =>
              CasePair l $ \ofs, list_fun =>
              let lst = list_fun $ MkStaticEW ofs in
              CasePair lst $ \lst, snd_fun =>
              DeRefOffset ofs $ \i =>
              LetRegion $ \r =>
              LetRegionValue r (LtI64C 5 i) $ \b =>
              CaseEither b
                (\f => FunApp2 "filterLt5List" filterLt5List (UnBox lst))
                (\t => let res = FunApp2 "filterLt5List" filterLt5List (UnBox lst) in
                       MkLeft $ let i = Copy $ MkStaticEW i in MkPair (MkOffset i) $ MkPair (MkBox res) i
                )
              -- TODO: return input end-witness
          )
          --(\r => MkRight $ Copy $ MkStaticEW r)
          (\r => MkRight MkT0)

    -- error
      {-
      copyList : {ew_in1 : _} -> {r_in1 : _} -> {loc_in1 : Loc r_in1} -> Exp Rev_my_ty loc_in1 ew_in1 ->
                 {r_out : _} -> {loc_out : Loc r_out} -> Exp Rev_my_ty loc_out EW
      -}
    -- ok
      copyList : {ew_in1 : _} -> {r_in1 : _} -> {loc_in1 : Loc r_in1} -> {r_out : _} -> {loc_out : Loc r_out} ->
                 Exp Rev_my_ty loc_in1 ew_in1 -> Exp Rev_my_ty loc_out EW
      copyList a =
        CaseEither a
          (\l =>
              CasePair l $ \ofs, list_fun =>
              let lst = list_fun $ MkStaticEW ofs in
              CasePair lst $ \lst, snd_fun =>
              DeRefOffset ofs $ \i =>
              let res = FunApp2 "copyList" copyList (UnBox lst) in
              MkLeft $ let i = Copy $ MkStaticEW i in MkPair (MkOffset i) $ MkPair (MkBox res) i
              -- TODO: return input end-witness
          )
          (\r => MkRight MkT0)


      appendList : {ew_in1 : _} -> {r_in1 : _} -> {loc_in1 : Loc r_in1} ->
                   {ew_in2 : _} -> {r_in2 : _} -> {loc_in2 : Loc r_in2} ->
                   {r_out : _} -> {loc_out : Loc r_out} ->
                   Arg [Exp Rev_my_ty loc_in1 ew_in1, Exp Rev_my_ty loc_in2 ew_in2] ->
                   Exp Rev_my_ty loc_out EW
      appendList (ArgN a (Arg1 b)) =
        CaseEither a
          (\l =>
              CasePair l $ \ofs, list_fun =>
              let lst = list_fun $ MkStaticEW ofs in
              CasePair lst $ \lst, snd_fun =>
              DeRefOffset ofs $ \i =>
              let res = FunAppNew "appendList" appendList $ ArgN (UnBox lst) $ Arg1 b in
              MkLeft $ let i = Copy $ MkStaticEW i in MkPair (MkOffset i) $ MkPair (MkBox res) i
              -- TODO: return input end-witness
          )
          (\r => FunApp2 "copyList" copyList b)

  in Main $
      LetRegion $ \r =>
      LetRegionValue r (MkI64 1) $ \i =>
      LetRegion $ \r =>
      LetRegionValue r (FunApp2 "genList" genList i) $ \l =>
      PrintValue l $ \_ =>
      FunApp2 "printList" printList l


test_13 : Program
test_13 = Main $
      LetRegion $ \r =>
      LetRegionValue r (let i1 = MkI64 9 in MkPair i1 (MkOffset i1)) $ \v =>
      PrintValue v $ \_ =>
      CasePair v $ \i2, snd_fun =>
      let i3 = snd_fun (MkStaticEW i2) in
      DeRefOffset i3 $ \i4 =>
      PrintI64 i4 $ \_ =>
      MkT0

test_14 : Program
test_14 = Main $
      LetRegion $ \r =>
      LetRegionValue r (let i1 = MkI64 9 in MkPair i1 (MkPtr i1)) $ \v =>
      PrintValue v $ \_ =>
      CasePair v $ \i2, snd_fun =>
      let i3 = snd_fun (MkStaticEW i2) in
      DeRefPtr i3 $ \i4 =>
      PrintI64 i4 $ \_ =>
      MkT0

test_15 : Program
test_15 =
  let printPair : {ew : _} -> {r_in : _} -> {loc_in : Loc r_in} -> {r_out : _} -> {loc_out : Loc r_out} -> Exp (Pair I64 I64) loc_in ew -> Exp T0 loc_out EW
      printPair p =
        CasePair p $ \fst, snd_fun =>
        PrintI64 fst $ \fst =>
        MkT0
  in Main $
      LetRegion $ \r =>
      LetRegionValue r (MkPair (MkI64 7) (MkI64 8)) $ \t1 =>
      FunApp2 "printPair" printPair t1

test_16 : Program
test_16 =
  let printPair : {ew : _} -> {r_in : _} -> {loc_in : Loc r_in} -> {r_out : _} -> {loc_out : Loc r_out} -> Exp (Pair I64 I64) loc_in ew -> Exp T0 loc_out EW
      printPair p =
        CasePair p $ \fst, snd_fun =>
        PrintI64 fst $ \_ =>
        let snd = snd_fun (MkStaticEW fst) in
        PrintI64 snd $ \_ =>
        MkT0
  in Main $
      LetRegion $ \r =>
      LetRegionValue r (MkPair (MkI64 7) (MkI64 8)) $ \t1 =>
      FunApp2 "printPair" printPair t1

test_17 : Program
test_17 =
  let printPair : {ew : _} -> {r_in : _} -> {loc_in : Loc r_in} -> {r_out : _} -> {loc_out : Loc r_out} -> Exp (Pair I64 I64) loc_in ew -> Exp T0 loc_out EW
      printPair p =
        CasePair p $ \fst, snd_fun =>
        let snd = snd_fun (MkStaticEW fst) in
        PrintI64 snd $ \_ =>
        PrintI64 fst $ \_ =>
        MkT0
  in Main $
      LetRegion $ \r =>
      LetRegionValue r (MkPair (MkI64 7) (MkI64 8)) $ \t1 =>
      FunApp2 "printPair" printPair t1

test_20 : Program
test_20 =
  let printPair2 : {r_in : _} -> {loc_in : Loc r_in} -> {r_out : _} -> {loc_out : Loc r_out} ->
                   Arg [Exp (Pair I64 I64) loc_in ew_in] -> Exp T0 loc_out EW
      printPair2 (Arg1 p) =
        CasePair p $ \fst, snd_fun =>
        let snd = snd_fun (MkStaticEW fst) in
        PrintI64 snd $ \_ =>
        PrintI64 fst $ \_ =>
        MkT0
  in Main $
      LetRegion $ \r =>
      LetRegionValue r (MkPair (MkI64 7) (MkI64 8)) $ \t1 =>
      FunAppNew "printPair2" printPair2 $ Arg1 t1

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
  -}
  --_ <- compileProgram "sample_tup2_01_rev_cont" $ Main sample_tup2_01_rev_cont
  _ <- compileProgram "sample_tup2_01" $ Main sample_tup2_01
  _ <- compileProgram "sample_tup2_02" $ Main sample_tup2_02
  {-
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
  {-
  _ <- compileProgram "test01" test_1
  _ <- compileProgram "test02" test_2
  _ <- compileProgram "test05" test_5
  -}
  {-
  _ <- compileProgram "test8" test_8
  -}
  {-
  _ <- compileProgram "test10" test_10
  _ <- compileProgram "test11" test_11
  -}
  _ <- compileProgram "test12" test_12
  _ <- compileProgram "test13" test_13
  _ <- compileProgram "test14" test_14
  _ <- compileProgram "test15" test_15
  _ <- compileProgram "test16" test_16
  _ <- compileProgram "test17" test_17
  pure ()
{-
TODO:
  list:
    done - map (+1) list
    done - filter
    sum
    done - append

  tree
    build
    sum
-}
