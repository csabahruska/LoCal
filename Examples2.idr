module Examples2

import LoCal
import Dynamic

--export infixr 5 #
export infixr 5 ##

%inline
(#) : Ty -> Ty -> Ty
(#) a b = Pair a b

%inline
(##) : {a, b : Ty} -> {loc : _} ->
    let locFst = LocAfterTag "Pair" a loc in
    let locSnd = LocAfter b locFst in
    Exp a locFst EW [] -> Exp b locSnd EW [] -> Exp (Pair a b) loc EW []

(##) = MkPair

-- RTup2 a b   = Pair (Offset b) (Pair a b)
-- RTup3 a b c = Pair (Offset b) (Pair (Offset c) (Pair a (Pair b c)))
-- RTup3 a b c = Offset b # Offset c # a # b # c


{-
sample_tup2_01 : {r : _} -> {loc : Loc r} -> Exp (Offset I64 # I64 # I64) loc EW
sample_tup2_01 = let a = MkI64' 102 in MkOffset a ## MkI64 12 ## MkI64 103

sample_tup2_02 : {r : _} -> {loc : Loc r} -> Exp (I64 # Offset I64 # I64 # I64) loc EW
sample_tup2_02 = let a = MkI64 102 in a ## MkOffset a ## a ## MkI64 103
-}

-- TODO: codegen this
sample_tup2_03 : {r : _} -> {loc : Loc r} -> Exp (I64 # Offset I64 # I64 # I64) loc EW []
sample_tup2_03 = let a = MkI64 102 in MkPair (Copy a) $ MkPair (MkOffset a) $ MkPair ( a) $ MkI64 103
{-
sample_tup2_03_err : {r : _} -> {loc : Loc r} -> Exp (I64 # Offset I64 # I64 # I64) loc EW
sample_tup2_03_err = let a = MkI64 102 in MkPair a $ MkPair (MkOffset a) $ MkPair a $ MkI64 103
-}
sample_a : {r : _} -> {loc : Loc r} -> Exp I64 loc EW []
sample_a = MkI64 102

{-
sample_tup2_03_err : {r : _} -> {loc : Loc r} -> Exp (I64 # I64) loc EW
sample_tup2_03_err = let a = MkI64 102 in MkPair a a
-}

sample_tup2_04 : {r : _} -> {loc : Loc r} -> Exp (I64 # I64) loc EW []
sample_tup2_04 = MkPair sample_a sample_a

My_ty3 : Ty
My_ty3 = Ptr $ Box "My_ty3" My_ty3

sample_box_ptr : {r : _} -> {loc : Loc r} -> Exp My_ty3 loc EW []
sample_box_ptr = MkPtr {loc_in=loc} $ MkBox sample_box_ptr

public export
AddI64 : {r1, r2 : _} -> {ew1, ew2 : _} -> {loc_in1 : Loc r1} -> {loc_in2 : Loc r2} -> Exp I64 loc_in1 ew1 [] -> Exp I64 loc_in2 ew2 [] -> Exp I64 loc EW []
AddI64 = I64Op2 Plus

public export
EqI64 : {r1, r2 : _} -> {ew1, ew2 : _} -> {loc_in1 : Loc r1} -> {loc_in2 : Loc r2} -> Exp I64 loc_in1 ew1 [] -> Exp I64 loc_in2 ew2 [] -> Exp (Either T0 T0) loc EW []
EqI64 = I64Cmp EQ

public export
AddI64C : Int -> {r1 : _} -> {ew1 : _} -> {loc_in1 : Loc r1} -> Exp I64 loc_in1 ew1 [] -> Exp I64 loc EW []
AddI64C i e = LetRegion $ \r => LetRegionValue r (MkI64 i) $ \i => I64Op2 Plus i e

public export
EqI64C, LtI64C : Int -> {r1 : _} -> {ew1 : _} -> {loc_in1 : Loc r1} -> Exp I64 loc_in1 ew1 [] -> Exp (Either T0 T0) loc EW []
EqI64C i e = LetRegion $ \r => LetRegionValue r (MkI64 i) $ \i => I64Cmp EQ e i
LtI64C i e = LetRegion $ \r => LetRegionValue r (MkI64 i) $ \i => I64Cmp LT e i

-------------------------------------------
-- Boxing experiment --------------
-------------------------------------------

-- data IntList = Cons Int IntList
--              | Nil

My_ty : Ty
My_ty = Either (Pair I64 $ Box "My_ty" My_ty) T0

sample_box_03 : {r : _} -> {loc : Loc r} -> Exp My_ty loc EW []
sample_box_03 = MkRight MkT0

sample_box_04 : {r : _} -> {loc : Loc r} -> Exp (Box "My_ty" My_ty) loc EW []
sample_box_04 = MkBox sample_box_03

sample_box_05 : {r : _} -> {loc : Loc r} -> Exp My_ty loc EW []
sample_box_05 = UnBox sample_box_04

sample_box_06 : {r : _} -> {loc : Loc r} -> Exp My_ty loc EW []
sample_box_06 = MkLeft $ MkPair (MkI64 1) sample_box_04

sample_box_07 : {r : _} -> {loc : Loc r} -> Exp My_ty loc EW []
sample_box_07 = MkLeft $ MkPair (MkI64 2) $ MkBox sample_box_06

-- data IntList = Cons IntList Int
--              | Nil

Rev_my_ty : Ty
Rev_my_ty = Either (Pair (Offset I64) $ Pair (Box "Rev_my_ty" Rev_my_ty) I64) T0

sample_box_13 : {r : _} -> {loc : Loc r} -> Exp Rev_my_ty loc EW []
sample_box_13 = MkRight MkT0

sample_box_14 : {r : _} -> {loc : Loc r} -> Exp (Box "Rev_my_ty" Rev_my_ty) loc EW []
sample_box_14 = MkBox sample_box_13

sample_box_15 : {r : _} -> {loc : Loc r} -> Exp Rev_my_ty loc EW []
sample_box_15 = UnBox sample_box_14

sample_box_16 : {r : _} -> {loc : Loc r} -> Exp Rev_my_ty loc EW []
sample_box_16 = MkLeft $ let i = MkI64 1 in MkPair (MkOffset i) $ MkPair (MkBox sample_box_13) i

sample_box_17 : {r : _} -> {loc : Loc r} -> Exp Rev_my_ty loc EW []
sample_box_17 = MkLeft $ let i = MkI64 2 in MkPair (MkOffset i) $ MkPair (MkBox sample_box_16) i

-------------------------------------------
-- END of boxing experiment
-------------------------------------------

i64 : {r : _} -> {loc : Loc r} -> Exp I64 loc EW []
i64 = MkI64 1

sample_tup2_01 : {r : _} -> {loc : Loc r} -> Exp (Pair I64 I64) loc EW []
sample_tup2_01 =
  -- create i64 values
  let i1 = MkI64 101 in
  let i2 = MkI64 102 in
  MkPair i1 i2

sample_tup2_01_sharing : {r : _} -> {loc : Loc r} -> Exp (Pair I64 (Offset I64)) loc EW []
sample_tup2_01_sharing =
  -- create i64 values
  let i1 = MkI64 101 in
  MkPair i1 (MkOffset i1)

sample_tup2_01_sharing2 : {r : _} -> {loc : Loc r} -> Exp (Pair (Offset I64) I64) loc EW []
sample_tup2_01_sharing2 =
  -- create i64 values
  let i1 = MkI64 101 in
  MkPair (MkOffset i1) i1

sample_tup2_02 : {r : _} -> {loc : Loc r} -> Exp (Pair (Pair I64 I64) (Pair I64 I64)) loc EW []
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
covering
mapSuccList_rev : {ew : _} -> {r_out : _} -> {loc_out : Loc r_out} ->
              Arg [Exp Rev_my_ty loc_in ew []] -> Exp Rev_my_ty loc_out EW []
mapSuccList_rev (ArgN a Arg0) =
  CaseEither a
    (\l =>
        let ofs = GetFst l in
        let lst = GetFst $ GetSnd l $ StaticEW ofs in
        DeRefOffset ofs $ \i =>

        let res = FunAppDef "mapSuccList_rev" mapSuccList_rev (ArgN (UnBox lst) Arg0) in
        MkLeft $ let j = AddI64C 1 i in MkPair (MkOffset j) $ MkPair (MkBox res) j
        -- TODO: return input end-witness
    )
    --(\r => MkRight $ Copy $ StaticEW r)
    (\r => MkRight MkT0)

mapSuccList_rev_bug : {ew : _} -> {r_out : _} -> {loc_out : Loc r_out} ->
              Arg [Exp Rev_my_ty loc_in ew []] -> Exp Rev_my_ty loc_out EW []
mapSuccList_rev_bug (ArgN a Arg0) =
  CaseEither a
    (\l =>
        let ofs = GetFst l in
        let lst = GetFst $ GetSnd l $ StaticEW ofs in
        DeRefOffset ofs $ \i => -- shadowing
        -- Q: why does not compile?
        -- Q: what is the meaning?
        -- Q: is it correct at all?

        let res = FunAppDef "mapSuccList_rev_bug" mapSuccList_rev_bug (ArgN (UnBox lst) Arg0) in
        MkLeft $ let i = AddI64C 1 i in MkPair (MkOffset i) $ MkPair (MkBox res) i
        -- TODO: return input end-witness
    )
    --(\r => MkRight $ Copy $ StaticEW r)
    (\r => MkRight MkT0)

genList_rev : {r_out : _} -> {loc_out : Loc r_out} -> Arg [Exp I64 loc_in EW []] -> Exp Rev_my_ty loc_out EW []
genList_rev (ArgN i Arg0) =
  LetRegion $ \r =>
  LetRegionValue r (EqI64C 10 i) $ \b =>
  CaseEither b
    (\f =>
        LetRegion $ \r =>
        LetRegionValue r (AddI64C 1 i) $ \next =>
        -- working
        let res = FunAppDef "genList_rev" genList_rev (ArgN next Arg0) in
        --FunApp "genList_rev" genList_rev next $ \res =>
        MkLeft $ let j = Copy $ StaticEW i in MkPair (MkOffset j) $ MkPair (MkBox res) j
    )
    (\t => MkRight MkT0)

printList_rev : {ew : _} -> {r_out : _} -> {loc_out : Loc r_out} -> Arg [Exp Rev_my_ty loc_in ew []] -> Exp T0 loc_out EW []
printList_rev (ArgN a Arg0) =
  CaseEither a
    (\l =>
        let ofs = GetFst l in
        let lst = GetFst $ GetSnd l $ StaticEW ofs in
        DeRefOffset ofs $ \i =>
        PrintI64 i $ \_ =>
        FunAppDef "printList_rev" printList_rev (ArgN (UnBox lst) Arg0)
    )
    (\r => MkT0)

filterLt5List_rev : {ew : _} -> {r_out : _} -> {loc_out : Loc r_out} ->
              Arg [Exp Rev_my_ty loc_in ew []] -> Exp Rev_my_ty loc_out EW []
filterLt5List_rev (ArgN a Arg0) =
  CaseEither a
    (\l =>
        let ofs = GetFst l in
        let lst = GetFst $ GetSnd l $ StaticEW ofs in
        DeRefOffset ofs $ \i =>
        LetRegion $ \r =>
        LetRegionValue r (LtI64C 5 i) $ \b =>
        CaseEither b
          (\f => FunAppDef "filterLt5List_rev" filterLt5List_rev (ArgN (UnBox lst) Arg0))
          (\t => let res = FunAppDef "filterLt5List_rev" filterLt5List_rev (ArgN (UnBox lst) Arg0) in
                 MkLeft $ let j = Copy $ StaticEW i in MkPair (MkOffset j) $ MkPair (MkBox res) j
          )
        -- TODO: return input end-witness
    )
    --(\r => MkRight $ Copy $ StaticEW r)
    (\r => MkRight MkT0)

copyList_rev : {ew_in1 : _} -> {r_out : _} -> {loc_out : Loc r_out} ->
           Arg [Exp Rev_my_ty loc_in1 ew_in1 []] -> Exp Rev_my_ty loc_out EW []
copyList_rev (ArgN a Arg0) =
  CaseEither a
    (\l =>
        let ofs = GetFst l in
        let lst = GetFst $ GetSnd l $ StaticEW ofs in
        DeRefOffset ofs $ \i =>
        let res = FunAppDef "copyList_rev" copyList_rev (ArgN (UnBox lst) Arg0) in
        MkLeft $ let j = Copy $ StaticEW i in MkPair (MkOffset j) $ MkPair (MkBox res) j
        -- TODO: return input end-witness
    )
    (\r => MkRight MkT0)

--covering
appendList_rev :  {ew_in1 : _} ->
                  {ew_in2 : _} ->
             {r_out : _} -> {loc_out : Loc r_out} ->
             -- ????? why should we specify n=2 ???
             Arg {n=2} [Exp Rev_my_ty loc_in1 ew_in1 [], Exp Rev_my_ty loc_in2 ew_in2 []] ->
             Exp Rev_my_ty loc_out EW []
appendList_rev (ArgN a (ArgN b Arg0)) =
  CaseEither a
    (\l =>
        let ofs = GetFst l in
        let lst = GetFst $ GetSnd l $ StaticEW ofs in
        DeRefOffset ofs $ \i =>
        let res = FunAppDef "appendList_rev" appendList_rev (ArgN (UnBox lst) $ ArgN b Arg0) in
        MkLeft $ let j = Copy $ StaticEW i in MkPair (MkOffset j) $ MkPair (MkBox res) j
        -- TODO: return input end-witness
    )
    (\r => FunAppDef "copyList_rev" copyList_rev (ArgN b Arg0))

public export
test_14_bug : Program -- this actually works
test_14_bug = Main $
  LetRegion $ \r =>
  LetRegionValue r (MkI64 1) $ \i =>
  LetRegion $ \r =>
  --LetRegionValue r (MkRight MkT0) $ \l =>
  LetRegionValue r (FunAppDef "genList_rev" genList_rev (ArgN i Arg0)) $ \l1 =>
  LetRegion $ \r =>
  LetRegionValue r (FunAppDef "mapSuccList_rev" mapSuccList_rev (ArgN l1 Arg0)) $ \l2 =>
  LetRegion $ \r =>
  LetRegionValue r (FunAppDef "filterLt5List_rev" filterLt5List_rev (ArgN l2 Arg0)) $ \l3 =>
  let l4 = FunAppDef "appendList_rev" appendList_rev (ArgN l3 $ ArgN l3 Arg0) in
  PrintValue l1 $ \_ =>
  PrintValue l4 $ \_ =>
  LetRegion $ \r =>
  LetRegionValue r (FunAppDef "printList_rev" printList_rev (ArgN l4 Arg0)) $ \_ => l4

public export
test_14_bug_unroll : Program -- this actually works
test_14_bug_unroll = Main $
  LetRegion $ \r =>
  LetRegionValue r (MkI64 1) $ \i =>
  LetRegion $ \r =>
  --LetRegionValue r (MkRight MkT0) $ \l3 =>
  LetRegionValue r (genList_rev (ArgN {fun="genList_rev"} i Arg0)) $ \l1 =>
  LetRegion $ \r =>
  LetRegionValue r (mapSuccList_rev (ArgN {fun="mapSuccList_rev"} l1 Arg0)) $ \l2 =>
  LetRegion $ \r =>
  LetRegionValue r (filterLt5List_rev (ArgN {fun="filterLt5List_rev"} l2 Arg0)) $ \l3 =>
  -- Q: what is the problem? is it that l3 is used twice in the arg list and the meta level does not guarantee arg distinction?
  -- A: no
  let l4 = appendList_rev (ArgN {fun="appendList_rev"} l3 $ ArgN l3 Arg0) in
  PrintValue l1 $ \_ =>
  PrintValue l4 $ \_ =>
  LetRegion $ \r =>
  LetRegionValue r (printList_rev (ArgN {fun="printList_rev"} l4 Arg0)) $ \_ => l4

test_12 : Program
test_12 = Main $
  LetRegion $ \r =>
  LetRegionValue r (MkI64 1) $ \i =>
  LetRegion $ \r =>
  LetRegionValue r (FunAppDef "genList_rev" genList_rev (ArgN i Arg0)) $ \l =>
  PrintValue l $ \_ =>
  FunAppDef "printList_rev" printList_rev (ArgN l Arg0)

test_13 : Program
test_13 = Main $
  LetRegion $ \r =>
  LetRegionValue r (let i1 = MkI64 9 in MkPair i1 (MkOffset i1)) $ \v =>
  PrintValue v $ \_ =>
  let i2 = GetFst v in
  let i3 = GetSnd v $ StaticEW i2 in
  DeRefOffset i3 $ \i4 =>
  PrintI64 i4 $ \_ =>
  MkT0

test_14 : Program
test_14 = Main $
  LetRegion $ \r =>
  LetRegionValue r (let i1 = MkI64 9 in MkPair i1 (MkPtr i1)) $ \v =>
  PrintValue v $ \_ =>
  let i2 = GetFst v in
  let i3 = GetSnd v (StaticEW i2) in
  DeRefPtr i3 $ \i4 =>
  PrintI64 i4 $ \_ =>
  MkT0

test_15 : Program
test_15 =
  let printPair : {ew : _} -> {r_out : _} -> {loc_out : Loc r_out} -> Arg [Exp (Pair I64 I64) loc_in ew []] -> Exp T0 loc_out EW []
      printPair (ArgN p Arg0) =
        let fst = GetFst p in
        PrintI64 fst $ \fst =>
        MkT0
  in Main $
      LetRegion $ \r =>
      LetRegionValue r (MkPair (MkI64 7) (MkI64 8)) $ \t1 =>
      FunAppDef "printPair" printPair (ArgN t1 Arg0)

test_16 : Program
test_16 =
  let printPair : {ew : _} -> {r_out : _} -> {loc_out : Loc r_out} -> Arg [Exp (Pair I64 I64) loc_in ew []] -> Exp T0 loc_out EW []
      printPair (ArgN p Arg0) =
        let fst = GetFst p in
        PrintI64 fst $ \_ =>
        let snd = GetSnd p (StaticEW fst) in
        PrintI64 snd $ \_ =>
        MkT0
  in Main $
      LetRegion $ \r =>
      LetRegionValue r (MkPair (MkI64 7) (MkI64 8)) $ \t1 =>
      FunAppDef "printPair" printPair (ArgN t1 Arg0)

test_17 : Program
test_17 =
  let printPair : {ew : _} -> {r_out : _} -> {loc_out : Loc r_out} -> Arg [Exp (Pair I64 I64) loc_in ew []] -> Exp T0 loc_out EW []
      printPair (ArgN p Arg0)=
        let fst = GetFst p in
        let snd = GetSnd p (StaticEW fst) in
        PrintI64 snd $ \_ =>
        PrintI64 fst $ \_ =>
        MkT0
  in Main $
      LetRegion $ \r =>
      LetRegionValue r (MkPair (MkI64 7) (MkI64 8)) $ \t1 =>
      FunAppDef "printPair" printPair (ArgN t1 Arg0)

test_20 : Program
test_20 =
  let printPair2 : {r_out : _} -> {loc_out : Loc r_out} ->
                   Arg [Exp (Pair I64 I64) loc_in ew_in []] -> Exp T0 loc_out EW []
      printPair2 (ArgN p Arg0) =
        let fst = GetFst p in
        let snd = GetSnd p (StaticEW fst) in
        PrintI64 snd $ \_ =>
        PrintI64 fst $ \_ =>
        MkT0
  in Main $
      LetRegion $ \r =>
      LetRegionValue r (MkPair (MkI64 7) (MkI64 8)) $ \t1 =>
      FunAppDef "printPair2" printPair2 (ArgN t1 Arg0)

-- test
--compileProgram : String -> Program -> IO String
--compileProgram _ _ = pure ""

-- BUGS

public export
ListInt_Rev : Ty
ListInt_Rev = Either (Pair (Box "ListInt_Rev" ListInt_Rev) I64) T0

genListInt_Rev : {r_out : _} -> {loc_out : Loc r_out} -> Arg [Exp I64 loc_in EW []] -> Exp ListInt_Rev loc_out EW []
genListInt_Rev (ArgN i Arg0) =
  LetRegion $ \r =>
  LetRegionValue r (EqI64C 10 i) $ \b =>
  CaseEither b
    (\f =>
        LetRegion $ \r =>
        LetRegionValue r (AddI64C 1 i) $ \next =>
        -- working
        let res = FunAppDef "genListInt_Rev" genListInt_Rev (ArgN next Arg0) in
        --FunApp "genList_rev" genList_rev next $ \res =>
        MkLeft $ let j = Copy $ StaticEW i in MkPair (MkBox res) j
    )
    (\t => MkRight MkT0)

mapSuccListInt_Rev : {ew : _} -> {r_out : _} -> {loc_out : Loc r_out} -> Arg [Exp ListInt_Rev loc_in ew []] -> Exp ListInt_Rev loc_out EW []
mapSuccListInt_Rev (ArgN a Arg0) =
  CaseEither a
    {-
    (\l => let lst = GetFst l in
           let i   = GetSnd l (GenEW lst) in
           MkLeft $ MkPair (MkBox $ FunAppDef "mapSuccListInt_Rev" mapSuccListInt_Rev (ArgN (UnBox lst) Arg0)) $ AddI64C 1 i
    )
    -}
    (\l => MkLeft ( MkPair (MkBox ( FunAppDef "mapSuccListInt_Rev" mapSuccListInt_Rev (ArgN (UnBox (GetFst l)) Arg0)))
                           (I64Op2 Plus (LetRegionValue (MkRegion 8) (MkI64 1) id         ) (GetSnd l (GenEW (GetFst l))))))
    {-
    -- from hical
    (\_ => MkLeft ( MkPair (MkBox ( FunAppDef "mapSuccListInt_Rev" mapSuccListInt_Rev (ArgN Var {-BUG-} Arg0)))
                           (I64Op2 Plus (LetRegionValue (MkRegion 8) (MkI64 1) (\_ => Var)) (GetSnd Var (GenEW (GetFst Var))))))
    -}
{-
                              (ArgN
                                {s = [] {a = Type}}
                                {fun = "mapSuccList"} {n = 0}
                                {t = Either (Pair (Box "Rev_my_ty" Rev_my_ty) I64) T0}
                                {r_arg = MkArgRegion "mapSuccList" 0}
                                {loc_arg = LocAfterTag {r = MkArgRegion "mapSuccList" 0} "Pair" (Box "Rev_my_ty" Rev_my_ty)
                                          (LocAfterTag {r = MkArgRegion "mapSuccList" 0} "Left" (Pair (Box "Rev_my_ty" Rev_my_ty) I64)
                                          (LocStart (Either (Pair (Box "Rev_my_ty" Rev_my_ty) I64) T0) (MkArgRegion "mapSuccList" 0)))}
                                {ew = EW}
                                (Var
                                  {{r:3205} = MkArgRegion "mapSuccList" 0}
                                  {sew = [] {a = Type}} {ew = EW}
                                  {loc = LocAfterTag {r = MkArgRegion "mapSuccList" 0} "Pair" (Box "Rev_my_ty" Rev_my_ty)
                                        (LocAfterTag {r = MkArgRegion "mapSuccList" 0} "Left" (Pair (Box "Rev_my_ty" Rev_my_ty) I64)
                                        (LocStart (Either (Pair (Box "Rev_my_ty" Rev_my_ty) I64) T0) (MkArgRegion "mapSuccList" 0)))}
                                  {t = Either (Pair (Box "Rev_my_ty" Rev_my_ty) I64) T0})
                                (Arg0 {fun = "mapSuccList"})))
-}
    (\r => MkRight MkT0)

{-
  hical compiled code for mapSuccListInt_Rev with main expression
  Main (LetRegionValue (MkRegion 1) (MkRight MkT0)
    (\_ => FunAppDef "mapSuccList" 
    (\_ => CaseEither Var (\_ => MkLeft (MkPair (MkBox (FunApp "mapSuccList" (ArgN Var Arg0))) (I64Op2 Plus (LetRegionValue (MkRegion 8) (MkI64 1) (\_ => Var)) (GetSnd Var (GenEW (GetFst Var)))))) (\_ => MkRight MkT0)) (ArgN Var Arg0)))

  hical compiled code for mapSuccListInt_Rev

  (\_ =>
    CaseEither Var
      (\_ => MkLeft (MkPair
                (MkBox (FunApp "mapSuccList" (ArgN Var Arg0)))
                (I64Op2 Plus (LetRegionValue (MkRegion 8) (MkI64 1) (\_ => Var)) (GetSnd Var (GenEW (GetFst Var))))))
      (\_ => MkRight MkT0)
  )
-}

test_bug01 : Program
test_bug01 = Main $
  LetRegion $ \r =>
  LetRegionValue r (MkRight MkT0) $ \l =>
  let x = FunAppDef "mapSuccListInt_Rev" mapSuccListInt_Rev (ArgN l Arg0) in
  PrintValue x $ \_ => x


test_bug02 : Program
test_bug02 = Main {res=ListInt_Rev}
  (let i1 = MkI64 1 in
  CaseEither
    (LetRegionValue (MkRegion 10003)
      (I64Cmp EQ i1 (LetRegionValue (MkRegion 10005) (MkI64 10) (\x => x)))
      (\y => y))
    (\_ => MkLeft $ MkPair (MkBox $ MkRight MkT0) i1)
    (\_ => MkRight MkT0)
  )

test_bug03 : Program
test_bug03 = Main {res=ListInt_Rev}
  (let i1 = MkI64 1 in
  CaseEither
    (LetRegionValue (MkRegion 10003)
      (I64Cmp EQ i1 i1)
      (\y => y))
    (\_ => MkLeft $ MkPair (MkBox $ MkRight MkT0) i1)
    (\_ => MkRight MkT0)
  )

test_bug04 : Program
test_bug04 = Main
  (let i1 = MkI64 1 in
  CaseEither {c=Either I64 T0} (LetRegionValue (MkRegion 10003) (I64Cmp EQ i1 i1) (\y => y))
    (\_ => MkLeft i1)
    (\_ => MkRight MkT0)
  )

-- Q: what is the interpretation of this?
-- Q: how to resolve this?
test_bug05 : Program
test_bug05 = Main
  (let i1 = MkRight MkT0 in
  CaseEither {c=Either I64 T0} (LetRegionValue (MkRegion 10003) (Copy i1) (\y => y))
    (\_ => i1)
    (\_ => i1)
  )

test_bug06 : Program
test_bug06 = Main
  (let i1 = MkI64 12 in
  PrintValue (LetRegionValue (MkRegion 10003) (Copy i1) (\y => y))
    (\_ => i1)
  )

partial main : IO ()
main = do
  _ <- compileProgram "test_bug06" test_bug06
  --_ <- compileProgram "test_bug05" test_bug05
  --_ <- compileProgram "test_bug04" test_bug04
  --_ <- compileProgram "test_bug03" test_bug03
  --_ <- compileProgram "test_bug02" test_bug02
  --_ <- compileProgram "test_14_bug_unroll" test_14_bug_unroll -- fixed
  --_ <- compileProgram "test_bug01" test_bug01
  --_ <- compileProgram "test_14_bug" test_14_bug
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
