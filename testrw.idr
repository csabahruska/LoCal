import LoCal
import Dynamic

Rev_my_ty : Ty
Rev_my_ty = Either (Pair (Offset I64) $ Pair (Box "Rev_my_ty" Rev_my_ty) I64) T0

public export
AddI64 : {r1, r2 : _} -> {ew1, ew2 : _} -> {loc_in1 : Loc r1} -> {loc_in2 : Loc r2} -> Exp I64 loc_in1 (R ew1) [] -> Exp I64 loc_in2 (R ew2) [] -> Exp I64 loc W []
AddI64 = I64Op2 Plus

public export
EqI64 : {r1, r2 : _} -> {ew1, ew2 : _} -> {loc_in1 : Loc r1} -> {loc_in2 : Loc r2} -> Exp I64 loc_in1 (R ew1) [] -> Exp I64 loc_in2 (R ew2) [] -> Exp (Either T0 T0) loc W []
EqI64 = I64Cmp EQ

public export
AddI64C : Int -> {r1 : _} -> {ew1 : _} -> {loc_in1 : Loc r1} -> Exp I64 loc_in1 (R ew1) [] -> Exp I64 loc W []
AddI64C i e = LetRegion $ \r => LetRegionValue r (MkI64 i) $ \i => I64Op2 Plus i e

public export
EqI64C, LtI64C : Int -> {r1 : _} -> {ew1 : _} -> {loc_in1 : Loc r1} -> Exp I64 loc_in1 (R ew1) [] -> Exp (Either T0 T0) loc W []
EqI64C i e = LetRegion $ \r => LetRegionValue r (MkI64 i) $ \i => I64Cmp EQ e i
LtI64C i e = LetRegion $ \r => LetRegionValue r (MkI64 i) $ \i => I64Cmp LT e i

mapSuccList_rev : {ew : _} -> {r_out : _} -> {loc_out : Loc r_out} ->
              Arg [Exp Rev_my_ty loc_in ew []] -> Exp Rev_my_ty loc_out W []
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

genList_rev : {r_out : _} -> {loc_out : Loc r_out} -> Arg [Exp I64 loc_in REW []] -> Exp Rev_my_ty loc_out W []
genList_rev (ArgN i Arg0) =
  LetRegion $ \r =>
  LetRegionValue r (EqI64C 160 i) $ \b =>
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

printList_rev : {ew : _} -> {r_out : _} -> {loc_out : Loc r_out} -> Arg [Exp Rev_my_ty loc_in (R ew) []] -> Exp T0 loc_out W []
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
              Arg [Exp Rev_my_ty loc_in (R ew) []] -> Exp Rev_my_ty loc_out W []
filterLt5List_rev (ArgN a Arg0) =
  CaseEither a
    (\l =>
        let ofs = GetFst l in
        let lst = GetFst $ GetSnd l $ StaticEW ofs in
        DeRefOffset ofs $ \i =>
        LetRegion $ \r =>
        LetRegionValue r (LtI64C 80 i) $ \b =>
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
           Arg [Exp Rev_my_ty loc_in1 (R ew_in1) []] -> Exp Rev_my_ty loc_out W []
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
             Arg {n=2} [Exp Rev_my_ty loc_in1 (R ew_in1) [], Exp Rev_my_ty loc_in2 (R ew_in2) []] ->
             Exp Rev_my_ty loc_out W []
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
  LetRegionValue MainRegion l4 $ \l4 =>
  PrintValue l4 $ \_ =>
  LetRegion $ \r =>
  LetRegionValue r (printList_rev (ArgN {fun="printList_rev"} l4 Arg0)) $ \_ => l4

public export
test_14_bug : Program -- this actually works
test_14_bug = Main $
  LetRegion $ \r =>
  LetRegionValue r (MkI64 1) $ \i =>
  LetRegion $ \r =>
  --LetRegionValue r (MkRight MkT0) $ \l3 =>
  LetRegionValue r (FunAppDef "genList_rev" genList_rev (ArgN i Arg0)) $ \l1 =>
  LetRegion $ \r =>
  LetRegionValue r (FunAppDef "mapSuccList_rev" mapSuccList_rev (ArgN l1 Arg0)) $ \l2 =>
  LetRegion $ \r =>
  LetRegionValue r (FunAppDef "filterLt5List_rev" filterLt5List_rev (ArgN l2 Arg0)) $ \l3 =>
  -- Q: what is the problem? is it that l3 is used twice in the arg list and the meta level does not guarantee arg distinction?
  -- A: no
  let l4 = FunAppDef "appendList_rev" appendList_rev (ArgN l3 $ ArgN l3 Arg0) in
  PrintValue l1 $ \_ =>
  LetRegionValue MainRegion l4 $ \l4 =>
  PrintValue l4 $ \_ =>
  LetRegion $ \r =>
  LetRegionValue r (FunAppDef "printList_rev" printList_rev (ArgN l4 Arg0)) $ \_ => l4

partial main : IO ()
main = do
  _ <- compileProgram "test_14_bug" test_14_bug -- fixed
  _ <- compileProgram "test_14_bug_unroll" test_14_bug_unroll -- fixed
  pure ()