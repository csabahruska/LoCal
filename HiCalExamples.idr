module HiCalExamples
import HiCal

public export
AddI64C : Int -> Exp I64 -> Exp I64
AddI64C i = I64Op2 Plus (MkI64 i)

public export
EqI64C, LtI64C : Int -> Exp I64 -> Exp (Either T0 T0)
EqI64C i e = I64Cmp EQ e (MkI64 i)
LtI64C i e = I64Cmp LT e (MkI64 i)

public export
Rev_my_ty : Ty
Rev_my_ty = Either (Pair (Box "Rev_my_ty" Rev_my_ty) I64) T0

public export
mapSuccList : Arg [Exp Rev_my_ty] -> Exp Rev_my_ty
mapSuccList (ArgN a Arg0) =
  CaseEither a
    (\l => CasePair l $ \lst, i =>
            MkLeft $ MkPair (MkBox $ FunAppDef "mapSuccList" mapSuccList (ArgN (UnBox lst) Arg0)) $ AddI64C 1 i
    )
    (\r => MkRight MkT0)

genList : Arg [Exp I64] -> Exp Rev_my_ty
genList (ArgN i Arg0) =
  CaseEither (EqI64C 10 i)
    (\f => MkLeft $ MkPair (MkBox $ FunAppDef "genList" genList (ArgN (AddI64C 1 i) Arg0)) i)
    --(\f => MkLeft $ MkPair (MkBox $ MkRight MkT0) (AddI64C 1 i))
    (\t => MkRight MkT0)

printList : Arg [Exp Rev_my_ty] -> Exp T0
printList (ArgN a Arg0) =
  CaseEither a
    (\l =>
        CasePair l $ \lst, i =>
        PrintI64 i $ \_ =>
        FunAppDef "printList" printList (ArgN (UnBox lst) Arg0)
    )
    (\r => MkT0)


filterLt5List : Arg [Exp Rev_my_ty] -> Exp Rev_my_ty
filterLt5List (ArgN a Arg0) =
  CaseEither a
    (\l => CasePair l $ \lst, i =>
        CaseEither (LtI64C 5 i)
          (\f => FunAppDef "filterLt5List" filterLt5List (ArgN (UnBox lst) Arg0))
          (\t => MkLeft $ MkPair (MkBox $ FunAppDef "filterLt5List" filterLt5List (ArgN (UnBox lst) Arg0)) i)
    )
    (\r => MkRight MkT0)

copyList : Arg [Exp Rev_my_ty] -> Exp Rev_my_ty
copyList (ArgN a Arg0) =
  CaseEither a
    (\l => CasePair l $ \lst, i => MkLeft $ MkPair (MkBox $ FunAppDef "copyList" copyList (ArgN (UnBox lst) Arg0)) i)
    (\r => MkRight MkT0)

appendList : Arg {n=2} [Exp Rev_my_ty, Exp Rev_my_ty] -> Exp Rev_my_ty
appendList (ArgN a (ArgN b Arg0)) =
  CaseEither a
    (\l => CasePair l $ \lst, i => MkLeft $ MkPair (MkBox $ FunAppDef "appendList" appendList (ArgN (UnBox lst) $ ArgN b Arg0)) i)
    (\r => FunAppDef "copyList" copyList (ArgN b Arg0))

public export
test_12 : Program
test_12 = Main $
  let i = MkI64 1 in
  Let (FunAppDef "genList" genList (ArgN i Arg0)) $ \l =>
  PrintValue l $ \_ =>
  FunAppDef "printList" printList (ArgN l Arg0)

public export
test_12_bug : Program
test_12_bug = Main $
  let i = MkI64 1 in
  Let (FunAppDef "genList" genList (ArgN i Arg0)) $ \l =>
  PrintValue l $ \_ =>
  --Let (FunAppDef "mapSuccList" mapSuccList (ArgN l Arg0)) $ \l2 =>
  let l2 = FunAppDef "mapSuccList" mapSuccList (ArgN l Arg0) in
  --PrintValue l2 $ \_ =>
  FunAppDef "printList" printList (ArgN l2 Arg0)

public export
test_13 : Program
test_13 = Main $
  let i = MkI64 1 in
  Let (FunAppDef "genList" genList (ArgN i Arg0)) $ \l =>
  PrintValue l $ \_ =>
  FunAppDef "printList" printList (ArgN l Arg0)

{-
hical:
Main
  (Let (CaseEither
          (I64Cmp EQ (MkI64 10) (MkI64 1))
          (\f => MkLeft (MkPair (MkBox (FunAppDef "genList" genList (ArgN (I64Op2 Plus (MkI64 1) (MkI64 1)) Arg0))) (MkI64 1)))
          (\t => MkRight MkT0)
       )
       (\l => PrintValue l (\_ =>
        CaseEither l
          (\l => CasePair l (\lst, i => PrintI64 i (\_ => FunAppDef "printList" printList (ArgN (UnBox lst) Arg0))))
          (\r => MkT0))))

local:
Main (
  LetRegionValue (MkRegion 1)
    (CaseEither
      (LetRegionValue
        (MkRegion 4)
        (I64Cmp EQ (LetRegionValue (MkRegion 5) (MkI64 10) (\_ => Var)) (LetRegionValue (MkRegion 6) (MkI64 1) (\_ => Var)))
        (\_ => Var)
      )
      (\_ => MkLeft (MkPair (MkBox (
              FunAppDef "genList" (\_ =>
                CaseEither (LetRegionValue (MkRegion 13) (I64Cmp EQ (LetRegionValue (MkRegion 14) (MkI64 10) (\_ => Var)) Var) (\_ => Var))
                  (\_ => MkLeft (
                          MkPair (
                            MkBox ( FunApp "genList" (ArgN
                              (LetRegionValue (MkRegion 16) (I64Op2 Plus (LetRegionValue (MkRegion 17) (MkI64 1) (\_ => Var)) Var) (\_ => Var)) Arg0)))
                            (Copy Var)))
                  (\_ => MkRight MkT0))
                (ArgN (LetRegionValue (MkRegion 8)
                  (I64Op2 Plus (LetRegionValue (MkRegion 9) (MkI64 1) (\_ => Var)) (LetRegionValue (MkRegion 10) (MkI64 1) (\_ => Var))) (\_ => Var)) Arg0))) (MkI64 1))
      )
      (\_ => MkRight MkT0))
    (\_ => PrintValue Var (\_ =>
      CaseEither Var
        (\_ => PrintI64 (GetSnd Var (GenEW (GetFst Var)))
                (\_ => FunAppDef "printList"
                        (\_ => CaseEither Var
                                (\_ => PrintI64 (GetSnd Var (GenEW (GetFst Var))) (\_ => FunApp "printList" (ArgN (UnBox (GenEW (GetFst Var))) Arg0)))
                                (\_ => MkT0))
                        (ArgN (UnBox (GenEW (GetFst Var))) Arg0))
        )
        (\_ => MkT0))))
-}
public export
test_13_unroll : Program
test_13_unroll = Main $
  let i = MkI64 1 in
  Let (genList (ArgN i Arg0)) $ \l =>
  PrintValue l $ \_ =>
  printList (ArgN l Arg0)

public export
test_14_bug : Program
test_14_bug = Main $
  --let l = MkRight MkT0 in
  Let (MkRight MkT0) $ \l =>
  --PrintValue l $ \_ =>
  FunAppDef "mapSuccList" mapSuccList (ArgN l Arg0)
  {-
  Let (FunAppDef "mapSuccList" mapSuccList (ArgN l Arg0)) $ \l2 =>
  PrintValue l2 $ \_ =>
  FunAppDef "printList" printList (ArgN l2 Arg0)
  -}

public export
test_14_bug2 : Program
test_14_bug2 = Main $
  let l = MkRight MkT0 in
  PrintValue l $ \_ =>
  Let (FunAppDef "mapSuccList" mapSuccList (ArgN l Arg0)) $ \l2 =>
  PrintValue l2 $ \_ =>
  FunAppDef "printList" printList (ArgN l2 Arg0)


public export
test_14_bug_full : Program -- this actually works
test_14_bug_full = Main $
  Let (MkI64 1) $ \i =>
  Let (FunAppDef "genList" genList (ArgN i Arg0)) $ \l1 =>
  Let (FunAppDef "mapSuccList" mapSuccList (ArgN l1 Arg0)) $ \l2 =>
  Let (FunAppDef "filterLt5List" filterLt5List (ArgN l2 Arg0)) $ \l3 =>
  let l4 = FunAppDef "appendList" appendList (ArgN l3 $ ArgN l3 Arg0) in
  PrintValue l1 $ \_ =>
  PrintValue l4 $ \_ =>
  Let (FunAppDef "printList" printList (ArgN l4 Arg0)) $ \_ => l4

public export
test_14_bug_full_unroll : Program -- this actually works
test_14_bug_full_unroll = Main $
  Let (MkI64 1) $ \i =>
  --let i = (MkI64 1) in -- $ \i =>
  --Let (genList (ArgN i Arg0)) $ \l1 =>
  let l1 = genList (ArgN i Arg0) in
  --Let (mapSuccList (ArgN l1 Arg0)) $ \l2 =>
  --Let (filterLt5List (ArgN l2 Arg0)) $ \l3 =>
  --let l4 = appendList (ArgN l3 $ ArgN l3 Arg0) in
  --PrintValue l1 $ \_ =>
  --PrintValue l4 $ \_ =>
  --Let (printList (ArgN l4 Arg0)) $ \_ => l4
  l1
{-
Main (
  LetRegionValue (MkRegion 1) (MkRight MkT0) (\_ =>
    FunAppDef "mapSuccList"
      (\_ => CaseEither Var
        (\_ => MkLeft (MkPair
                (MkBox (FunApp "mapSuccList" (ArgN Var Arg0)))
                (I64Op2 Plus (LetRegionValue (MkRegion 8) (MkI64 1) (\_ => Var)) (GetSnd Var (GenEW (GetFst Var)))))
        )
        (\_ => MkRight MkT0)
      )
      (ArgN Var Arg0))
 )
-}

{-
Main
  {res = Either (Pair (Box "Rev_my_ty" Rev_my_ty) I64) T0}
  (LetRegionValue
    {{r:2445} = MkRegion -1} {ews = [] {a = Type}} {ew = EW}
    {loc = LocStart (Either (Pair (Box "Rev_my_ty" Rev_my_ty) I64) T0) (MkRegion -1)}
    {a = Either (Pair (Box "Rev_my_ty" Rev_my_ty) I64) T0}
    {t_val = Either (Pair (Box "Rev_my_ty" Rev_my_ty) I64) T0}
    (MkRegion 1)
    (MkRight
      {{r:2609} = MkRegion 1}
      {a = Pair (Box "Rev_my_ty" Rev_my_ty) I64}
      {b = T0}
      {loc = LocStart (Either (Pair (Box "Rev_my_ty" Rev_my_ty) I64) T0) (MkRegion 1)}
      (MkT0
        {{r:3027} = MkRegion 1}
        {loc = LocAfterTag {r = MkRegion 1} "Right" T0 (LocStart (Either (Pair (Box "Rev_my_ty" Rev_my_ty) I64) T0) (MkRegion 1))}
      )
    )
    (\_ : Exp {r = MkRegion 1} (Either (Pair (Box "Rev_my_ty" Rev_my_ty) I64) T0)
              (LocStart (Either (Pair (Box "Rev_my_ty" Rev_my_ty) I64) T0) (MkRegion 1)) EW ([] {a = Type}) =>
          FunAppDef
            {exps_in = (::) {a = Type}
                            (Exp {r = MkArgRegion "mapSuccList" 0}
                                 (Either (Pair (Box "Rev_my_ty" Rev_my_ty) I64) T0)
                                 (LocStart (Either (Pair (Box "Rev_my_ty" Rev_my_ty) I64) T0) (MkArgRegion "mapSuccList" 0)) EW ([] {a = Type})) ([] {a = Type})
            }
            {n = 1}
            {fun_ews = [] {a = Type}}
            {res = Either (Pair (Box "Rev_my_ty" Rev_my_ty) I64) T0}
            {r_res = MkRegion -1}
            {loc_res = LocStart (Either (Pair (Box "Rev_my_ty" Rev_my_ty) I64) T0) (MkRegion -1)}
            "mapSuccList"
            (\_ : Arg {fun = "mapSuccList"} {n = 1}
                      ((::) {a = Type}
                            (Exp {r = MkArgRegion "mapSuccList" 0}
                                 (Either (Pair (Box "Rev_my_ty" Rev_my_ty) I64) T0)
                                 (LocStart (Either (Pair (Box "Rev_my_ty" Rev_my_ty) I64) T0) (MkArgRegion "mapSuccList" 0)) EW ([] {a = Type})
                            ) ([] {a = Type})
                      ) =>
                CaseEither
                  {{r:2761} = MkRegion -1}
                  {r_scrut = MkArgRegion "mapSuccList" 0}
                  {a = Pair (Box "Rev_my_ty" Rev_my_ty) I64}
                  {b = T0}
                  {c = Either (Pair (Box "Rev_my_ty" Rev_my_ty) I64) T0}
                  {loc_scrut = LocStart (Either (Pair (Box "Rev_my_ty" Rev_my_ty) I64) T0) (MkArgRegion "mapSuccList" 0)}
                  {ew_scrut = EW}
                  {ew = EW}
                  {loc = LocStart (Either (Pair (Box "Rev_my_ty" Rev_my_ty) I64) T0) (MkRegion -1)}
                  {ews = [] {a = Type}}
                  (Var
                    {{r:3205} = MkArgRegion "mapSuccList" 0}
                    {sew = [] {a = Type}}
                    {ew = EW}
                    {loc = LocStart (Either (Pair (Box "Rev_my_ty" Rev_my_ty) I64) T0) (MkArgRegion "mapSuccList" 0)}
                    {t = Either (Pair (Box "Rev_my_ty" Rev_my_ty) I64) T0}
                  )
                  (\_ : Exp {r = MkArgRegion "mapSuccList" 0}
                            (Pair (Box "Rev_my_ty" Rev_my_ty) I64)
                            (LocAfterTag {r = MkArgRegion "mapSuccList" 0} "Left" (Pair (Box "Rev_my_ty" Rev_my_ty) I64)
                             (LocStart (Either (Pair (Box "Rev_my_ty" Rev_my_ty) I64) T0) (MkArgRegion "mapSuccList" 0))
                            ) EW ([] {a = Type}) =>
                    MkLeft
                      {{r:2579} = MkRegion -1}
                      {a = Pair (Box "Rev_my_ty" Rev_my_ty) I64}
                      {b = T0}
                      {loc = LocStart (Either (Pair (Box "Rev_my_ty" Rev_my_ty) I64) T0) (MkRegion -1)}
                      (MkPair
                        {{r:2549} = MkRegion -1}
                        {a = Box "Rev_my_ty" Rev_my_ty}
                        {b = I64}
                        {loc = LocAfterTag {r = MkRegion -1} "Left" (Pair (Box "Rev_my_ty" Rev_my_ty) I64)
                              (LocStart (Either (Pair (Box "Rev_my_ty" Rev_my_ty) I64) T0) (MkRegion -1))}
                        (MkBox
                          {{r:2488} = MkRegion -1} {ew = EW}
                          {loc = LocAfterTag {r = MkRegion -1} "Pair" (Box "Rev_my_ty" Rev_my_ty)
                                (LocAfterTag {r = MkRegion -1} "Left" (Pair (Box "Rev_my_ty" Rev_my_ty) I64)
                                (LocStart (Either (Pair (Box "Rev_my_ty" Rev_my_ty) I64) T0) (MkRegion -1)))}
                          {t = Either (Pair (Box "Rev_my_ty" Rev_my_ty) I64) T0}
                          {n = "Rev_my_ty"}
                          (FunApp
                            {{fun:2883} = "mapSuccList"}
                            {{n:2882} = 1}
                            {exps_in = (::) {a = Type}
                              (Exp
                                {r = MkArgRegion "mapSuccList" 0}
                                (Either (Pair (Box "Rev_my_ty" Rev_my_ty) I64) T0)
                                (LocStart (Either (Pair (Box "Rev_my_ty" Rev_my_ty) I64) T0) (MkArgRegion "mapSuccList" 0))
                                EW ([] {a = Type})) ([] {a = Type})}
                            {fun_ews = [] {a = Type}}
                            {res = Either (Pair (Box "Rev_my_ty" Rev_my_ty) I64) T0}
                            {r_res = MkRegion -1}
                            {loc_res = LocAfterTag {r = MkRegion -1} "Pair" (Box "Rev_my_ty" Rev_my_ty)
                                      (LocAfterTag {r = MkRegion -1} "Left" (Pair (Box "Rev_my_ty" Rev_my_ty) I64)
                                      (LocStart (Either (Pair (Box "Rev_my_ty" Rev_my_ty) I64) T0) (MkRegion -1)))}
                            "mapSuccList"
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
                        )
                        (I64Op2
                          {{r:3085} = MkRegion -1}
                          {loc = LocAfter {r = MkRegion -1} I64
                                (LocAfterTag {r = MkRegion -1} "Pair" (Box "Rev_my_ty" Rev_my_ty)
                                (LocAfterTag {r = MkRegion -1} "Left" (Pair (Box "Rev_my_ty" Rev_my_ty) I64)
                                (LocStart (Either (Pair (Box "Rev_my_ty" Rev_my_ty) I64) T0) (MkRegion -1))))}
                          Plus
                          {ew1 = EW} {ew2 = EW}
                          {r_in1 = MkRegion 8} {r_in2 = MkArgRegion "mapSuccList" 0}
                          {loc_in1 = LocStart I64 (MkRegion 8)}
                          {loc_in2 = LocAfter {r = MkArgRegion "mapSuccList" 0} I64
                                    (LocAfterTag {r = MkArgRegion "mapSuccList" 0} "Pair" (Box "Rev_my_ty" Rev_my_ty)
                                    (LocAfterTag {r = MkArgRegion "mapSuccList" 0} "Left" (Pair (Box "Rev_my_ty" Rev_my_ty) I64)
                                    (LocStart (Either (Pair (Box "Rev_my_ty" Rev_my_ty) I64) T0) (MkArgRegion "mapSuccList" 0))))}
                          (LetRegionValue
                            {{r:2445} = MkRegion 8} {ews = [] {a = Type}} {ew = EW}
                            {loc = LocStart I64 (MkRegion 8)} {a = I64} {t_val = I64}
                            (MkRegion 8)
                            (MkI64 {{r:3039} = MkRegion 8} {loc = LocStart I64 (MkRegion 8)} 1)
                            (\_ : Exp {r = MkRegion 8} I64 (LocStart I64 (MkRegion 8)) EW ([] {a = Type}) =>
                                Var {{r:3205} = MkRegion 8} {sew = [] {a = Type}} {ew = EW} {loc = LocStart I64 (MkRegion 8)} {t = I64}))
                          (GetSnd
                            {r_tup = MkArgRegion "mapSuccList" 0}
                            {a = Box "Rev_my_ty" Rev_my_ty}
                            {b = I64}
                            {loc_tup = LocAfterTag {r = MkArgRegion "mapSuccList" 0} "Left" (Pair (Box "Rev_my_ty" Rev_my_ty) I64)
                                      (LocStart (Either (Pair (Box "Rev_my_ty" Rev_my_ty) I64) T0) (MkArgRegion "mapSuccList" 0))}
                            {ew_tup = EW}
                            (Var
                              {{r:3205} = MkArgRegion "mapSuccList" 0}
                              {sew = [] {a = Type}}
                              {ew = EW}
                              {loc = LocAfterTag {r = MkArgRegion "mapSuccList" 0} "Left" (Pair (Box "Rev_my_ty" Rev_my_ty) I64)
                                    (LocStart (Either (Pair (Box "Rev_my_ty" Rev_my_ty) I64) T0) (MkArgRegion "mapSuccList" 0))}
                              {t = Pair (Box "Rev_my_ty" Rev_my_ty) I64}
                            )
                            (GenEW
                              {t = Box "Rev_my_ty" Rev_my_ty}
                              {r = MkArgRegion "mapSuccList" 0}
                              {loc = LocAfterTag {r = MkArgRegion "mapSuccList" 0} "Pair" (Box "Rev_my_ty" Rev_my_ty)
                                    (LocAfterTag {r = MkArgRegion "mapSuccList" 0} "Left" (Pair (Box "Rev_my_ty" Rev_my_ty) I64)
                                    (LocStart (Either (Pair (Box "Rev_my_ty" Rev_my_ty) I64) T0) (MkArgRegion "mapSuccList" 0)))}
                              {ew_in = NoEW}
                              (GetFst
                                {r_tup = MkArgRegion "mapSuccList" 0}
                                {a = Box "Rev_my_ty" Rev_my_ty}
                                {b = I64}
                                {loc_tup = LocAfterTag {r = MkArgRegion "mapSuccList" 0} "Left" (Pair (Box "Rev_my_ty" Rev_my_ty) I64)
                                          (LocStart (Either (Pair (Box "Rev_my_ty" Rev_my_ty) I64) T0) (MkArgRegion "mapSuccList" 0))}
                                {ew_tup = EW}
                                (Var
                                  {{r:3205} = MkArgRegion "mapSuccList" 0}
                                  {sew = [] {a = Type}}
                                  {ew = EW}
                                  {loc = LocAfterTag {r = MkArgRegion "mapSuccList" 0} "Left" (Pair (Box "Rev_my_ty" Rev_my_ty) I64)
                                        (LocStart (Either (Pair (Box "Rev_my_ty" Rev_my_ty) I64) T0) (MkArgRegion "mapSuccList" 0))}
                                  {t = Pair (Box "Rev_my_ty" Rev_my_ty) I64})))
                          )))) (\_ : Exp {r = MkArgRegion "mapSuccList" 0} T0 (LocAfterTag {r = MkArgRegion "mapSuccList" 0} "Right" T0 (LocStart (Either (Pair (Box "Rev_my_ty" Rev_my_ty) I64) T0) (MkArgRegion "mapSuccList" 0))) EW ([] {a = Type}) =>
MkRight {{r:2609} = MkRegion -1} {a = Pair (Box "Rev_my_ty" Rev_my_ty) I64} {b = T0} {loc = LocStart (Either (Pair (Box "Rev_my_ty" Rev_my_ty) I64) T0) (MkRegion -1)} (MkT0 {{r:3027} = MkRegion -1} {loc = LocAfterTag {r = MkRegion -1} "Right" T0 (LocStart (Either (Pair (Box "Rev_my_ty" Rev_my_ty) I64) T0) (MkRegion -1))}))) (ArgN {s = [] {a = Type}} {fun = "mapSuccList"} {n = 0} {t = Either (Pair (Box "Rev_my_ty" Rev_my_ty) I64) T0} {r_arg = MkRegion 1} {loc_arg = LocStart (Either (Pair (Box "Rev_my_ty" Rev_my_ty) I64) T0) (MkRegion 1)} {ew = EW} (Var {{r:3205} = MkRegion 1} {sew = [] {a = Type}} {ew = EW} {loc = LocStart (Either (Pair (Box "Rev_my_ty" Rev_my_ty) I64) T0) (MkRegion 1)} {t = Either (Pair (Box "Rev_my_ty" Rev_my_ty) I64) T0}) (Arg0 {fun = "mapSuccList"}))))
-}
public export
test_bug3 : Program
test_bug3 = Main $ PrintValue
  (CaseEither {a=T0} (MkRight MkT0) (\_ => MkT0) (\_ => MkT0)) $ \_ =>
  MkT0

{-
Main (LetRegionValue (MkRegion 2)
  (CaseEither (LetRegionValue (MkRegion 5) (I64Cmp EQ Var (LetRegionValue (MkRegion 7) (MkI64 10) (\_ => Var))) (\_ => Var))
    (\_ =>
      MkLeft (MkPair (MkBox (FunAppDef "genList" (\_ =>
        CaseEither (LetRegionValue (MkRegion 14) (I64Cmp EQ Var (LetRegionValue (MkRegion 15) (MkI64 10) (\_ => Var))) (\_ => Var))
          (\_ => MkLeft (MkPair (MkBox (FunApp "genList" (ArgN (LetRegionValue (MkRegion 17) (I64Op2 Plus (LetRegionValue (MkRegion 18) (MkI64 1) (\_ => Var)) Var) (\_ =>
                  Var)) Arg0))) (Copy Var)))
          (\_ => MkRight MkT0))
        (ArgN (LetRegionValue (MkRegion 9) (I64Op2 Plus (LetRegionValue (MkRegion 10) (MkI64 1) (\_ => Var)) Var) (\_ => Var)) Arg0))) (MkI64 1)))
    (\_ => MkRight MkT0))

  (\_ => LetRegionValue (MkRegion 20) (CaseEither Var (\_ => MkLeft (MkPair (MkBox (FunAppDef "mapSuccList" (\_ => CaseEither Var (\_ =>
MkLeft (MkPair (MkBox (FunApp "mapSuccList" (ArgN (UnBox (GenEW (GetFst Var))) Arg0))) (I64Op2 Plus (LetRegionValue (MkRegion 31) (MkI64 1) (\_ =>
Var)) (GenEW (GetSnd Var (GenEW (GetFst Var))))))) (\_ => MkRight MkT0)) (ArgN (UnBox (GenEW (GetFst Var))) Arg0))) (I64Op2 Plus (LetRegionValue (MkRegion 32) (MkI64 1) (\_ =>
Var)) (GenEW (GetSnd Var (GenEW (GetFst Var))))))) (\_ => MkRight MkT0)) (\_ => LetRegionValue (MkRegion 34) (CaseEither Var (\_ =>
CaseEither (LetRegionValue (MkRegion 41) (I64Cmp LT (GenEW (GetSnd Var (GenEW (GetFst Var)))) (LetRegionValue (MkRegion 42) (MkI64 5) (\_ => Var))) (\_ => Var)) (\_ =>
FunAppDef "filterLt5List" (\_ => CaseEither Var (\_ =>
CaseEither (LetRegionValue (MkRegion 50) (I64Cmp LT (GenEW (GetSnd Var (GenEW (GetFst Var)))) (LetRegionValue (MkRegion 51) (MkI64 5) (\_ => Var))) (\_ => Var)) (\_ =>
FunApp "filterLt5List" (ArgN (UnBox (GenEW (GetFst Var))) Arg0)) (\_ =>
MkLeft (MkPair (MkBox (FunApp "filterLt5List" (ArgN (UnBox (GenEW (GetFst Var))) Arg0))) (Copy (GenEW (GetSnd Var (GenEW (GetFst Var)))))))) (\_ =>
MkRight MkT0)) (ArgN (UnBox (GenEW (GetFst Var))) Arg0)) (\_ =>
MkLeft (MkPair (MkBox (FunApp "filterLt5List" (ArgN (UnBox (GenEW (GetFst Var))) Arg0))) (Copy (GenEW (GetSnd Var (GenEW (GetFst Var)))))))) (\_ => MkRight MkT0)) (\_ =>
PrintValue Var (\_ => PrintValue (LetRegionValue (MkRegion 112) (CaseEither Var (\_ =>
MkLeft (MkPair (MkBox (FunApp "appendList" (ArgN (UnBox (GenEW (GetFst Var))) (ArgN Var Arg0)))) (Copy (GenEW (GetSnd Var (GenEW (GetFst Var))))))) (\_ =>
FunApp "copyList" (ArgN Var Arg0))) (\_ => Var)) (\_ => LetRegionValue (MkRegion 56) (CaseEither (LetRegionValue (MkRegion 80) (CaseEither Var (\_ =>
MkLeft (MkPair (MkBox (FunApp "appendList" (ArgN (UnBox (GenEW (GetFst Var))) (ArgN Var Arg0)))) (Copy (GenEW (GetSnd Var (GenEW (GetFst Var))))))) (\_ =>
FunApp "copyList" (ArgN Var Arg0))) (\_ => Var)) (\_ => PrintI64 (GenEW (GetSnd Var (GenEW (GetFst Var)))) (\_ => FunAppDef "printList" (\_ => CaseEither Var (\_ =>
PrintI64 (GenEW (GetSnd Var (GenEW (GetFst Var)))) (\_ => FunApp "printList" (ArgN (UnBox (GenEW (GetFst Var))) Arg0))) (\_ => MkT0)) (ArgN (UnBox (GenEW (GetFst Var))) Arg0))) (\_ =>
MkT0)) (\_ => CaseEither Var (\_ =>
MkLeft (MkPair (MkBox (FunApp "appendList" (ArgN (UnBox (GenEW (GetFst Var))) (ArgN Var Arg0)))) (Copy (GenEW (GetSnd Var (GenEW (GetFst Var))))))) (\_ =>
FunApp "copyList" (ArgN Var Arg0)))))))))

-}




{-
Main (
  CaseEither (LetRegionValue (MkRegion 3) (I64Cmp EQ Var (LetRegionValue (MkRegion 5) (MkI64 10) (\_ => Var))) (\_ => Var))
    (\_ => MkLeft (MkPair (MkBox
            (FunAppDef "genList" (\_ => CaseEither (LetRegionValue (MkRegion 12) (I64Cmp EQ Var (LetRegionValue (MkRegion 13) (MkI64 10) (\_ => Var))) (\_ => Var)) (\_ =>
              MkLeft (MkPair (MkBox (FunApp "genList" (ArgN (LetRegionValue (MkRegion 15) (I64Op2 Plus (LetRegionValue (MkRegion 16) (MkI64 1) (\_ => Var)) Var) (\_ =>
              Var)) Arg0))) (Copy Var))) (\_ => MkRight MkT0)) (ArgN (LetRegionValue (MkRegion 7) (I64Op2 Plus (LetRegionValue (MkRegion 8) (MkI64 1) (\_ => Var)) Var) (\_ =>
              Var)) Arg0))
            ) (MkI64 1)))
    (\_ => MkRight MkT0))

-}