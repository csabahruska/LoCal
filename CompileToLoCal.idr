module CompileToLoCal

import Data.SortedMap
import Control.Monad.State
import Decidable.Equality
import Data.Primitives.Interpolation

import HiCal as Hi
import LoCal as Lo

data LocInfo : Type where
  MkLocInfo : {r : _} -> (loc : Loc r) -> LocInfo

data HiExp : Type where
  MkHiExp : {t : _} -> Exp t -> HiExp

data LoExp : Type where
  MkLoExp : {t : _} -> {r : _} -> {loc : Loc r} -> Exp t loc EW [] -> LoExp

data LoExp2 : Lo.Ty -> Type where
  MkLoExp2 : {t : _} -> {r : _} -> {loc : Loc r} -> Exp t loc EW [] -> LoExp2 t

record LocState where
  constructor MkLocState
  counter   : Int
  locInfos  : SortedMap Int LocInfo
  hiExps    : SortedMap Int HiExp
  loExps    : SortedMap Int LoExp

emptyLocState : LocState
emptyLocState = MkLocState
  { counter   = 0
  , locInfos  = empty
  , hiExps    = empty
  , loExps    = empty
  }

M = State LocState

newId : M Int
newId = state (\m => ({counter $= (+ 1)} m, m.counter))

addHiExp : {t : _} -> Int -> Exp t -> M ()
addHiExp i e = modify {hiExps $= insert i (MkHiExp e)}

getHiExp : Int -> M HiExp
getHiExp i = do
  Just he <- gets $ lookup i . (.hiExps)
    | Nothing => assert_total $ idris_crash $ "missing HiExp for \{i}"
  pure he

lookupLoExp : Int -> M (Maybe LoExp)
lookupLoExp i = gets $ lookup i . (.loExps)

addLoExp : {t : _} -> {r : _} -> {loc : Loc r} -> Int -> Exp t loc EW [] -> M ()
addLoExp i e = modify {loExps $= insert i (MkLoExp e)}

compileTy : Hi.Ty -> Lo.Ty
compileTy = \case
  T0          => T0
  I64         => I64
  Pair a b    => Pair (compileTy a) (compileTy b)
  Either a b  => Either (compileTy a) (compileTy b)
  Box n a     => Box n $ compileTy a

compileIntOp2 : Hi.IntOp2 -> Lo.IntOp2
compileIntOp2 = \case
  Plus  => Plus
  Sub   => Sub
  Times => Times
  Quot  => Quot
  Rem   => Rem

compileCmpOp : Hi.CmpOp -> Lo.CmpOp
compileCmpOp = \case
  EQ  => EQ
  GE  => GE
  GT  => GT
  LE  => LE
  LT  => LT
  NE  => NE

{-
--compileExp : {t2 : _} -> {r : _} -> {loc : Loc r} -> {ew : _} -> {ews : _} -> Hi.Exp t -> Lo.Exp t2 loc ew ews
--compileExp : Hi.Exp t -> Lo.Exp (compileTy t) loc EW []
compileExp : {t2 : _} -> Hi.Exp t -> Lo.Exp t2 loc EW []

compileExp MkT0 = case decEq t2 T0 of
  Yes Refl => MkT0
  No _     => assert_total $ idris_crash "MkT0"

--compileExp MkT0 = let Yes Refl = decEq t2 T0 | No _ => assert_total $ idris_crash "MkT0" in MkT0

--compileExp (MkPair a b) = MkPair (compileExp a) (compileExp b)
compileExp e = ?fdsfd

compileProgram : Hi.Program -> Lo.Program
compileProgram (Main {res=resHi} e) = Main {res = compileTy resHi} $ compileExp e
-}
------
compileExp2 : {r : _} -> {loc : Loc r} -> Hi.Exp t -> M (Lo.Exp (compileTy t) loc EW [])
needsLoc : {t : _} -> Hi.Exp t -> M (LoExp2 (compileTy t))

{-
  LetRegionValue : {t_val : _} -> (r_val : Region) -> Exp t_val (LocStart t_val r_val) EW [] ->
                   (Exp t_val (LocStart t_val r_val) EW [] -> Exp a loc ew ews) -> Exp a loc ew ews

-}
needsLoc (Var i) = lookupLoExp i >>= \case
  Just (MkLoExp {t=t_lo} le) =>
        case decEq t_lo (compileTy t) of
          No _     => assert_total $ idris_crash "needsLoc Lo.Ty mismatch"
          Yes Refl => pure (MkLoExp2 le)

  Nothing => ?todo
needsLoc e = do
  let r = MkRegion !newId
  le <- compileExp2 {loc = LocStart (compileTy t) r} e
  pure $ MkLoExp2 $ LetRegionValue r le id

compileExp2 MkT0 = pure MkT0
compileExp2 (MkI64 i) = pure $ MkI64 i
compileExp2 (MkPair a b) = pure $ MkPair !(compileExp2 a) !(compileExp2 b)
compileExp2 (MkLeft a) = pure $ MkLeft !(compileExp2 a)
compileExp2 (MkRight b) = pure $ MkRight !(compileExp2 b)
compileExp2 (UnBox a) = pure $ UnBox !(compileExp2 a)
compileExp2 (MkBox a) = pure $ MkBox !(compileExp2 a)

{-
  TODO: consume args

  CasePair   : {a, b, c : Ty} -> Exp (Pair a b) -> (Exp a -> Exp b -> Exp c) -> Exp c
  CaseEither : {a, b, c : Ty} -> Exp (Either a b) -> (Exp a -> Exp c) -> (Exp b -> Exp c) -> Exp c
  FunAppNew : String -> (fun_def  : Arg exps_in  -> Exp res) -> (fun_args : Arg exps_in) -> Exp res
-}


--compileExp2 (CaseEither scrut lcont rcont) = CaseEither (compileExp2 scrut) (\l => compileExp2 $ lcont Var) (\r => compileExp2 $ rcont Var)

compileExp2 (I64Op2 op (MkI64 a) b) = do
  MkLoExp2 b_lo <- needsLoc b
  pure $ I64Op2CE (compileIntOp2 op) a b_lo

compileExp2 (I64Op2 op a (MkI64 b)) = do
  MkLoExp2 a_lo <- needsLoc a
  pure $ I64Op2EC (compileIntOp2 op) a_lo b

compileExp2 (I64Op2 op a b) = do
  MkLoExp2 a_lo <- needsLoc a
  MkLoExp2 b_lo <- needsLoc b
  pure $ I64Op2 (compileIntOp2 op) a_lo b_lo

compileExp2 (I64Cmp op (MkI64 a) b) = do
  MkLoExp2 b_lo <- needsLoc b
  pure $ I64CmpC (compileCmpOp op) a b_lo

compileExp2 (I64Cmp op a b) = do
  MkLoExp2 a_lo <- needsLoc a
  MkLoExp2 b_lo <- needsLoc b
  pure $ I64Cmp (compileCmpOp op) a_lo b_lo

compileExp2 (PrintValue a cont) = do
  MkLoExp2 a_lo <- needsLoc a
  cont_lo <- compileExp2 $ cont ()
  pure $ PrintValue a_lo (\() => cont_lo)

compileExp2 (PrintI64 a cont) = do
  MkLoExp2 a_lo <- needsLoc a
  cont_lo <- compileExp2 $ cont ()
  pure $ PrintI64 a_lo (\() => cont_lo)

compileExp2 (Let v cont) = do
  i <- newId
  addHiExp i v
  compileExp2 $ cont $ Var i

compileExp2 (Var i) = lookupLoExp i >>= \case
  {-
    HINT:
      - for the first encounter, lookup v and compile it, store the result
      - otherwise lookup the compiled expression and return a Copy of it
  -}
  Nothing => do
    MkHiExp {t=t_he} he <- getHiExp i
    case decEq t_he t of
      No _     => assert_total $ idris_crash "Var Hi.Ty mismatch"
      Yes Refl => do
        le <- compileExp2 he
        let MkLoExp {t=t_lo} _ = MkLoExp le
        case decEq t_lo (compileTy t) of
          No _     => assert_total $ idris_crash "Var Lo.Ty mismatch1"
          Yes Refl => do
            addLoExp i le
            pure le
  Just (MkLoExp {t=t_lo} le) => case decEq t_lo (compileTy t) of
    No _     => assert_total $ idris_crash "Var Lo.Ty mismatch2"
    Yes Refl => pure $ Copy le


{-
  IDEA:
    make compilation in two pass,
    first collect info about missing pieces
    second use the collected info to transform the code and data representation

  PLAN:
    for first just do a direct translation with fixups, and collect and print collected issues
-}

compileExp2 e = ?missingHiExp

compileProgram2 : Hi.Program -> Lo.Program
compileProgram2 (Main e) = Main (evalState emptyLocState $ compileExp2 e)

test, test2 : Lo.Program
test = compileProgram2 $ Main $ Let MkT0 $ \t0 => MkPair t0 t0
test2 = compileProgram2 $ Main $ PrintI64 (MkI64 1) $ \() => MkT0

{-
data Program : Type where
  Main  : {res : Ty} -> Exp res -> Program

data Program : Type where
  Main  : {res : Ty} -> Exp res (LocStart res (MkRegion (-1))) EW [] -> Program
-}