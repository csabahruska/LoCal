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

{-
  TODO: share Ty and Ops between HiCal an LoCal
-}
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

compileExp2 : {r : _} -> {loc : Loc r} -> Hi.Exp t -> M (Lo.Exp (compileTy t) loc EW [])

needsLoc : {t : _} -> Hi.Exp t -> M (LoExp2 (compileTy t))
needsLoc (Var i) = lookupLoExp i >>= \case
  -- HINT: this is correct
  Just (MkLoExp {t=t_lo} le) =>
        case decEq t_lo (compileTy t) of
          No _     => assert_total $ idris_crash "needsLoc Lo.Ty mismatch"
          Yes Refl => pure (MkLoExp2 le)
  Nothing => do
    -- TODO: mark for fixup
    -- HINT: this var can come from: Fun arg, CasePair cont args, CaseEither cont left/right arg, or from Let
    -- TODO: save region id => Var i => HiExp origin / LoExp (with real location)
    let r = MkRegion !newId
    pure $ MkLoExp2 $ LetRegionValue r Var id
needsLoc e = do
  -- HINT: this is correct
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

  FunAppNew : String -> (fun_def  : Arg exps_in  -> Exp res) -> (fun_args : Arg exps_in) -> Exp res
-}
compileExp2 (FunAppNew name def args) = pure Var -- TODO

compileExp2 (CasePair a cont) = do
  let fst = Var !newId
      snd = Var !newId
  {-
    IDEA: replace fst and snd with GetFst <<comp a>> and GetSnd <comp a>> fst-ew
  -}
  --MkLoExp2 a_lo <- needsLoc a
  -- TODO: save a + fst and a + snd for later recovery
  compileExp2 $ cont fst snd

compileExp2 (CaseEither a l_cont r_cont) = do
  let l = Var !newId
      r = Var !newId
      -- TODO: save these vars for substitution on the recovery pass
      -- Q: or is this correct?
  MkLoExp2 a_lo <- needsLoc a
  l_cont_lo <- compileExp2 $ l_cont l
  r_cont_lo <- compileExp2 $ r_cont r
  pure $ NewCaseEither a_lo (\l => l_cont_lo) (\r => r_cont_lo)

{-
  PLAN:
    1) run the analysis in the monad, that can collect data,
    2) then based on the collected data, use a pure function to build the final result
-}

{-
  TODO:
    - model function arguments ; those vars are stored elsewhere
-}

-- optimization {

compileExp2 (I64Op2 op (MkI64 a) b) = do
  MkLoExp2 b_lo <- needsLoc b
  pure $ I64Op2CE (compileIntOp2 op) a b_lo

compileExp2 (I64Op2 op a (MkI64 b)) = do
  MkLoExp2 a_lo <- needsLoc a
  pure $ I64Op2EC (compileIntOp2 op) a_lo b

compileExp2 (I64Cmp op (MkI64 a) b) = do
  MkLoExp2 b_lo <- needsLoc b
  pure $ I64CmpC (compileCmpOp op) a b_lo

-- optimization }

compileExp2 (I64Op2 op a b) = do
  MkLoExp2 a_lo <- needsLoc a
  MkLoExp2 b_lo <- needsLoc b
  pure $ I64Op2 (compileIntOp2 op) a_lo b_lo

compileExp2 (I64Cmp op a b) = do
  MkLoExp2 a_lo <- needsLoc a
  MkLoExp2 b_lo <- needsLoc b
  pure $ I64Cmp (compileCmpOp op) a_lo b_lo

compileExp2 (PrintValue a cont) = do
  cont_lo <- compileExp2 $ cont ()
  MkLoExp2 a_lo <- needsLoc a
  pure $ PrintValue a_lo (\() => cont_lo)

compileExp2 (PrintI64 a cont) = do
  cont_lo <- compileExp2 $ cont ()
  MkLoExp2 a_lo <- needsLoc a
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
    Yes Refl => pure $ Copy le -- TODO: use indirection to keep sharing, but it would need changes in the exp type


{-
  IDEA:
    make compilation in two pass,
    first collect info about missing pieces
    second use the collected info to transform the code and data representation

  PLAN:
    for first just do a direct translation with fixups, and collect and print collected issues

  IDEA:
    two pass translation
      1) find every Var owner that assigns location to Var
         alias: infer destination locations
        Q: is it possible to compute it in a single linear pass?
-}

compileProgram2 : Hi.Program -> Lo.Program
compileProgram2 (Main e) = Main (evalState emptyLocState $ compileExp2 e)

test, test2, test3, test4 : Lo.Program
test = compileProgram2 $ Main $ Let MkT0 $ \t0 => MkPair t0 t0
test2 = compileProgram2 $ Main $ PrintI64 (MkI64 1) $ \() => MkT0
test3 = compileProgram2 $ Main $ Let (MkI64 1) $ \i => PrintI64 i $ \() => i
test4 = compileProgram2 $ Main $ Let (MkI64 1) $ \i => MkPair (I64Op2 Plus i i) i

{-
data Program : Type where
  Main  : {res : Ty} -> Exp res -> Program

data Program : Type where
  Main  : {res : Ty} -> Exp res (LocStart res (MkRegion (-1))) EW [] -> Program
-}