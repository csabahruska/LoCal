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
  holes     : SortedMap Int Int

emptyLocState : LocState
emptyLocState = MkLocState
  { counter   = 0
  , locInfos  = empty
  , hiExps    = empty
  , loExps    = empty
  , holes     = empty
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

addHole : Int -> Int -> M ()
addHole rid i = modify {holes $= insert rid i}

lookupHole : Int -> M (Either HiExp LoExp)
lookupHole rid = ?lookupHole1

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

writeExp : {r : _} -> {loc : Loc r} -> Hi.Exp t -> M (Lo.Exp (compileTy t) loc EW [])

{-
  IDEA:
    use two compile modes:
      - write ; the destination is known ; fixed location
      - read  ; the origin is arbitrary  ; arbitrary location

  ALGORITHM:
    pass 1) always create a local exp, build merge region info ; DONE
    pass 2) merge regions
              cases:
                region-id => hi.var-id => lo.exp is
                  missing ; then it is an intermediate value, so allocate once (at the LetTick position) and refer it multiple times
                  exist   ; replace Lo.Var with a new Lo.Var

-}

readExp : {t : _} -> Hi.Exp t -> M (LoExp2 (compileTy t))
readExp (Var i) = lookupLoExp i >>= \case
  -- HINT: get location for an already written value
  Just (MkLoExp {t=t_lo} le) =>
        case decEq t_lo (compileTy t) of
          No _     => assert_total $ idris_crash "readExp Lo.Ty mismatch"
          Yes Refl => pure (MkLoExp2 le)
  Nothing => do
    -- HINT: this var can come from: Fun arg, CasePair cont args, CaseEither cont left/right arg, or from Let
    -- save region id => Var i => HiExp origin / LoExp (with real location)
    {-
      NOTES:
        possible origins of Var in scope
          Fun arg     - has location
          CasePair    - has location
          CaseEither  - has location
          Let - gets location at the first encounter
    -}
    rid <- newId
    addHole rid i -- region-id => Hi.Var id
    pure $ MkLoExp2 $ LetRegionValue (MkRegion rid) Var id
readExp e = do
  -- HINT: create region for intermediate value
  let r = MkRegion !newId
  le <- writeExp {loc = LocStart (compileTy t) r} e
  pure $ MkLoExp2 $ LetRegionValue r le id

writeExp MkT0 = pure MkT0
writeExp (MkI64 i) = pure $ MkI64 i
writeExp (MkPair a b) = pure $ MkPair !(writeExp a) !(writeExp b)
writeExp (MkLeft a) = pure $ MkLeft !(writeExp a)
writeExp (MkRight b) = pure $ MkRight !(writeExp b)
writeExp (UnBox a) = pure $ UnBox !(writeExp a)
writeExp (MkBox a) = pure $ MkBox !(writeExp a)

{-
  TODO:
    - compile all functions
-}

{-
  TODO: consume args

  FunAppNew : String -> (fun_def  : Arg exps_in  -> Exp res) -> (fun_args : Arg exps_in) -> Exp res
-}
writeExp (FunAppNew name def args) = pure Var -- TODO

writeExp (CasePair {a, b} tup cont) = do
  fst <- newId
  snd <- newId
  {-
    IDEA: replace fst and snd with GetFst <<comp a>> and GetSnd <comp a>> fst-ew
  -}
  MkLoExp2 {loc=loc_tup} tup_lo <- readExp tup
  let ewFst = GenEW $ GetFst tup_lo
  addLoExp fst ewFst
  addLoExp snd $ GetSnd tup_lo ewFst
  writeExp $ cont (Var fst) (Var snd)

writeExp (CaseEither {a, b} scrut l_cont r_cont) = do
  l <- newId
  r <- newId
      -- TODO: save these vars for substitution on the recovery pass
      -- Q: or is this correct?
  MkLoExp2 {loc=loc_scrut} scrut_lo <- readExp scrut
  let locL = LocAfterTag "Left"  (compileTy a) loc_scrut
      locR = LocAfterTag "Right" (compileTy b) loc_scrut
  addLoExp {t=compileTy a} {loc=locL} l Var
  addLoExp {t=compileTy b} {loc=locR} r Var
  l_cont_lo <- writeExp $ l_cont $ Var l
  r_cont_lo <- writeExp $ r_cont $ Var r
  pure $ NewCaseEither scrut_lo (\l => l_cont_lo) (\r => r_cont_lo)

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

writeExp (I64Op2 op (MkI64 a) b) = do
  MkLoExp2 b_lo <- readExp b
  pure $ I64Op2CE (compileIntOp2 op) a b_lo

writeExp (I64Op2 op a (MkI64 b)) = do
  MkLoExp2 a_lo <- readExp a
  pure $ I64Op2EC (compileIntOp2 op) a_lo b

writeExp (I64Cmp op (MkI64 a) b) = do
  MkLoExp2 b_lo <- readExp b
  pure $ I64CmpC (compileCmpOp op) a b_lo

-- optimization }

writeExp (I64Op2 op a b) = do
  MkLoExp2 a_lo <- readExp a
  MkLoExp2 b_lo <- readExp b
  pure $ I64Op2 (compileIntOp2 op) a_lo b_lo

writeExp (I64Cmp op a b) = do
  MkLoExp2 a_lo <- readExp a
  MkLoExp2 b_lo <- readExp b
  pure $ I64Cmp (compileCmpOp op) a_lo b_lo

writeExp (PrintValue a cont) = do
  cont_lo <- writeExp $ cont ()
  MkLoExp2 a_lo <- readExp a
  pure $ PrintValue a_lo (\() => cont_lo)

writeExp (PrintI64 a cont) = do
  cont_lo <- writeExp $ cont ()
  MkLoExp2 a_lo <- readExp a
  pure $ PrintI64 a_lo (\() => cont_lo)

writeExp (Let v cont) = do
  i <- newId
  addHiExp i v
  pure $ LetTick i !(writeExp $ cont $ Var i)

writeExp (Var i) = lookupLoExp i >>= \case
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
        le <- writeExp he
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
compileExp : {r : _} -> {loc : Loc r} -> Hi.Exp t -> M (Lo.Exp (compileTy t) loc EW [])

fixHoles : (Lo.Exp t loc EW []) -> M (Lo.Exp t loc EW [])
fixHoles (LetRegionValue (MkRegion rid) Var _) = lookupHole rid >>= \case
  Left (MkHiExp he) => do
    -- TODO: this is an impossible case, because LetTick will add the final lo.exp
    -- allocate region for intermediate value
    ?allocIntermediateValue
  Right (MkLoExp le) => ?replaceHoleValue
    -- TODO: add decEq-s
    --pure le

fixHoles e = pure e

{-
  TODO:
    pass2 deals with:
      LetTick             - check if lo.exp exists if not then compile and allocate hi.exp to lo.exp a new region
      LetRegionValue Var  - lookup and replace region-id => hi.var-id => lo.exp l it must exist at this time
-}

compileExp e = fixHoles !(writeExp e)

compileProgram : Hi.Program -> Lo.Program
compileProgram (Main e) = Main $ evalState emptyLocState $ compileExp e

test, test2, test3, test4 : Lo.Program
test = compileProgram $ Main $ Let MkT0 $ \t0 => MkPair t0 t0
test2 = compileProgram $ Main $ PrintI64 (MkI64 1) $ \() => MkT0
test3 = compileProgram $ Main $ Let (MkI64 1) $ \i => PrintI64 i $ \() => i
test4 = compileProgram $ Main $ Let (MkI64 1) $ \i => MkPair (I64Op2 Plus i i) i
