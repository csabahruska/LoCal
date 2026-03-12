module HiCalToLoCal

import Data.Maybe
import Data.SortedSet
import Data.SortedMap
import Control.Monad.State
import Decidable.Equality
import Data.Primitives.Interpolation
import Debug.Trace

import HiCal as Hi
import LoCal as Lo

data HiExp : Type where
  MkHiExp : {t : _} -> Exp t -> HiExp

data LoExpW : Type where
  MkLoExpW : {t : _} -> {r : _} -> {loc : Loc r} -> Exp t loc W [] -> LoExpW

data LoExpREW : Type where
  MkLoExpREW : {t : _} -> {r : _} -> {loc : Loc r} -> Exp t loc REW [] -> LoExpREW

data LoExpREWt : Lo.Ty -> Type where
  MkLoExpREWt : {t : _} -> {r : _} -> {loc : Loc r} -> Exp t loc REW [] -> LoExpREWt t

data LoExpRt : Lo.Ty -> Type where
  MkLoExpRt : {ew : _} -> {t : _} -> {r : _} -> {loc : Loc r} -> Exp t loc (R ew) [] -> LoExpRt t

data LoArg : (fun : String) -> (n : Nat) -> Type where
  MkLoArg : {-{t : _} -> -} Lo.Arg {fun} {n} t -> LoArg fun n

{-
assertHoleFree (MkOffset e) = assertHole r >> assertHoleFree e
assertHoleFree (DeRefOffset e cont) = assertHole r >> assertHoleFree e >> assertHoleFree (cont {r_val=MkRegion !(newId)} Var)
assertHoleFree (MkPtr e) = assertHole r >> assertHoleFree e
assertHoleFree (DeRefPtr e cont) = assertHole r >> assertHoleFree e >> assertHoleFree (cont {r_val=MkRegion !(newId)} Var)
assertHoleFree (PairEW a b) = assertHole r >> assertHoleFree a >> assertHoleFree b
assertHoleFree (LeftEW a b) = assertHole r >> assertHoleFree a >> assertHoleFree b
assertHoleFree (RightEW a b) = assertHole r >> assertHoleFree a >> assertHoleFree b
-}


argLen : Lo.Arg x -> Nat
argLen Arg0 = 0
argLen (ArgN _ a) = 1 + argLen a

hiArgLen : Hi.Arg x -> Nat
hiArgLen Arg0 = 0
hiArgLen (ArgN _ a) = 1 + hiArgLen a

toVar : {t1 : _} -> {r1 : _} -> {loc1 : Loc r1} -> {ew1 : _} -> Lo.Exp t1 loc1 ew1 [] -> Lo.Exp t1 loc1 REW []
toVar _ = Lo.Var

record LocState where
  constructor MkLocState
  counter   : Int
  hiExps    : SortedMap Int HiExp
  loExps    : SortedMap Int LoExpREW
  holes     : SortedMap Int Int -- rid -> hi.var i
  funs      : SortedSet String

emptyLocState : LocState
emptyLocState = MkLocState
  { counter   = 0
  , hiExps    = empty
  , loExps    = empty
  , holes     = empty
  , funs      = empty
  }

M = State LocState

traceM : String -> M ()
traceM s = pure $ trace s ()

assertHole : String -> Region -> M ()
assertHole msg (MkRegion rid) = do
  Nothing <- gets $ lookup rid . (.holes)
    | Just _ => assert_total $ idris_crash $ "\{msg} exp in hole region \{rid}"
  pure ()
assertHole msg (MkArgRegion _ _) = pure ()

newId : M Int
newId = state (\m => ({counter $= (+ 1)} m, m.counter))

addHiExp : {t : _} -> Int -> Exp t -> M ()
addHiExp i e = do
  traceM "fill Hi.Var \{i} with HiExp type: \{show t}"
  modify {hiExps $= insert i (MkHiExp e)}

getHiExp : Int -> M HiExp
getHiExp i = do
  Just he <- gets $ lookup i . (.hiExps)
    | Nothing => assert_total $ idris_crash $ "missing HiExp for \{i}"
  pure he

lookupLoExpREW : Int -> M (Maybe LoExpREW)
lookupLoExpREW i = gets $ lookup i . (.loExps)

addLoExpREW : {t : _} -> {r : _} -> {loc : Loc r} -> Int -> Exp t loc REW [] -> M ()
addLoExpREW i e = do
  traceM "fill Hi.Var \{i} with LoExpREW type: \{show t}"
  modify {loExps $= insert i (MkLoExpREW e)}

addHole : Int -> Int -> M ()
addHole rid i = modify {holes $= insert rid i}

getHoleExp : Int -> M LoExpREW
getHoleExp rid = do
  Just i <- gets $ lookup rid . (.holes)
    | Nothing => assert_total $ idris_crash $ "missing hole for \{rid}"
  Just le <- lookupLoExpREW i
    | Nothing => assert_total $ idris_crash $ "missing LoExpREW for \{i}"
  pure le

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

compileExp : {t : _} -> {r : _} -> {loc : Loc r} -> Hi.Exp t -> M (Lo.Exp (compileTy t) loc W [])
writeExp   : {t : _} -> {r : _} -> {loc : Loc r} -> Hi.Exp t -> M (Lo.Exp (compileTy t) loc W [])
readExp    : {t : _} ->                             Hi.Exp t -> M (LoExpREWt (compileTy t))

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
{-
  hi.exp read semantics:
    Let         - traverse read     wdone rdone
    MkT0        - alloc region      wdone rdone
    MkI64       - alloc region      wdone rdone
    MkPair      - alloc region      wdone rdone
    MkLeft      - alloc region      wdone rdone
    MkRight     - alloc region      wdone rdone
    FunAppDef   - alloc region      TODO  rdone
    I64Op2      - alloc region      wdone rdone
    I64Cmp      - alloc region      wdone rdone
    MkBox       - traverse read     wdone rdone
    UnBox       - traverse read     wdone rdone
    CasePair    - traverse read     wdone rdone
    CaseEither  - traverse read     wdone rdone
    PrintI64    - traverse read     wdone rdone
    PrintValue  - traverse read     wdone rdone
    Var         - read              wdone rdone
-}

allocInNewRegion : {t : _} -> Hi.Exp t -> M (LoExpREWt (compileTy t))
allocInNewRegion e = do
  -- HINT: create region for intermediate value
  let r = MkRegion !newId
  traceM "allocInNewRegion \{show r} START"
  le <- writeExp {loc = LocStart (compileTy t) r} e
  traceM "allocInNewRegion \{show r} END"
  pure $ MkLoExpREWt $ LetRegionValue r le id

readExp (Var i) = lookupLoExpREW i >>= \case
  -- HINT: get location for an already written value
  Just (MkLoExpREW {t=t_lo} le) =>
        case decEq t_lo (compileTy t) of
          No _     => assert_total $ idris_crash "readExp Lo.Ty mismatch\n expected \{show $ compileTy t}\n got: \{show t_lo}"
          Yes Refl => pure (MkLoExpREWt le)
  Nothing => do
    -- HINT: this var can come from: Fun arg, CasePair cont args, CaseEither cont left/right arg, or from Let
    -- save region id => Var i => HiExp origin / LoExpREW (with real location)
    {-
      NOTES:
        possible origins of Var in scope
          Fun arg     - has location
          CasePair    - has location
          CaseEither  - has location
          Let - gets location at the first encounter
    -}
    -- TODO: create only one hole ; Q: would it work if we'd use the Hi.Var id as region-id for hole?
    rid <- newId
    -- Q: maybe this branch is a dead end and we should backtrack earlier?
    addHole rid i -- region-id => Hi.Var id
    --assert_total $ idris_crash "new hole \{rid} => Hi.Var id: \{i} type: \{show t}"
    traceM "new hole \{rid} => Hi.Var id: \{i} type: \{show t}"
    pure $ MkLoExpREWt {loc = LocStart (compileTy t) (MkRegion (-666))} $ Tick rid -- LetRegionValue (MkRegion rid) Lo.Var id
    --MkLoExpREWt : {t : _} -> {r : _} -> {loc : Loc r} -> Exp t loc REW [] -> LoExpREWt t

-- TODO: maybe other expressions are possible
readExp (UnBox a) = do
  MkLoExpREWt a_lo <- readExp a
  pure $ MkLoExpREWt $ UnBox a_lo

readExp (MkBox a) = do
  MkLoExpREWt a_lo <- readExp a
  pure $ MkLoExpREWt $ MkBox a_lo

readExp (PrintValue a cont) = do
  MkLoExpREWt a_lo <- readExp a
  MkLoExpREWt cont_lo <- readExp $ cont ()
  pure $ MkLoExpREWt $ PrintValue a_lo (\_ => cont_lo)

readExp (PrintI64 a cont) = do
  MkLoExpREWt a_lo <- readExp a
  MkLoExpREWt cont_lo <- readExp $ cont ()
  pure $ MkLoExpREWt $ PrintI64 a_lo (\_ => cont_lo)

readExp hiexp@(CaseEither {a, b} scrut l_cont r_cont) = do
  s1 <- get
  l <- newId
  r <- newId
      -- TODO: save these vars for substitution on the recovery pass
      -- Q: or is this correct?
  MkLoExpREWt {loc=loc_scrut} scrut_lo <- readExp scrut
  let locL = LocAfterTag "Left"  (compileTy a) loc_scrut
      locR = LocAfterTag "Right" (compileTy b) loc_scrut
  addLoExpREW {t=compileTy a} {loc=locL} l Lo.Var
  addLoExpREW {t=compileTy b} {loc=locR} r Lo.Var
  MkLoExpREWt {r=l_r, loc=l_loc} l_cont_lo <- readExp $ l_cont $ Var l
  MkLoExpREWt {r=r_r, loc=r_loc} r_cont_lo <- readExp $ r_cont $ Var r
  case decEq l_r r_r of
    Yes Refl => case decEq l_loc r_loc of
      Yes Refl => pure $ MkLoExpREWt $ CaseEither scrut_lo (\l => l_cont_lo) (\r => r_cont_lo)
      No _     => assert_total $ idris_crash "left - right loc mismatch"
    No _ => do
      -- backtrack to the start and try again
      put s1
      allocInNewRegion hiexp -- : {t : _} -> Hi.Exp t -> M (LoExpREWt (compileTy t))

      --r_cont_lo <- writeExp {r=l_r, loc=l_loc} $ r_cont $ Var r
      --pure $ MkLoExpREWt $ CaseEither scrut_lo (\l => l_cont_lo) (\r => LetRegionValue l_r r_cont_lo id)
      --assert_total $ idris_crash "left - right region mismatch l_r: \{show l_r} r_r: \{show r_r}"

readExp (CasePair {a, b} tup cont) = do
  fst <- newId
  snd <- newId
  {-
    IDEA: replace fst and snd with GetFst <<comp a>> and GetSnd <comp a>> fst-ew
  -}
  MkLoExpREWt {loc=loc_tup} tup_lo <- readExp tup
  let ewFst = GenEW $ GetFst tup_lo
  addLoExpREW fst ewFst
  addLoExpREW snd $ GenEW $ GetSnd tup_lo ewFst
  readExp $ cont (Var fst) (Var snd)

readExp (Let v cont) = do
  i <- newId
  MkLoExpREWt v_lo <- readExp v
  addLoExpREW i v_lo
  readExp $ cont $ Var i

readExp e@(MkT0{})      = allocInNewRegion e
readExp e@(MkI64{})     = allocInNewRegion e
readExp e@(MkPair{})    = allocInNewRegion e
readExp e@(MkLeft{})    = allocInNewRegion e
readExp e@(MkRight{})   = allocInNewRegion e
readExp e@(FunAppDef{}) = allocInNewRegion e
readExp e@(I64Op2{})    = allocInNewRegion e
readExp e@(I64Cmp{})    = allocInNewRegion e

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

  FunAppDef : String -> (fun_def  : Arg exps_in  -> Exp res) -> (fun_args : Arg exps_in) -> Exp res

  FunAppDef : {fun_ews : _} -> {res : _} -> {r_res : _} -> {loc_res : Loc r_res} ->
           String -> (fun_def : Arg exps_in -> Exp res loc_res EW fun_ews) -> (fun_args : Arg exps_in) -> Exp res loc_res EW fun_ews
-}
writeExp (FunAppDef name def args) = do

  -- done - only convert once!
  -- Q: how to support recursion?
  -- A: FunApp
  -- TODO: prove that Hi.Arg x has length of n
{-
      let toParams : {fun : _} -> Arg {fun} {n} a -> Arg {fun} {n} a
          toParams (Arg0) = Arg0
          toParams (ArgN {fun, t, n} e a) = ArgN {n, loc_arg=LocStart t $ MkArgRegion fun n} Var $ toParams {n} a
-}
  f <- gets (.funs)
  let readArg : Hi.Arg {n} x -> M (Hi.Arg {n} x, LoArg name n)
      readArg {n=0} Hi.Arg0 = pure $ (Hi.Arg0, MkLoArg Lo.Arg0)
      readArg {n=S n} (ArgN {t} e a) = do
        i <- newId
        -- Q: should we save this var ids?
        MkLoExpREWt {loc=e_loc} e_lo <- readExp e
        --addLoExpREW : {t : _} -> {r : _} -> {loc : Loc r} -> Int -> Exp t loc EW [] -> M ()
        let loc_arg=LocStart (compileTy t) $ MkArgRegion name n
        addLoExpREW {t=compileTy t, loc=loc_arg} i Lo.Var
        (l, MkLoArg a_lo) <- readArg a
        traceM "ArgN - writeExp - FunAppDef \{name} - readArg \{n} - \{showLoExpTag e_lo}"
        pure (ArgN (Hi.Var i) l, MkLoArg $ Lo.ArgN e_lo a_lo)

  (args_hi, MkLoArg args_lo) <- readArg args
  --compileExp : {t : _} -> {r : _} -> {loc : Loc r} -> Hi.Exp t -> M (Lo.Exp (compileTy t) loc EW [])
  if contains name f
    then do
      traceM "SKIP def: \{name}"
      pure $ FunApp name args_lo
    else do
      traceM "WRITE def: \{name}"
      modify {funs $= insert name}
      --body_lo <- compileExp $ def args_hi
      body_lo <- writeExp $ def args_hi
      pure $ FunAppDef name (\_ => body_lo) args_lo

writeExp (CasePair {a, b} tup cont) = do
  fst <- newId
  snd <- newId
  {-
    IDEA: replace fst and snd with GetFst <<comp a>> and GetSnd <comp a>> fst-ew
  -}
  MkLoExpREWt {loc=loc_tup} tup_lo <- readExp tup
  let ewFst = GenEW $ GetFst tup_lo
  addLoExpREW fst ewFst
  addLoExpREW snd $ GenEW $ GetSnd tup_lo ewFst
  writeExp $ cont (Var fst) (Var snd)

writeExp (CaseEither {a, b} scrut l_cont r_cont) = do
  l <- newId
  r <- newId
      -- TODO: save these vars for substitution on the recovery pass
      -- Q: or is this correct?
  MkLoExpREWt {loc=loc_scrut} scrut_lo <- readExp scrut
  let locL = LocAfterTag "Left"  (compileTy a) loc_scrut
      locR = LocAfterTag "Right" (compileTy b) loc_scrut
  addLoExpREW {t=compileTy a} {loc=locL} l Lo.Var
  addLoExpREW {t=compileTy b} {loc=locR} r Lo.Var
  l_cont_lo <- writeExp $ l_cont $ Var l
  r_cont_lo <- writeExp $ r_cont $ Var r
  pure $ CaseEither scrut_lo (\l => l_cont_lo) (\r => r_cont_lo)

{-
  PLAN:
    1) run the analysis in the monad, that can collect data,
    2) then based on the collected data, use a pure function to build the final result
-}

{-
  TODO:
    - model function arguments ; those vars are stored elsewhere
-}

writeExp (I64Op2 op a b) = do
  MkLoExpREWt a_lo <- readExp a
  MkLoExpREWt b_lo <- readExp b
  pure $ I64Op2 (compileIntOp2 op) a_lo b_lo

writeExp (I64Cmp op a b) = do
  MkLoExpREWt a_lo <- readExp a
  MkLoExpREWt b_lo <- readExp b
  pure $ I64Cmp (compileCmpOp op) a_lo b_lo

writeExp (PrintValue a cont) = do
  cont_lo <- writeExp $ cont ()
  MkLoExpREWt a_lo <- readExp a
  pure $ PrintValue a_lo (\_ => cont_lo)

writeExp (PrintI64 a cont) = do
  cont_lo <- writeExp $ cont ()
  MkLoExpREWt a_lo <- readExp a
  pure $ PrintI64 a_lo (\_ => cont_lo)

{-
readExp (Let v cont) = do
  i <- newId
  MkLoExpREWt v_lo <- readExp v
  addLoExpREW i v_lo
  readExp $ cont $ Var i
-}
{-
writeExp (Let v cont) = do
  i <- newId
  MkLoExpREWt v_lo <- readExp v
  addLoExpREW i v_lo
  readExp $ cont $ Var i
-}

writeExp (Let {a} v cont) = do
  i <- newId
  addHiExp i v -- BUG: this is not the right semantics, what if it has no write position?
  s1 <- get
  traceM " ---- BACKTRACK POINT \{s1.counter} -----"
  le <- writeExp $ cont $ Var i
  --pure $ LetTick i !(writeExp $ cont $ Var i)
  -- TODO: uncovered case, when 'v' was used only in read positions
  {-
    IDEA:
      check if v has a write owner and keep it if so
      if not, then revert the transformation and redo it with allocating v in a new region

    TODO: make this algorithm linear with using a region inference preprocessing pass
  -}
  lookupLoExpREW i >>= \case
    Just _ => pure le
    Nothing => do
      traceM " ---- BACKTRACK TO \{s1.counter} -----"
      put s1
      -- HINT: create region for intermediate value
      let rid = MkRegion !newId
      traceM "writeExp Let - create new region: \{show rid}"
      v_le <- writeExp {t=a} {loc = LocStart (compileTy a) rid} v
      addLoExpREW i $ toVar v_le
      le <- writeExp $ cont $ Var i
      pure $ LetRegionValue rid v_le (\_ => le)

writeExp (Var i) = lookupLoExpREW i >>= \case
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
        let MkLoExpW {t=t_lo} _ = MkLoExpW le
        case decEq t_lo (compileTy t) of
          No _     => assert_total $ idris_crash "Var Lo.Ty mismatch1"
          Yes Refl => do
            --addLoExpREW i le
            -- HINT: write lets are always expand
            pure le

  Just (MkLoExpREW {t=t_lo} le) => case decEq t_lo (compileTy t) of
    No _     => assert_total $ idris_crash "Var Lo.Ty mismatch2"
    Yes Refl => pure $ Copy le -- TODO: use indirection to keep sharing, but it would need changes in the exp type

writeExp e = assert_total $ idris_crash "writeExp - TODO"

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
{-
  lo.exp semantics:
    LetRegionValue  - read, write   rdone, wdone
    Copy            - read, write   rdone, wdone   ; rsem: use loc
    MkBox           - read, write   rdone, wdone   ; rsem: traverse exp
    UnBox           - read, write   rdone, wdone   ; rsem: traverse exp
    MkPair          - read, write   rdone, wdone   ; rsem: use loc
    MkLeft          - read, write   rdone, wdone   ; rsem: use loc
    MkRight         - read, write   rdone, wdone   ; rsem: use loc
    GetFst          - read          rdone          ; rsem: traverse exp + recalculate loc
    GetSnd          - read          rdone          ; rsem: traverse exp + recalculate loc
    CaseEither      - read, write   rdone  wdone   ; rsem: traverse exp + recalculate loc
    FunAppDef       - read, write   TODO   TODO
    MkT0            - read, write   rdone, wdone   ; rsem: use loc
    MkI64           - read, write   rdone, wdone   ; rsem: use loc
    I64Op2          - read, write   rdone, wdone   ; rsem: use loc
    I64Cmp          - read, write   rdone, wdone   ; rsem: use loc
    PrintI64        - read, write   rdone, wdone
    PrintValue      - read, write   rdone, wdone
    Var             - read          rdone          ; rsem: use loc
    GenEW           - read          TODO
    AddEW           - not used
    MkOffset        - not used
    DeRefOffset     - not used
    MkPtr           - not used
    DeRefPtr        - not used
    LetRegion       - not used
    StaticEW        - not used
    PairEW          - not used
    LeftEW          - not used
    RightEW         - not used
-}

fixHolesReadEW  : {t : _} -> {r : _} -> {loc : Loc r} -> {ew : _} -> Lo.Exp t loc (R ew) [] -> M (LoExpREWt t)
fixHolesRead    : {t : _} -> {r : _} -> {loc : Loc r} -> {ew : _} -> Lo.Exp t loc (R ew) [] -> M (LoExpRt t)
fixHolesWrite   : {t : _} -> {r : _} -> {loc : Loc r} -> (Lo.Exp t loc W []) -> M (Lo.Exp t loc W [])

fixHolesReadEW a = do
  MkLoExpRt {ew = a_ew} a_lo <- fixHolesRead a
  case decEq EW a_ew of
    No _     => assert_total $ idris_crash "EW mismatch"
    Yes Refl => pure $ MkLoExpREWt a_lo

fixHolesRead {t} (Lo.Tick rid) = do
  MkLoExpREW {t=t_le} le <- getHoleExp rid
  case decEq t t_le of
    No _     => assert_total $ idris_crash "type mismatch"
    Yes Refl => fixHolesRead le

fixHolesRead (LetRegionValue val_r val cont) = do
  val2 <- fixHolesWrite val
  MkLoExpRt cont2 <- fixHolesRead $ cont Lo.Var
  pure $ MkLoExpRt $ LetRegionValue val_r val2 (\_ => cont2)

fixHolesRead (PrintI64 a cont) = do
  MkLoExpRt a_lo <- fixHolesRead a
  MkLoExpRt cont_lo <- fixHolesRead $ cont ()
  pure $ MkLoExpRt $ PrintI64 a_lo (\_ => cont_lo)

fixHolesRead (PrintValue a cont) = do
  MkLoExpREWt a_lo <- fixHolesReadEW a
  MkLoExpRt cont_lo <- fixHolesRead $ cont ()
  pure $ MkLoExpRt $ PrintValue a_lo (\_ => cont_lo)

fixHolesRead (CaseEither {a, b} scrut l_cont r_cont) = do
  MkLoExpRt {loc=scrut_loc} scrut_lo <- fixHolesRead scrut
  let locL = LocAfterTag "Left"  a scrut_loc
      locR = LocAfterTag "Right" b scrut_loc
  MkLoExpRt {ew=l_ew, r=l_r, loc=l_loc} l_cont_lo <- fixHolesRead $ l_cont Lo.Var
  MkLoExpRt {ew=r_ew, r=r_r, loc=r_loc} r_cont_lo <- fixHolesRead $ r_cont Lo.Var
  case decEq l_ew r_ew of
    No _     => assert_total $ idris_crash "EW mismatch"
    Yes Refl => case decEq l_r r_r of
      No _     => assert_total $ idris_crash "region mismatch"
      Yes Refl => case decEq l_loc r_loc of
        No _     => assert_total $ idris_crash "loc mismatch"
        Yes Refl => pure $ MkLoExpRt $ CaseEither scrut_lo (\_ => l_cont_lo) (\_ => r_cont_lo)

{-
  MkLoExpREW {t=t_le} le <- getHoleExp rid
  case decEq t t_le of
    No _     => assert_total $ idris_crash "type mismatch"
    Yes Refl => fixHolesRead le

  Just i <- gets $ lookup rid . (.holes)
    | Nothing => assert_total $ idris_crash $ "missing hole for \{rid}"
-}
fixHolesRead {loc, ew} v@Lo.Var = do
  let (MkRegion rid) = r
        | _ => pure (MkLoExpRt v) --assert_total $ idris_crash "expected MkRegion"
  gets (lookup rid . (.holes)) >>= \case
    Nothing => pure (MkLoExpRt v)
    {-
    Just _ => do
      MkLoExpREW {t=t_le,loc=loc_le} le <- getHoleExp rid
      case decEq t t_le of
        No _     => assert_total $ idris_crash "fixHolesRead Var - type mismatch, expected: \{show t} got: \{show t_le}\n var loc: \{show loc}\n hole loc: \{show loc_le}"
        Yes Refl => pure (MkLoExpRt $ toVar le)
    -}
    Just _ => do -- change the region, keep the location
      let fixLoc : (r2 : _) -> Loc r1 -> Loc r2
          fixLoc r2 (LocStart a r1) = LocStart a r2
          fixLoc r2 (LocAfter a l1) = LocAfter a $ fixLoc r2 l1
          fixLoc r2 (LocAfterTag s a l1) = LocAfterTag s a $ fixLoc r2 l1

      MkLoExpREW {r=r_le} le <- getHoleExp rid
      pure $ MkLoExpRt {r=r_le, loc=fixLoc r_le loc, ew=ew} Lo.Var
{-
fixHolesRead {loc} (MkI64{})    = pure $ MkLoExpRt {loc, ew=EW} $ Var
fixHolesRead {loc} (MkT0{})     = pure $ MkLoExpRt {loc, ew=EW} $ Var
fixHolesRead {loc} (I64Op2{})   = pure $ MkLoExpRt {loc, ew=EW} $ Var
fixHolesRead {loc} (I64Cmp{})   = pure $ MkLoExpRt {loc, ew=EW} $ Var
fixHolesRead {loc} (Copy{})     = pure $ MkLoExpRt {loc, ew=EW} $ Var
fixHolesRead {loc} (MkPair{})   = pure $ MkLoExpRt {loc, ew=EW} $ Var
fixHolesRead {loc} (MkLeft{})   = pure $ MkLoExpRt {loc, ew=EW} $ Var
fixHolesRead {loc} (MkRight{})  = pure $ MkLoExpRt {loc, ew=EW} $ Var
-}
fixHolesRead (MkBox a) = fixHolesRead a >>= \(MkLoExpRt {loc=a_loc, ew=a_ew} a_lo) => pure $ MkLoExpRt {loc=a_loc, ew=a_ew} $ MkBox a_lo
fixHolesRead (UnBox a) = fixHolesRead a >>= \(MkLoExpRt {loc=a_loc, ew=a_ew} a_lo) => pure $ MkLoExpRt {loc=a_loc, ew=a_ew} $ UnBox a_lo
fixHolesRead (GetFst tup) = fixHolesRead tup >>= \(MkLoExpRt tup_lo) => pure $ MkLoExpRt (GetFst tup_lo)

fixHolesRead (GetSnd {a} tup fst) = do
  MkLoExpRt {r=tup_r, loc=tup_loc} tup_lo <- fixHolesRead tup
  MkLoExpREWt {r=fst_r, loc=fst_loc} fst_lo <- fixHolesReadEW fst
  case decEq tup_r fst_r of
    No _     => assert_total $ idris_crash "GetSnd region mismatch, expected: \{show tup_r} got: \{show fst_r}"
    Yes Refl => case decEq fst_loc (LocAfterTag "Pair" a tup_loc) of
      No _     => assert_total $ idris_crash "GetSnd loc mismatch"
      Yes Refl => pure $ MkLoExpRt (GetSnd tup_lo fst_lo)
      _ => assert_total $ idris_crash "GetSnd loc decEq needs some fix"

fixHolesRead (GenEW a) = fixHolesRead a >>= \(MkLoExpRt {loc=a_loc} a_lo) => pure $ MkLoExpRt {loc=a_loc} $ GenEW a_lo
--fixHolesRead (FunAppDef{}) = assert_total $ idris_crash "fixHolesRead - FunAppDef"
--fixHolesRead (FunApp{}) = assert_total $ idris_crash "fixHolesRead - FunApp"
fixHolesRead _ = assert_total $ idris_crash "impossible case"

-- ---------------------------------------------------
--
-- ---------------------------------------------------
--
-- ---------------------------------------------------
getLoc : {t : _} -> {l : Loc r} -> (Exp t l _ _) -> Loc r
getLoc {l} _ = l

--fixHolesWrite (LetRegionValue _ Var _) = assert_total $ idris_crash "fixHolesWrite - region hole"
fixHolesWrite (LetRegionValue val_r val cont) = do
  val2 <- fixHolesWrite val
  cont2 <- fixHolesWrite $ cont Var
  pure $ LetRegionValue val_r val2 (\_ => cont2)

fixHolesWrite (CaseEither scrut l_cont r_cont) = do
  MkLoExpRt scrut_lo <- fixHolesRead scrut
  l_cont2 <- fixHolesWrite $ l_cont Var
  r_cont2 <- fixHolesWrite $ r_cont Var
  pure $ CaseEither scrut_lo (\_ => l_cont2) (\_ => r_cont2)

fixHolesWrite (I64Op2 op a b) = do
  MkLoExpRt a_lo <- fixHolesRead a
  MkLoExpRt b_lo <- fixHolesRead b
  pure $ I64Op2 op a_lo b_lo

fixHolesWrite (I64Cmp op a b) = do
  MkLoExpRt a_lo <- fixHolesRead a
  MkLoExpRt b_lo <- fixHolesRead b
  pure $ I64Cmp op a_lo b_lo

fixHolesWrite (PrintI64 a cont) = do
  MkLoExpRt a_lo <- fixHolesRead a
  cont_lo <- fixHolesWrite $ cont ()
  pure $ PrintI64 a_lo (\_ => cont_lo)

fixHolesWrite (PrintValue a cont) = do
  MkLoExpREWt a_lo <- fixHolesReadEW a
  cont_lo <- fixHolesWrite $ cont ()
  pure $ PrintValue a_lo (\_ => cont_lo)

fixHolesWrite (Copy a) = do
  MkLoExpREWt a_lo <- fixHolesReadEW a
  pure $ Copy a_lo

{-
  FunAppDef : {res : _} -> {r_res : _} -> {loc_res : Loc r_res} ->
  only read:
    GetFst : {r_tup : _} -> {a, b : Ty} -> {loc_tup : Loc r_tup} -> {ew_tup : _} ->
    GetSnd : {r_tup : _} -> {a, b : Ty} -> {loc_tup : Loc r_tup} -> {ew_tup: _} ->
    GenEW : Exp t loc ew_in [] -> Exp t loc EW []
    Var
-}

fixHolesWrite (MkPair a b) = [| MkPair (fixHolesWrite a) (fixHolesWrite b) |]
fixHolesWrite (MkLeft a) = [| MkLeft (fixHolesWrite a) |]
fixHolesWrite (MkRight a) = [| MkRight (fixHolesWrite a) |]
fixHolesWrite (MkBox a) = [| MkBox (fixHolesWrite a) |]
fixHolesWrite (UnBox a) = [| UnBox (fixHolesWrite a) |]
fixHolesWrite MkT0 = pure MkT0
fixHolesWrite (MkI64 i) = pure $ MkI64 i

-- HINT: no GenEW in write position

-- IDEA: handle only the possible constructors
{-
  impossible constructors:
    MkOffset
    DeRefOffset
    MkPtr
    DeRefPtr

    LetRegion

    StaticEW
    PairEW
    LeftEW
    RightEW
    AddEW

  impossible at write, only at read:
    Var
    GenEW
-}
{-
fixHolesWrite Var = pure Var
fixHolesWrite (GenEW a) = do
  MkLoExpREWt a_lo <- fixHolesRead a
  pure $ GenEW a_lo
-}

--fixHolesWrite (Var{}) = assert_total $ idris_crash "fixHolesWrite - Var"

fixHolesWrite (LetRegion{}) = assert_total $ idris_crash "fixHolesWrite - LetRegion"
--fixHolesWrite (GetSnd{}) = assert_total $ idris_crash "fixHolesWrite - GetSnd"
fixHolesWrite (GetEWS{}) = assert_total $ idris_crash "fixHolesWrite - GetEWS"
--fixHolesWrite (FunAppDef n _ _) = assert_total $ idris_crash "fixHolesWrite - FunAppDef \{n}"
--fixHolesWrite a@(FunAppDef name def args) = pure a
{-
readExp : {t : _} -> Hi.Exp t -> M (LoExpREWt (compileTy t))

data Hi.Arg : (sig : List Type) -> Type where
  Arg0 : Arg []
  ArgN : {t : _} -> Exp t -> Arg s -> Arg (Exp t :: s)

data Lo.Arg : (sig : List Type) -> Type where
  Arg0 : Arg []
  ArgN : {t : _} -> {r : _} -> {loc : Loc r} -> {ew : _} -> Exp t loc ew [] -> Arg s -> Arg (Exp t loc ew [] :: s)

  FunAppDef : {exps_in : _} -> {fun_ews : _} -> {res : _} -> {r_res : _} -> {loc_res : Loc r_res} ->
           String ->
           (fun_def  : Arg exps_in  -> Exp res loc_res EW fun_ews) ->
           (fun_args : Arg exps_in) -> Exp res loc_res EW fun_ews

fixHolesWrite : {t : _} -> {r : _} -> {loc : Loc r} -> (Lo.Exp t loc EW []) -> M (Lo.Exp t loc EW [])
-}

fixHolesWrite (FunAppDef name def arg) = do
  {-
    TODO:
      - fix holes for fun app args
      - create new fun def arg (Var) to apply them to def body
      - fix holes in def body
  -}

  let fixHolesReadArg : {-{x : List Type} -> -}Lo.Arg {fun} {n} x -> M (LoArg fun n)
      --fixHolesReadArg = ?fixHolesReadArg0
      --fixHolesReadArg (ArgN e a) = pure $ MkLoArg $ ArgN e a
      --fixHolesReadArg (Lo.ArgN {t=t1, r=r1, loc=loc1, ew=ew1} e a) = do
      fixHolesReadArg (Lo.ArgN {n} e a) = do
        MkLoExpRt e_lo <- fixHolesRead e
        MkLoArg a_lo <- fixHolesReadArg a
        traceM "ArgN - fixHolesWrite - FunAppDef \{name} - fixHolesReadArg \{n} - \{showLoExpTag e} \{showLoExpTag e_lo}"
        pure $ MkLoArg $ ArgN e_lo a_lo
      fixHolesReadArg Lo.Arg0 = pure $ MkLoArg Arg0 -- Q: why is this needed to for coverage?

      toArgVar : {fun : _} -> Lo.Arg {fun} {n} x -> Lo.Arg {fun} {n} x
      toArgVar Arg0 = Arg0
      toArgVar (ArgN {r_arg, loc_arg} e a) = ArgN {r_arg, loc_arg} Var $ toArgVar a

  MkLoArg arg_lo <- fixHolesReadArg arg
  --body_lo <- fixHolesWrite $ (believe_me def) $ toArgVar arg_lo
  body_lo <- fixHolesWrite $ def $ arg -- toArgVar arg
  unless (argLen arg_lo == argLen arg) $ assert_total $ idris_crash "arg len mismatch - FunAppDef \{argLen arg_lo} \{argLen arg}"
  --trace "arg len OK - FunAppDef \{argLen arg_lo} \{argLen arg} \{name}" $
  pure $ FunAppDef name (\_ => body_lo) arg_lo
{-
  -- TODO: (args_hi, MkLoArg args_lo) <- fixHolesReadArg args
  -- body_lo <- fixHolesWrite $ (trace "fixHolesWrite def" def) args_hi
  MkLoArg {t=exp_ins2} args_lo <- fixHolesReadArg args
  body_lo <- fixHolesWrite $ def args_lo
  let MkLoExpREW {t=res2} body_lo2 = MkLoExpREW body_lo
  case decEq t res2 of
    No _     => assert_total $ idris_crash "fixHolesWrite FunAppDef res"
    Yes Refl => pure $ FunAppDef {exp_ins=exp_ins2} {res=t} name (\_ => body_lo2) $ believe_me args_lo
-}

--fixHolesReadArg : {t : _} -> Lo.Arg t -> M LoArg
fixHolesWrite (FunApp name arg) = do -- assert_total $ idris_crash "fixHolesWrite - FunApp \{name}"
  let fixHolesReadArg : {-{x : _} -> -}Lo.Arg {fun} {n} x -> M (LoArg fun n)
      --fixHolesReadArg (ArgN e a) = pure $ MkLoArg $ ArgN e a
      fixHolesReadArg (ArgN {n} e a) = do
        MkLoExpRt e_lo <- fixHolesRead e
        MkLoArg a_lo <- fixHolesReadArg a
        traceM "ArgN - fixHolesWrite - FunApp \{name} - fixHolesReadArg \{n} - \{showLoExpTag e} \{showLoExpTag e_lo}"
        pure $ MkLoArg $ ArgN e_lo a_lo
      fixHolesReadArg Arg0 = pure $ MkLoArg Arg0 -- Q: why is this needed to for coverage?
      --fixHolesReadArg Arg0 = pure $ MkLoArg Arg0 -- Q: why is this not enough for coverage?
  MkLoArg arg_lo <- fixHolesReadArg arg
  unless (argLen arg_lo == argLen arg) $ assert_total $ idris_crash "arg len mismatch - FunApp \{argLen arg_lo} \{argLen arg}"
  --trace "arg len OK - FunApp \{argLen arg_lo} \{argLen arg} \{name}" $
  pure $ FunApp name arg_lo

fixHolesWrite (MkOffset{}) = assert_total $ idris_crash "fixHolesWrite - MkOffset"
fixHolesWrite (DeRefOffset{}) = assert_total $ idris_crash "fixHolesWrite - DeRefOffset"
fixHolesWrite (MkPtr{}) = assert_total $ idris_crash "fixHolesWrite - MkPtr"
fixHolesWrite (DeRefPtr{}) = assert_total $ idris_crash "fixHolesWrite - DeRefPtr"
{-
fixHolesWrite (StaticEW{}) = assert_total $ idris_crash "fixHolesWrite - StaticEW"
fixHolesWrite (GenEW{}) = assert_total $ idris_crash "fixHolesWrite - GenEW"
fixHolesWrite (LeftEW{}) = assert_total $ idris_crash "fixHolesWrite - LeftEW"
fixHolesWrite (RightEW{}) = assert_total $ idris_crash "fixHolesWrite - RightEW"
fixHolesWrite (PairEW{}) = assert_total $ idris_crash "fixHolesWrite - PairEW"
-}
fixHolesWrite e = assert_total $ idris_crash "fixHolesWrite - TODO"

{-
  TODO:
    pass2 deals with:
      LetRegionValue Var  - lookup and replace region-id => hi.var-id => lo.exp l it must exist at this time
-}

assertHoleFree : {t : _} -> {r : _} -> {loc : Loc r} -> {ew : _} -> Lo.Exp t loc ew ews -> M ()
compileExp e = do
  e2 <- writeExp e
  assertHoleFree e2
  pure e2
  {-
  e2 <- fixHolesWrite !(writeExp e)
  assertHoleFree e2
  pure e2
  -}
public export compileProgram : Hi.Program -> Lo.Program
compileProgram (Main e) = evalState emptyLocState $ do
  e' <- compileExp e
  pure $ Main $ LetRegionValue MainRegion e' id



assertHoleFreeArgs : Lo.Arg x -> M ()
assertHoleFreeArgs (ArgN e a) = assertHoleFree e >> assertHoleFreeArgs a
assertHoleFreeArgs Arg0 = pure ()

--assertHoleFree (LetRegion{}) = assert_total $ idris_crash "assertHoleFree - LetRegion"
--assertHoleFree (AddEW{}) = assert_total $ idris_crash "assertHoleFree - AddEW"
--assertHoleFree (GetEWS{}) = assert_total $ idris_crash "assertHoleFree - GetEWS"

--assertHoleFree (LetRegionValue r_val Var _) = assert_total $ idris_crash "assertHoleFree - HOLE: \{show r_val}"
assertHoleFree (LetRegionValue r_val e cont) = assertHole "LetRegionValue" r >> assertHoleFree e >> assertHoleFree (cont Var)
assertHoleFree (Copy e) = assertHole "Copy" r >> assertHoleFree e
assertHoleFree (MkBox e) = assertHole "MkBox" r >> assertHoleFree e
assertHoleFree (UnBox e) = assertHole "UnBox" r >> assertHoleFree e
assertHoleFree (MkPair a b) = assertHole "MkPair" r >> assertHoleFree a >> assertHoleFree b
assertHoleFree (MkLeft a) = assertHole "MkLeft" r >> assertHoleFree a
assertHoleFree (MkRight a) = assertHole "MkRight" r >> assertHoleFree a
assertHoleFree (GetFst a) = assertHole "GetFst" r >> assertHoleFree a
assertHoleFree (GetSnd a b) = assertHole "GetSnd" r >> assertHoleFree a >> assertHoleFree b
assertHoleFree (CaseEither a lc rc) = assertHole "CaseEither" r >> assertHoleFree a >> assertHoleFree (lc Var) >> assertHoleFree (rc Var)
assertHoleFree (FunAppDef _ f a) = assertHole "FunAppDef" r >> assertHoleFree (f a) >> assertHoleFreeArgs a
assertHoleFree (FunApp _ a) = assertHole "FunApp" r >> assertHoleFreeArgs a
assertHoleFree (MkT0) = assertHole "MkT0" r >> pure ()
assertHoleFree (MkI64{}) = assertHole "MkI64" r >> pure ()
assertHoleFree (I64Op2 _ a b) = assertHole "I64Op2" r >> assertHoleFree a >> assertHoleFree b
assertHoleFree (I64Cmp _ a b) = assertHole "I64Cmp" r >> assertHoleFree a >> assertHoleFree b
assertHoleFree (PrintI64 a cont) = assertHole "PrintI64" r >> assertHoleFree a >> assertHoleFree (cont ())
assertHoleFree (PrintValue a cont) = assertHole "PrintValue" r >> assertHoleFree a >> assertHoleFree (cont ())
assertHoleFree (Var) = assertHole "Var" r >> pure ()
assertHoleFree (StaticEW a) = assertHole "StaticEW" r >> assertHoleFree a
assertHoleFree (GenEW a) = assertHole "GenEW" r >> assertHoleFree a

{-
assertHoleFree (MkOffset e) = assertHole r >> assertHoleFree e
assertHoleFree (DeRefOffset e cont) = assertHole r >> assertHoleFree e >> assertHoleFree (cont {r_val=MkRegion !(newId)} Var)
assertHoleFree (MkPtr e) = assertHole r >> assertHoleFree e
assertHoleFree (DeRefPtr e cont) = assertHole r >> assertHoleFree e >> assertHoleFree (cont {r_val=MkRegion !(newId)} Var)
assertHoleFree (PairEW a b) = assertHole r >> assertHoleFree a >> assertHoleFree b
assertHoleFree (LeftEW a b) = assertHole r >> assertHoleFree a >> assertHoleFree b
assertHoleFree (RightEW a b) = assertHole r >> assertHoleFree a >> assertHoleFree b
-}
assertHoleFree _ = assert_total $ idris_crash "assertHoleFree - TODO"
