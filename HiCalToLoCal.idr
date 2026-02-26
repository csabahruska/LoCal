module HiCalToLoCal

import Data.SortedMap
import Control.Monad.State
import Decidable.Equality
import Data.Primitives.Interpolation

import HiCal as Hi
import LoCal as Lo

data HiExp : Type where
  MkHiExp : {t : _} -> Exp t -> HiExp

data LoExp : Type where
  MkLoExp : {t : _} -> {r : _} -> {loc : Loc r} -> Exp t loc EW [] -> LoExp

data LoExp2 : Lo.Ty -> Type where
  MkLoExp2 : {t : _} -> {r : _} -> {loc : Loc r} -> Exp t loc EW [] -> LoExp2 t

data LoExp3 : Lo.Ty -> Type where
  MkLoExp3 : {ew : _} -> {t : _} -> {r : _} -> {loc : Loc r} -> Exp t loc ew [] -> LoExp3 t

record LocState where
  constructor MkLocState
  counter   : Int
  hiExps    : SortedMap Int HiExp
  loExps    : SortedMap Int LoExp
  holes     : SortedMap Int Int

emptyLocState : LocState
emptyLocState = MkLocState
  { counter   = 0
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

getHoleExp : Int -> M LoExp
getHoleExp rid = do
  Just i <- gets $ lookup rid . (.holes)
    | Nothing => assert_total $ idris_crash $ "missing hole for \{rid}"
  Just le <- lookupLoExp i
    | Nothing => assert_total $ idris_crash $ "missing LoExp for \{i}"
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

writeExp : {t : _} -> {r : _} -> {loc : Loc r} -> Hi.Exp t -> M (Lo.Exp (compileTy t) loc EW [])

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
    FunAppNew   - alloc region      TODO  rdone
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

allocInNewRegion : {t : _} -> Hi.Exp t -> M (LoExp2 (compileTy t))
allocInNewRegion e = do
  -- HINT: create region for intermediate value
  let r = MkRegion !newId
  le <- writeExp {loc = LocStart (compileTy t) r} e
  pure $ MkLoExp2 $ LetRegionValue r le id

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
-- TODO: maybe other expressions are possible
readExp (UnBox a) = do
  MkLoExp2 a_lo <- readExp a
  pure $ MkLoExp2 $ UnBox a_lo

readExp (MkBox a) = do
  MkLoExp2 a_lo <- readExp a
  pure $ MkLoExp2 $ MkBox a_lo

readExp (PrintValue a cont) = do
  MkLoExp2 a_lo <- readExp a
  MkLoExp2 cont_lo <- readExp $ cont ()
  pure $ MkLoExp2 $ PrintValue a_lo (\_ => cont_lo)

readExp (PrintI64 a cont) = do
  MkLoExp2 a_lo <- readExp a
  MkLoExp2 cont_lo <- readExp $ cont ()
  pure $ MkLoExp2 $ PrintI64 a_lo (\_ => cont_lo)

readExp (CaseEither {a, b} scrut l_cont r_cont) = do
  l <- newId
  r <- newId
      -- TODO: save these vars for substitution on the recovery pass
      -- Q: or is this correct?
  MkLoExp2 {loc=loc_scrut} scrut_lo <- readExp scrut
  let locL = LocAfterTag "Left"  (compileTy a) loc_scrut
      locR = LocAfterTag "Right" (compileTy b) loc_scrut
  addLoExp {t=compileTy a} {loc=locL} l Var
  addLoExp {t=compileTy b} {loc=locR} r Var
  MkLoExp2 {r=l_r, loc=l_loc} l_cont_lo <- readExp $ l_cont $ Var l
  MkLoExp2 {r=r_r, loc=r_loc} r_cont_lo <- readExp $ r_cont $ Var r
  case decEq l_r r_r of
    No _     => assert_total $ idris_crash "left - right region mismatch"
    Yes Refl => case decEq l_loc r_loc of
      No _     => assert_total $ idris_crash "left - right loc mismatch"
      Yes Refl => pure $ MkLoExp2 $ NewCaseEither scrut_lo (\l => l_cont_lo) (\r => r_cont_lo)

readExp (CasePair {a, b} tup cont) = do
  fst <- newId
  snd <- newId
  {-
    IDEA: replace fst and snd with GetFst <<comp a>> and GetSnd <comp a>> fst-ew
  -}
  MkLoExp2 {loc=loc_tup} tup_lo <- readExp tup
  let ewFst = GenEW $ GetFst tup_lo
  addLoExp fst ewFst
  addLoExp snd $ GetSnd tup_lo ewFst
  readExp $ cont (Var fst) (Var snd)

readExp (Let v cont) = do
  i <- newId
  MkLoExp2 v_lo <- readExp v
  addLoExp i v_lo
  readExp $ cont $ Var i

readExp e@(MkT0{})      = allocInNewRegion e
readExp e@(MkI64{})     = allocInNewRegion e
readExp e@(MkPair{})    = allocInNewRegion e
readExp e@(MkLeft{})    = allocInNewRegion e
readExp e@(MkRight{})   = allocInNewRegion e
readExp e@(FunAppNew{}) = allocInNewRegion e
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

  FunAppNew : String -> (fun_def  : Arg exps_in  -> Exp res) -> (fun_args : Arg exps_in) -> Exp res

  FunAppNew : {fun_ews : _} -> {res : _} -> {r_res : _} -> {loc_res : Loc r_res} ->
           String -> (fun_def : Arg exps_in -> Exp res loc_res EW fun_ews) -> (fun_args : Arg exps_in) -> Exp res loc_res EW fun_ews
-}
writeExp (FunAppNew name def args) = assert_total $ idris_crash "writeExp - FunAppNew"

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
  pure $ PrintValue a_lo (\_ => cont_lo)

writeExp (PrintI64 a cont) = do
  cont_lo <- writeExp $ cont ()
  MkLoExp2 a_lo <- readExp a
  pure $ PrintI64 a_lo (\_ => cont_lo)

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
compileExp : {t : _} -> {r : _} -> {loc : Loc r} -> Hi.Exp t -> M (Lo.Exp (compileTy t) loc EW [])
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
    NewCaseEither   - read, write   rdone  wdone   ; rsem: traverse exp + recalculate loc
    FunAppNew       - read, write   TODO   TODO
    MkT0            - read, write   rdone, wdone   ; rsem: use loc
    MkI64           - read, write   rdone, wdone   ; rsem: use loc
    I64Op2          - read, write   rdone, wdone   ; rsem: use loc
    I64Cmp          - read, write   rdone, wdone   ; rsem: use loc
    PrintI64        - read, write   rdone, wdone
    PrintValue      - read, write   rdone, wdone
    Var             - read          rdone          ; rsem: use loc
    LetTick         - read, write   rdone  wdone   ; rsem: traverse exp
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

fixHolesReadEW  : {t : _} -> {r : _} -> {loc : Loc r} -> {ew : _} -> Lo.Exp t loc ew [] -> M (LoExp2 t)
fixHolesRead    : {t : _} -> {r : _} -> {loc : Loc r} -> {ew : _} -> Lo.Exp t loc ew [] -> M (LoExp3 t)
fixHolesWrite   : {t : _} -> {r : _} -> {loc : Loc r} -> (Lo.Exp t loc EW []) -> M (Lo.Exp t loc EW [])

fixHolesReadEW a = do
  MkLoExp3 {ew = a_ew} a_lo <- fixHolesRead a
  case decEq EW a_ew of
    No _     => assert_total $ idris_crash "EW mismatch"
    Yes Refl => pure $ MkLoExp2 a_lo

fixHolesRead {t} (LetRegionValue (MkRegion rid) Var _) = do
  MkLoExp {t=t_le} le <- getHoleExp rid
  case decEq t t_le of
    No _     => assert_total $ idris_crash "type mismatch"
    Yes Refl => pure $ MkLoExp3 le

fixHolesRead (LetRegionValue val_r val cont) = do
  val2 <- fixHolesWrite val
  MkLoExp3 cont2 <- fixHolesRead $ cont Var
  pure $ MkLoExp3 $ LetRegionValue val_r val2 (\_ => cont2)

fixHolesRead (PrintI64 a cont) = do
  MkLoExp3 a_lo <- fixHolesRead a
  MkLoExp3 cont_lo <- fixHolesRead $ cont ()
  pure $ MkLoExp3 $ PrintI64 a_lo (\_ => cont_lo)

fixHolesRead (PrintValue a cont) = do
  MkLoExp2 a_lo <- fixHolesReadEW a
  MkLoExp3 cont_lo <- fixHolesRead $ cont ()
  pure $ MkLoExp3 $ PrintValue a_lo (\_ => cont_lo)

fixHolesRead (NewCaseEither {a, b} scrut l_cont r_cont) = do
  MkLoExp3 {loc=scrut_loc} scrut_lo <- fixHolesRead scrut
  let locL = LocAfterTag "Left"  a scrut_loc
      locR = LocAfterTag "Right" b scrut_loc
  MkLoExp3 {ew=l_ew, r=l_r, loc=l_loc} l_cont_lo <- fixHolesRead $ l_cont Var
  MkLoExp3 {ew=r_ew, r=r_r, loc=r_loc} r_cont_lo <- fixHolesRead $ r_cont Var
  case decEq l_ew r_ew of
    No _     => assert_total $ idris_crash "EW mismatch"
    Yes Refl => case decEq l_r r_r of
      No _     => assert_total $ idris_crash "region mismatch"
      Yes Refl => case decEq l_loc r_loc of
        No _     => assert_total $ idris_crash "loc mismatch"
        Yes Refl => pure $ MkLoExp3 $ NewCaseEither scrut_lo (\_ => l_cont_lo) (\_ => r_cont_lo)

fixHolesRead v@Var              = pure $ MkLoExp3 v
fixHolesRead {loc} (MkI64{})    = pure $ MkLoExp3 {loc, ew=EW} $ Var
fixHolesRead {loc} (MkT0{})     = pure $ MkLoExp3 {loc, ew=EW} $ Var
fixHolesRead {loc} (I64Op2{})   = pure $ MkLoExp3 {loc, ew=EW} $ Var
fixHolesRead {loc} (I64Cmp{})   = pure $ MkLoExp3 {loc, ew=EW} $ Var
fixHolesRead {loc} (Copy{})     = pure $ MkLoExp3 {loc, ew=EW} $ Var
fixHolesRead {loc} (MkPair{})   = pure $ MkLoExp3 {loc, ew=EW} $ Var
fixHolesRead {loc} (MkLeft{})   = pure $ MkLoExp3 {loc, ew=EW} $ Var
fixHolesRead {loc} (MkRight{})  = pure $ MkLoExp3 {loc, ew=EW} $ Var
fixHolesRead (MkBox a) = fixHolesRead a >>= \(MkLoExp3 {loc=a_loc, ew=a_ew} a_lo) => pure $ MkLoExp3 {loc=a_loc, ew=a_ew} Var
fixHolesRead (UnBox a) = fixHolesRead a >>= \(MkLoExp3 {loc=a_loc, ew=a_ew} a_lo) => pure $ MkLoExp3 {loc=a_loc, ew=a_ew} Var
fixHolesRead (LetTick _ a) = fixHolesRead a >>= \(MkLoExp3 {loc=a_loc, ew=a_ew} a_lo) => pure $ MkLoExp3 {loc=a_loc, ew=a_ew} Var
fixHolesRead (GetFst tup) = fixHolesRead tup >>= \(MkLoExp3 tup_lo) => pure $ MkLoExp3 (GetFst tup_lo)

fixHolesRead (GetSnd {a} tup fst) = do
  MkLoExp3 {r=tup_r, loc=tup_loc} tup_lo <- fixHolesRead tup
  MkLoExp2 {r=fst_r, loc=fst_loc} fst_lo <- fixHolesReadEW fst
  case decEq tup_r fst_r of
    No _     => assert_total $ idris_crash "GetSnd region mismatch"
    Yes Refl => case decEq fst_loc (LocAfterTag "Pair" a tup_loc) of
      No _     => assert_total $ idris_crash "GetSnd loc mismatch"
      Yes Refl => pure $ MkLoExp3 (GetSnd tup_lo fst_lo)
      _ => assert_total $ idris_crash "GetSnd loc decEq needs some fix"

fixHolesRead (GenEW{}) = assert_total $ idris_crash "TODO - GenEW"
fixHolesRead (FunAppNew{}) = assert_total $ idris_crash "TODO - FunAppNew"
fixHolesRead _ = assert_total $ idris_crash "impossible case"

-- ---------------------------------------------------
--
-- ---------------------------------------------------
--
-- ---------------------------------------------------

fixHolesWrite (LetTick i e) = lookupLoExp i >>= \case
  Just _ => fixHolesWrite e -- HINT: no allocation is needed because it is allocated
  Nothing => do
    -- the hi.exp has no destination so it is an intermediate value and needs a new region
    MkHiExp {t=t_he} he <- getHiExp i
    let val_r   = MkRegion !newId
        val_t   = compileTy t_he
        val_loc = LocStart val_t val_r
    le <- writeExp {loc = val_loc} he
    addLoExp {t=val_t} {loc=val_loc} i Var
    e2 <- fixHolesWrite e
    pure $ LetRegionValue {t_val = val_t} val_r (believe_me le) (\_ => e2)

fixHolesWrite (LetRegionValue _ Var _) = assert_total $ idris_crash "fixHolesWrite - region hole"
fixHolesWrite (LetRegionValue val_r val cont) = do
  val2 <- fixHolesWrite val
  cont2 <- fixHolesWrite $ cont Var
  pure $ LetRegionValue val_r val2 (\_ => cont2)

fixHolesWrite (NewCaseEither scrut l_cont r_cont) = do
  MkLoExp3 scrut_lo <- fixHolesRead scrut
  l_cont2 <- fixHolesWrite $ l_cont Var
  r_cont2 <- fixHolesWrite $ r_cont Var
  pure $ NewCaseEither scrut_lo (\_ => l_cont2) (\_ => r_cont2)

fixHolesWrite (I64Op2 op a b) = do
  MkLoExp3 a_lo <- fixHolesRead a
  MkLoExp3 b_lo <- fixHolesRead b
  pure $ I64Op2 op a_lo b_lo

fixHolesWrite (I64Cmp op a b) = do
  MkLoExp3 a_lo <- fixHolesRead a
  MkLoExp3 b_lo <- fixHolesRead b
  pure $ I64Cmp op a_lo b_lo

fixHolesWrite (PrintI64 a cont) = do
  MkLoExp3 a_lo <- fixHolesRead a
  cont_lo <- fixHolesWrite $ cont ()
  pure $ PrintI64 a_lo (\_ => cont_lo)

fixHolesWrite (PrintValue a cont) = do
  MkLoExp2 a_lo <- fixHolesReadEW a
  cont_lo <- fixHolesWrite $ cont ()
  pure $ PrintValue a_lo (\_ => cont_lo)

fixHolesWrite (Copy a) = do
  MkLoExp2 a_lo <- fixHolesReadEW a
  pure $ Copy a_lo

{-
  FunAppNew : {res : _} -> {r_res : _} -> {loc_res : Loc r_res} ->
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
  MkLoExp2 a_lo <- fixHolesRead a
  pure $ GenEW a_lo
-}

fixHolesWrite (Var{}) = assert_total $ idris_crash "fixHolesWrite - Var"
{-
fixHolesWrite (LetRegion{}) = assert_total $ idris_crash "fixHolesWrite - LetRegion"
fixHolesWrite (GetSnd{}) = assert_total $ idris_crash "fixHolesWrite - GetSnd"
fixHolesWrite (GetEWS{}) = assert_total $ idris_crash "fixHolesWrite - GetEWS"
fixHolesWrite (FunAppNew{}) = assert_total $ idris_crash "fixHolesWrite - FunAppNew"
fixHolesWrite (MkOffset{}) = assert_total $ idris_crash "fixHolesWrite - MkOffset"
fixHolesWrite (DeRefOffset{}) = assert_total $ idris_crash "fixHolesWrite - DeRefOffset"
fixHolesWrite (MkPtr{}) = assert_total $ idris_crash "fixHolesWrite - MkPtr"
fixHolesWrite (DeRefPtr{}) = assert_total $ idris_crash "fixHolesWrite - DeRefPtr"
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
      LetTick             - check if lo.exp exists if not then compile and allocate hi.exp to lo.exp a new region
      LetRegionValue Var  - lookup and replace region-id => hi.var-id => lo.exp l it must exist at this time
-}

compileExp e = fixHolesWrite !(writeExp e)

public export compileProgram : Hi.Program -> Lo.Program
compileProgram (Main e) = evalState emptyLocState $ [| Main $ compileExp e |]
