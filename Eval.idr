module Eval

import Data.Maybe
import Data.SortedMap
import Control.Monad.State
import Data.Buffer

import LoCal

data FunDef : Type where
  MkFunDef : {arg : Ty} -> {res : Ty} -> (Exp arg -> Exp res) -> FunDef

{-
  TODO:
    do no store loc exp, instead interpret it immediately

  INSIGHT:
    - locations are static relative positions in the region
      + this is true for inferred, compile time/type level recursions, including function calls
      + boxing and uncontrolled recursive function calls must return cursors, which are runtime loctations
      Q: what is the precise relation between compile time (static) locations and runtime (dynamic) locations?
    - region is a base position in a buffer
    - locations are translated into static code during compilation, but it could be represented as a map during interpretation
-}
record LocDef where
  constructor MkLocDef
  region  : Int
  offset  : Int

record Machine where
  constructor MkMachine
  counter   : Int
  functions : SortedMap Int FunDef
  regions   : SortedMap Int Buffer
  locations : SortedMap Int LocDef

emptyMachine : Machine
emptyMachine = MkMachine
  { counter   = 0
  , functions = empty
  , regions   = empty
  , locations = empty
  }

data Val
  = VRef Int Int -- buffer, index
  | VVoid

M = StateT Machine IO

newId : M Int
newId = state (\m => ({counter $= (+ 1)} m, m.counter))

addFun : Int -> FunDef -> M ()
addFun funId fun = modify {functions $= insert funId fun}

loadProgram : Program -> M Int
loadProgram (Main (MkFunId mainId)) =
  pure mainId
loadProgram (MkDec cont) =
  loadProgram $ cont (MkFunId !newId)
loadProgram (MkDef (MkFunId funId) fun prog) = do
  addFun funId (MkFunDef fun)
  loadProgram prog

newRegion : M Int
newRegion = do
  Just buf <- newBuffer (1024)
    | Nothing => assert_total $ idris_crash "INTERNAL ERROR: new region"
  i <- newId
  modify {regions $= insert i buf}
  pure i

partial getLocDef : Int -> M LocDef
getLocDef i = do
  Just ld <- lookup i <$> gets locations
  pure ld

partial sizeOf : Ty -> Int
sizeOf T0 = 0
sizeOf (Tup2 a b) = 1 + sizeOf a + sizeOf b
sizeOf (Either a b) = 1 + sizeOf a + sizeOf b -- TODO
sizeOf I64 = 1
{-
  | DecBox (Ty -> Ty)
  | DefBox Ty Ty Ty
-}

partial newLocation : LocExp r -> M Int
newLocation le = do
  i <- newId
  loc <- case le of
    LocStart (MkRegion r) => pure (MkLocDef {region = r, offset = 0})
    LocAfter ty (MkLoc l) => {offset $= (+ (sizeOf ty))} <$> getLocDef l
    LocAfterTag (MkLoc l) => {offset $= (+ 1)} <$> getLocDef l
  modify {locations $= insert i loc}
  pure i

Env = SortedMap Int Val

addEnv : Val -> Env -> M (Exp t, Env)
partial callFun : Int -> Val -> M Val
partial evalExp : Env -> Exp t -> M (Env, Val)

addEnv v env = do
  i <- newId
  pure $ (Var i, insert i v env)

callFun funId arg = do
  Just (MkFunDef fun) <- lookup funId <$> gets functions
  (v, env) <- addEnv arg empty
  snd <$> evalExp env (fun v)

{-
  INSIGHT:
    the interpretation/execution is not based on the exp tree, but the location ordering,
    this is needed for the right serialized ordering based on the spec.
    i.e. the either actual size is depending on the actual value, the location position/offset is depending on the actual values

  algorithm:
    - build location chain
    - assign values to locations
    - traverse location chain and set concrete offsets based on value sizes

  Q: could be problematic with a wrong data dependency order?

  the output of the interpretation is an ordering
    we need two types of interpretation:
    + type structure interpretation, calculating the tags, i.e. deciding left or right of either
    + concrete program interpretation

  the mapping is static, because the source code (Exp) fully defines it statically, there is no recursion in it, no boxing
  so the placement is computable
-}
evalExp env (Var i) = pure (env, fromMaybe VVoid $ lookup i env) -- TODO: proper error handling
evalExp env (LetRegion cont) = evalExp env $ cont (MkRegion !newRegion)
evalExp env (LetLoc le cont) = do
  i <- newLocation le
  evalExp env $ cont (MkLoc i) (MkLoc i)
evalExp env (Ret l (Var i)) = pure (env, fromMaybe VVoid $ lookup i env)
{-
  TODO:
    create example for either
-}
--  Let : (1 _ : Loc a _) -> Exp a -> (1 _ : Exp a -> Exp b) -> Exp b



public export partial
eval : Program -> IO (Machine, Val)
eval prog = runStateT emptyMachine $ do
  mainId <- loadProgram prog
  callFun mainId VVoid

{-
  use module Data.Buffer
    newBuffer : HasIO io => Int -> io (Maybe Buffer)
    newBuffer size

-}

{-
  TODO:
    - define state
    - define memory management structures
    - eval functions
    - eval expression
-}

{-
record StateT (stateType : Type) (m : Type -> Type) (a : Type) where
  constructor ST
  runStateT' : stateType -> m (stateType, a)
-}
