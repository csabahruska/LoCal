module LoCal

public export
data Ty
  = T0
  | Tup2 Ty Ty
  | Either Ty Ty
  | I64
  | DecBox (Ty -> Ty)
  | DefBox Ty Ty Ty

{-
  INSIGHT:
    control flow construct data
      if          -> + types
      basic block -> * types
    unconsrained recursion needs Box!!!
-}

{-
  REPRESENTATION:
    - no tag:   I64
    - has tag:  Tup2, Either

  FUTURE WORK:
    - no tag for Tup2 ; problem to solve is location aliasing
-}


public export
data Region : Type where
  MkRegion : Int -> Region

public export
data Loc : (t : Ty) -> (1 r : Region) -> Type where
  MkLoc : Int -> Loc t r

public export
data LocExp : (1 r : Region) -> Type where
  LocStart    : (1 r : Region) -> LocExp r
  LocAfter    : Ty -> (1 _ : Loc _ r) -> LocExp r   -- Q: dynamically/runtime known? maybe a better name is RuntimeAfter ; A: NO!
          --    ^ this should be a value variable instead of Ty, that would solve the sizeof problem with either's left/right
          --    Q: what problem would it cause?
  LocAfterTag : (1 _ : Loc _ r) -> LocExp r         -- statically known ; used for jump over the tag

data Fun : (arg : Ty) -> (res : Ty) -> Type

{-
  Q:
    do we need locations for building only?
    do we need locations for deconstruction?

  - locations can be queried from variables
-}

{-
  mvp simplifications:
    - only tup2 and either ; product and sum type
    - only I64 interger primitive type
    - functions with only single argument
    - no sharing

  Q: what about stack frames and stack based memory management?
  Q: what about returning values in registers?
  A: use special region for that, or use escape analysis on regions

  mvp example:
    - program read user input N:int
    - creates a List of Int from 1 to N unpacked in a buffer

-}

{-
  currently sharing is not supported
  for support we need:
    + indirection value
    + location for indirection
    + linear value types ; in Let
    + dup hoas primitive

  IDEA:
    locations are linear, values are not
    sharing could be supported by recognizing non linear value usage
    for duplicates instead of the value an indirection is written
-}

{-
  sharing support:
    - explicit indirections, linear locations, DUP for locations to model indirection
    - implicit sharing: use coercions for automatic DUP insertion
-}

{-
  TODO: refactor to
    - simple expression ; value definition
    - bind chain ; various lets, return value
    + check this during hoas interpretation
    + the last expression of a bind chain must be a hoas variable
-}
{-
public export
data Exp : (t : Ty) -> Type where

  -- primitive values
  MkI64 : Int -> Exp I64

  -- value shapes, ADT can be modeled with these
  MkTup2  : Exp a -> Exp b -> Exp (Tup2 a b)
  MkLeft  : Exp a -> Exp (Either a b)
  MkRight : Exp b -> Exp (Either a b)

  CaseFst     : Exp (Tup2 a b)   -> (1 _ : Exp a -> Exp c) -> Exp c
  CaseSnd     : Exp (Tup2 a b)   -> (1 _ : Exp b -> Exp c) -> Exp c
  CaseEither  : Exp (Either a b) -> (1 _ : Exp a -> Exp c) -> (1 _ : Exp b -> Exp c) -> Exp c

  -- location related
  LetRegion : (1 _ : (1 _ : Region) -> Exp a) -> Exp a
  LetLoc : {t : Ty} -> (1 _ : LocExp r) -> (1 _ : (1 _ : Loc t r) -> (1 _ : Loc t r) -> Exp a) -> Exp a -- Q: is this needed? use loc expressions for construction?

  -- generic
  Let : (1 _ : Loc a _) -> Exp a -> (1 _ : Exp a -> Exp b) -> Exp b
  Ret : (1 end_witness : Loc a _) -> Exp b -> Exp b

  FunApp : Fun arg res -> Exp arg -> Exp res

  -- internal
  Var : Int -> Exp a
-}
public export
data Exp : (t : Ty) -> (r : Region) -> Type where

  -- primitive values
  MkI64 : Int -> Exp I64 r

  -- value shapes, ADT can be modeled with these
  MkTup2  : Exp a r -> Exp b r -> Exp (Tup2 a b) r
  MkLeft  : Exp a r -> Exp (Either a b) r
  MkRight : Exp b r -> Exp (Either a b) r

  CaseFst     : Exp (Tup2 a b) r   -> (1 _ : Exp a r -> Exp c r_out) -> Exp c r_out
  CaseSnd     : Exp (Tup2 a b) r   -> (1 _ : Exp b r -> Exp c r_out) -> Exp c r_out
  CaseEither  : Exp (Either a b) r -> (1 _ : Exp a r -> Exp c r_out) -> (1 _ : Exp b r -> Exp c r_out) -> Exp c r_out

  -- location related
  LetRegion : (1 _ : (1 _ : Region) -> Exp a r) -> Exp a r
  LetLoc : {t : Ty} -> (1 _ : LocExp r) -> (1 _ : (1 _ : Loc t r) -> (1 _ : Loc t r) -> Exp a r_out) -> Exp a r_out -- Q: is this needed? use loc expressions for construction?

  -- generic
  Let : (1 loc : Loc a r) -> Exp a r -> (1 _ : Exp a r -> Exp b r_out) -> Exp b r_out
  --Ret : (1 end_witness : Loc a _) -> Exp b -> Exp b

  FunApp : Fun arg res -> Exp arg r_in -> Exp res r_out

  -- internal
  Var : Int -> Exp a r

public export
data Fun : (arg : Ty) -> (res : Ty) -> Type where
  MkFunId : Int -> Fun arg res

public export
data Program : Type where
  Main  : (main : Fun T0 res) -> Program
  MkDec : {arg : Ty} -> {res : Ty} -> (Fun arg res -> Program) -> Program
  MkDef : {arg : Ty} -> {res : Ty} -> Fun arg res -> (Exp arg r_in -> Exp res r_out) -> Program -> Program

-- -------------------------------

{-
  TODO:
    - separate expressions from value definitions
    - make all location variables linear, one for values one for locations
    - add function return (terminator expression)
      + that would take a location and a value
      + or it would take a variable
         * this would need a new location expression type: function return value ; NO - it should use the after location
-}

{-
  TODO:
    - write buffer based interpreter
    - write C backend
    - write example for function call
  Q: should we distinguish register and memory values ; ref or immediate value?
-}

{-
  Q: how to express location relations?
    a) flattened low level: sequence of prim types            ; locations are sequenced linearly           (list of locations) ; compatible with linear types
    b) high level:          sequence of high level structures ; locations can be referenced multiple times (tree of locations) ; needs multi modality

  NOTE:
    the problem of the list of locations approach is that it fixes the layout and we want to support filed reordering, so the location language must support that


  PROBLEM:
    currently a tup2 I64 I64 representation can be arbitraty, but it will be written correctly due to locations,
      but the consumer (reader) side might use a different layout,
      for example the producer side could use a [TAG, trash, fst I64, trash, snd I64] layout
      and the consumer side just would expect a packed [TAG, fst I64, snd I64] layout,
      which would not work
    to solve it the type and layout must be attached
    Q: where to attach?
      a) Ty
      b) Exp  ; <=== I'd prefer this

    Q: what would be the layout language?

  LAYOUT MVP:
    - force to use packed ; left to right layout ordering
    - make it correct by construction
-}



-- -------------------------------

-- multi arg modeling
{-
data Arg : (sig : List Ty) -> Type where
  NilArg : Arg Nil
  MkArg : Exp t -> Arg s -> Arg (t :: s)

test2 : Arg [I64, I64]
test2 = MkArg (MkI64 1) $ MkArg (MkI64 2) $ NilArg

FunTy : List Ty -> Ty -> Type
FunTy [] r = Exp r
FunTy (t::ts) r = Exp t -> FunTy ts r

fn : FunTy [I64, I64] I64
fn = \a => \b => b
-}
{-
  ingredients
    App - function + one argument
    Tup2
    Either
    Top level functions:
      def + arr
    fst, snd
    either - control flow based eliminator
-}

{-
  NOTES:
    location is: staticly known or dynamicly/runtime known
-}

{-
  put either and tup2 and I64 into buffers
-}

{-
  IDEA:
    hybrid elaborator:
      + edsl with type guarantees derived from meta language
        example: usual functional language (L1 gibbon)
      + edsl hoas interpreter that infers dsl types further
        example: functional language with locations (L2 gibbon)
                 the interpreter would insert locations
                 the LoCal is a correct by construction language for locations, the interpreter would build it
-}

{-
  TODO:
    - create high level simple functional hoas edsl
    - create interpreter that compiles the high level hoas edsl to LoCal edsl, with inferring and inserting locations
-}

{-
  INSIGHT:
  - the interpreter might rely on a less typed IR for input, i.e. when linearity would be broken due to interpretation requirements
  - locations might be pre interpreted before value allocations, so that the addresses would be already available
-}

{-
  INSIGHT:
  - location is the descriptor where to find the data
    + if it is static then to can turn to code
    + if it is dynamic then it needs runtime interpretation

  Q: is this a valid example?
      create a value: Tup2 [garbage] fst snd
      pass to a function to return the snd
      Q: can the callee skip the [garbage]?
      A: YES, if the input location is passed statically or dynamically

  Q: can the target language implemented as a fully dynamic system that works with dynamic locations and buffers,
     and with staging we could specialize the static parts of the programs?
     would this be the same system as gibbon/LoCal?


  IDEA/EXPERIMENT:
    create a high level functional language that works without locations but runs on serialized representation,
    where all locations are handled dynamically in an interpreter

    INSIGHT:
      the source code statically defines the constructed values and their positions, but in not serialized way,
      but when the locations are derived only from source code then they are static also, because the source code is static


  METHOD:
    high level language (simple functional language)
    interpreted on the target system's architecture (buffer based system)
    everything is runtime
    OUTCOME:
      structured implementation
      with staging the static parts we can get a compiler and an efficient but generic solution

    Q: what if we use the LoCal language as an input and for interpretation?
    INSIGHT: LoCal = high level language + locations

    Q: what about interleaved garbage in the result data?
    TODO:
      - create a gibbon example for this, check the C code ; see: WritePackedFile
        gibbon allocates garbage into a separate region, and it puts the output into the same region
      - how will my interpreter handle this?
-}
