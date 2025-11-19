module LoCal

public export
data Ty
  = T0
  | Tup2 Ty Ty
  | Either Ty Ty
  | I64
  | DecBox (Ty -> Ty)
  | DefBox Ty Ty Ty
  | Ind Ty -- raw pointer ; no tag ; just the location data

{-
  INSIGHT:
    control flow construct data
      if          -> + types
      basic block -> * types
    unconsrained recursion needs Box!!!
-}

{-
  REPRESENTATION:
    - no tag:   I64, Tup2
    - has tag:  Either

  FUTURE WORK:
    - either should use only one bit tag
      + implement packing of multiple tags into a byte or multiple bytes
      + implement sub byte/word addressing but by tags and data
    - add alignment control to locations
-}


public export
data Region : Type where
  MkRegion : Int -> Region

data LocExp : (r : Region) -> Type

public export
data Loc : (r : Region) -> Type where
  MkLoc : Int -> Loc r
  MkLE  : LocExp r -> Loc r

public export
data Size
  = STup2 Size Size
  -- | SEither Size Size
  | STag Size
  | SInt Int
  | D
--  = S Int -- static size
--  | D     -- dynamics size

{-
public export
Num Size where
  --(S a) + (S b) = S (a + b)
  (+) = \_,_ => D
  (*) = \_,_ => D
  fromInteger = \i => SInt (fromInteger i)
-}



public export
data LocExp : (r : Region) -> Type where
  LocStart    : (r : Region) -> LocExp r
  LocAfter    : Size -> (Loc r) -> LocExp r   -- Q: dynamically/runtime known? maybe a better name is RuntimeAfter ; A: NO!
                -- IDEA: location is not the right thing that descibes the next location
                --        instead it would be the end witness of some value!
                --        location + size-witness = end-witness
          --    ^ this should be a value variable instead of Ty, that would solve the sizeof problem with either's left/right
          --    Q: what problem would it cause?
  LocAfterTag : (Loc r) -> LocExp r         -- statically known ; used for jump over the tag
--  LocInd      : (1 _ : Loc r) -> LocExp r

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
--public export
--data Exp : (l : Type) -> Type where
--data Exp2 : (t : Ty) -> (loc : Loc r) -> (size : Int) -> Type

-- HINT: sizes are for 64 bit system in bytes
public export
data Exp : (t : Ty) -> (loc : Loc r) -> (size : Size) -> Type where
--data Exp : (t : Ty) -> (r : Region) -> Type where

  -- Q: when to introduce new regions?
  LetRegion : (r : Region -> Exp t loc s) -> Exp t loc s
  Let : {loc_in : _} -> Exp a loc_in s_in -> (Exp a loc_in s_in -> Exp t loc s) -> Exp t loc s

  -- primops
  PrintI64 : {loc_in : _} -> Exp I64 loc_in (SInt 8) -> Exp T0 loc (SInt 0)

  -- indirection
  MkInd : {loc_in, loc_ind : Loc r} -> Exp t loc_in s -> Exp (Ind t) loc_ind (SInt 8) -- within the same region
  MkIndLong : Exp t loc_in s -> Exp (Ind t) loc_ind (SInt 8)                             -- cross region

  -- to copy values cross region
  Copy : Exp t loc_in s -> Exp t loc s

  {-
  MkInd : {t : Ty} -> {loc_arg : _} ->
    let loc_ind = MkLE (LocInd loc_arg) in
    Exp t loc_arg -> Exp t loc_ind
  -}
  -- primitive values
  MkI64 : Int -> Exp I64 loc (SInt 8)

  -- value shapes, ADT can be modeled with these
  {-
    MkTup2 is the only place that introduces after relation between locations
    IDEA:
      - instead of LocAfter Ty we should use size which should be included in the Exp
      - the Exp size could be used to define the region size also
  -}
  MkTup2 : {a, b : Ty} -> {a_s, b_s : Size} -> {loc : Loc r} ->
    let locFst = loc in
    let locSnd = MkLE (LocAfter a_s locFst) in
    Exp a locFst a_s -> Exp b locSnd b_s -> Exp (Tup2 a b) loc (STup2 a_s b_s)

  MkLeft  : {a, b : Ty} -> {s : Size} -> {loc : Loc r} ->
    let locArg = MkLE (LocAfterTag loc) in
    Exp a locArg s -> Exp (Either a b) loc (STag s)

  MkRight : {a, b : Ty} -> {s : Size} -> {loc : Loc r} ->
    let locArg = MkLE (LocAfterTag loc) in
    Exp b locArg s -> Exp (Either a b) loc (STag s)

{-
  TODO:
    every data access needs to be tested to Ind and do the dereference for it
    INSIGHT: sharing poisons code, because requires interpretation
-}
  PrjFst : {a, c : Ty} -> {s_a, s_out : Size} -> {loc : Loc r} -> {loc_out : Loc r_out} -> Exp (Tup2 a b) loc (STup2 s_a _) ->
            let locFst = loc in
            (Exp a locFst s_a -> Exp c loc_out s_out) -> Exp c loc_out s_out

  PrjSnd : {a, b, c : Ty} -> {s_a, s_b, s_out : Size} -> {loc : Loc r} -> {loc_out : Loc r_out} -> Exp (Tup2 a b) loc (STup2 s_a s_b) ->
            let locFst = loc in
            let locSnd = MkLE (LocAfter s_a locFst) in
            (Exp b locSnd s_b -> Exp c loc_out s_out) -> Exp c loc_out s_out

{-
  IDEA:
    - model custsors and end witnesses
    - sizeof handling
      + can generate end-witness at compile time from Ty                        ; compile time = end-witness value
      + can genetrate end-witness producing runtime function at compile time    ; runtime      = end-witness function : value -> end-witness
-}

  CaseEither : {a, b, c : Ty} -> {s, s_l, s_r, s_out : Size} -> {loc : Loc r} -> {loc_out : Loc r_out} -> Exp (Either a b) loc (STag s) {-(SEither s_l s_r)-} ->
               let locArg = MkLE (LocAfterTag loc) in
               (Exp a locArg s_l -> Exp c loc_out s_out) -> (Exp b locArg s_r -> Exp c loc_out s_out) -> Exp c loc_out s_out
               -- PROBLEM/TODO: what if the output size differs?
               -- IDEAS: is the result size an Either Int Int?
{-

  -- location related
  LetLoc : {t : Ty} -> (1 _ : LocExp r) -> (1 _ : (1 _ : Loc t r) -> (1 _ : Loc t r) -> Exp a r_out) -> Exp a r_out -- Q: is this needed? use loc expressions for construction?
  --Ret : (1 end_witness : Loc a _) -> Exp b -> Exp b

  FunApp : Fun arg res -> Exp arg r_in -> Exp res r_out
-}

  -- internal
  Var : Int -> Exp a loc s

public export
data Fun : (arg : Ty) -> (res : Ty) -> Type where
  MkFunId : Int -> Fun arg res
{-
public export
data Program : Type where
  Main  : (main : Fun T0 res) -> Program
  MkDec : {arg : Ty} -> {res : Ty} -> (Fun arg res -> Program) -> Program
  MkDef : {arg : Ty} -> {res : Ty} -> Fun arg res -> (Exp arg r_in -> Exp res r_out) -> Program -> Program
-}
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
