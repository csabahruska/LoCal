module LoCal

public export
data Ty
  = T0
  | STup2 Ty Ty   -- serial access only, fst then snd
  | RTup2 Ty Ty   -- random access, O(1) access of snd
  | Either Ty Ty
  | I64
  | Ind Ty -- raw pointer ; no tag ; just the location data
  -- IDEA: Offset - region local ; Ptr - cross region
  -- recursive type support
  | DecTy String
  | DefTy Ty{-expect DecTy-} Ty Ty

public export
FromString Ty where fromString = DecTy

{-
  INSIGHT:
    control flow construct data
      if          -> + types
      basic block -> * types
    unconstrained recursion needs Box!!!
-}

{-
  REPRESENTATION:
    - no tag:   I64, STup2, RTup2
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

public export
data Loc : (r : Region) -> (t : Ty) -> Type where
  LocStart    : (t : Ty) -> (r : Region) -> Loc r t
  LocAfter    : (t : Ty) -> Loc r t_prev -> Loc r t   -- Q: dynamically/runtime known? maybe a better name is RuntimeAfter ; A: NO!
                -- INSIGHT: if we would put Ty to this (instead of static size that would provide enough information to generate runtime function to calculate an endwitness
                -- IDEA: location is not the right thing that descibes the next location
                --        instead it would be the end witness of some value!
                --        location + size-witness = end-witness
          --    ^ this should be a value variable instead of Ty, that would solve the sizeof problem with either's left/right
          --    Q: what problem would it cause?
  LocAfterTag : String -> (t : Ty) -> Loc r t_prev -> Loc r t         -- statically known ; used for jump over the tag

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
    locations are linear, values are not ; INSIGHT: locations are identifiers for values, so values are linear also
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

public export
data Exp : (t : Ty) -> (loc : Loc r t) -> Type where

  -- Q: when to introduce new regions?
  LetRegion : (Region -> Exp t loc) -> Exp t loc
  -- TODO: add AllocInNewRegion primitive

  -- Q: not needed? A: Right, let is not needed, use LetRegionValue instead
  --Let : {r_in : _} -> {t_in : _} -> {loc_in : Loc r_in t_in} -> Exp t_in loc_in -> (Exp t_in loc_in -> Exp t loc) -> Exp t loc

  -- Q: not needed? A: Not needed, use meta language let because every LoCal value istead, because every value resides only one location
  --LetSubValue : {loc_in : Loc r t_in} -> {loc : Loc r t} -> Exp t_in loc_in -> (Exp t_in loc_in -> Exp t loc) -> Exp t loc

  LetRegionValue : {t : _} -> {a : _} -> {loc : Loc r a} -> (r : Region) -> Exp t (LocStart t r) -> (Exp t (LocStart t r) -> Exp a loc) -> Exp a loc

  -- primops
  PrintI64 : {r_in : _} -> {loc_in : Loc r_in I64} -> Exp I64 loc_in -> Exp T0 loc

  -- indirection
  MkInd : {loc_in : Loc r t} -> {loc_ind : Loc r (Ind t)} -> Exp t loc_in -> Exp (Ind t) loc_ind -- within the same region
  DeRef : {loc_in : Loc r t} -> {loc_ind : Loc r (Ind t)} -> Exp (Ind t) loc_ind -> Exp t loc_in -- within the same region

  MkIndLong : {r_in : _} -> {loc_in : Loc r_in t} -> Exp t loc_in -> Exp (Ind t) loc_ind      -- cross region
  DeRefLong : {r_in : _} -> {loc_in : Loc r_in t} -> Exp (Ind t) loc_ind -> Exp t loc_in      -- cross region

  -- to copy values cross region
  Copy : {r_in : _} -> {loc_in : Loc r_in t} -> Exp t loc_in -> Exp t loc

  -- primitive values
  MkI64 : Int -> Exp I64 loc

  -- I64 primops
  AddI64 : {r_in : _} -> {r_in2 : _} -> {loc_in : Loc r_in I64} -> {loc_in2 : Loc r_in2 I64} -> Exp I64 loc_in -> Exp I64 loc_in2 -> Exp I64 loc
  EqI64  : {r_in : _} -> {r_in2 : _} -> {loc_in : Loc r_in I64} -> {loc_in2 : Loc r_in2 I64} -> Exp I64 loc_in -> Exp I64 loc_in2 -> Exp (Either T0 T0) loc

  -- value shapes, ADT can be modeled with these
  {-
    MkTup2 is the only place that introduces after relation between locations
    IDEA:
      - instead of LocAfter Ty we should use size which should be included in the Exp
      - the Exp size could be used to define the region size also
  -}

  MkSTup2 : {a, b : Ty} -> {loc : Loc r _} ->
    let locFst = LocAfterTag "STup2" a loc in
    let locSnd = LocAfter b locFst in
    Exp a locFst -> Exp b locSnd -> Exp (STup2 a b) loc

  MkRTup2 : {a, b : Ty} -> {loc : Loc r _} ->
    let locFst = LocAfterTag "RTup2" a loc in
    let locSnd = LocAfter b locFst in
    Exp a locFst -> Exp b locSnd -> Exp (RTup2 a b) loc

  MkLeft  : {a, b : Ty} -> {loc : Loc r _} ->
    let locArg = LocAfterTag "Left" a loc in
    Exp a locArg -> Exp (Either a b) loc

  MkRight : {a, b : Ty} -> {loc : Loc r _} ->
    let locArg = LocAfterTag "Right" b loc in
    Exp b locArg -> Exp (Either a b) loc

{-
  TODO:
    every data access needs to be tested to Ind and do the dereference for it
    INSIGHT: sharing poisons code, because requires interpretation
-}
  -- random access tup2
  PrjFst : {r : _} -> {a, b, c : Ty} -> {loc : Loc r _} -> {loc_out : Loc r_out _} -> Exp (RTup2 a b) loc ->
            let locFst = LocAfterTag "RTup2" a loc in
            (Exp a locFst -> Exp c loc_out) -> Exp c loc_out

  PrjSnd : {r : _} -> {a, b, c : Ty} -> {loc : Loc r _} -> {loc_out : Loc r_out _} -> Exp (RTup2 a b) loc ->
            let locFst = LocAfterTag "RTup2" a loc in
            let locSnd = LocAfter b locFst in
            (Exp b locSnd -> Exp c loc_out) -> Exp c loc_out

  -- serial access tup2
  -- TODO: this is not the right model ; traverse effect checking is needed anyways
  {-
  CaseSTup2 : {r : _} -> {a, b, c, d : Ty} -> {loc : Loc r _} -> {loc_out1 : Loc r_out1 _} -> {loc_out2 : Loc r_out2 _} -> Exp (STup2 a b) loc ->
              let locFst = LocAfterTag "STup2" a loc in
              let locSnd = LocAfter b locFst in
              (Exp a locFst -> Exp c loc_out1) -> (Exp b locSnd -> Exp c loc_out1 -> Exp d loc_out2) -> Exp d loc_out2
  -}
  CaseSTup2 : {r : _} -> {a, b, c : Ty} -> {loc : Loc r _} -> {loc_out : Loc r_out _} -> Exp (STup2 a b) loc ->
              let locFst = LocAfterTag "STup2" a loc in
              let locSnd = LocAfter b locFst in
              (Exp a locFst -> Exp b locSnd -> Exp c loc_out) -> Exp c loc_out
{-
  IDEA:
    - model custsors and end witnesses
    - sizeof handling
      + can generate end-witness at compile time from Ty                        ; compile time = end-witness value
      + can genetrate end-witness producing runtime function at compile time    ; runtime      = end-witness function : value -> end-witness
-}

  CaseEither : {r : _} -> {a, b, c : Ty} -> {scrut_loc : Loc r _} -> {loc_out : Loc r_out _} -> Exp (Either a b) scrut_loc ->
               let locL = LocAfterTag "Left" a scrut_loc in
               let locR = LocAfterTag "Right" b scrut_loc in
               (Exp a locL -> Exp c loc_out) -> (Exp b locR -> Exp c loc_out) -> Exp c loc_out
               -- PROBLEM/TODO: what if the output size differs?
               -- A: there is no problem because the location would be the same and the end witness will be different
               -- IDEAS: is the result size an Either Int Int?

  FunApp : {r_in : _} -> {r_out : _} -> {loc_in : Loc r_in arg} -> {loc_out : Loc r_out res} -> Fun arg res -> Exp arg loc_in -> Exp res loc_out
  -- TODO: check the typing rules for function application in LoCal type system
  FunApp2 : {r_in : _} -> {r_out : _} -> {loc_in : Loc r_in arg} -> {loc_out : Loc r_out res} ->
            String ->
            (Exp arg loc_in -> Exp res loc_out) -> Exp arg loc_in -> Exp res loc_out

  -- internal
  Var : {-{a : _} -> {r : _} -> {loc : Loc r a} ->-} Exp a loc

public export
data Fun : (arg : Ty) -> (res : Ty) -> Type where
  MkFunId : Int -> Fun arg res

public export
data Program : Type where
  Main2  : (Exp T0 (LocStart T0 (MkRegion (-1))) -> Exp res (LocStart res (MkRegion (-2)))) -> Program
  Main3  : {res : Ty} -> Exp res (LocStart res (MkRegion (-4))) -> Program
  Main  : (main : Fun T0 res) -> Program
  MkDec : {- {arg : Ty} -> {res : Ty} -> -} (Fun arg res -> Program) -> Program
  MkDef : {arg : Ty} -> {res : Ty}{- -> {r_in : _} -> {r_out : _}-} -> {loc_in : Loc r_in arg} -> {loc_out : Loc r_out res}
          -> Fun arg res -> (Exp arg loc_in -> Exp res loc_out) -> Program -> Program

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
  TODO:
    - add Ind eliminator: DeRef
    Q: when a pointer is a forward reference then is it possile that it will be dereferred before it is written?
    A: yes, which is wrong.
      Q: how to avoid this situation? is it possible to track effects in types?


  TODO:
    done - add STup2 and RTup2 and their eliminators ; this solves the traversal problem by making it expicit and correct by construction
    - add example for STup2
    - add static or dynamic assertion to MkInd to check that the referred value is written ; this guarantees the correctness of DeRef
      every function argument must be fully written, every return value must be fully written
-}
