module LoCal

public export
data Ty : Type where
  T0      : Ty
  STup2   : Ty -> Ty -> Ty   -- serial access only, fst then snd
  RTup2   : Ty -> Ty -> Ty   -- random access, O(1) access of snd
  Either  : Ty -> Ty -> Ty
  I64     : Ty
  Offset  : Ty -> Ty -- signed pointer offset value
  Ptr     : Ty -> Ty -- raw pointer ; no tag ; just the location data
  -- IDEA: Offset - region local ; Ptr - cross region
  -- recursive type support
  Box     : Lazy Ty -> Ty

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
data Loc : (r : Region) -> Type where
  LocStart    : (t : Ty) -> (r : Region) -> Loc r
  LocAfter    : (t : Ty) -> Loc r -> Loc r   -- Q: dynamically/runtime known? maybe a better name is RuntimeAfter ; A: NO!
                -- INSIGHT: if we would put Ty to this (instead of static size that would provide enough information to generate runtime function to calculate an endwitness
                -- IDEA: location is not the right thing that descibes the next location
                --        instead it would be the end witness of some value!
                --        location + size-witness = end-witness
          --    ^ this should be a value variable instead of Ty, that would solve the sizeof problem with either's left/right
          --    Q: what problem would it cause?
  LocAfterTag : String -> (t : Ty) -> Loc r -> Loc r         -- statically known ; used for jump over the tag

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

public export
data EndWitness = NoEW | EW

-- TODO: add linear arrows to guarantee that codegen happens for each expression exactly once

public export
data Exp : (t : Ty) -> (loc : Loc r) -> (ew : EndWitness) -> Type where

  -- Q: when to introduce new regions? A: for intermediate values
  LetRegion : (Region -> Exp t loc ew) -> Exp t loc ew
  LetRegionValue : {t : _} -> {a : _} -> (r : Region) -> Exp t (LocStart t r) EW -> (Exp t (LocStart t r) EW -> Exp a loc ew_out) -> Exp a loc ew_out

  -- primops
  PrintI64 : {r_in : _} -> {loc_in : Loc r_in} -> Exp I64 loc_in _ -> (Exp I64 loc_in EW -> Exp res loc ew) -> Exp res loc ew

  -- prints the buffer content at the location in hexadecimal ; requires full traversal effect on the argument, so the end-witness should be available
  PrintValue : {r_in : _} -> {t : _} -> {loc_in : Loc r_in} -> Exp t loc_in EW -> (Exp t loc_in EW -> Exp res loc ew) -> Exp res loc ew

  -- indirection, within same region
  MkOffset    : {loc_in : Loc r} -> {loc : Loc r} -> Exp t loc_in ew_in -> (Exp t loc_in ew_in -> Exp (Offset t) loc_ofs EW -> Exp res loc ew_out) -> Exp res loc ew_out

  DeRefOffset : {t : _} -> {r_in : _} -> {loc_in : Loc r_in} ->
                Exp (Offset t) loc_in ew_in -> (Exp (Offset t) loc_in EW -> (loc_val : Loc r_in) -> Exp t loc_val NoEW -> Exp res loc ew_out) -> Exp res loc ew_out

  -- indirection, cross region
  MkPtr    : {r_in : _} -> {loc_in : Loc r_in} -> Exp t loc_in ew_in -> (Exp t loc_in ew_in -> Exp (Ptr t) loc_ptr EW -> Exp res loc ew_out) -> Exp res loc ew_out

  DeRefPtr : {t : _} -> {r_in : _} -> {loc_in : Loc r_in} ->
             Exp (Ptr t) loc_in ew_in -> (Exp (Ptr t) loc_in EW -> (r_val : _) -> (loc_val : Loc r_val) -> Exp t loc_val NoEW -> Exp res loc ew_out) -> Exp res loc ew_out

  -- boxing
  MkBox : {x : _} -> {r : _} -> {loc : Loc r} -> Exp x loc ew -> (Exp x loc ew -> Exp (Box x) loc ew -> Exp a loc_out ew_out) -> Exp a loc_out ew_out
  UnBox : {x : _} -> {r : _} -> {loc : Loc r} -> Exp (Box x) loc ew -> (Exp (Box x) loc ew -> Exp x loc ew -> Exp a loc_out ew_out) -> Exp a loc_out ew_out

  -- to copy values cross region ; requires full traversal effect on the argument, so the end-witness should be available
  Copy : {r_in : _} -> {loc_in : Loc r_in} -> Exp t loc_in EW -> (Exp t loc_in EW -> Exp t loc EW -> Exp o loc_out ew_out) -> Exp o loc_out ew_out

  -- primitive values
  MkT0 : (Exp T0 loc EW -> Exp o loc_out ew_out) -> Exp o loc_out ew_out
  MkI64 : Int -> (Exp I64 loc EW -> Exp o loc_out ew_out) -> Exp o loc_out ew_out

  -- I64 primops
  AddI64 : {r_in : _} -> {r_in2 : _} -> {loc_in : Loc r_in} -> {loc_in2 : Loc r_in2} -> Exp I64 loc_in ew1 -> Exp I64 loc_in2 ew2 ->
           (Exp I64 loc_in EW -> Exp I64 loc_in2 EW -> Exp I64 loc EW -> Exp o loc_out ew_out) -> Exp o loc_out ew_out

  EqI64  : {r_in : _} -> {r_in2 : _} -> {loc_in : Loc r_in} -> {loc_in2 : Loc r_in2} -> Exp I64 loc_in ew1 -> Exp I64 loc_in2 ew2 ->
           (Exp I64 loc_in EW -> Exp I64 loc_in2 EW -> Exp (Either T0 T0) loc EW -> Exp o loc_out ew_out) -> Exp o loc_out ew_out

  -- value shapes, ADT can be modeled with these
  {-
    MkTup2 is the only place that introduces after relation between locations
    IDEA:
      - instead of LocAfter Ty we should use size which should be included in the Exp
      - the Exp size could be used to define the region size also
  -}

  MkSTup2 : {a, b, o : Ty} -> {loc : Loc r} -> {ew2, ew_out : _} -> {loc_out : _} ->
    let locFst = LocAfterTag "STup2" a loc in
    let locSnd = LocAfter b locFst in
    Exp a locFst EW -> Exp b locSnd ew2 -> (Exp a locFst EW -> Exp b locSnd ew2 -> Exp (STup2 a b) loc ew2 -> Exp o loc_out ew_out) -> Exp o loc_out ew_out

  MkRTup2 : {a, b, o : Ty} -> {loc : Loc r} -> {ew2, ew_out : _} -> {loc_out : _} ->
    let locFst = LocAfterTag "RTup2" a loc in
    let locSnd = LocAfter b locFst in
    Exp a locFst EW -> Exp b locSnd ew2 -> (Exp a locFst EW -> Exp b locSnd ew2 -> Exp (RTup2 a b) loc ew2 -> Exp o loc_out ew_out) -> Exp o loc_out ew_out

  MkLeft  : {a, b, o : Ty} -> {loc : Loc r} -> {ew, ew_out : _} -> {loc_out : _} ->
    let locArg = LocAfterTag "Left" a loc in
    Exp a locArg ew -> (Exp a locArg ew -> Exp (Either a b) loc ew -> Exp o loc_out ew_out) -> Exp o loc_out ew_out

  MkRight : {a, b, o : Ty} -> {loc : Loc r} -> {ew, ew_out : _} -> {loc_out : _} ->
    let locArg = LocAfterTag "Right" b loc in
    Exp b locArg ew -> (Exp b locArg ew -> Exp (Either a b) loc ew -> Exp o loc_out ew_out) -> Exp o loc_out ew_out

{-
  TODO:
    every data access needs to be tested to Ind and do the dereference for it
    INSIGHT: sharing poisons code, because requires interpretation
-}

  -- random access tup2
  PrjFst : {r_tup : _} -> {a, b, c : Ty} -> {loc_tup : Loc r_tup} -> {loc_out : Loc r_out} -> {ew, ew_out : _} -> Exp (RTup2 a b) loc_tup ew ->
            let locFst = LocAfterTag "RTup2" a loc_tup in
            (Exp (RTup2 a b) loc_tup ew -> Exp a locFst EW -> Exp c loc_out ew_out) -> Exp c loc_out ew_out

  PrjSnd : {r_tup : _} -> {a, b, c : Ty} -> {loc_tup : Loc r_tup} -> {loc_out : Loc r_out} -> {ew, ew_out : _} -> Exp (RTup2 a b) loc_tup ew ->
            let locFst = LocAfterTag "RTup2" a loc_tup in
            let locSnd = LocAfter b locFst in
            (Exp (RTup2 a b) loc_tup ew -> Exp b locSnd ew -> (Exp b locSnd EW -> Exp (RTup2 a b) loc_tup EW) -> Exp c loc_out ew_out) -> Exp c loc_out ew_out

  -- serial access tup2
  -- TODO: this is not the right model ; traverse effect checking is needed anyways
  CaseSTup2 : {r_tup : _} -> {a, b, c : Ty} -> {loc_tup : Loc r_tup} -> {loc_out : Loc r_out} -> {ew, ew1, ew_out : _} -> Exp (STup2 a b) loc_tup ew ->
              let locFst = LocAfterTag "STup2" a loc_tup in
              let locSnd = LocAfter b locFst in
              ( Exp a locFst ew1 ->
                (Exp a locFst EW -> Exp b locSnd NoEW) -> -- gives access for snd
                (Exp b locSnd EW -> Exp (STup2 a b) loc_tup EW) -> -- gives end-witness for STup2
                Exp c loc_out ew_out
              ) -> Exp c loc_out ew_out

{-
  IDEA:
    - model cursors and end witnesses
    - sizeof handling
      + can generate end-witness at compile time from Ty                        ; compile time = end-witness value
      + can genetrate end-witness producing runtime function at compile time    ; runtime      = end-witness function : value -> end-witness
-}

  CaseEither : {r : _} -> {a, b, c : Ty} -> {scrut_loc : Loc r} -> {loc_out : Loc r_out} -> {ew, ew_out : _} ->Exp (Either a b) scrut_loc ew ->
               let locL = LocAfterTag "Left" a scrut_loc in
               let locR = LocAfterTag "Right" b scrut_loc in
               (Exp a locL ew -> (Exp a locL EW -> Exp (Either a b) scrut_loc EW) -> Exp c loc_out ew_out) ->
               (Exp b locR ew -> (Exp b locR EW -> Exp (Either a b) scrut_loc EW) -> Exp c loc_out ew_out) ->
               Exp c loc_out ew_out
               -- PROBLEM/TODO: what if the output size differs?
               -- A: there is no problem because the location would be the same and the end witness will be different
               -- IDEAS: is the result size an Either Int Int?

  FunApp : {r_in : _} -> {r_out : _} -> {t_arg : _} -> {loc_in : Loc r_in} -> {loc_out : Loc r_out} -> {ew, ew2 : _} ->
           String ->
           (Exp t_arg loc_in ew -> (Exp t_arg loc_in ew2, Exp res loc_out EW)) ->
           Exp t_arg loc_in ew ->
           (Exp t_arg loc_in ew2 -> Exp res loc_out EW -> Exp res2 loc_out2 ew_out2) ->
           Exp res2 loc_out2 ew_out2

  -- internal
  Var : Exp a loc ew

public export
data Program : Type where
  Main  : {res : Ty} -> Exp res (LocStart res (MkRegion (-1))) EW -> Program

-- -------------------------------

{-
  TODO:
    SKIP - write buffer based interpreter
    done - write C backend
    done - write example for function call
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
    done - add Ind eliminator: DeRefPtr
    Q: when a pointer is a forward reference then is it possile that it will be dereferred before it is written?
    A: yes, which is wrong.
      Q: how to avoid this situation? is it possible to track effects in types?


  TODO:
    done - add STup2 and RTup2 and their eliminators ; this solves the traversal problem by making it expicit and correct by construction
    - add example for STup2
    - add static or dynamic assertion to MkInd to check that the referred value is written ; this guarantees the correctness of DeRefPtr
      every function argument must be fully written, every return value must be fully written
-}
