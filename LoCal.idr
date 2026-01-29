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

public export
getStaticSize : Ty -> Maybe Int
getStaticSize = \case
  T0    => Just 0
  I64   => pure 8
  Offset _ => pure 8
  Ptr _ => pure 8
  STup2 a b => do
    sa <- getStaticSize a
    sb <- getStaticSize b
    pure (sa + sb)
  RTup2 a b => do
    sa <- getStaticSize a
    sb <- getStaticSize b
    pure (sa + sb) -- HINT: no indirection is needed when fst static size is known
  Either a b => do
    sa <- getStaticSize a
    sb <- getStaticSize b
    if sa == sb -- special case, when the left and right size matches and statically known
      then Just (1 + sa)
      else Nothing
  Box _ => Nothing

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
          -- TODO: LocAfter should get a proof that an end-witness is existing for prev loc
          --        maybe EndWitness should be indexed with Loc then it would be the proof
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
data EndWitness = NoEW | EW -- TODO: index it with Loc

-- TODO: add linear arrows to guarantee that codegen happens for each expression exactly once

public export
data Exp : (t : Ty) -> (loc : Loc r) -> (ew : EndWitness) -> Type where

  -- Q: when to introduce new regions? A: for intermediate values
  -- OK
  LetRegion : (Region -> Exp t loc ew) -> Exp t loc ew
  -- OK
  LetRegionValue : {t_val : _} -> (r_val : Region) -> Exp t_val (LocStart t_val r_val) EW -> (Exp t_val (LocStart t_val r_val) EW -> Exp a loc ew) -> Exp a loc ew

  MkStaticEW : {t : _} -> {r_in : _} -> {loc_in : Loc r_in} -> {auto _ : Just size = getStaticSize t} ->
               Exp t loc_in _ ->
              (Exp t loc_in EW -> Exp res loc ew) ->
                                  Exp res loc ew

  -- primops
  PrintI64 : {r_in : _} -> {loc_in : Loc r_in} ->
              Exp I64 loc_in _ ->
             (Exp I64 loc_in EW -> Exp res loc ew) ->
                                   Exp res loc ew

  -- prints the buffer content at the location in hexadecimal ; requires full traversal effect on the argument, so the end-witness should be available
  PrintValue : {r_in : _} -> {t : _} -> {loc_in : Loc r_in} ->
                Exp t loc_in EW ->
               (Exp t loc_in EW -> Exp res loc ew) ->
                                   Exp res loc ew

  -- indirection, within same region
  MkOffset    : {t : _} -> {r_in : _} -> {loc_in : Loc r_in} -> {loc_ofs : Loc r_in} ->
                 Exp t loc_in ew_in ->
                (Exp t loc_in ew_in -> Exp (Offset t) loc_ofs EW -> Exp a loc ew) ->
                                                                    Exp a loc ew

  DeRefOffset : {t : _} -> {r_in : _} -> {loc_in : Loc r_in} ->
                 Exp (Offset t) loc_in ew_in ->
                (Exp (Offset t) loc_in EW -> (loc_val : Loc r_in) -> Exp t loc_val NoEW -> Exp a loc ew) ->
                                                                                           Exp a loc ew

  -- indirection, cross region
  MkPtr    : {t : _} -> {r_in : _} -> {r_ptr : _} -> {loc_in : Loc r_in} -> {loc_ptr : Loc r_ptr} ->
              Exp t loc_in ew_in ->
             (Exp t loc_in ew_in -> Exp (Ptr t) loc_ptr EW -> Exp a loc ew) ->
                                                              Exp a loc ew

  DeRefPtr : {t : _} -> {r_in : _} -> {loc_in : Loc r_in} ->
              Exp (Ptr t) loc_in ew_in ->
             (Exp (Ptr t) loc_in EW -> (r_val : _) -> (loc_val : Loc r_val) -> Exp t loc_val NoEW -> Exp a loc ew) ->
                                                                                                     Exp a loc ew

  -- boxing
  -- OK
  MkBox : {x : _} -> {r_box : _} -> {loc_box : Loc r_box} ->
          Exp x loc_box ew_box ->
         (Exp x loc_box ew_box -> Exp (Box x) loc_box ew_box -> Exp a loc ew) ->
                                                                Exp a loc ew
  -- OK
  UnBox : {x : _} -> {r_box : _} -> {loc_box : Loc r_box} ->
          Exp (Box x) loc_box ew_box ->
         (Exp (Box x) loc_box ew_box -> Exp x loc_box ew_box -> Exp a loc ew) ->
                                                                Exp a loc ew

  -- to copy values cross region ; requires full traversal effect on the argument, so the end-witness should be available
  Copy : {t : _} -> {r_in, r_copy : _} -> {loc_in : Loc r_in} -> {loc_copy : Loc r_copy} ->
         Exp t loc_in EW ->
        (Exp t loc_in EW -> Exp t loc_copy EW -> Exp a loc ew) ->
                                                 Exp a loc ew

  -- primitive values
  -- OK
  MkT0 : {r_val : _} -> {loc_val : Loc r_val} ->
        (Exp T0 loc_val EW -> Exp a loc ew) ->
                              Exp a loc ew
  -- OK
  MkI64 : Int -> {r_val : _} -> {loc_val : Loc r_val} ->
         (Exp I64 loc_val EW -> Exp a loc ew) ->
                                Exp a loc ew

  -- I64 primops
  AddI64 : {r_in, r_in2, r_res : _} -> {loc_in : Loc r_in} -> {loc_in2 : Loc r_in2} -> {loc_res : Loc r_res} ->
           Exp I64 loc_in ew1 -> Exp I64 loc_in2 ew2 ->
          (Exp I64 loc_in EW  -> Exp I64 loc_in2 EW  -> Exp I64 loc_res EW -> Exp a loc ew) ->
                                                                              Exp a loc ew

  EqI64  : {r_in, r_in2, r_res : _} -> {loc_in : Loc r_in} -> {loc_in2 : Loc r_in2} -> {loc_res : Loc r_res} ->
           Exp I64 loc_in ew1 -> Exp I64 loc_in2 ew2 ->
          (Exp I64 loc_in EW  -> Exp I64 loc_in2 EW  -> Exp (Either T0 T0) loc_res EW -> Exp a loc ew) ->
                                                                                         Exp a loc ew

  -- value shapes, ADT can be modeled with these
  {-
    MkTup2 is the only place that introduces after relation between locations
    IDEA:
      - instead of LocAfter Ty we should use size which should be included in the Exp
      - the Exp size could be used to define the region size also
  -}

  MkSTup2 : {a, b, o : Ty} -> {r_tup : _} -> {loc_tup : Loc r_tup} -> {ew, ewSnd : _} -> {loc : _} ->
    let locFst = LocAfterTag "STup2" a loc_tup in
    let locSnd = LocAfter b locFst in
    Exp a locFst EW -> Exp b locSnd ewSnd ->
   (Exp a locFst EW -> Exp b locSnd ewSnd -> Exp (STup2 a b) loc_tup ewSnd -> Exp o loc ew) ->
                                                                              Exp o loc ew

  -- OK
  MkRTup2 : {a, b, o : Ty} -> {r_tup : _} -> {loc_tup : Loc r_tup} -> {ew, ewSnd : _} -> {loc : _} ->
    let locFst = LocAfterTag "RTup2" a loc_tup in
    let locSnd = LocAfter b locFst in
    -- Q: should ew2 be EW instead?
    -- Q: can we create values without creating end-witness at all?
    Exp a locFst EW -> Exp b locSnd ewSnd ->
   (Exp a locFst EW -> Exp b locSnd ewSnd -> Exp (RTup2 a b) loc_tup ewSnd -> Exp o loc ew) ->
                                                                              Exp o loc ew

  -- OK
  MkLeft  : {a, b, o : Ty} -> {r_left : _} -> {loc_left : Loc r_left} -> {ew, ewArg : _} -> {loc : _} ->
    let locArg = LocAfterTag "Left" a loc_left in
    Exp a locArg ewArg ->
   (Exp a locArg ewArg -> Exp (Either a b) loc_left ewArg -> Exp o loc ew) ->
                                                             Exp o loc ew

  -- OK
  MkRight : {a, b, o : Ty} -> {r_right : _} -> {loc_right : Loc r_right} -> {ew, ewArg : _} -> {loc : _} ->
    let locArg = LocAfterTag "Right" b loc_right in
    Exp b locArg ewArg ->
   (Exp b locArg ewArg -> Exp (Either a b) loc_right ewArg -> Exp o loc ew) ->
                                                              Exp o loc ew

{-
  TODO:
    every data access needs to be tested to Ind and do the dereference for it
    INSIGHT: sharing poisons code, because requires interpretation
-}
  -- random access tup2
  PrjFst : {r_tup : _} -> {a, b, c : Ty} -> {loc_tup : Loc r_tup} -> {ew, ew_tup : _} -> {loc : _} ->
           Exp (RTup2 a b) loc_tup ew_tup ->
           let locFst = LocAfterTag "RTup2" a loc_tup in
          (Exp (RTup2 a b) loc_tup ew_tup -> Exp a locFst EW -> Exp c loc ew) ->
                                                                Exp c loc ew

  PrjSnd : {r_tup : _} -> {a, b, c : Ty} -> {loc_tup : Loc r_tup} -> {ew, ew_tup : _} -> {loc : _} ->
           Exp (RTup2 a b) loc_tup ew_tup ->
           let locFst = LocAfterTag "RTup2" a loc_tup in
           let locSnd = LocAfter b locFst in
           ( Exp (RTup2 a b) loc_tup ew_tup ->
             Exp b locSnd ew_tup ->
             (tup_ew_fun : Exp b locSnd EW -> Exp (RTup2 a b) loc_tup EW) ->
             Exp c loc ew
           ) -> Exp c loc ew

  -- serial access tup2
  CaseSTup2 : {r_tup : _} -> {a, b, c : Ty} -> {loc_tup : Loc r_tup} -> {ew_tup, ew : _} -> {loc : _} ->
              Exp (STup2 a b) loc_tup ew_tup ->
              let locFst = LocAfterTag "STup2" a loc_tup in
              let locSnd = LocAfter b locFst in
              ( Exp a locFst NoEW ->
                -- gives access for snd
                (snd_fun : Exp a locFst EW -> Exp b locSnd ew_tup) ->
                -- gives end-witness for STup2
                (tup_ew_fun : Exp b locSnd EW -> Exp (STup2 a b) loc_tup EW) ->
                Exp c loc ew
              ) -> Exp c loc ew

{-
  IDEA:
    - model cursors and end witnesses
    - sizeof handling
      + can generate end-witness at compile time from Ty                        ; compile time = end-witness value
      + can genetrate end-witness producing runtime function at compile time    ; runtime      = end-witness function : value -> end-witness
-}
  CaseEither : {r_scrut : _} -> {a, b, c : Ty} -> {loc_scrut : Loc r_scrut} -> {ew_scrut, ew : _} -> {loc : _} ->
               Exp (Either a b) loc_scrut ew_scrut ->
               let locL = LocAfterTag "Left" a loc_scrut in
               let locR = LocAfterTag "Right" b loc_scrut in
               (Exp a locL ew_scrut -> (either_ew_fun : Exp a locL EW -> Exp (Either a b) loc_scrut EW) -> Exp c loc ew) ->
               (Exp b locR ew_scrut -> (either_ew_fun : Exp b locR EW -> Exp (Either a b) loc_scrut EW) -> Exp c loc ew) ->
               Exp c loc ew
               -- PROBLEM/TODO: what if the output size differs?
               -- A: there is no problem because the location would be the same and the end witness will be different
               -- IDEAS: is the result size an Either Int Int?

  FunApp : {r_arg, r_res : _} -> {t_arg, res : _} -> {loc_arg : Loc r_arg} -> {loc_res : Loc r_res} ->
           String ->
           --(fun_def : Exp t_arg loc_arg ew_arg -> (Exp t_arg loc_arg ew_arg_out, Exp res loc_res EW)) ->
           (fun_def : Exp t_arg loc_arg ew_arg -> Exp res loc_res EW) ->
           Exp t_arg loc_arg ew_arg ->
           --(Exp t_arg loc_arg ew_arg_out -> Exp res loc_res EW -> Exp c loc ew) ->
           (Exp res loc_res EW -> Exp c loc ew) ->
           Exp c loc ew

  -- internal
  Var : {t_var : _} -> {r_var : _} -> {loc_var : Loc r_var} -> Exp t_var loc_var ew

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
