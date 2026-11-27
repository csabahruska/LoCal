# LoCal

An improved version of Gibbon compiler's Location Calculus as an Idris2 EDSL.

### Overview

The LoCal Idris EDSL describes data representations based on this paper: https://gibbon-compiler.github.io/public/pldi19ext.pdf.
It can represent arbitrary data structures, numbers, records, algebraic data types, recursive structures, and indirections,
as well as functions operating on them while guaranteeing valid representation handling.

Language properties are enforced via types. Every aspect is modeled as a type index on `Exp`: the represented data type, its memory layout (`loc`), and whether it has been written or read (i.e., reached the end of the data).

### Represented Data Types

Composite types are built from primitives, for example, `Bool` can be `Either T0` (holding a single bit of information).
Records come from pairs, algebraic data types from nested `Either` and pair types, recursive types from `Box`, and indirections from `Offset` or `Ptr`.

```idris
data Ty : Type where
  T0      : Ty  -- zero sized tuple
  Pair    : Ty -> Ty -> Ty   -- serial access only, fst then snd
  Either  : Ty -> Ty -> Ty
  I64     : Ty
  -- IDEA: Offset - region local ; Ptr - cross region
  Offset  : Ty -> Ty -- signed pointer offset value
  Ptr     : Ty -> Ty -- raw pointer ; no tag ; just the location data
  -- recursive type support
  Box     : String -> Lazy Ty -> Ty
```

### Memory Layout

Placement is determined by `Region` and `Loc`. A `Region` is a contiguous data buffer, while a `Loc` specifies the relative positions of elements within it.

```idris
data Region : Type where
  MkRegion    : Int -> Region
  MkArgRegion : String -> Nat -> Region

data Loc : (r : Region) -> Type where
  LocStart    : (t : Ty) -> (r : Region) -> Loc r
  LocAfter    : (t : Ty) -> Loc r -> Loc r
  LocAfterTag : String -> (t : Ty) -> Loc r -> Loc r -- statically known ; used for jump over the tag
```

### Data Access: Read/Write and Start/End

Because the language models immutable data, writing (constructing values) and reading (destructing values) are separated.
A value cannot be read until it is fully constructed (that is, until its last element is written) which `RWMode` models.

`EndWitness` is another key concept. Elements sit contiguously in the buffer, and accessing a subsequent element requires processing the preceding one, meaning learning its size.
Having an end witness means the size at `loc` is known, granting access to the next element.
In write mode (`W`), an end witness is produced automatically as data is written and the buffer pointer advances,
whereas in read mode (`R`), it is obtained only after the data has been processed.

```idris
data EndWitness = NoEW | EW -- TODO: index it with Loc
data RWMode = R EndWitness | W -- W always has end-witness
```

### LoCal Expressions

`Exp` is the core of the EDSL, using type indices to enforce domain invariants. The final `saved_ews` index is incomplete and currently unused, remaining only as a proof of concept from an earlier experiment.

`Exp` supports:
* Primitive operations on primitive types (such as `I64`)
* Constructing data (`I64`, pairs, `Either`)
* Destructing data (pairs, `Either`)
* Creating and reading indirections
* Boxing and unboxing recursive types
* Explicit sharing (`Copy`)
* Creating regions (buffers)
* Function definitions and calls
* Producing end witnesses

```idris
data Exp : (t : Ty) -> (loc : Loc r) -> (rw : RWMode) -> (saved_ews : List Type) -> Type

  -- Q: when to introduce new regions? A: for intermediate values
  LetRegion : (Region -> Exp t loc rw ews) -> Exp t loc rw ews -- TODO: remove this op, or add an iterpretation layer that evaluates it
  LetRegionValue : {t_val : _} -> (r_val : Region) -> Exp t_val (LocStart t_val r_val) W [] ->
                   (Exp t_val (LocStart t_val r_val) REW [] -> Exp a loc rw ews) -> Exp a loc rw ews

  -- to copy values cross region ; requires full traversal effect on the argument, so the end-witness should be available
  Copy : {r_in : _} -> {loc_in : Loc r_in} -> Exp t loc_in REW [] -> Exp t loc W []

  -- boxing
  MkBox : {t : Ty} -> {n : String} -> Exp t loc rw [] -> Exp (Box n $ Delay t) loc rw []
  UnBox : {t : Ty} -> {n : String} -> Exp (Box n $ Delay t) loc rw [] -> Exp t loc rw []

  -- value shapes, ADT can be modeled with these

  -- MkPair is the only origin of the 'after' relation between locations
  MkPair : {a, b : Ty} -> {loc : _} ->
    let locFst = LocAfterTag "Pair" a loc in
    let locSnd = LocAfter b locFst in
    Exp a locFst W [] -> Exp b locSnd W [] -> Exp (Pair a b) loc W []

  MkLeft  : {a, b : Ty} -> {loc : _} ->
    let locArg = LocAfterTag "Left" a loc in
    Exp a locArg W [] -> Exp (Either a b) loc W []

  MkRight : {a, b : Ty} -> {loc : _} ->
    let locArg = LocAfterTag "Right" b loc in
    Exp b locArg W [] -> Exp (Either a b) loc W []

  -- serial access pair
  GetFst : {r_tup : _} -> {a, b : Ty} -> {loc_tup : Loc r_tup} -> {ew_tup : _} ->
              Exp (Pair a b) loc_tup (R ew_tup) [] ->
              let locFst = LocAfterTag "Pair" a loc_tup in
              Exp a locFst RNoEW []

  GetSnd : {r_tup : _} -> {a, b : Ty} -> {loc_tup : Loc r_tup} -> {ew_tup: _} ->
           Exp (Pair a b) loc_tup (R ew_tup) [] ->
           let locFst = LocAfterTag "Pair" a loc_tup in
           let locSnd = LocAfter b locFst in
           Exp a locFst REW [] -> Exp b locSnd (R ew_tup) []

  CaseEither : {rw : _} -> {r_scrut : _} -> {a, b, c : Ty} -> {loc_scrut : Loc r_scrut} -> {ew_scrut : _} -> {loc : _} -> {ews : _} ->
               Exp (Either a b) loc_scrut (R ew_scrut) [] ->
               let locL = LocAfterTag "Left"  a loc_scrut in
               let locR = LocAfterTag "Right" b loc_scrut in
               (Exp a locL (R ew_scrut) [] -> Exp c loc rw ews) ->
               (Exp b locR (R ew_scrut) [] -> Exp c loc rw ews) ->
               Exp c loc rw ews

  -- IDEA: store end-witnesses as an index in Exp
  AddEW : Exp t1 loc1 REW [] -> Exp t2 loc2 rw2 ews2 -> Exp t2 loc2 rw2 (Exp t1 loc1 REW [] :: ews2)
  GetEWS : Exp _ _ _ fun_ews -> (Arg fun_ews -> Exp c loc rw ews) -> Exp c loc rw ews

  FunAppDef : {fun_ews : _} -> {res : _} -> {r_res : _} -> {loc_res : Loc r_res} ->
           (fun : String) ->
           (fun_def  : Arg {fun} {n} exps_in  -> Exp res loc_res W fun_ews) ->
           (fun_args : Arg {fun} {n} exps_in) -> Exp res loc_res W fun_ews

  FunApp : {fun_ews : _} -> {res : _} -> {r_res : _} -> {loc_res : Loc r_res} ->
           String ->
           (fun_args : Arg exps_in) -> Exp res loc_res W fun_ews

  -- indirection, within same region
  MkOffset    : {r : _} -> {loc, loc_in : Loc r} -> Exp x loc_in W [] -> Exp (Offset x) loc W []
  DeRefOffset : {x : _} -> {ew_in : _} -> {r_in : _} -> {loc_in : Loc r_in} ->
                Exp (Offset x) loc_in (R ew_in) [] -> ({r_val : _} -> Exp x (LocStart x r_val) RNoEW [] -> Exp a loc rw ews) -> Exp a loc rw ews

  -- indirection, cross region
  MkPtr    : {rw_in : _} -> {r_in : _} -> {loc_in : Loc r_in} -> Exp x loc_in rw_in [] -> Exp (Ptr x) loc W []
  DeRefPtr : {x : _} -> {ew_in : _} -> {r_in : _} -> {loc_in : Loc r_in} ->
             Exp (Ptr x) loc_in (R ew_in) [] -> ({r_val : _} -> Exp x (LocStart x r_val) RNoEW [] -> Exp a loc rw ews) -> Exp a loc rw ews

  -- primitive values
  MkT0  : Exp T0 loc W []
  MkI64 : Int -> Exp I64 loc W []

  -- I64 primops
  I64Op2  : IntOp2 -> {ew1, ew2 : _} -> {r_in1, r_in2 : _} -> {loc_in1 : Loc r_in1} -> {loc_in2 : Loc r_in2} -> Exp I64 loc_in1 (R ew1) [] -> Exp I64 loc_in2 (R ew2) [] -> Exp I64 loc W []
  I64Cmp  : CmpOp  -> {ew1, ew2 : _} -> {r_in1, r_in2 : _} -> {loc_in1 : Loc r_in1} -> {loc_in2 : Loc r_in2} -> Exp I64 loc_in1 (R ew1) [] -> Exp I64 loc_in2 (R ew2) [] -> Exp (Either T0 T0) loc W []

  -- IO primops
  PrintI64 : {ew_in : _} -> {r_in : _} -> {loc_in : Loc r_in} -> Exp I64 loc_in (R ew_in) [] -> (() -> Exp t loc rw ews) -> Exp t loc rw ews

  -- prints the buffer content at the location in hexadecimal
  PrintValue : {t_in : _} -> {r_in : _} -> {loc_in : Loc r_in} -> Exp t_in loc_in REW [] -> (() -> Exp t loc rw ews) -> Exp t loc rw ews

  -- end-witnesses
  StaticEW : {ew_in : _} -> {auto prf : True = isStaticSize t} -> Exp t loc (R ew_in) [] -> Exp t loc REW []

  GenEW : {t : _} -> {r : _} -> {loc : Loc r} -> {ew_in : _} -> Exp t loc (R ew_in) [] -> Exp t loc REW []

  PairEW : {r_tup : _} -> {a, b : Ty} -> {loc_tup : Loc r_tup} -> {ew_tup : _} ->
           Exp (Pair a b) loc_tup (R ew_tup) [] ->
           let locFst = LocAfterTag "Pair" a loc_tup in
           let locSnd = LocAfter b locFst in
           Exp b locSnd REW [] -> Exp (Pair a b) loc_tup REW []

  LeftEW : {ew_scrut : _} -> {r_scrut : _} -> {a, b : Ty} -> {loc_scrut : Loc r_scrut} ->
           Exp (Either a b) loc_scrut (R ew_scrut) [] ->
           let locL = LocAfterTag "Left" a loc_scrut in
           Exp a locL REW [] -> Exp (Either a b) loc_scrut REW []

  RightEW : {ew_scrut : _} -> {r_scrut : _} -> {a, b : Ty} -> {loc_scrut : Loc r_scrut} ->
            Exp (Either a b) loc_scrut (R ew_scrut) [] ->
            let locR = LocAfterTag "Right" b loc_scrut in
            Exp b locR REW [] -> Exp (Either a b) loc_scrut REW []
```

### Simple Examples

```idris
i64 : {loc : _} -> Exp I64 loc W []
i64 = MkI64 1

sample_tup2_01 : {r : _} -> {loc : Loc r} -> Exp (Pair I64 I64) loc W []
sample_tup2_01 =
  -- create i64 values
  let i1 = MkI64 101 in
  let i2 = MkI64 201 in
  MkPair i1 i2

sample_left_01 : {r : _} -> {loc : Loc r} -> Exp (Either (Pair I64 I64) I64) loc W []
sample_left_01 = MkLeft sample_tup2_01

test3 : Program
test3 = Main $ LetRegionValue MainRegion (MkI64 1) $ \i => PrintI64 i $ \() => i

test4 : Program
test4 = Main $
  LetRegion $ \r => LetRegionValue r (MkI64 1) $ \i =>
  LetRegionValue MainRegion (MkPair (I64Op2 Plus i i) (Copy i)) id
```

### Source Code Structure

* `LoCal.idr` — Location Calculus definition
* `Dynamic.idr` — C codegen backend for Location Calculus
* `HiCal.idr` — High-level EDSL serving as a simple frontend language for LoCal
* `HiCalToLoCal.idr` — Compiles `HiCal` to Location Calculus
* `Driver.idr` — `HiCal` to LoCal compiler driver
* `Examples2.idr` — Outdated examples
* `Examples3.idr` — Simple LoCal examples
* `HiCalExamples.idr` — `HiCal` examples