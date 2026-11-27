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

```idris
data Exp : (t : Ty) -> (loc : Loc r) -> (rw : RWMode) -> (saved_ews : List Type) -> Type
```

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