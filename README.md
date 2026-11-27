# LoCal

An improved version of Gibbon compiler's Location Calculus as Idris2 EDSL.

### Bevezeto

A LoCal Idris EDSL az adatreprezentaciok leirasara keszult, az alabbi cikk alapjan: https://gibbon-compiler.github.io/public/pldi19ext.pdf
Segitsegevel leirhato tetszoleges adatszerkezet, szamok, rekordok, algebrai adattipusok, rekurziv adatszerkezetek es indirekciok.
Tovabba leirhatok azok a fuggvenyek is amik ezeken az adatokon dolgoznak, ugy hogy a reprezentaciot garantaltan helyesen kezelik.

A LoCal nyelv tulajdonsagai tipusokkal vannak garantaltan betartatva. Minden aspektus az Exp adattipus egy egy indexekent van modellezve,
 a reprezentalt adat tipusa, a memoria layoutja (location), hogy mar irtuk vagy olvastuk e (eljutottunk e az adat vegere)

### A reprezentalt adat tipusa
A reprezentalt adat a kovetkezo elemekbol epulhet fel.
Az osszetett adatok primitivekbol epulnek fel, pl a Bool az Either T0, igy pont egy bitnyi informaciot tartalmaz.
A rekordok parokbol az algebrai adattipusok egymasba agyazott either es par elemekbol epulnek fel.
A rekurziv adattipusokat a Box primitivvel lehet kifejezni, az indirekciokat pedig Offset vagy Ptr tipussal.

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

### Memory layout
Az adat elhelyezkedeset a region es location hatarozza meg.
A region egy buffer amiben egybefuggo adat van, a location az adat elemeinek elhelyezkedeset mondja meg egymashoz viszonyitva.

```idris
data Region : Type where
  MkRegion    : Int -> Region
  MkArgRegion : String -> Nat -> Region

data Loc : (r : Region) -> Type where
  LocStart    : (t : Ty) -> (r : Region) -> Loc r
  LocAfter    : (t : Ty) -> Loc r -> Loc r
  LocAfterTag : String -> (t : Ty) -> Loc r -> Loc r -- statically known ; used for jump over the tag
```

### Adateleres, iras olvasas, adat eleje es vege
A nyelv immutable adatokat modellez, igy kulon van valasztva az iras es olvasas, azaz amikor erteket rakunk ossze es amikor erteket szedunk szet.
Ez lenyegeben azt jeleti hogy egy erteket addig nem olvashatunk amig nem raktuk ossze teljesen azaz amig nem irtuk ki az utolso elemet is.
Ezt modellezi az RWMode.

A masik fontos koncepcio az EndWitness. Az adatok a bufferben szigoruan egymas mellett (szomszedosan) helyezkednek el, es ha hozzaferest szeretnenk kapni egy elemre akkor
ahhoz kotelezoen fel kell valahogy dolgozni az elotte levo elemet. A feldolgozas itt az adat meretenek megismereset jelenti.
Az end witness azt jelenti hogy tudjuk az adott location levo adat meretet ezert mar van hozzaferesunk a rakovetkezo adatelemhez is.
Az iras/olvasas es end-witness tulajdonsag kozott van osszefugges, eszerint modelleztem ezeket az EDSL-ben.
Minden irott adat eseteben automatikusan eloall az end-witness ahogy beleirjuk az adatot a bufferbe es ezzel noveljuk a buffer pointert.
Mig az olvasas modban csak akkor kapjuk meg az end-witness-t az adatot mar feldolgoztuk.

```idris
data EndWitness = NoEW | EW -- TODO: index it with Loc
data RWMode = R EndWitness | W -- W always has end-witness
```

### LoCal kifejezesek, a lenyeg
Az expression tipus az EDSL lenyege. A tipus indexek kenyszeritik ki domain invariansait.
Az utolso index a `saved_ews` meg nincs teljesen befejezve, ez jelenleg nincs hasznalatban csak proof of concept szerepet szolgalt egy korabbi kiserletben.

```idris
data Exp : (t : Ty) -> (loc : Loc r) -> (rw : RWMode) -> (saved_ews : List Type) -> Type
```

Az Exp osszetevoi:
  + primitiv muveletek a primitiv tipusokhoz mint az I64
  + adatok konstrualasa: I64, parok, either
  + adatok szetszedese: parok, either
  + indirekcio keszitese, olvasasa
  + rekurziv tipusok ki es becsomagolasa
  + explicit sharing (copy)
  + regio (buffer) keszitese
  + fuggveny definicio es fuggvenyhivas
  + end-witness eloallitasa

### Nehany egyszeru pelda

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

### Forraskod szerkezete

 - LoCal.idr - Location Calculus definicioja
 - Dynamic.idr - C codegen backend for Location Calculus
 - HiCal.idr - high level EDSL, that serves as a simple frontend language for LoCal
 - HiCalToLoCal.idr - compiles to Location Calculus
 - Driver.idr - HiCal to LoCal compiler driver
 - Examples2.idr - outdated examples
 - Examples3.idr - simple LoCal examples
 - HiCalExamples.idr - HiCal examples
