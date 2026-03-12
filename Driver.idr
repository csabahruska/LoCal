module Driver

import HiCal as Hi
import HiCalToLoCal as Hi
import LoCal as Lo
import Dynamic as Lo
import System
import System.File
import HiCalExamples

partial test0, test1, test2, test3, test4, test12 : Lo.Program
test0 = Hi.compileProgram $ Main MkT0
test1 = Hi.compileProgram $ Main $ Let MkT0 $ \t0 => MkPair t0 t0
test2 = Hi.compileProgram $ Main $ PrintI64 (MkI64 1) $ \() => MkT0
test3 = Hi.compileProgram $ Main $ Let (MkI64 1) $ \i => PrintI64 i $ \() => i
test4 = Hi.compileProgram $ Main $ Let (MkI64 1) $ \i => Let (MkPair (I64Op2 Plus i i) i) $ \j => PrintValue j $ \() => j
test12 = Hi.compileProgram test_12
test12_bug = Hi.compileProgram test_12_bug
test13 = Hi.compileProgram test_13
test13_unroll = Hi.compileProgram test_13_unroll
test14_bug = Hi.compileProgram test_14_bug
test14_bug2 = Hi.compileProgram test_14_bug2
test14_bug_full = Hi.compileProgram test_14_bug_full
test14_bug_full_unroll = Hi.compileProgram test_14_bug_full_unroll
test_bug3_lo = Hi.compileProgram test_bug3
bug01_lo = Hi.compileProgram bug01
test_let01_lo = Hi.compileProgram test_let01
test_let02_lo = Hi.compileProgram test_let02

{-
  Main {res = Pair I64 I64}
    (MkPair {{r:2038} = MkRegion -1} {a = I64} {b = I64} {loc = LocStart (Pair I64 I64) (MkRegion -1)}
      (I64Op2 {{r:2529} = MkRegion -1} {{r:2528} = MkRegion -1} {{r:2527} = MkRegion -1}
        {loc = LocAfterTag {r = MkRegion -1} "Pair" I64 (LocStart (Pair I64 I64) (MkRegion -1))}
        Plus {ew1 = EW} {ew2 = EW}
        {loc_in1 = LocAfter {r = MkRegion -1} I64 (LocAfterTag {r = MkRegion -1} "Pair" I64 (LocStart (Pair I64 I64) (MkRegion -1)))}
        {loc_in2 = LocAfter {r = MkRegion -1} I64 (LocAfterTag {r = MkRegion -1} "Pair" I64 (LocStart (Pair I64 I64) (MkRegion -1)))}
        (MkI64 {{r:2485} = MkRegion -1} {loc = LocAfter {r = MkRegion -1} I64 (LocAfterTag {r = MkRegion -1} "Pair" I64 (LocStart (Pair I64 I64) (MkRegion -1)))} 1)
        (MkI64 {{r:2485} = MkRegion -1} {loc = LocAfter {r = MkRegion -1} I64 (LocAfterTag {r = MkRegion -1} "Pair" I64 (LocStart (Pair I64 I64) (MkRegion -1)))} 1))
        (MkI64 {{r:2485} = MkRegion -1} {loc = LocAfter {r = MkRegion -1} I64 (LocAfterTag {r = MkRegion -1} "Pair" I64 (LocStart (Pair I64 I64) (MkRegion -1)))} 1))
-}
partial main : IO ()
main = do
  putStrLn "starting.."
  _ <- Lo.compileProgram "hi_bug01" bug01_lo -- TODO: fix bug: some FunAppDef-s are lost and turned to FunApp???
  _ <- Lo.compileProgram "hi_test14_bug_full_unroll" test14_bug_full_unroll -- TODO: fix bug: some FunAppDef-s are lost and turned to FunApp???

  _ <- Lo.compileProgram "hi_test_bug3" test_bug3_lo
  _ <- Lo.compileProgram "hi_test14_bug_full" test14_bug_full -- fixed

  _ <- Lo.compileProgram "hi_test_let01" test_let01_lo
  _ <- Lo.compileProgram "hi_test_let02" test_let02_lo

  _ <- Lo.compileProgram "hi_test01" test1
  _ <- Lo.compileProgram "hi_test03" test3
  _ <- Lo.compileProgram "hi_test04" test4

  _ <- Lo.compileProgram "hi_test00" test0
  _ <- Lo.compileProgram "hi_test02" test2

  _ <- Lo.compileProgram "hi_test12_bug" test12_bug -- fixed
  _ <- Lo.compileProgram "hi_test12" test12
  _ <- Lo.compileProgram "hi_test13" test13

  _ <- Lo.compileProgram "hi_test13_unroll_bug" test13_unroll -- fixed
  _ <- Lo.compileProgram "hi_test14_bug" test14_bug -- fixed
  _ <- Lo.compileProgram "hi_test14_bug2" test14_bug2 -- fixed

  pure ()
