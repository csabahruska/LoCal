module Driver

import HiCal as Hi
import HiCalToLoCal as Hi
import LoCal as Lo
import Dynamic as Lo
import System
import System.File

test0, test1, test2, test3, test4 : Hi.Program
test0 = Main MkT0
test1 = Main $ Let MkT0 $ \t0 => MkPair t0 t0
test2 = Main $ PrintI64 (MkI64 1) $ \() => MkT0
test3 = Main $ Let (MkI64 1) $ \i => PrintI64 i $ \() => i
test4 = Main $ Let (MkI64 1) $ \i => MkPair (I64Op2 Plus i i) i
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
  _ <- enableRawMode
  print "starting..\n"
  --_ <- Lo.compileProgram "hi_test01-dummy" $ Main MkT0
  p2 <- Hi.compileProgram test0
  print "finished\n"
  --_ <- Lo.compileProgram "hi_test00" p2
  --_ <- Lo.compileProgram "hi_test00" test0
  --_ <- Lo.compileProgram "hi_test01" test1
  --_ <- Lo.compileProgram "hi_test02" test2
  --_ <- Lo.compileProgram "hi_test03" test3
  --_ <- Lo.compileProgram "hi_test04" test4
  pure ()
