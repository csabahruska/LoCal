import LoCal

--MainWrite v = Main $ LetRegionValue MainRegion v id

test_bug06 : Program
test_bug06 = Main $ LetRegionValue MainRegion
  (let i1 = MkI64 12 in
  PrintValue (LetRegionValue (MkRegion 10003) (Copy i1) (\y => y))
    (\_ => i1)
  ) id

test_bug04 : Program
test_bug04 = Main $ LetRegionValue MainRegion
  (let i1 = MkI64 1 in
  CaseEither {c=Either I64 T0} (LetRegionValue (MkRegion 10003) (I64Cmp EQ i1 i1) (\y => y))
    (\_ => MkLeft i1)
    (\_ => MkRight MkT0)
  ) id

-- Q: what is the interpretation of this?
-- Q: how to resolve this?
test_bug05 : Program
test_bug05 = Main $ LetRegionValue MainRegion
  (let i1 = MkRight MkT0 in
  CaseEither {c=Either I64 T0} (LetRegionValue (MkRegion 10003) (Copy i1) (\y => y))
    (\_ => i1)
    (\_ => i1)
  ) id
