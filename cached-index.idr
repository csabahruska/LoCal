isZero : Int -> Bool
isZero 0 = True
isZero _ = False

data K : Type where
  K2 : (a : Int) -> {default (_ ** Refl) c : (b ** (b = isZero a))} -> K

v : Int -> K
v i = K2 i

s : Int -> String
s i = case v i of
  K2 a {c} => show c.fst
