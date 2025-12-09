foo : Int -> Int -> Bool
foo n m with (n) | (m)
  _ | 2 | 3 = True
  _ | _ | _ = False
