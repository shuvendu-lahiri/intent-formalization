module Test.ExtendedGCD

open CLRS.Ch31.ExtendedGCD.Spec

let test1 () : Lemma (extended_gcd 30 18 == (| 6, -1, 2 |)) =
  assert_norm (extended_gcd 30 18 == (| 6, -1, 2 |))
