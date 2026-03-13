module Test.GCD

open CLRS.Ch31.GCD.Spec

(* Completeness: gcd_spec uniquely determines output for given inputs.
   gcd_impl postcondition: result == gcd_spec a b *)

let test_gcd_12_8 () : Lemma (gcd_spec 12 8 == 4) = assert_norm (gcd_spec 12 8 == 4)
let test_gcd_35_15 () : Lemma (gcd_spec 35 15 == 5) = assert_norm (gcd_spec 35 15 == 5)
let test_gcd_100_0 () : Lemma (gcd_spec 100 0 == 100) = assert_norm (gcd_spec 100 0 == 100)
let test_gcd_7_7 () : Lemma (gcd_spec 7 7 == 7) = assert_norm (gcd_spec 7 7 == 7)
