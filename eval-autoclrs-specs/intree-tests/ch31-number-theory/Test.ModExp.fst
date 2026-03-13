module Test.ModExp

open CLRS.Ch31.ModExp.Spec

(* Completeness: mod_exp_spec uniquely determines output.
   mod_exp_impl postcondition: result == mod_exp_spec b e m *)

let test_modexp_2_10_1000 () : Lemma (mod_exp_spec 2 10 1000 == 24) =
  assert_norm (mod_exp_spec 2 10 1000 == 24)
let test_modexp_3_5_7 () : Lemma (mod_exp_spec 3 5 7 == 5) =
  assert_norm (mod_exp_spec 3 5 7 == 5)
let test_modexp_5_3_13 () : Lemma (mod_exp_spec 5 3 13 == 8) =
  assert_norm (mod_exp_spec 5 3 13 == 8)
