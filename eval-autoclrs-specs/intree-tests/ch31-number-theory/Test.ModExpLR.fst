module Test.ModExpLR

open CLRS.Ch31.ModExp.Spec

(* Completeness: mod_exp_lr_impl uses same spec as mod_exp_impl.
   Postcondition: result == mod_exp_spec b e m *)

let test_modexplr_2_10_1000 () : Lemma (mod_exp_spec 2 10 1000 == 24) =
  assert_norm (mod_exp_spec 2 10 1000 == 24)
let test_modexplr_3_5_7 () : Lemma (mod_exp_spec 3 5 7 == 5) =
  assert_norm (mod_exp_spec 3 5 7 == 5)
