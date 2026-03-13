module Test.KMP

open FStar.Seq
open CLRS.Ch32.KMP.Spec

(* Top-level function: count_matches_spec
   text = [1; 2; 1; 2; 1], pattern = [1; 2; 1]
   Pattern matches at positions 0 and 2 → count = 2 *)
let text : seq int = seq_of_list [1; 2; 1; 2; 1]
let pattern : seq int = seq_of_list [1; 2; 1]
let short_text : seq int = seq_of_list [1; 2]
let pat1 : seq int = seq_of_list [1]

(* === Completeness (Appendix B): count_matches_spec uniquely determines output === *)
let test_count_complete (y:nat) : Lemma
  (requires count_matches_spec text pattern 5 3 == y)
  (ensures y == 2) =
  assert_norm (count_matches_spec text pattern 5 3 == 2)

let test_no_match_complete (y:nat) : Lemma
  (requires count_matches_spec short_text pattern 2 3 == y)
  (ensures y == 0) =
  assert_norm (count_matches_spec short_text pattern 2 3 == 0)

let test_single_pat_complete (y:nat) : Lemma
  (requires count_matches_spec text pat1 5 1 == y)
  (ensures y == 3) =
  assert_norm (count_matches_spec text pat1 5 1 == 3)
