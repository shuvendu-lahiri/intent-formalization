module Test.RabinKarp

open FStar.Mul
module Seq = FStar.Seq
open CLRS.Ch32.RabinKarp.Spec

(* Top-level function: matches_at_dec (decidable pattern match at position)
   text = [1; 2; 1; 2; 1], pattern = [1; 2; 1]
   Pattern matches at positions 0 and 2 *)
let text : Seq.seq nat = Seq.seq_of_list [1; 2; 1; 2; 1]
let pat : Seq.seq nat = Seq.seq_of_list [1; 2; 1]

(* === Completeness (Appendix B): matches_at_dec uniquely determines output === *)
let test_match_0_complete (y:bool) : Lemma
  (requires matches_at_dec text pat 0 == y)
  (ensures y == true) =
  assert_norm (matches_at_dec text pat 0 == true)

let test_no_match_1_complete (y:bool) : Lemma
  (requires matches_at_dec text pat 1 == y)
  (ensures y == false) =
  assert_norm (matches_at_dec text pat 1 == false)

let test_match_2_complete (y:bool) : Lemma
  (requires matches_at_dec text pat 2 == y)
  (ensures y == true) =
  assert_norm (matches_at_dec text pat 2 == true)

(* hash is the core Rabin-Karp computation *)
let seq123 : Seq.seq nat = Seq.seq_of_list [1; 2; 3]

let test_hash_complete (y:int) : Lemma
  (requires hash seq123 10 7 0 3 == y)
  (ensures y == 4) =
  assert_norm (hash seq123 10 7 0 3 == 4)
