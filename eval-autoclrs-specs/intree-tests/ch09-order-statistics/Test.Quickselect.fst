module Test.Quickselect

module Seq = FStar.Seq
open CLRS.Ch09.PartialSelectionSort.Spec

(* Top-level function: select_spec
   Quickselect Impl ensures result == select_spec s k.
   select_spec(s, k) returns the k-th smallest element of s. *)

let s1 : Seq.seq int = Seq.seq_of_list [3; 1; 4; 1; 5]

(* === Completeness (Appendix B): select_spec uniquely determines output === *)
#push-options "--z3rlimit 100"
let test_select_0_complete (y:int) : Lemma
  (requires select_spec s1 0 == y)
  (ensures y == 1) =
  assert_norm (select_spec s1 0 == 1)

let test_select_2_complete (y:int) : Lemma
  (requires select_spec s1 2 == y)
  (ensures y == 3) =
  assert_norm (select_spec s1 2 == 3)

let test_select_4_complete (y:int) : Lemma
  (requires select_spec s1 4 == y)
  (ensures y == 5) =
  assert_norm (select_spec s1 4 == 5)
#pop-options
