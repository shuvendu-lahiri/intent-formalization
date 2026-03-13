module Test.Heap

(* Completeness test for CLRS Heapsort specification.
   Tests that sorted + permutation uniquely determines output.
   NOTE: Direct Pulse impl call blocked by SZ.fits refinement issue
   on implicit args. Tests the specification instead. *)

open CLRS.Ch06.Heap.Spec

module Seq = FStar.Seq
module SP = FStar.Seq.Properties
module HS = CLRS.Ch06.Heap.Spec

#push-options "--z3rlimit 400 --fuel 8 --ifuel 4"

let completeness_sort3 (s: Seq.seq int)
  : Lemma
    (requires HS.sorted s /\ SP.permutation int (Seq.seq_of_list [3; 1; 2]) s)
    (ensures Seq.index s 0 == 1 /\ Seq.index s 1 == 2 /\ Seq.index s 2 == 3)
= SP.perm_len (Seq.seq_of_list [3; 1; 2]) s;
  assert_norm (SP.count 1 (Seq.seq_of_list [3; 1; 2]) == 1);
  assert_norm (SP.count 2 (Seq.seq_of_list [3; 1; 2]) == 1);
  assert_norm (SP.count 3 (Seq.seq_of_list [3; 1; 2]) == 1);
  assert_norm (SP.count 0 (Seq.seq_of_list [3; 1; 2]) == 0);
  assert_norm (SP.count 4 (Seq.seq_of_list [3; 1; 2]) == 0)

#pop-options
