module Test.MergeSort

open FStar.Seq
open FStar.Seq.Properties
open CLRS.Common.SortSpec
open Pulse.Lib.BoundedIntegers

#push-options "--z3rlimit 400 --fuel 8 --ifuel 4"

let std_sort3 (s: seq int)
  : Lemma
    (requires (forall (i j:nat). Prims.op_LessThanOrEqual i j /\
                                 Prims.op_LessThan j (length s) ==>
                                 Prims.op_LessThanOrEqual (index s i) (index s j)) /\
              FStar.Seq.Properties.permutation int (seq_of_list [3; 1; 2]) s)
    (ensures index s 0 == 1 /\ index s 1 == 2 /\ index s 2 == 3)
= perm_len (seq_of_list [3; 1; 2]) s;
  assert_norm (count 1 (seq_of_list [3; 1; 2]) == 1);
  assert_norm (count 2 (seq_of_list [3; 1; 2]) == 1);
  assert_norm (count 3 (seq_of_list [3; 1; 2]) == 1);
  assert_norm (count 0 (seq_of_list [3; 1; 2]) == 0);
  assert_norm (count 4 (seq_of_list [3; 1; 2]) == 0)

let completeness_sort3 (s: seq int)
  : Lemma
    (requires sorted s /\ permutation (seq_of_list [3; 1; 2]) s)
    (ensures index s 0 == 1 /\ index s 1 == 2 /\ index s 2 == 3)
= assert (forall (i j:nat). (i <= j) == Prims.op_LessThanOrEqual i j);
  assert (forall (x y:int). (x <= y) == Prims.op_LessThanOrEqual x y);
  reveal_opaque (`%permutation) (permutation (seq_of_list [3; 1; 2]) s);
  std_sort3 s

#pop-options
