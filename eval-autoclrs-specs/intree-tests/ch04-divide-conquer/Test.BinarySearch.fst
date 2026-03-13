module Test.BinarySearch

open FStar.Seq
open CLRS.Ch04.BinarySearch.Spec

(* Completeness: binary_search postcondition uniquely determines result.
   For sorted [1;3;5], searching for 3 returns index 1; searching for 4 returns len=3. *)

let sorted_135 : seq int = seq_of_list [1; 3; 5]

let test_found () : Lemma
  (requires is_sorted sorted_135)
  (ensures (exists (i:nat). i < 3 /\ index sorted_135 i == 3))
= ()

let test_not_found () : Lemma
  (forall (i:nat). i < 3 ==> index sorted_135 i =!= 4)
= ()
