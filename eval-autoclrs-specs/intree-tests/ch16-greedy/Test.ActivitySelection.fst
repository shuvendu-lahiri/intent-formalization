module Test.ActivitySelection

open FStar.List.Tot
module Seq = FStar.Seq
open CLRS.Ch16.ActivitySelection.Spec

(* Top-level function: max_compatible_count (GTot, not normalizable)
   Activities: start=[1;3;4;6], finish=[3;5;6;9]
   Max compatible set: {0,1,3}, count = 3

   Note: max_compatible_count is GTot and cannot be reduced by assert_norm.
   Testing compatible/mutually_compatible predicates instead. *)
let start : Seq.seq int = Seq.seq_of_list [1; 3; 4; 6]
let finish : Seq.seq int = Seq.seq_of_list [3; 5; 6; 9]

(* === Completeness: finish_sorted, compatible, mutually_compatible === *)
let test_sorted () : Lemma (finish_sorted finish) = ()
let test_mutual_compat () : Lemma (mutually_compatible start finish [0; 1; 3]) = ()
