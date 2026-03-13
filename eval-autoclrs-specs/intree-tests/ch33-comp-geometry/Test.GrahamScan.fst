module Test.GrahamScan

open FStar.Seq
open CLRS.Ch33.Segments.Spec
open CLRS.Ch33.GrahamScan.Spec

let test1 () : Lemma (find_bottom_spec (seq_of_list [0; 1; 2]) (seq_of_list [2; 0; 1]) == 1) =
  assert_norm (find_bottom_spec (seq_of_list [0; 1; 2]) (seq_of_list [2; 0; 1]) == 1)
