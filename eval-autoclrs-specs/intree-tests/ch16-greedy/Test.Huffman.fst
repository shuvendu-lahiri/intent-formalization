module Test.Huffman

open FStar.List.Tot
open CLRS.Ch16.Huffman.Spec

(* Top-level function: huffman_build
   Builds optimal Huffman tree from frequency list *)

let tree2 = huffman_build [5; 9]
let tree3 = huffman_build [5; 9; 12]

(* === Completeness (Appendix B): huffman_build uniquely determines output === *)
let test_freq_2_complete (y:int) : Lemma
  (requires freq_of tree2 == y)
  (ensures y == 14) =
  assert_norm (freq_of tree2 == 14)

let test_cost_2_complete (y:int) : Lemma
  (requires cost tree2 == y)
  (ensures y == 14) =
  assert_norm (cost tree2 == 14)

let test_freq_3_complete (y:int) : Lemma
  (requires freq_of tree3 == y)
  (ensures y == 26) =
  assert_norm (freq_of tree3 == 26)

let test_cost_3_complete (y:int) : Lemma
  (requires cost tree3 == y)
  (ensures y == 40) =
  assert_norm (cost tree3 == 40)
