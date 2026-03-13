module Test.JarvisMarch

open FStar.Mul
module Seq = FStar.Seq
open CLRS.Ch33.Segments.Spec
open CLRS.Ch33.JarvisMarch.Spec

(* Top-level functions: jarvis_march_spec, find_leftmost_spec *)

(* Triangle: 3 points all on hull *)
let xs3 : Seq.seq int = Seq.seq_of_list [0; 4; 2]
let ys3 : Seq.seq int = Seq.seq_of_list [0; 0; 3]

(* 4 points: (0,0), (2,0), (1,2), (1,1) — hull has 3 vertices *)
let xs : Seq.seq int = Seq.seq_of_list [0; 2; 1; 1]
let ys : Seq.seq int = Seq.seq_of_list [0; 0; 2; 1]

(* === Completeness (Appendix B): jarvis_march_spec uniquely determines output === *)
#push-options "--z3rlimit 100"
let test_triangle_complete (y:int) : Lemma
  (requires jarvis_march_spec xs3 ys3 == y)
  (ensures y == 3) =
  assert_norm (jarvis_march_spec xs3 ys3 == 3)

let test_leftmost_complete (y:int) : Lemma
  (requires find_leftmost_spec xs ys == y)
  (ensures y == 0) =
  assert_norm (find_leftmost_spec xs ys == 0)

let test_hull_4_complete (y:int) : Lemma
  (requires jarvis_march_spec xs ys == y)
  (ensures y == 3) =
  assert_norm (jarvis_march_spec xs ys == 3)
#pop-options
