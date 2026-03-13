module Test.DFS

open FStar.Mul
open FStar.Seq
open CLRS.Ch22.DFS.Spec

(* Top-level function: dfs
   Graph: 3 vertices, edges: 0→1, 0→2 (adjacency lists) *)
let adj0 : seq int = seq_of_list [1; 2]
let adj1 : seq int = Seq.empty #int
let adj2 : seq int = Seq.empty #int
let adj : seq (seq int) = seq_of_list [adj0; adj1; adj2]

let result = dfs adj 3

(* === Completeness (Appendix B): dfs uniquely determines output === *)
#push-options "--z3rlimit 100"
let test_n_complete (y:int) : Lemma
  (requires result.n == y)
  (ensures y == 3) =
  assert_norm (result.n == 3)

let test_time_complete (y:int) : Lemma
  (requires result.time == y)
  (ensures y == 6) =
  assert_norm (result.time == 6)
#pop-options
