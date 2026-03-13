module Test.BFS

open FStar.Mul
open FStar.Seq
open CLRS.Ch22.BFS.Spec

(* Top-level function: bfs_distance
   Graph: 3 vertices, edges: 0→1, 0→2
   Adjacency matrix (3×3 flat) *)
let adj : seq int = seq_of_list [0; 1; 1; 0; 0; 0; 0; 0; 0]

(* === Completeness (Appendix B): bfs_distance uniquely determines output === *)
let test_dist_self_complete (y:int) : Lemma
  (requires bfs_distance 3 adj 0 0 == y)
  (ensures y == 0) =
  assert_norm (bfs_distance 3 adj 0 0 == 0)

let test_dist_1_complete (y:int) : Lemma
  (requires bfs_distance 3 adj 0 1 == y)
  (ensures y == 1) =
  assert_norm (bfs_distance 3 adj 0 1 == 1)

let test_dist_2_complete (y:int) : Lemma
  (requires bfs_distance 3 adj 0 2 == y)
  (ensures y == 1) =
  assert_norm (bfs_distance 3 adj 0 2 == 1)
