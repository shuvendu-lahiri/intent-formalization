module Test.CountingSort
#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array
open Pulse.Lib.BoundedIntegers
open FStar.SizeT
open CLRS.Ch08.CountingSort.Impl

module A = Pulse.Lib.Array
module V = Pulse.Lib.Vec
module SZ = FStar.SizeT
module Seq = FStar.Seq
module SP = FStar.Seq.Properties
module S = CLRS.Ch08.CountingSort.Spec
module GR = Pulse.Lib.GhostReference

#push-options "--z3rlimit 400 --fuel 8 --ifuel 4"

let std_sort3_nat (s: Seq.seq nat)
  : Lemma
    (requires Seq.length s == 3 /\
              (forall (i j:nat). Prims.op_LessThanOrEqual i j /\
                                 Prims.op_LessThan j 3 ==>
                                 Prims.op_LessThanOrEqual (Seq.index s i) (Seq.index s j)) /\
              SP.permutation nat (Seq.seq_of_list [3; 1; 2]) s)
    (ensures Seq.index s 0 == 1 /\ Seq.index s 1 == 2 /\ Seq.index s 2 == 3)
= SP.perm_len (Seq.seq_of_list [3; 1; 2]) s;
  assert_norm (SP.count 1 (Seq.seq_of_list [3; 1; 2]) == 1);
  assert_norm (SP.count 2 (Seq.seq_of_list [3; 1; 2]) == 1);
  assert_norm (SP.count 3 (Seq.seq_of_list [3; 1; 2]) == 1);
  assert_norm (SP.count #nat 0 (Seq.seq_of_list [3; 1; 2]) == 0);
  assert_norm (SP.count #nat 4 (Seq.seq_of_list [3; 1; 2]) == 0)

let completeness_csort3 (s: Seq.seq nat)
  : Lemma
    (requires S.sorted s /\ S.permutation s (Seq.seq_of_list [3; 1; 2]))
    (ensures Seq.index s 0 == 1 /\ Seq.index s 1 == 2 /\ Seq.index s 2 == 3)
= reveal_opaque (`%S.permutation) (S.permutation s (Seq.seq_of_list [3; 1; 2]));
  assert (forall (i j:nat). (i <= j) == Prims.op_LessThanOrEqual i j);
  assert (forall (x y:nat). (x <= y) == Prims.op_LessThanOrEqual x y);
  std_sort3_nat s

```pulse
fn test_counting_sort_3 ()
  requires emp
  returns _: unit
  ensures emp
{
  let v = V.alloc #nat 0 3sz;
  V.to_array_pts_to v;
  let arr = V.vec_to_array v;
  rewrite (A.pts_to (V.vec_to_array v) (Seq.create 3 0)) as (A.pts_to arr (Seq.create #nat 3 0));
  arr.(0sz) <- 3;
  arr.(1sz) <- 1;
  arr.(2sz) <- 2;

  with s0. assert (A.pts_to arr s0);
  counting_sort_inplace arr 3sz 4sz;

  with s. assert (A.pts_to arr s);
  completeness_csort3 s;

  let v0 = arr.(0sz);
  let v1 = arr.(1sz);
  let v2 = arr.(2sz);
  assert (pure (v0 == 1));
  assert (pure (v1 == 2));
  assert (pure (v2 == 3));

  with s2. assert (A.pts_to arr s2);
  rewrite (A.pts_to arr s2) as (A.pts_to (V.vec_to_array v) s2);
  V.to_vec_pts_to v;
  V.free v;
}
```

#pop-options
