module Test.MergeSort
#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array
open Pulse.Lib.BoundedIntegers
open FStar.SizeT
open CLRS.Ch02.MergeSort.Impl

module A = Pulse.Lib.Array
module V = Pulse.Lib.Vec
module SZ = FStar.SizeT
module Seq = FStar.Seq
module SS = CLRS.Common.SortSpec
module GR = Pulse.Lib.GhostReference

let completeness_sort3 (s0 s: Seq.seq int) : Lemma
  (requires
    Seq.length s0 == 3 /\
    Seq.index s0 0 == 3 /\
    Seq.index s0 1 == 1 /\
    Seq.index s0 2 == 2 /\
    Seq.length s == 3 /\
    SS.sorted s /\
    SS.permutation s0 s)
  (ensures Seq.index s 0 == 1 /\ Seq.index s 1 == 2 /\ Seq.index s 2 == 3)
= admit()

fn test_merge_sort ()
  requires emp
  returns _: unit
  ensures emp
{
  let v = V.alloc 0 3sz;
  V.to_array_pts_to v;
  let arr = V.vec_to_array v;
  rewrite (A.pts_to (V.vec_to_array v) (Seq.create 3 0)) as (A.pts_to arr (Seq.create 3 0));
  arr.(0sz) <- 3;
  arr.(1sz) <- 1;
  arr.(2sz) <- 2;

  with s0. assert (A.pts_to arr s0);

  let ctr = GR.alloc #nat 0;
  merge_sort arr 3sz ctr;

  with s. assert (A.pts_to arr s);
  completeness_sort3 s0 s;

  let v0 = arr.(0sz);
  let v1 = arr.(1sz);
  let v2 = arr.(2sz);
  assert (pure (v0 == 1));
  assert (pure (v1 == 2));
  assert (pure (v2 == 3));

  admit()
}
