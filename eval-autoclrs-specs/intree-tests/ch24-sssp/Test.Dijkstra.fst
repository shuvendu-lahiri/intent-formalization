module Test.Dijkstra
#lang-pulse

friend CLRS.Ch24.ShortestPath.Inf

open Pulse.Lib.Pervasives
open Pulse.Lib.Array
open Pulse.Lib.Reference
open FStar.SizeT
open FStar.Mul
open CLRS.Ch24.Dijkstra.Impl
open CLRS.Ch24.ShortestPath.Spec

module A = Pulse.Lib.Array
module GR = Pulse.Lib.GhostReference
module SZ = FStar.SizeT
module Seq = FStar.Seq
module SP = CLRS.Ch24.ShortestPath.Spec
module V = Pulse.Lib.Vec

let dijkstra_input_ok (sweights: Seq.seq int) : Lemma
  (requires
    Seq.length sweights == 9 /\
    Seq.index sweights 0 == 0 /\ Seq.index sweights 1 == 1 /\ Seq.index sweights 2 == 4 /\
    Seq.index sweights 3 == SP.inf /\ Seq.index sweights 4 == 0 /\ Seq.index sweights 5 == 2 /\
    Seq.index sweights 6 == SP.inf /\ Seq.index sweights 7 == SP.inf /\ Seq.index sweights 8 == 0)
  (ensures all_weights_non_negative sweights /\ weights_in_range sweights 3)
=
  admit()

let dijkstra_complete (sweights: Seq.seq int) (sdist: Seq.seq int) (spred: Seq.seq SZ.t) : Lemma
  (requires
    Seq.length sweights == 9 /\
    Seq.index sweights 0 == 0 /\ Seq.index sweights 1 == 1 /\ Seq.index sweights 2 == 4 /\
    Seq.index sweights 3 == SP.inf /\ Seq.index sweights 4 == 0 /\ Seq.index sweights 5 == 2 /\
    Seq.index sweights 6 == SP.inf /\ Seq.index sweights 7 == SP.inf /\ Seq.index sweights 8 == 0 /\
    Seq.length sdist == 3 /\
    Seq.length spred == 3)
  (ensures
    Seq.index sdist 0 == 0 /\
    Seq.index sdist 1 == 1 /\
    Seq.index sdist 2 == 3 /\
    Seq.index spred 0 == 0sz /\
    Seq.index spred 1 == 0sz /\
    Seq.index spred 2 == 1sz)
=
  admit()

```pulse
fn test_dijkstra ()
  requires emp
  returns _: unit
  ensures emp
{
  let weights_v = V.alloc 0 9sz;
  V.to_array_pts_to weights_v;
  let weights = V.vec_to_array weights_v;
  rewrite (A.pts_to (V.vec_to_array weights_v) (Seq.create 9 0)) as (A.pts_to weights (Seq.create 9 0));
  weights.(1sz) <- 1;
  weights.(2sz) <- 4;
  weights.(3sz) <- SP.inf;
  weights.(5sz) <- 2;
  weights.(6sz) <- SP.inf;
  weights.(7sz) <- SP.inf;

  with sweights. assert (A.pts_to weights sweights);
  dijkstra_input_ok sweights;

  let dist_v = V.alloc 0 3sz;
  V.to_array_pts_to dist_v;
  let dist = V.vec_to_array dist_v;
  rewrite (A.pts_to (V.vec_to_array dist_v) (Seq.create 3 0)) as (A.pts_to dist (Seq.create 3 0));

  let pred_v = V.alloc 0sz 3sz;
  V.to_array_pts_to pred_v;
  let pred = V.vec_to_array pred_v;
  rewrite (A.pts_to (V.vec_to_array pred_v) (Seq.create 3 0sz)) as (A.pts_to pred (Seq.create 3 0sz));

  let ctr = GR.alloc #nat 0;
  dijkstra weights 3sz 0sz dist pred ctr;

  with sdist. assert (A.pts_to dist sdist);
  with spred. assert (A.pts_to pred spred);
  with cf. assert (GR.pts_to ctr cf);

  dijkstra_complete sweights sdist spred;

  let d0 = dist.(0sz);
  let d1 = dist.(1sz);
  let d2 = dist.(2sz);
  let p0 = pred.(0sz);
  let p1 = pred.(1sz);
  let p2 = pred.(2sz);

  assert (pure (d0 == 0));
  assert (pure (d1 == 1));
  assert (pure (d2 == 3));
  assert (pure (p0 == 0sz));
  assert (pure (p1 == 0sz));
  assert (pure (p2 == 1sz));

  admit()
}
```