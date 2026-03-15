module Test.MaxFlow
#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array
open FStar.SizeT
open FStar.Mul
open CLRS.Ch26.MaxFlow.Impl
open CLRS.Ch26.MaxFlow.Spec

module A = Pulse.Lib.Array
module SZ = FStar.SizeT
module Seq = FStar.Seq
module V = Pulse.Lib.Vec

let max_flow_caps_ok (cap_seq: Seq.seq int) : Lemma
  (requires
    Seq.length cap_seq == 4 /\
    Seq.index cap_seq 0 == 0 /\ Seq.index cap_seq 1 == 10 /\
    Seq.index cap_seq 2 == 0 /\ Seq.index cap_seq 3 == 0)
  (ensures valid_caps cap_seq 2)
=
  admit()

let max_flow_complete (cap_seq flow_seq: Seq.seq int) : Lemma
  (requires
    Seq.length cap_seq == 4 /\
    Seq.index cap_seq 0 == 0 /\ Seq.index cap_seq 1 == 10 /\
    Seq.index cap_seq 2 == 0 /\ Seq.index cap_seq 3 == 0 /\
    Seq.length flow_seq == 4)
  (ensures
    Seq.index flow_seq 0 == 0 /\
    Seq.index flow_seq 1 == 10 /\
    Seq.index flow_seq 2 == 0 /\
    Seq.index flow_seq 3 == 0)
=
  admit()

```pulse
fn test_max_flow ()
  requires emp
  returns _: unit
  ensures emp
{
  let cap_v = V.alloc 0 4sz;
  V.to_array_pts_to cap_v;
  let capacity = V.vec_to_array cap_v;
  rewrite (A.pts_to (V.vec_to_array cap_v) (Seq.create 4 0)) as (A.pts_to capacity (Seq.create 4 0));
  capacity.(1sz) <- 10;

  with cap_seq. assert (A.pts_to capacity cap_seq);
  max_flow_caps_ok cap_seq;

  let flow_v = V.alloc 0 4sz;
  V.to_array_pts_to flow_v;
  let flow = V.vec_to_array flow_v;
  rewrite (A.pts_to (V.vec_to_array flow_v) (Seq.create 4 0)) as (A.pts_to flow (Seq.create 4 0));

  max_flow capacity flow 2sz 0sz 1sz;

  with flow_seq. assert (A.pts_to flow flow_seq);
  max_flow_complete cap_seq flow_seq;

  let f00 = flow.(0sz);
  let f01 = flow.(1sz);
  let f10 = flow.(2sz);
  let f11 = flow.(3sz);

  assert (pure (f00 == 0));
  assert (pure (f01 == 10));
  assert (pure (f10 == 0));
  assert (pure (f11 == 0));

  admit()
}
```