module Test.ActivitySelection
#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array
open FStar.SizeT
open FStar.Mul
open CLRS.Ch16.ActivitySelection.Impl

module A = Pulse.Lib.Array
module GR = Pulse.Lib.GhostReference
module SZ = FStar.SizeT
module Seq = FStar.Seq
module V = Pulse.Lib.Vec

#push-options "--fuel 8 --ifuel 4 --z3rlimit 400"
let activity_input_ok
  (ss sf: Seq.seq int)
  (sout0: Seq.seq SZ.t)
  (start_times finish_times: A.array int)
  (out: A.array SZ.t)
  : Lemma
    (requires Seq.length ss == 3 /\
              Seq.length sf == 3 /\
              Seq.length sout0 == 3 /\
              Seq.index ss 0 == 1 /\ Seq.index ss 1 == 1 /\ Seq.index ss 2 == 2 /\
              Seq.index sf 0 == 2 /\ Seq.index sf 1 == 3 /\ Seq.index sf 2 == 100)
    (ensures activity_selection_pre 3sz ss sf sout0 start_times finish_times out)
= admit()

let completeness_activity_selection
  (count: SZ.t)
  (sout: Seq.seq SZ.t)
  (cf c0: nat)
  (ss sf: Seq.seq int)
  : Lemma
    (requires Seq.length ss == 3 /\
              Seq.length sf == 3 /\
              Seq.index ss 0 == 1 /\ Seq.index ss 1 == 1 /\ Seq.index ss 2 == 2 /\
              Seq.index sf 0 == 2 /\ Seq.index sf 1 == 3 /\ Seq.index sf 2 == 100 /\
              activity_selection_post count 3sz sout cf c0 ss sf)
    (ensures SZ.v count == 2 /\ Seq.index sout 0 == 0sz /\ Seq.index sout 1 == 2sz)
= admit()
#pop-options

fn test_activity_selection ()
  requires emp
  returns _: unit
  ensures emp
{
  let sv = V.alloc 0 3sz;
  V.to_array_pts_to sv;
  let start = V.vec_to_array sv;
  rewrite (A.pts_to (V.vec_to_array sv) (Seq.create 3 0))
       as (A.pts_to start (Seq.create 3 0));
  start.(0sz) <- 1;
  start.(1sz) <- 1;
  start.(2sz) <- 2;

  let fv = V.alloc 0 3sz;
  V.to_array_pts_to fv;
  let finish = V.vec_to_array fv;
  rewrite (A.pts_to (V.vec_to_array fv) (Seq.create 3 0))
       as (A.pts_to finish (Seq.create 3 0));
  finish.(0sz) <- 2;
  finish.(1sz) <- 3;
  finish.(2sz) <- 100;

  let ov = V.alloc 0sz 3sz;
  V.to_array_pts_to ov;
  let out = V.vec_to_array ov;
  rewrite (A.pts_to (V.vec_to_array ov) (Seq.create 3 0sz))
       as (A.pts_to out (Seq.create 3 0sz));

  let ctr = GR.alloc #nat 0;

  with ss0 sf0 sout0.
    assert (A.pts_to start ss0 ** A.pts_to finish sf0 ** A.pts_to out sout0);
  activity_input_ok ss0 sf0 sout0 start finish out;

  let count = activity_selection start finish out 3sz ctr;
  with sout cf.
    assert (A.pts_to start ss0 ** A.pts_to finish sf0 ** A.pts_to out sout ** GR.pts_to ctr cf **
            pure (activity_selection_post count 3sz sout cf 0 ss0 sf0));
  completeness_activity_selection count sout cf 0 ss0 sf0;

  let o0 = out.(0sz);
  let o1 = out.(1sz);
  assert (pure (SZ.v count == 2));
  assert (pure (o0 == 0sz));
  assert (pure (o1 == 2sz));

  admit()
}
