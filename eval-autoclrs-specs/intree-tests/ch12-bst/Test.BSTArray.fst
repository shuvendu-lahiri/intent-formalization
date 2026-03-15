module Test.BSTArray
#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array
open FStar.SizeT
open FStar.Mul
open CLRS.Ch12.BSTArray.Impl

module A = Pulse.Lib.Array
module GR = Pulse.Lib.GhostReference
module SZ = FStar.SizeT
module Seq = FStar.Seq
module V = Pulse.Lib.Vec

#push-options "--fuel 8 --ifuel 4 --z3rlimit 400"
let bstarray_input_ok (keys: Seq.seq int) (valid: Seq.seq bool) : Lemma
  (requires Seq.length keys == 1 /\
            Seq.length valid == 1 /\
            Seq.index keys 0 == 7 /\
            Seq.index valid 0 == true)
  (ensures subtree_in_range keys valid 1 0 (-100) 100)
= admit()

let completeness_bstarray_search (result: option SZ.t) (keys: Seq.seq int) (valid: Seq.seq bool) : Lemma
  (requires Seq.length keys == 1 /\
            Seq.length valid == 1 /\
            Seq.index keys 0 == 7 /\
            Seq.index valid 0 == true /\
            (Some? result ==> (
              SZ.v (Some?.v result) < Seq.length keys /\
              SZ.v (Some?.v result) < Seq.length valid /\
              Seq.index valid (SZ.v (Some?.v result)) == true /\
              Seq.index keys (SZ.v (Some?.v result)) == 7)) /\
            (None? result ==> ~(key_in_subtree keys valid 1 0 7)))
  (ensures Some? result /\ SZ.v (Some?.v result) == 0)
= admit()
#pop-options

fn test_bst_array ()
  requires emp
  returns _: unit
  ensures emp
{
  let kv = V.alloc 0 1sz;
  V.to_array_pts_to kv;
  let keys = V.vec_to_array kv;
  rewrite (A.pts_to (V.vec_to_array kv) (Seq.create 1 0))
       as (A.pts_to keys (Seq.create 1 0));
  keys.(0sz) <- 7;

  let vv = V.alloc false 1sz;
  V.to_array_pts_to vv;
  let valid = V.vec_to_array vv;
  rewrite (A.pts_to (V.vec_to_array vv) (Seq.create 1 false))
       as (A.pts_to valid (Seq.create 1 false));
  valid.(0sz) <- true;

  let t : bst = { keys = keys; valid = valid; cap = 1sz };
  let ctr = GR.alloc #nat 0;
  let lo = hide (-100);
  let hi = hide 100;

  with ks0 vs0.
    assert (A.pts_to keys ks0 ** A.pts_to valid vs0);
  bstarray_input_ok ks0 vs0;

  let result = tree_search t #ks0 #vs0 #lo #hi 7 ctr;
  with ks1 vs1 cf.
    assert (A.pts_to keys ks1 ** A.pts_to valid vs1 ** GR.pts_to ctr cf **
            pure (Seq.length ks1 == 1 /\
                  Seq.length vs1 == 1 /\
                  Seq.index ks1 0 == 7 /\
                  Seq.index vs1 0 == true /\
                  (Some? result ==> (
                    SZ.v (Some?.v result) < Seq.length ks1 /\
                    SZ.v (Some?.v result) < Seq.length vs1 /\
                    Seq.index vs1 (SZ.v (Some?.v result)) == true /\
                    Seq.index ks1 (SZ.v (Some?.v result)) == 7)) /\
                  (None? result ==> ~(key_in_subtree ks1 vs1 1 0 7))));
  completeness_bstarray_search result ks1 vs1;
  assert (pure (Some? result));
  assert (pure (SZ.v (Some?.v result) == 0));

  admit()
}
