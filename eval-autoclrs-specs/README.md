# Intent Formalization for AutoCLRS Algorithms

Completeness testing of verified algorithm implementations from the
[AutoCLRS](https://github.com/FStarLang/AutoCLRS) repository — verified
Pulse implementations of algorithms from *Introduction to Algorithms* (CLRS).

See the [Intent Formalization blog](https://risemsr.github.io/blog/2026-03-05-shuvendu-intent-formalization/) for an overview of the research direction.

Uses the **completeness testing** approach from:

> **Evaluating LLM-driven User-Intent Formalization for Verification-Aware Languages**
> *Shuvendu K. Lahiri*, FMCAD 2024.
> [https://arxiv.org/abs/2406.09757](https://arxiv.org/abs/2406.09757)
>
> Specifically, the **Appendix B** method for completeness checking.

## Method

Each test is a **black-box completeness check** against the implementation:

```
test(x) { y = algorithm(x); assert(y == expected) }
```

- Call the **Pulse implementation** directly (e.g., `quicksort`)
- Import **only** the `Impl` module — no spec modules exposed
- Assert the output equals a concrete expected value
- The test verifies iff the postcondition (spec) is strong enough to prove `y == expected`

All AutoCLRS implementations are Pulse, so all tests use `#lang-pulse`.

## AutoCLRS Submodule

AutoCLRS is included as a git submodule at `eval-autoclrs-specs/autoclrs/`,
pinned to commit [`1984af1`](https://github.com/FStarLang/AutoCLRS/tree/1984af1a9e22c74709293060e649054969f10c2d).

## Evaluation Results

| # | Algorithm | Ch | Impl Function | Test File | Status | Notes |
|---|-----------|-----|--------------|-----------|--------|-------|
| 1 | Quicksort | ch07 | `quicksort` | [Test.Quicksort.fst](intree-tests/ch07-quicksort/Test.Quicksort.fst) | 🔨 | Pulse test; pending verification |

### Example: Quicksort Completeness Test

The `quicksort` implementation has the postcondition:
```
ensures exists* s. (A.pts_to a s ** pure (sorted s /\ permutation s0 s))
```
i.e., the output is **sorted** and a **permutation** of the input.

```pulse
module Test.Quicksort
#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array
open FStar.SizeT
open CLRS.Ch07.Quicksort.Impl   // only the Impl — no spec modules

fn test_quicksort_3 ()
  requires emp
  ensures emp
{
  // --- Setup input array [3; 1; 2] ---
  let v = V.alloc 0 3sz;
  V.to_array_pts_to v;
  let arr = V.vec_to_array v;
  rewrite ... as (A.pts_to arr (Seq.create 3 0));
  arr.(0sz) <- 3; arr.(1sz) <- 1; arr.(2sz) <- 2;
  // arr now holds s0 = [3; 1; 2]

  // --- Call implementation ---
  quicksort arr 3sz;
  // Postcondition gives us: sorted s /\ permutation [3;1;2] s

  // --- Assert output == expected ---
  with s. assert (A.pts_to arr s);
  // s is the output sequence; we assert it equals [1; 2; 3]
  assert (pure (s `Seq.equal` Seq.seq_of_list [1; 2; 3]));
  // F* must prove [1;2;3] is the ONLY sequence satisfying
  //   sorted s /\ permutation [3;1;2] s
  // This succeeds iff the spec is COMPLETE

  // --- Cleanup ---
  ...
}
```

The test imports `CLRS.Ch07.Quicksort.Impl` and calls `quicksort` on `[3, 1, 2]`.
It then asserts the result is `[1, 2, 3]`. If the postcondition (`sorted ∧ permutation`)
is strong enough to uniquely determine the output, F* can prove `s == [1; 2; 3]` —
demonstrating completeness. No spec functions are referenced in the test.

### Verification

Tests are verified using the AutoCLRS build system (`make verify`), which invokes
F* with the Pulse plugin for `#lang-pulse` files.

```bash
# From the autoclrs/autoclrs/ch07-quicksort/ directory:
make verify
```

This requires a working F* + Pulse build (see [setup.sh](autoclrs/setup.sh) in the submodule).

**Current status:** Pending — requires Pulse plugin build.

## References

- [Lahiri, "Evaluating LLM-driven User-Intent Formalization for Verification-Aware Languages", FMCAD 2024](https://arxiv.org/abs/2406.09757)
- [AutoCLRS: Verified CLRS Algorithms in F*](https://github.com/FStarLang/AutoCLRS)
- [AutoCLRS Blog Post](https://risemsr.github.io/blog/2026-03-06-autoclrs/)
- [Intent Formalization Blog Post](https://risemsr.github.io/blog/2026-03-05-shuvendu-intent-formalization/)
