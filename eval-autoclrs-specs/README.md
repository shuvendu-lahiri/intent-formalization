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
- Import **only** the `Impl` module — no spec modules exposed in the test
- Assert the output equals a concrete expected value
- The test verifies iff the postcondition (spec) is strong enough to prove `y == expected`

Most AutoCLRS implementations are Pulse (imperative), so tests use `#lang-pulse`.
A few algorithms have pure F\* specs only (no Pulse impl), tested as pure lemmas.

## AutoCLRS Submodule

AutoCLRS is included as a git submodule at `eval-autoclrs-specs/autoclrs/`,
pinned to commit [`1984af1`](https://github.com/FStarLang/AutoCLRS/tree/1984af1a9e22c74709293060e649054969f10c2d).

## Evaluation Results

**Summary: 32 ✅ verified, 6 ❌ failed, 5 ⚠️ blocked by upstream, 5 ⏳ not reached — 48 tests total**

### Sorting (ch02, ch06, ch07, ch08)

| # | Algorithm | Ch | Test File | Status | Notes |
|---|-----------|-----|-----------|--------|-------|
| 1 | InsertionSort | ch02 | [Test.InsertionSort.fst](intree-tests/ch02-getting-started/Test.InsertionSort.fst) | ✅ | Pulse impl call; BoundedIntegers bridge |
| 2 | MergeSort | ch02 | [Test.MergeSort.fst](intree-tests/ch02-getting-started/Test.MergeSort.fst) | ✅ | Pulse impl call; BoundedIntegers bridge |
| 3 | Heapsort | ch06 | [Test.Heap.fst](intree-tests/ch06-heapsort/Test.Heap.fst) | ✅ | Pure spec test (SZ.fits prevents Pulse call) |
| 4 | Quicksort | ch07 | [Test.Quicksort.fst](intree-tests/ch07-quicksort/Test.Quicksort.fst) | ✅ | Pulse impl call; reference example |
| 5 | BucketSort | ch08 | [Test.BucketSort.fst](intree-tests/ch08-linear-sorting/Test.BucketSort.fst) | ✅ | Pure spec test |
| 6 | RadixSort | ch08 | [Test.RadixSort.fst](intree-tests/ch08-linear-sorting/Test.RadixSort.fst) | ✅ | Pure spec test |
| 7 | CountingSort | ch08 | [Test.CountingSort.fst](intree-tests/ch08-linear-sorting/Test.CountingSort.fst) | ❌ | Pulse call fails (subtyping) |

### Search & Selection (ch04, ch09)

| # | Algorithm | Ch | Test File | Status | Notes |
|---|-----------|-----|-----------|--------|-------|
| 8 | BinarySearch | ch04 | [Test.BinarySearch.fst](intree-tests/ch04-divide-conquer/Test.BinarySearch.fst) | ✅ | Pulse impl call |
| 9 | MaxSubarray | ch04 | [Test.MaxSubarray.fst](intree-tests/ch04-divide-conquer/Test.MaxSubarray.fst) | ✅ | Pure spec test |
| 10 | MatrixMultiply | ch04 | [Test.MatrixMultiply.fst](intree-tests/ch04-divide-conquer/Test.MatrixMultiply.fst) | ❌ | Pulse call fails |
| 11 | MinMax | ch09 | [Test.MinMax.fst](intree-tests/ch09-order-statistics/Test.MinMax.fst) | ⚠️ | Upstream build error (Quickselect.Impl.fst) |
| 12 | PartialSelectionSort | ch09 | [Test.PartialSelectionSort.fst](intree-tests/ch09-order-statistics/Test.PartialSelectionSort.fst) | ⚠️ | Upstream build error |
| 13 | Quickselect | ch09 | [Test.Quickselect.fst](intree-tests/ch09-order-statistics/Test.Quickselect.fst) | ⚠️ | Upstream build error |
| 14 | SimultaneousMinMax | ch09 | [Test.SimultaneousMinMax.fst](intree-tests/ch09-order-statistics/Test.SimultaneousMinMax.fst) | ⚠️ | Upstream build error |

### Data Structures (ch10, ch11, ch12, ch13)

| # | Algorithm | Ch | Test File | Status | Notes |
|---|-----------|-----|-----------|--------|-------|
| 15 | Stack | ch10 | [Test.Stack.fst](intree-tests/ch10-elementary-ds/Test.Stack.fst) | ✅ | Pulse impl call |
| 16 | SLL | ch10 | [Test.SLL.fst](intree-tests/ch10-elementary-ds/Test.SLL.fst) | ✅ | Pulse impl call |
| 17 | DLL | ch10 | [Test.DLL.fst](intree-tests/ch10-elementary-ds/Test.DLL.fst) | ❌ | Pulse call fails |
| 18 | Queue | ch10 | [Test.Queue.fst](intree-tests/ch10-elementary-ds/Test.Queue.fst) | ⏳ | Not reached (DLL error stops make) |
| 19 | HashTable | ch11 | [Test.HashTable.fst](intree-tests/ch11-hash-tables/Test.HashTable.fst) | ✅ | Pulse impl call |
| 20 | BST | ch12 | [Test.BST.fst](intree-tests/ch12-bst/Test.BST.fst) | ✅ | Pulse impl call |
| 21 | BSTArray | ch12 | [Test.BSTArray.fst](intree-tests/ch12-bst/Test.BSTArray.fst) | ✅ | Pulse impl call |
| 22 | RBTree | ch13 | [Test.RBTree.fst](intree-tests/ch13-rbtree/Test.RBTree.fst) | ⚠️ | Upstream build error (RBTree.Impl.fsti) |

### Dynamic Programming (ch15)

| # | Algorithm | Ch | Test File | Status | Notes |
|---|-----------|-----|-----------|--------|-------|
| 23 | LCS | ch15 | [Test.LCS.fst](intree-tests/ch15-dynamic-programming/Test.LCS.fst) | ❌ | Pulse call fails |
| 24 | MatrixChain | ch15 | [Test.MatrixChain.fst](intree-tests/ch15-dynamic-programming/Test.MatrixChain.fst) | ⏳ | Not reached (LCS error stops make) |
| 25 | RodCutting | ch15 | [Test.RodCutting.fst](intree-tests/ch15-dynamic-programming/Test.RodCutting.fst) | ⏳ | Not reached |

### Greedy (ch16)

| # | Algorithm | Ch | Test File | Status | Notes |
|---|-----------|-----|-----------|--------|-------|
| 26 | ActivitySelection | ch16 | [Test.ActivitySelection.fst](intree-tests/ch16-greedy/Test.ActivitySelection.fst) | ✅ | Pulse impl call |
| 27 | Huffman | ch16 | [Test.Huffman.fst](intree-tests/ch16-greedy/Test.Huffman.fst) | ✅ | Pulse impl call |

### Union-Find & Graphs (ch21, ch22)

| # | Algorithm | Ch | Test File | Status | Notes |
|---|-----------|-----|-----------|--------|-------|
| 28 | UnionFind | ch21 | [Test.UnionFind.fst](intree-tests/ch21-disjoint-sets/Test.UnionFind.fst) | ✅ | Pulse impl call |
| 29 | BFS | ch22 | [Test.BFS.fst](intree-tests/ch22-elementary-graph/Test.BFS.fst) | ✅ | Pulse impl call |
| 30 | DFS | ch22 | [Test.DFS.fst](intree-tests/ch22-elementary-graph/Test.DFS.fst) | ✅ | Pulse impl call |
| 31 | TopologicalSort | ch22 | [Test.TopologicalSort.fst](intree-tests/ch22-elementary-graph/Test.TopologicalSort.fst) | ✅ | Pulse impl call |

### MST & Shortest Paths (ch23, ch24, ch25, ch26)

| # | Algorithm | Ch | Test File | Status | Notes |
|---|-----------|-----|-----------|--------|-------|
| 32 | Kruskal | ch23 | [Test.Kruskal.fst](intree-tests/ch23-mst/Test.Kruskal.fst) | ⏳ | Not reached (Prim error stops make) |
| 33 | Prim | ch23 | [Test.Prim.fst](intree-tests/ch23-mst/Test.Prim.fst) | ❌ | Error 310 (module not found) |
| 34 | BellmanFord | ch24 | [Test.BellmanFord.fst](intree-tests/ch24-sssp/Test.BellmanFord.fst) | ❌ | Error 310 (module not found) |
| 35 | Dijkstra | ch24 | [Test.Dijkstra.fst](intree-tests/ch24-sssp/Test.Dijkstra.fst) | ⏳ | Not reached |
| 36 | FloydWarshall | ch25 | [Test.FloydWarshall.fst](intree-tests/ch25-apsp/Test.FloydWarshall.fst) | ✅ | Pulse impl call |
| 37 | MaxFlow | ch26 | [Test.MaxFlow.fst](intree-tests/ch26-max-flow/Test.MaxFlow.fst) | ✅ | Pulse impl call |

### Number Theory (ch31)

| # | Algorithm | Ch | Test File | Status | Notes |
|---|-----------|-----|-----------|--------|-------|
| 38 | GCD | ch31 | [Test.GCD.fst](intree-tests/ch31-number-theory/Test.GCD.fst) | ✅ | Pure spec test |
| 39 | ModExp | ch31 | [Test.ModExp.fst](intree-tests/ch31-number-theory/Test.ModExp.fst) | ✅ | Pure spec test |
| 40 | ModExpLR | ch31 | [Test.ModExpLR.fst](intree-tests/ch31-number-theory/Test.ModExpLR.fst) | ✅ | Pure spec test |
| 41 | ExtendedGCD | ch31 | [Test.ExtendedGCD.fst](intree-tests/ch31-number-theory/Test.ExtendedGCD.fst) | ✅ | Pure spec test |

### String Matching (ch32)

| # | Algorithm | Ch | Test File | Status | Notes |
|---|-----------|-----|-----------|--------|-------|
| 42 | NaiveStringMatch | ch32 | [Test.NaiveStringMatch.fst](intree-tests/ch32-string-matching/Test.NaiveStringMatch.fst) | ✅ | Pure spec test |
| 43 | KMP | ch32 | [Test.KMP.fst](intree-tests/ch32-string-matching/Test.KMP.fst) | ✅ | Pure spec test |
| 44 | RabinKarp | ch32 | [Test.RabinKarp.fst](intree-tests/ch32-string-matching/Test.RabinKarp.fst) | ✅ | Pure spec test |

### Computational Geometry (ch33)

| # | Algorithm | Ch | Test File | Status | Notes |
|---|-----------|-----|-----------|--------|-------|
| 45 | Segments | ch33 | [Test.Segments.fst](intree-tests/ch33-comp-geometry/Test.Segments.fst) | ✅ | Pure spec test |
| 46 | GrahamScan | ch33 | [Test.GrahamScan.fst](intree-tests/ch33-comp-geometry/Test.GrahamScan.fst) | ✅ | Pure spec test |
| 47 | JarvisMarch | ch33 | [Test.JarvisMarch.fst](intree-tests/ch33-comp-geometry/Test.JarvisMarch.fst) | ✅ | Pure spec test |

### Approximation (ch35)

| # | Algorithm | Ch | Test File | Status | Notes |
|---|-----------|-----|-----------|--------|-------|
| 48 | VertexCover | ch35 | [Test.VertexCover.fst](intree-tests/ch35-approximation/Test.VertexCover.fst) | ✅ | Pure spec test |

### Legend

- ✅ **Verified**: completeness test type-checks with F\* + Pulse plugin
- ❌ **Failed**: test file written but verification fails (Pulse subtyping / module errors)
- ⚠️ **Blocked**: upstream AutoCLRS build error prevents chapter from building
- ⏳ **Not reached**: `make verify` stopped at an earlier error in the same chapter

### Example: Quicksort Completeness Test

The `quicksort` implementation has the postcondition:
```
ensures exists* s. (A.pts_to a s ** pure (sorted s /\ permutation s0 s))
```
i.e., the output is **sorted** and a **permutation** of the input.

The completeness test:
1. Creates input array `[3, 1, 2]`
2. Calls `quicksort arr 3sz` (the Pulse implementation)
3. Proves the output must be `[1, 2, 3]` via a completeness lemma
4. Reads each element and asserts `v0 == 1`, `v1 == 2`, `v2 == 3`

The completeness lemma works by:
- Revealing the opaque `permutation` predicate to expose `FStar.Seq.Properties.permutation`
- Using `count`-based reasoning: since `[3,1,2]` has exactly one copy of each element, any sorted permutation must be `[1,2,3]`
- Bridging `BoundedIntegers` typeclass operators (`<=`) to standard `Prims.op_LessThanOrEqual` for Z3

```fstar
(* Pure helper: sorted + permutation of [3;1;2] uniquely determines [1;2;3] *)
let std_sort3 (s: Seq.seq int)
  : Lemma
    (requires (forall (i j:nat). Prims.op_LessThanOrEqual i j /\
                                 Prims.op_LessThan j (Seq.length s) ==>
                                 Prims.op_LessThanOrEqual (Seq.index s i) (Seq.index s j)) /\
              SP.permutation int (Seq.seq_of_list [3; 1; 2]) s)
    (ensures Seq.index s 0 == 1 /\ Seq.index s 1 == 2 /\ Seq.index s 2 == 3)
= SP.perm_len (Seq.seq_of_list [3; 1; 2]) s;
  assert_norm (SP.count 1 (Seq.seq_of_list [3; 1; 2]) == 1);
  assert_norm (SP.count 2 (Seq.seq_of_list [3; 1; 2]) == 1);
  assert_norm (SP.count 3 (Seq.seq_of_list [3; 1; 2]) == 1);
  assert_norm (SP.count 0 (Seq.seq_of_list [3; 1; 2]) == 0);
  assert_norm (SP.count 4 (Seq.seq_of_list [3; 1; 2]) == 0)

(* Bridges BoundedIntegers typeclass operators to Prims operators *)
let completeness_sort3 (s: Seq.seq int)
  : Lemma
    (requires SS.sorted s /\ SP.permutation int (Seq.seq_of_list [3; 1; 2]) s)
    (ensures Seq.index s 0 == 1 /\ Seq.index s 1 == 2 /\ Seq.index s 2 == 3)
= assert (forall (i j:nat). (i <= j) == Prims.op_LessThanOrEqual i j);
  assert (forall (x y:int). (x <= y) == Prims.op_LessThanOrEqual x y);
  std_sort3 s
```

The Pulse test then calls the implementation and uses the lemma:
```pulse
fn test_quicksort_3 ()
  requires emp
  ensures emp
{
  // Setup input [3; 1; 2]
  ...
  arr.(0sz) <- 3; arr.(1sz) <- 1; arr.(2sz) <- 2;

  // y = quicksort(x)
  quicksort arr 3sz;

  // assert(y == expected)
  with s. assert (A.pts_to arr s);
  reveal_opaque (`%SS.permutation) (SS.permutation s0 s);
  completeness_sort3 s;

  let v0 = arr.(0sz); let v1 = arr.(1sz); let v2 = arr.(2sz);
  assert (pure (v0 == 1));  // ✅ F* proves output[0] == 1
  assert (pure (v1 == 2));  // ✅ F* proves output[1] == 2
  assert (pure (v2 == 3));  // ✅ F* proves output[2] == 3
  ...
}
```

## Reproducing the Verification

### Prerequisites

Build F\* and Pulse following the [AutoCLRS setup instructions](autoclrs/setup.sh):

```bash
# Clone and build (from a Linux/WSL environment)
cd eval-autoclrs-specs/autoclrs
bash setup.sh          # builds F*, Pulse, Karamel, Steel
export FSTAR_EXE=$(pwd)/FStar/bin/fstar.exe
```

### Running Tests

Each test file lives alongside the AutoCLRS chapter source.
Copy the test files into the AutoCLRS build tree and run `make verify`:

```bash
# Example: verify quicksort completeness test
cp intree-tests/ch07-quicksort/Test.Quicksort.fst autoclrs/ch07-quicksort/
cd autoclrs/ch07-quicksort
make verify
# Output:
#    CHECK           Test.Quicksort.fst
#    Verified module: Test.Quicksort
#    All verification conditions discharged successfully
```

To verify all chapters:

```bash
for ch in ch02-getting-started ch04-divide-conquer ch06-heapsort ch07-quicksort \
          ch08-linear-sorting ch10-elementary-ds ch11-hash-tables ch12-bst \
          ch15-dynamic-programming ch16-greedy ch21-disjoint-sets \
          ch22-elementary-graph ch23-mst ch24-sssp ch25-apsp ch26-max-flow \
          ch31-number-theory ch32-string-matching ch33-comp-geometry ch35-approximation; do
  echo "=== $ch ==="
  cp intree-tests/${ch}/Test.*.fst autoclrs/${ch}/ 2>/dev/null
  (cd autoclrs/${ch} && rm -rf _cache .depend && make verify) || echo "FAILED: $ch"
done
```

**Note**: ch09 and ch13 have upstream build errors in AutoCLRS and cannot currently be verified.

### Known Limitations

1. **SZ.fits refinement on implicit args**: Heapsort's Pulse implementation has a `SZ.fits` refinement on an erased implicit parameter that cannot be satisfied from test code (Pulse emits subtyping checks as isolated SMT queries). Workaround: pure spec test.

2. **BoundedIntegers bridge**: Sorting algorithms using `CLRS.Common.SortSpec.sorted` require bridging BoundedIntegers typeclass operators to `Prims` operators for Z3. See the `std_sort3` / `completeness_sort3` pattern.

3. **Error 310 in ch23/ch24**: Some test files reference modules not in the chapter's include path.

4. **Upstream build errors**: ch09 (`Quickselect.Impl.fst` Error 47) and ch13 (`RBTree.Impl.fsti` Error 189) fail to build in the upstream AutoCLRS repo itself.

## References

- [Lahiri, "Evaluating LLM-driven User-Intent Formalization for Verification-Aware Languages", FMCAD 2024](https://arxiv.org/abs/2406.09757)
- [AutoCLRS: Verified CLRS Algorithms in F*](https://github.com/FStarLang/AutoCLRS)
- [AutoCLRS Blog Post](https://risemsr.github.io/blog/2026-03-06-autoclrs/)
- [Intent Formalization Blog Post](https://risemsr.github.io/blog/2026-03-05-shuvendu-intent-formalization/)
