# Intent Formalization Agent

Evaluates the quality of formal specifications using **symbolic testing** from the
[FMCAD 2024 paper](https://arxiv.org/abs/2406.09757) (Lahiri et al.).
Targets F* specifications from the [AutoCLRS](https://github.com/FStarLang/AutoCLRS) repository —
verified implementations of algorithms from *Introduction to Algorithms* (CLRS).

## What It Does

Given a formal specification φ(x, y) and concrete test cases {(i₁, o₁), …, (iₙ, oₙ)},
the agent evaluates two properties:

| Property | Question | F* Encoding |
|----------|----------|-------------|
| **Soundness** | Does φ hold on known-good I/O? | `Lemma (φ(input, expected))` |
| **Completeness** ([Appendix B](https://arxiv.org/abs/2406.09757)) | Does φ uniquely determine the output? | `Lemma (requires φ(input, y)) (ensures y == expected)` |

A specification that is **sound but incomplete** accepts the correct output but also admits
wrong outputs (e.g., "sorted" without "permutation" for sorting).

## Approach: In-Tree F* Tests

Test files are placed **directly in AutoCLRS chapter directories** and verified using
the same `make verify` build system. This ensures:

- **Faithful spec evaluation** — tests import and call the exact AutoCLRS specifications
- **No override/copy mechanisms** — the build system handles all dependencies
- **`friend` declarations** for modules with abstract `.fsti` interfaces (e.g., `ShortestPath.Inf`)

## Evaluation Results — 46 Algorithms Verified ✅

**202 total assertions**: 146 soundness + 56 completeness across 22 chapters.

| # | Algorithm | Ch | Test File | Sound | Complete | Notes |
|---|-----------|-----|-----------|-------|----------|-------|
| 1 | InsertionSort | ch02 | [Test.InsertionSort.fst](eval-autoclrs-specs/intree-tests/ch02-getting-started/Test.InsertionSort.fst) | ✅ 3 | ✅ 3 | sorted + permutation |
| 2 | MergeSort | ch02 | [Test.MergeSort.fst](eval-autoclrs-specs/intree-tests/ch02-getting-started/Test.MergeSort.fst) | ✅ 4 | ✅ 2 | seq_merge on 1-element seqs |
| 3 | MaxSubarray (Kadane) | ch04 | [Test.MaxSubarray.fst](eval-autoclrs-specs/intree-tests/ch04-divide-conquer/Test.MaxSubarray.fst) | ✅ 4 | ✅ 2 | max contiguous sum |
| 4 | BinarySearch | ch04 | [Test.BinarySearch.fst](eval-autoclrs-specs/intree-tests/ch04-divide-conquer/Test.BinarySearch.fst) | ✅ 3 | ✅ 2 | found/not-found |
| 5 | MatrixMultiply | ch04 | [Test.MatrixMultiply.fst](eval-autoclrs-specs/intree-tests/ch04-divide-conquer/Test.MatrixMultiply.fst) | ✅ 3 | ✅ 1 | dot product spec |
| 6 | Heap (Heapsort) | ch06 | [Test.Heap.fst](eval-autoclrs-specs/intree-tests/ch06-heapsort/Test.Heap.fst) | ✅ 3 | ✅ 1 | max-heap + swap |
| 7 | Quicksort | ch07 | [Test.Quicksort.fst](eval-autoclrs-specs/intree-tests/ch07-quicksort/Test.Quicksort.fst) | ✅ 2 | ✅ 1 | friend for Complexity |
| 8 | CountingSort | ch08 | [Test.CountingSort.fst](eval-autoclrs-specs/intree-tests/ch08-linear-sorting/Test.CountingSort.fst) | ✅ 3 | ✅ 1 | stable sort in range |
| 9 | BucketSort | ch08 | [Test.BucketSort.fst](eval-autoclrs-specs/intree-tests/ch08-linear-sorting/Test.BucketSort.fst) | ✅ 3 | ✅ 1 | bucket distribution |
| 10 | RadixSort | ch08 | [Test.RadixSort.fst](eval-autoclrs-specs/intree-tests/ch08-linear-sorting/Test.RadixSort.fst) | ✅ 3 | ✅ 1 | digit-wise sort |
| 11 | MinMax | ch09 | [Test.MinMax.fst](eval-autoclrs-specs/intree-tests/ch09-order-statistics/Test.MinMax.fst) | ✅ 3 | ✅ 1 | min/max of array |
| 12 | SimultaneousMinMax | ch09 | [Test.SimultaneousMinMax.fst](eval-autoclrs-specs/intree-tests/ch09-order-statistics/Test.SimultaneousMinMax.fst) | ✅ 3 | ✅ 1 | pair comparison |
| 13 | PartialSelectionSort | ch09 | [Test.PartialSelectionSort.fst](eval-autoclrs-specs/intree-tests/ch09-order-statistics/Test.PartialSelectionSort.fst) | ✅ 2 | ✅ 1 | is_sorted on result |
| 14 | Quickselect | ch09 | [Test.Quickselect.fst](eval-autoclrs-specs/intree-tests/ch09-order-statistics/Test.Quickselect.fst) | ✅ 3 | ✅ 1 | kth element |
| 15 | Stack | ch10 | [Test.Stack.fst](eval-autoclrs-specs/intree-tests/ch10-elementary-ds/Test.Stack.fst) | ✅ 3 | ✅ 1 | push/pop/empty |
| 16 | Queue | ch10 | [Test.Queue.fst](eval-autoclrs-specs/intree-tests/ch10-elementary-ds/Test.Queue.fst) | ✅ 3 | ✅ 1 | enqueue/dequeue FIFO |
| 17 | Singly Linked List | ch10 | [Test.SLL.fst](eval-autoclrs-specs/intree-tests/ch10-elementary-ds/Test.SLL.fst) | ✅ 3 | ✅ 1 | insert/search/length |
| 18 | Doubly Linked List | ch10 | [Test.DLL.fst](eval-autoclrs-specs/intree-tests/ch10-elementary-ds/Test.DLL.fst) | ✅ 3 | ✅ 1 | insert/delete |
| 19 | HashTable | ch11 | [Test.HashTable.fst](eval-autoclrs-specs/intree-tests/ch11-hash-tables/Test.HashTable.fst) | ✅ 3 | ✅ 1 | hash chain insert/search |
| 20 | BST | ch12 | [Test.BST.fst](eval-autoclrs-specs/intree-tests/ch12-bst/Test.BST.fst) | ✅ 7 | ✅ 2 | search/insert/delete/inorder |
| 21 | BSTArray | ch12 | [Test.BSTArray.fst](eval-autoclrs-specs/intree-tests/ch12-bst/Test.BSTArray.fst) | ✅ 2 | ✅ 1 | ⚠️ base cases only (norm-limited) |
| 22 | LCS | ch15 | [Test.LCS.fst](eval-autoclrs-specs/intree-tests/ch15-dynamic-programming/Test.LCS.fst) | ✅ 3 | ✅ 1 | longest common subseq |
| 23 | MatrixChain | ch15 | [Test.MatrixChain.fst](eval-autoclrs-specs/intree-tests/ch15-dynamic-programming/Test.MatrixChain.fst) | ✅ 1 | ✅ 1 | ⚠️ mc_inner_k only (norm-limited) |
| 24 | RodCutting | ch15 | [Test.RodCutting.fst](eval-autoclrs-specs/intree-tests/ch15-dynamic-programming/Test.RodCutting.fst) | ✅ 4 | ✅ 2 | optimal revenue DP |
| 25 | ActivitySelection | ch16 | [Test.ActivitySelection.fst](eval-autoclrs-specs/intree-tests/ch16-greedy/Test.ActivitySelection.fst) | ✅ 3 | ✅ 1 | greedy compatible set |
| 26 | Huffman | ch16 | [Test.Huffman.fst](eval-autoclrs-specs/intree-tests/ch16-greedy/Test.Huffman.fst) | ✅ 3 | ✅ 1 | encoding tree build |
| 27 | UnionFind | ch21 | [Test.UnionFind.fst](eval-autoclrs-specs/intree-tests/ch21-disjoint-sets/Test.UnionFind.fst) | ✅ 3 | ✅ 1 | ⚠️ find only (norm-limited) |
| 28 | BFS | ch22 | [Test.BFS.fst](eval-autoclrs-specs/intree-tests/ch22-elementary-graph/Test.BFS.fst) | ✅ 3 | ✅ 1 | init state + enqueue |
| 29 | DFS | ch22 | [Test.DFS.fst](eval-autoclrs-specs/intree-tests/ch22-elementary-graph/Test.DFS.fst) | ✅ 4 | ✅ 1 | discover/color/time |
| 30 | TopologicalSort | ch22 | [Test.TopologicalSort.fst](eval-autoclrs-specs/intree-tests/ch22-elementary-graph/Test.TopologicalSort.fst) | ✅ 4 | ✅ 1 | has_edge predicate |
| 31 | Kruskal | ch23 | [Test.Kruskal.fst](eval-autoclrs-specs/intree-tests/ch23-mst/Test.Kruskal.fst) | ✅ 3 | ✅ 1 | MST edge spec |
| 32 | Prim | ch23 | [Test.Prim.fst](eval-autoclrs-specs/intree-tests/ch23-mst/Test.Prim.fst) | ✅ 3 | ✅ 1 | friend for Prim.Spec |
| 33 | Dijkstra | ch24 | [Test.Dijkstra.fst](eval-autoclrs-specs/intree-tests/ch24-sssp/Test.Dijkstra.fst) | ✅ 3 | ✅ 1 | friend for ShortestPath.Inf |
| 34 | BellmanFord | ch24 | [Test.BellmanFord.fst](eval-autoclrs-specs/intree-tests/ch24-sssp/Test.BellmanFord.fst) | ✅ 3 | ✅ 1 | friend for ShortestPath.Inf |
| 35 | FloydWarshall | ch25 | [Test.FloydWarshall.fst](eval-autoclrs-specs/intree-tests/ch25-apsp/Test.FloydWarshall.fst) | ✅ 5 | ✅ 1 | APSP distance matrix |
| 36 | MaxFlow | ch26 | [Test.MaxFlow.fst](eval-autoclrs-specs/intree-tests/ch26-max-flow/Test.MaxFlow.fst) | ✅ 3 | ✅ 1 | residual capacity |
| 37 | GCD | ch31 | [Test.GCD.fst](eval-autoclrs-specs/intree-tests/ch31-number-theory/Test.GCD.fst) | ✅ 3 | ✅ 3 | Euclidean GCD |
| 38 | ModExp | ch31 | [Test.ModExp.fst](eval-autoclrs-specs/intree-tests/ch31-number-theory/Test.ModExp.fst) | ✅ 3 | ✅ 2 | modular exponentiation |
| 39 | ExtendedGCD | ch31 | [Test.ExtendedGCD.fst](eval-autoclrs-specs/intree-tests/ch31-number-theory/Test.ExtendedGCD.fst) | ✅ 3 | ✅ 1 | Bézout coefficients |
| 40 | NaiveStringMatch | ch32 | [Test.NaiveStringMatch.fst](eval-autoclrs-specs/intree-tests/ch32-string-matching/Test.NaiveStringMatch.fst) | ✅ 3 | ✅ 1 | brute-force matching |
| 41 | RabinKarp | ch32 | [Test.RabinKarp.fst](eval-autoclrs-specs/intree-tests/ch32-string-matching/Test.RabinKarp.fst) | ✅ 3 | ✅ 1 | hash-based matching |
| 42 | KMP | ch32 | [Test.KMP.fst](eval-autoclrs-specs/intree-tests/ch32-string-matching/Test.KMP.fst) | ✅ 3 | ✅ 1 | failure function |
| 43 | Segments | ch33 | [Test.Segments.fst](eval-autoclrs-specs/intree-tests/ch33-comp-geometry/Test.Segments.fst) | ✅ 3 | ✅ 1 | cross product/intersection |
| 44 | GrahamScan | ch33 | [Test.GrahamScan.fst](eval-autoclrs-specs/intree-tests/ch33-comp-geometry/Test.GrahamScan.fst) | ✅ 3 | ✅ 1 | convex hull |
| 45 | JarvisMarch | ch33 | [Test.JarvisMarch.fst](eval-autoclrs-specs/intree-tests/ch33-comp-geometry/Test.JarvisMarch.fst) | ✅ 3 | ✅ 1 | gift wrapping |
| 46 | VertexCover | ch35 | [Test.VertexCover.fst](eval-autoclrs-specs/intree-tests/ch35-approximation/Test.VertexCover.fst) | ✅ 5 | ✅ 1 | approx cover |
| — | RBTree | ch13 | [Test.RBTree.fst](eval-autoclrs-specs/intree-tests/ch13-rbtree/Test.RBTree.fst) | ⛔ | ⛔ | Pre-existing AutoCLRS build error |

### Summary

- **46/47 algorithms verified** — all soundness and completeness tests pass
- **1 skipped** — RBTree has a pre-existing type error in the AutoCLRS `.fsti` file
- **3 normalization-limited** — BSTArray, MatrixChain, UnionFind test only base/simple cases
- **Verification log**: [`eval-autoclrs-specs/verification-log.txt`](eval-autoclrs-specs/verification-log.txt) — F* output from `make verify` across all 21 chapters (48 files)

### Technical Patterns

| Pattern | When Used | Example |
|---------|-----------|---------|
| `assert_norm (f x == y)` | Pure computation on concrete inputs | `assert_norm (gcd 12 8 == 4)` |
| `Lemma (requires φ) (ensures y == o)` | Completeness: spec uniquely determines output | `test_complete_1` in InsertionSort |
| `friend ModuleName` | Abstract `.fsti` functions | Dijkstra (`friend CLRS.Ch24.ShortestPath.Inf`) |
| `reveal_opaque` | Opaque-to-SMT predicates | `permutation` in SortSpec |
| `open Pulse.Lib.BoundedIntegers` | Sorting tests need `<=` | InsertionSort, MergeSort |

## Quick Start

### Prerequisites

- Windows with WSL (Ubuntu 24.04)
- F*, Pulse, and Z3 built inside WSL (see AutoCLRS build instructions)

### Run Verification

```bash
# Copy test files into AutoCLRS and verify
cp -r eval-autoclrs-specs/intree-tests/ch*/ ~/AutoCLRS/autoclrs/

# Verify a single chapter
cd ~/AutoCLRS/autoclrs/ch31-number-theory
make verify

# Verify all chapters
for ch in ~/AutoCLRS/autoclrs/ch*/; do
  echo "=== $ch ==="
  cd "$ch" && make verify && cd -
done
```

## Architecture

```
eval-autoclrs-specs/
  intree-tests/                     # F* test files (46 algorithms)
    ch02-getting-started/
      Test.InsertionSort.fst        # In-tree test file
      Test.MergeSort.fst
    ch24-sssp/
      Test.Dijkstra.fst             # Uses friend for abstract ShortestPath.Inf
      Test.Dijkstra.fsti            # Empty .fsti required for friend mechanism
      Test.BellmanFord.fst
      Test.BellmanFord.fsti
    ...
AutoCLRS/                           # Git submodule: FStarLang/AutoCLRS
.github/
  copilot-instructions.md           # Project context for Copilot
  agents/fstar-spec-evaluator.agent.md  # Custom agent definition
```

## References

- [Lahiri et al., "Evaluating LLM-generated Formal Specifications", FMCAD 2024](https://arxiv.org/abs/2406.09757)
- [AutoCLRS: Verified CLRS Algorithms in F*](https://github.com/FStarLang/AutoCLRS)
- [Intent Formalization Blog Post](https://risemsr.github.io/blog/2026-03-05-shuvendu-intent-formalization/)
- [AutoCLRS Blog Post](https://risemsr.github.io/blog/2026-03-06-autoclrs/)
