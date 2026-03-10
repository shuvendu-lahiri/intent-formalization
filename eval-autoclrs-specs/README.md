# Intent Formalization for AutoCLRS Algorithms

Symbolic testing of F* specifications from the
[AutoCLRS](https://github.com/FStarLang/AutoCLRS) repository — verified
implementations of 52 algorithms from *Introduction to Algorithms* (CLRS).

See the [Intent Formalization blog](https://risemsr.github.io/blog/2026-03-05-shuvendu-intent-formalization/) for an overview of the research direction.

Uses the **soundness and completeness testing** approach from:

> **Evaluating LLM-driven User-Intent Formalization for Verification-Aware Languages**
> *Shuvendu K. Lahiri*, FMCAD 2024.
> [https://arxiv.org/abs/2406.09757](https://arxiv.org/abs/2406.09757)
>
> Specifically, the **Appendix B** method for completeness checking.

## Method

Given a formal specification φ(x, y) and concrete test cases {(i₁, o₁), …, (iₙ, oₙ)}:

| Property | Question | F* Encoding |
|----------|----------|-------------|
| **Soundness** | Does φ hold on known-good I/O? | `Lemma (φ(input, output))` |
| **Completeness** (Appendix B) | Does φ uniquely determine the output? | `Lemma (requires x = i ∧ φ(x,y)) (ensures y = o)` |

A specification that is **sound but incomplete** accepts the correct output but also
admits wrong outputs (e.g., "sorted" without "permutation" for sorting).

### Workflow

1. **Generate** — Python produces standalone F* modules encoding the spec + concrete test I/O
2. **Verify** — Each module is checked by F* (via Z3) in WSL
3. **Report** — "All verification conditions discharged" → PASS; otherwise → FAIL

No AI/LLM is used in the evaluation pipeline — only deterministic Python code generation
and the F* verifier.

## AutoCLRS Snapshot

Specifications evaluated against AutoCLRS at commit
[`1984af1`](https://github.com/FStarLang/AutoCLRS/tree/1984af1a9e22c74709293060e649054969f10c2d)
(March 2026). See the [AutoCLRS blog post](https://risemsr.github.io/blog/2026-03-06-autoclrs/)
for details on the verified CLRS algorithms.

## Evaluation Results

52 algorithms evaluated across 23 CLRS chapters. Each has 3 test cases for
soundness and completeness.

**Summary: 52/52 SOUND, 30/52 COMPLETE**

| # | Algorithm | CLRS Ch | Specification φ(x,y) | Soundness | Completeness | Notes |
|---|-----------|---------|----------------------|-----------|--------------|-------|
| 1 | Insertion Sort | Ch02 | sorted(y) ∧ permutation(x,y) | ✅ 3/3 | ✅ 3/3 | [tests](agent/algorithms.py#L53) · [soundness](agent/algorithms.py#L60) · [completeness](agent/algorithms.py#L95) |
| 2 | Merge Sort | Ch02 | sorted(y) ∧ permutation(x,y) | ✅ 3/3 | ✅ 3/3 | [tests](agent/algorithms.py#L53) · [soundness](agent/algorithms.py#L60) · [completeness](agent/algorithms.py#L95) |
| 3 | Heap Sort | Ch06 | sorted(y) ∧ permutation(x,y) | ✅ 3/3 | ✅ 3/3 | [tests](agent/algorithms.py#L53) · [soundness](agent/algorithms.py#L60) · [completeness](agent/algorithms.py#L95) |
| 4 | Quick Sort | Ch07 | sorted(y) ∧ permutation(x,y) | ✅ 3/3 | ✅ 3/3 | [tests](agent/algorithms.py#L53) · [soundness](agent/algorithms.py#L60) · [completeness](agent/algorithms.py#L95) |
| 5 | Counting Sort | Ch08 | sorted(y) ∧ perm(x,y) ∧ in_range | ✅ 3/3 | ✅ 3/3 | [tests](agent/algorithms.py#L625) · [soundness](agent/algorithms.py#L632) · [completeness](agent/algorithms.py#L676) |
| 6 | Binary Search | Ch04 | found⇒arr[i]=key ∧ ¬found⇒key∉arr | ✅ 3/3 | ⚠️ 2/3 | **Genuinely incomplete** — spec allows any `r < 0` for not-found · [tests](agent/algorithms.py#L207) · [soundness](agent/algorithms.py#L214) · [completeness](agent/algorithms.py#L250) |
| 7 | GCD | Ch31 | divides(g,a) ∧ divides(g,b) ∧ greatest | ✅ 3/3 | ✅ 3/3 | [tests](agent/algorithms.py#L155) · [soundness](agent/algorithms.py#L162) · [completeness](agent/algorithms.py#L181) |
| 8 | Max Subarray | Ch04 | ∃lo,hi. sum(arr[lo..hi])=r ∧ maximal | ✅ 3/3 | ✅ 3/3 | [tests](agent/algorithms.py#L307) · [soundness](agent/algorithms.py#L314) · [completeness](agent/algorithms.py#L365) |
| 9 | Modular Exp | Ch31 | result = b^e mod m ∧ 0 ≤ result < m | ✅ 3/3 | ✅ 3/3 | [tests](agent/algorithms.py#L422) · [soundness](agent/algorithms.py#L429) · [completeness](agent/algorithms.py#L445) |
| 10 | Cross Product | Ch33 | r = (p2−p1) × (p3−p1) | ✅ 3/3 | ✅ 3/3 | [tests](agent/algorithms.py#L474) · [soundness](agent/algorithms.py#L481) · [completeness](agent/algorithms.py#L497) |
| 11 | Segment Intersection | Ch33 | orientation-based intersection test | ✅ 3/3 | ✅ 3/3 | [tests](agent/algorithms.py#L529) · [soundness](agent/algorithms.py#L539) · [completeness](agent/algorithms.py#L576) |
| 12 | Stack (push/pop) | Ch10 | pop(push(s,x)) = (x, s) | ✅ 3/3 | ✅ 3/3 | [tests](agent/algorithms.py#L744) · [soundness](agent/algorithms.py#L752) · [completeness](agent/algorithms.py#L780) |
| 13 | Queue (enq/deq) | Ch10 | dequeue returns FIFO order | ✅ 3/3 | ✅ 3/3 | [tests](agent/algorithms.py#L817) · [soundness](agent/algorithms.py#L824) · [completeness](agent/algorithms.py#L853) |
| 14 | Topological Sort | Ch22 | valid topo order ∧ all_distinct | ✅ 3/3 | ❌ 0/3 | **Genuinely incomplete** — multiple valid orderings · [tests](agent/algorithms.py#L889) · [soundness](agent/algorithms.py#L899) · [completeness](agent/algorithms.py#L963) |
| 15 | LCS Length | Ch15 | r = lcs_length(x, y, \|x\|, \|y\|) | ✅ 3/3 | ✅ 3/3 | [tests](agent/algorithms.py#L1030) · [soundness](agent/algorithms.py#L1037) · [completeness](agent/algorithms.py#L1072) |
| 16 | String Matching | Ch32 | count_matches(text, pattern) = r | ✅ 3/3 | ✅ 3/3 | [tests](agent/algorithms.py#L1120) · [soundness](agent/algorithms.py#L1127) · [completeness](agent/algorithms.py#L1166) |
| 17 | Radix Sort | Ch08 | sorted(y) ∧ permutation(x,y) | ✅ 3/3 | ✅ 3/3 | Reuses sorting spec · [tests](agent/algorithms.py#L53) |
| 18 | Bucket Sort | Ch08 | sorted(y) ∧ permutation(x,y) | ✅ 3/3 | ✅ 3/3 | Reuses sorting spec · [tests](agent/algorithms.py#L53) |
| 19 | Minimum | Ch09 | m = min(arr) ∧ m ∈ arr | ✅ 3/3 | ✅ 3/3 | [tests](agent/algorithms.py#L1220) · [soundness](agent/algorithms.py#L1227) · [completeness](agent/algorithms.py#L1249) |
| 20 | Maximum | Ch09 | m = max(arr) ∧ m ∈ arr | ✅ 3/3 | ✅ 3/3 | [tests](agent/algorithms.py#L1282) · [soundness](agent/algorithms.py#L1289) · [completeness](agent/algorithms.py#L1310) |
| 21 | Min-Max | Ch09 | min ∧ max simultaneously | ✅ 3/3 | ✅ 3/3 | [tests](agent/algorithms.py#L1343) · [soundness](agent/algorithms.py#L1350) · [completeness](agent/algorithms.py#L1372) |
| 22 | Quickselect | Ch09 | kth smallest element | ✅ 3/3 | ❌ 0/3 | **Genuinely incomplete** — count-based spec doesn't pin output · [tests](agent/algorithms.py#L1403) · [soundness](agent/algorithms.py#L1410) · [completeness](agent/algorithms.py#L1433) |
| 23 | Extended GCD | Ch31 | gcd(a,b) = g ∧ a·x + b·y = g | ✅ 3/3 | ✅ 3/3 | [tests](agent/algorithms.py#L1466) · [soundness](agent/algorithms.py#L1473) · [completeness](agent/algorithms.py#L1490) |
| 24 | Matrix Multiply | Ch04 | C[i,j] = dot_product(A_row_i, B_col_j) | ✅ 3/3 | ❌ 0/3 | Z3 can't prove uniqueness · [tests](agent/algorithms.py#L1519) · [soundness](agent/algorithms.py#L1526) · [completeness](agent/algorithms.py#L1568) |
| 25 | Partition (Lomuto) | Ch07 | elements ≤ pivot before, > pivot after | ✅ 3/3 | ❌ 0/3 | **Genuinely incomplete** — multiple valid partitions · [tests](agent/algorithms.py#L1621) · [soundness](agent/algorithms.py#L1631) · [completeness](agent/algorithms.py#L1669) |
| 26 | Linked List Insert | Ch10 | head = new_elem ∧ tail = old_list | ✅ 3/3 | ✅ 3/3 | [tests](agent/algorithms.py#L1710) · [soundness](agent/algorithms.py#L1717) · [completeness](agent/algorithms.py#L1738) |
| 27 | Linked List Delete | Ch10 | element removed, rest preserved | ✅ 3/3 | ✅ 3/3 | [tests](agent/algorithms.py#L1765) · [soundness](agent/algorithms.py#L1772) · [completeness](agent/algorithms.py#L1801) |
| 28 | Hash Table | Ch11 | insert/lookup by key mod table_size | ✅ 3/3 | ✅ 3/3 | [tests](agent/algorithms.py#L1835) · [soundness](agent/algorithms.py#L1842) · [completeness](agent/algorithms.py#L1864) |
| 29 | BST Search | Ch12 | found ⇒ key in tree, ¬found ⇒ key ∉ tree | ✅ 3/3 | ✅ 3/3 | [tests](agent/algorithms.py#L1892) · [soundness](agent/algorithms.py#L1899) · [completeness](agent/algorithms.py#L1943) |
| 30 | BST Inorder | Ch12 | result = sorted keys from BST | ✅ 3/3 | ✅ 3/3 | [tests](agent/algorithms.py#L1990) · [soundness](agent/algorithms.py#L1997) · [completeness](agent/algorithms.py#L2037) |
| 31 | Rod Cutting | Ch15 | revenue ≥ each piece price | ✅ 3/3 | ❌ 0/3 | **Genuinely incomplete** — spec doesn't force optimality · [tests](agent/algorithms.py#L2081) · [soundness](agent/algorithms.py#L2088) · [completeness](agent/algorithms.py#L2120) |
| 32 | BFS Distance | Ch22 | shortest unweighted path distance | ✅ 3/3 | ❌ 0/3 | Z3 can't prove uniqueness · [tests](agent/algorithms.py#L2148) · [soundness](agent/algorithms.py#L2155) · [completeness](agent/algorithms.py#L2196) |
| 33 | DFS Times | Ch22 | d[v] < f[v] ∧ parenthesis theorem | ✅ 3/3 | ❌ 0/3 | **Genuinely incomplete** — timestamps depend on traversal order · [tests](agent/algorithms.py#L2581) · [soundness](agent/algorithms.py#L2591) · [completeness](agent/algorithms.py#L2625) |
| 34 | Dijkstra | Ch24 | dist[v] ≤ dist[u] + w(u,v) ∧ reachable | ✅ 3/3 | ❌ 0/3 | **Genuinely incomplete** — triangle inequality doesn't pin distances · [tests](agent/algorithms.py#L2240) · [soundness](agent/algorithms.py#L2249) · [completeness](agent/algorithms.py#L2295) |
| 35 | Bellman-Ford | Ch24 | dist[v] ≤ dist[u] + w(u,v) ∧ reachable | ✅ 3/3 | ❌ 0/3 | **Genuinely incomplete** — same as Dijkstra · [tests](agent/algorithms.py#L2328) · [soundness](agent/algorithms.py#L2335) · [completeness](agent/algorithms.py#L2376) |
| 36 | Floyd-Warshall | Ch25 | all-pairs shortest ∧ triangle inequality | ✅ 3/3 | ❌ 0/3 | **Genuinely incomplete** — triangle inequality necessary but not sufficient · [tests](agent/algorithms.py#L2407) · [soundness](agent/algorithms.py#L2415) · [completeness](agent/algorithms.py#L2460) |
| 37 | Activity Selection | Ch16 | max compatible non-overlapping activities | ✅ 3/3 | ✅ 3/3 | [tests](agent/algorithms.py#L2498) · [soundness](agent/algorithms.py#L2505) · [completeness](agent/algorithms.py#L2549) |
| 38 | KMP String Match | Ch32 | count_matches(text, pattern) = r | ✅ 3/3 | ✅ 3/3 | [tests](agent/algorithms.py#L1120) · [soundness](agent/algorithms.py#L1127) · [completeness](agent/algorithms.py#L1166) |
| 39 | Rabin-Karp | Ch32 | count_matches(text, pattern) = r | ✅ 3/3 | ✅ 3/3 | [tests](agent/algorithms.py#L1120) · [soundness](agent/algorithms.py#L1127) · [completeness](agent/algorithms.py#L1166) |
| 40 | BST Insert | Ch12 | sorted inorder ∧ contains new key | ✅ 3/3 | ❌ 0/3 | **Genuinely incomplete** · [tests](agent/algorithms.py#L2652) · [soundness](agent/algorithms.py#L2664) · [completeness](agent/algorithms.py#L2700) |
| 41 | BST Delete | Ch12 | sorted inorder ∧ key removed | ✅ 3/3 | ❌ 0/3 | **Genuinely incomplete** · [tests](agent/algorithms.py#L2732) · [soundness](agent/algorithms.py#L2739) · [completeness](agent/algorithms.py#L2774) |
| 42 | Matrix Chain | Ch15 | min scalar multiplications | ✅ 3/3 | ✅ 3/3 | [tests](agent/algorithms.py#L2808) · [soundness](agent/algorithms.py#L2815) · [completeness](agent/algorithms.py#L2849) |
| 43 | Huffman Coding | Ch16 | cost ≥ 0 (weak spec) | ✅ 3/3 | ❌ 0/3 | **Weak spec** · [tests](agent/algorithms.py#L2887) · [soundness](agent/algorithms.py#L2894) · [completeness](agent/algorithms.py#L2916) |
| 44 | DAG Shortest Paths | Ch24 | triangle inequality on DAG | ✅ 3/3 | ❌ 0/3 | Same as Dijkstra · [tests](agent/algorithms.py#L2944) · [soundness](agent/algorithms.py#L2951) · [completeness](agent/algorithms.py#L2986) |
| 45 | Kruskal MST | Ch23 | MST weight ≥ 0 (weak spec) | ✅ 3/3 | ❌ 0/3 | **Weak spec** · [tests](agent/algorithms.py#L3024) · [soundness](agent/algorithms.py#L3031) · [completeness](agent/algorithms.py#L3048) |
| 46 | Prim MST | Ch23 | MST weight ≥ 0 (weak spec) | ✅ 3/3 | ❌ 0/3 | **Weak spec** · [tests](agent/algorithms.py#L3070) · [soundness](agent/algorithms.py#L3077) · [completeness](agent/algorithms.py#L3094) |
| 47 | Union-Find | Ch21 | connected(u,v) matches union ops | ✅ 3/3 | ✅ 3/3 | [tests](agent/algorithms.py#L3116) · [soundness](agent/algorithms.py#L3123) · [completeness](agent/algorithms.py#L3183) |
| 48 | Primality Test | Ch31 | is_prime(n) = deterministic check | ✅ 3/3 | ✅ 3/3 | [tests](agent/algorithms.py#L3204) · [soundness](agent/algorithms.py#L3211) · [completeness](agent/algorithms.py#L3240) |
| 49 | Graham Scan | Ch33 | hull_size bounds (weak spec) | ✅ 3/3 | ⚠️ 1/3 | **Weak spec** · [tests](agent/algorithms.py#L3272) · [soundness](agent/algorithms.py#L3279) · [completeness](agent/algorithms.py#L3297) |
| 50 | Edmonds-Karp | Ch26 | max flow ≥ 0 ∧ capacities ≥ 0 | ✅ 3/3 | ❌ 0/3 | **Weak spec** · [tests](agent/algorithms.py#L3319) · [soundness](agent/algorithms.py#L3326) · [completeness](agent/algorithms.py#L3355) |
| 51 | Vertex Cover | Ch35 | cover_size ≤ n (weak spec) | ✅ 3/3 | ❌ 0/3 | **Weak spec** · [tests](agent/algorithms.py#L3377) · [soundness](agent/algorithms.py#L3384) · [completeness](agent/algorithms.py#L3401) |
| 52 | Partial Select Sort | Ch09 | k elements sorted | ✅ 3/3 | ❌ 0/3 | **Genuinely incomplete** · [tests](agent/algorithms.py#L3423) · [soundness](agent/algorithms.py#L3430) · [completeness](agent/algorithms.py#L3458) |

### Incompleteness Analysis

| Category | Count | Algorithms | Explanation |
|----------|-------|-----------|-------------|
| **Non-deterministic output** | 7 | Topo Sort, DFS, Partition, BST Insert/Delete, Quickselect, Partial Select | Multiple valid outputs exist for a given input |
| **Weak spec (genuine bug)** | 2 | Binary Search, Rod Cutting | Spec is too permissive |
| **Relational spec insufficient** | 4 | Dijkstra, Bellman-Ford, Floyd-Warshall, DAG SP | Triangle inequality necessary but not sufficient |
| **Weak spec (minimal)** | 6 | Huffman, Kruskal, Prim, Convex Hull, Max Flow, Vertex Cover | Only encodes bounds, not full property |
| **Z3 limitation** | 2 | Matrix Multiply, BFS Distance | Spec likely complete but Z3 can't prove |

## Reproducing Results

### Prerequisites

- Windows with WSL (Ubuntu 24.04) — or native Linux
- Python 3.10+
- F* verifier and Z3 solver built inside WSL

### Setup

```bash
# 1. Install WSL Ubuntu and OCaml toolchain
wsl --install -d Ubuntu
wsl -d Ubuntu -- bash -c "sudo apt-get update && sudo apt-get install -y \
  opam git make pkg-config libgmp-dev"

# 2. Install Z3 4.13.3
wsl -d Ubuntu -- bash -c "
  wget https://github.com/Z3Prover/z3/releases/download/z3-4.13.3/z3-4.13.3-x64-glibc-2.35.zip
  unzip z3-4.13.3-x64-glibc-2.35.zip
  sudo cp z3-4.13.3-x64-glibc-2.35/bin/z3 /usr/local/bin/z3-4.13.3
"

# 3. Clone and build F* from AutoCLRS snapshot
wsl -d Ubuntu -- bash -c "
  cd ~ && git clone --recurse-submodules https://github.com/FStarLang/AutoCLRS.git
  cd AutoCLRS && git checkout 1984af1a9e22c74709293060e649054969f10c2d
  cd fstar && opam init -y && eval \$(opam env)
  opam install --yes ocamlfind batteries stdint zarith yojson fileutils \
    pprint menhir sedlex ppxlib process ppx_deriving ppx_deriving_yojson
  make -j4 -C src/ocaml-output
  make -j4 -C ulib
"
```

### Run

```bash
# All 52 algorithms with 60-second per-test timeout
python agent/run_eval.py --all-algorithms --per-test-timeout 60

# Single algorithm
python agent/run_eval.py --algorithm insertion_sort

# All spec variants for one algorithm
python agent/run_eval.py --algorithm gcd --all-variants
```

### CLI Options

| Flag | Description |
|------|-------------|
| `--algorithm NAME` | Run a single algorithm (default: insertion_sort) |
| `--all-algorithms` | Run all 52 registered algorithms |
| `--spec-variant V` | Evaluate a specific spec variant (default: full) |
| `--all-variants` | Evaluate all spec variants |
| `--per-test-timeout N` | Skip tests exceeding N seconds (default: 60) |
| `--max-tests N` | Limit number of test cases per algorithm |

## How It Works

For each algorithm, `agent/algorithms.py` contains:

1. **Test cases** — 3 small concrete I/O pairs (e.g., `[3,1,2] → [1,2,3]` for sorting)
2. **Soundness generator** — produces an F* module asserting the spec holds on concrete I/O
3. **Completeness generator** — produces an F* module asserting the spec uniquely determines output

`agent/run_eval.py` orchestrates: generate F* → invoke verifier via WSL → collect results.

### Example: Sorting Soundness

```fstar
module IntentEval.InsertionSort.Soundness.Test0
open FStar.Seq
module Seq = FStar.Seq

let input  = Seq.seq_of_list [3; 1; 2]
let output = Seq.seq_of_list [1; 2; 3]

// Spec: sorted ∧ permutation
let soundness_test () : Lemma
  (is_sorted output /\ is_permutation input output)
= ()   // F* + Z3 discharge this automatically
```

### Example: Sorting Completeness (Appendix B)

```fstar
module IntentEval.InsertionSort.Completeness.Test0

let completeness_test (y: Seq.seq int) : Lemma
  (requires is_sorted y /\ is_permutation (Seq.seq_of_list [3; 1; 2]) y)
  (ensures  y == Seq.seq_of_list [1; 2; 3])
= ()   // If F* verifies this, the spec uniquely determines the output
```

## References

- [Lahiri, "Evaluating LLM-driven User-Intent Formalization for Verification-Aware Languages", FMCAD 2024](https://arxiv.org/abs/2406.09757)
- [AutoCLRS: Verified CLRS Algorithms in F*](https://github.com/FStarLang/AutoCLRS)
- [AutoCLRS Blog Post](https://risemsr.github.io/blog/2026-03-06-autoclrs/)
- [Intent Formalization Blog Post](https://risemsr.github.io/blog/2026-03-05-shuvendu-intent-formalization/)
