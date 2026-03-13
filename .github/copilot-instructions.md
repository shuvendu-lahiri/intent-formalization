# Copilot Instructions — Intent Formalization Agent

## Project Overview
This repo evaluates F* formal specifications from the [AutoCLRS](https://github.com/FStarLang/AutoCLRS)
repository (52 CLRS algorithms) using **symbolic testing** from the
[FMCAD 2024 paper](https://arxiv.org/abs/2406.09757) (Lahiri et al.).

For each specification φ(x, y) and test case (input, expected_output):
- **Soundness**: Prove `φ(input, expected)` — the spec accepts the correct output
- **Completeness** (Appendix B): Prove `∀y. φ(input, y) ⟹ y == expected` — the spec uniquely determines the output

## Environment

- **F* verification runs in WSL** (Ubuntu). The F* binary is at
  `~/AutoCLRS/FStar/stage2/out/bin/fstar.exe` (add to `PATH`).
- The **WSL build copy** of AutoCLRS is at `/root/AutoCLRS/autoclrs/` — separate from the
  Windows submodule at `AutoCLRS/` in the repo root.
- Files created on Windows must be **copied to the WSL path** before F* can verify them.
- **Do NOT push to any repo outside this repo** without explicit permission.

## Repository Structure

- `AutoCLRS/` — Git submodule of FStarLang/AutoCLRS (F* specs + Pulse implementations)
- `eval-autoclrs-specs/intree-tests/ch*/` — F* test files (46 algorithms across 22 chapters)

## AutoCLRS Build System

Each chapter directory has a Makefile that auto-discovers all `.fst`/`.fsti` files.

```bash
# Copy test files into WSL AutoCLRS tree
cp /mnt/c/Users/Shuvendu/.../intree-tests/ch02-getting-started/*.fst \
   /root/AutoCLRS/autoclrs/ch02-getting-started/

# Verify all files in a chapter
cd ~/AutoCLRS/autoclrs/ch02-getting-started && make verify

# Verify a single test file
make _cache/Test.InsertionSort.fst.checked V=1

# Clear stale cache before re-verifying changed files
rm -f .depend _cache/Test.InsertionSort.fst.checked
```

## F* Verification Patterns

### Soundness (spec holds on concrete I/O)
```fstar
(* Transparent functions: plain proof or assert_norm *)
let test_sound () : Lemma (gcd_spec 12 8 == 4) = ()

(* Recursive specs needing normalizer *)
let test_sound () : Lemma (optimal_revenue prices 4 == 10) =
  assert_norm (optimal_revenue prices 4 == 10)

(* Sorting: requires reveal_opaque for permutation *)
let test_sound () : Lemma (sorted y /\ permutation x y) =
  reveal_opaque (`%permutation) (permutation x y)
```

### Completeness (Appendix B: spec implies output uniqueness)
```fstar
(* Prove that any y satisfying the spec must equal the expected output *)
let test_complete (y: Seq.seq int) : Lemma
  (requires sorted y /\ permutation input y)
  (ensures y == expected) =
  reveal_opaque (`%permutation) (permutation input y);
  (* ... step-by-step SMT guidance ... *)
  Seq.lemma_eq_elim y expected
```

This is fundamentally different from testing wrong outputs with `[@@expect_failure]`.
The completeness proof requires guiding the SMT solver through count unfolding,
membership derivation, and sorted-constraint instantiation.

### Common patterns
- `open Pulse.Lib.BoundedIntegers` **before** `CLRS.Common.SortSpec` — needed for correct `<=` on `int`
- `reveal_opaque (\`%permutation) (permutation x y)` — `permutation` is `[@@"opaque_to_smt"]`
- `friend ModuleName` + empty `.fsti` — for modules with abstract interfaces (e.g., `ShortestPath.Inf`)
- `open FStar.Mul` — when integer multiplication `*` is needed
- `=` returns `bool` in F*, `==` returns `prop`
- Keep test inputs small (≤ 5 elements) — the normalizer struggles with larger recursive specs

### SMT guidance for completeness proofs on sequences
The SMT solver cannot do full case analysis on symbolic sequences. The proven pattern:
1. `reveal_opaque` to expose `permutation` (count-based)
2. Use `countN` helper lemmas to unfold `Seq.count` for length-N sequences
3. `assert_norm` count values on concrete input
4. Assert explicit membership disjunctions: `assert (y[0] = 1 \/ y[0] = 2 \/ ...)`
5. Instantiate `sorted` for specific index pairs: `assert (y[0] <= y[1])`
6. Derive each element step-by-step using count constraints
7. Finish with `Seq.lemma_eq_elim y expected`

### `Seq.count` unfolding (critical for completeness)
`Seq.count` is recursive and needs `--fuel N` for length-N sequences.
`Seq.tail s = Seq.slice s 1 (Seq.length s)` — requires `Seq.lemma_index_slice` to
connect slice indices back to parent sequence indices.
