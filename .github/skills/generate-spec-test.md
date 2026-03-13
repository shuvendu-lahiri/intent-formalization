# Skill: Generate Spec Test

Generate an F* test file for soundness/completeness evaluation of an AutoCLRS spec.

## Trigger
When the user asks to "create a test", "evaluate a spec", or "test an algorithm" from AutoCLRS.

## Steps

1. **Find the spec file**: Look in `~/AutoCLRS/autoclrs/<chapter>/CLRS.<Chapter>.<Algorithm>.Spec.fst`

2. **Read the spec**: Identify:
   - Key spec functions and their types (e.g., `gcd_spec : nat → nat → nat`)
   - Module opens (especially `Pulse.Lib.BoundedIntegers`, `FStar.Mul`)
   - Whether any dependency has an `.fsti` hiding concrete values
   - Whether any definition is `[@@"opaque_to_smt"]`

3. **Choose test strategy**:
   - **Transparent functions** (no `.fsti`, no opaque): use plain `= ()` proofs or `assert_norm`
   - **Recursive functions** (e.g., DP recurrences): use `assert_norm` with small inputs
   - **Abstract `.fsti`** (e.g., `inf`): use `friend` mechanism (create `.fsti` for test module)
   - **Opaque definitions** (e.g., `permutation`): use `reveal_opaque`
   - **Sorting specs**: open `Pulse.Lib.BoundedIntegers` before `CLRS.Common.SortSpec`

4. **Generate concrete test data**: Pick 2-3 small inputs where the expected output is known.
   Keep sizes small (≤ 5 elements for sequences, ≤ 3 nodes for graphs).

5. **Write the test file** with:
   - **Soundness proofs**: `let test_sound_N () : Lemma (spec_fn input == expected) = assert_norm (...)`
   - **Completeness proofs (Appendix B)**: Prove `∀y. φ(input, y) ⟹ y == expected`
     For scalar specs, this is a trivial lemma. For relational specs (sorting, permutation),
     this requires step-by-step SMT guidance — see `Test.InsertionSort.fst` for the reference pattern.

6. **Verify** using the verify-fstar skill.

## Example Output (scalar spec)
For `CLRS.Ch31.GCD.Spec`:
```fstar
module Test.GCD
open FStar.Mul
open CLRS.Ch31.GCD.Spec

(* Soundness *)
let test_sound_1 () : Lemma (gcd_spec 12 8 == 4) = ()
let test_sound_2 () : Lemma (gcd_spec 35 15 == 5) = ()

(* Completeness: spec uniquely determines output *)
let test_complete_1 (y: nat) : Lemma (requires gcd_spec 12 8 == y) (ensures y == 4) = ()
```
