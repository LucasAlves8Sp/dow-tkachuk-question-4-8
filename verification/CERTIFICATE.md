# Lean verification certificate

**Theorem:** `Question48.question_4_8` in [`Question48.lean`](../Question48.lean)

```lean
theorem question_4_8 {X : Type*} [TopologicalSpace X] [CompletelyRegularSpace X]
    (h : ∀ A : Set (Cp X), A.Countable → Pseudocomplete (closure A)) : IsPSpace X
```

## Result of the check

| Item | Value |
|---|---|
| Status | Compiled successfully: no errors, no warnings |
| `sorry` | none |
| Axioms used (`#print axioms`) | `propext`, `Classical.choice`, `Quot.sound` (Lean's standard axioms only) |
| Lean | 4.34.1 (commit `5045d0056413266e57c625dcd7c365b10e377c52`) |
| Mathlib | tag `v4.34.1`, commit `d13f23b723b8a846827a245b89c10fc7d3f11612` |
| Build command | `lake build` (1793 jobs, completed successfully) |
| Checked on | 2026-10-12 (UTC), Linux x86_64 |

Raw output of `lake env lean Question48.lean`: [`axioms_output.txt`](axioms_output.txt)

## SHA-256 of the verified files

```
33893957b4c87183fe8f4498564691ab07e91328735541835f894e4a72c37ecf  Question48.lean
d5edba4e4b8faad9c1baeadb265716d20d03be4d1a2647dc5e35b0c0325bea7b  lean-toolchain
9808fb39c2893e3c7485dcf97b4d5c293674e823f6d87bf2eea89bf851e2c412  lakefile.toml
150421bb1f6b15a83b040fd368786cc0a561d1223841d07a41e5d0aad1905fbf  lake-manifest.json
```

## Reproduce

```bash
git clone https://github.com/LucasAlves8Sp/dow-tkachuk-question-4-8.git
cd dow-tkachuk-question-4-8
lake exe cache get   # downloads precompiled Mathlib (optional, saves hours)
lake build           # prints the axiom list at the end
sha256sum -c verification/SHA256SUMS
```

## What the certificate does and does not say

Lean checks that the formal statement follows from the formal definitions. Whether the
definitions faithfully express the mathematics is a human judgement. They are short
and stated at the top of `Question48.lean`:

* `Cp X` is the set of continuous `X → ℝ` with the subspace topology of the product
  `X → ℝ` (pointwise convergence). Mathlib's `C(X, ℝ)` is deliberately *not* used,
  since it carries the compact-open topology.
* `Pseudocomplete` is Oxtoby's definition via sequences of π-bases.
* `IsPSpace X` means every countable intersection of open sets is open.
* `X` is only assumed completely regular (weaker than Tychonoff).

As a non-degeneracy check, the file also proves that every compact space is
pseudocomplete (`Pseudocomplete.of_compactSpace`).
