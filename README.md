# Pseudocompleteness of countable closures in $C_p(X)$: an answer to Dow–Tkachuk Question 4.8

**Author:** Lucas Alves de Almeida

This repository contains a solution, with a machine-checked proof in Lean 4, of an open
question from

> A. Dow and V. V. Tkachuk, *Reflecting topological properties in closed separable
> subspaces*, European Journal of Mathematics **11** (2025), Art. No. 5.
> [doi:10.1007/s40879-024-00790-w](https://doi.org/10.1007/s40879-024-00790-w)

> **Question 4.8.** Assume that $\overline{A}$ is pseudocomplete for any countable
> $A \subset C_p(X)$. Must $X$ be a P-space?

**Answer: yes, in ZFC.**

> **Status: candidate resolution.** The proof has been machine-checked in Lean 4 (see
> below) but has **not yet been checked by a human expert**. Feedback is welcome.

| | |
|---|---|
| Paper | [`paper/Pseudocompleteness_of_countable_closures.pdf`](paper/Pseudocompleteness_of_countable_closures.pdf) ([LaTeX source](paper/Pseudocompleteness_of_countable_closures.tex)) |
| Lean formalization | [`Question48.lean`](Question48.lean) |
| Verification certificate | [`verification/CERTIFICATE.md`](verification/CERTIFICATE.md) |

## The result

**Theorem.** If a Tychonoff space $X$ is not a P-space, then $C_p(X)$ contains a closed
separable metrizable linear subspace that is not pseudocomplete.

**Corollary (Question 4.8).** If the closure in $C_p(X)$ of every countable subset of
$C_p(X)$ is pseudocomplete, then $X$ is a P-space.

Here $C_p(X)$ is the space of continuous real functions on $X$ with the topology of
pointwise convergence, a *P-space* is a space in which countable intersections of open
sets are open, and pseudocompleteness is in the sense of Oxtoby.

Dow and Tkachuk had shown (their Theorem 3.10) that the conclusion holds when $X$ is
also assumed functionally countable. The result here removes that assumption.
Question 4.9 (whether $X$ must be functionally countable) is not addressed.

## Idea of the proof

1. **A non-open zero set.** If $X$ is not a P-space, there is a continuous
   $f\colon X\to[0,\infty)$ whose zero set $Z=f^{-1}(0)$ is not open. Pick points $x_n$
   with levels $t_n=f(x_n)$ satisfying $0<t_{n+1}<t_n/2$.
2. **Interpolation.** For a sequence $a\in\mathbb{R}^{\mathbb{N}}$ let $u_a$ be the
   piecewise-linear function with $u_a(t_n)=a_n$ and $u_a(0)=0$, and put
   $T(a)=u_a\circ f$. The map $T\colon\mathbb{R}^{\mathbb{N}}\to\mathbb{R}^X$ is linear and
   continuous, and evaluation at the points $x_n$ is a continuous left inverse, so the
   image $L=T(\mathbb{R}^{\mathbb{N}})$ is closed.
3. **A countable set.** Let $A$ be the image of the finitely supported rational
   sequences. Each member of $A$ is continuous on $X$, so $A\subseteq C_p(X)$, and its
   closure $F=L\cap C_p(X)$ is homeomorphic to the dense subgroup
   $G=\{a : T(a)\text{ is continuous}\}$ of $\mathbb{R}^{\mathbb{N}}$.
4. **The obstruction.** A dense pseudocomplete subgroup of $\mathbb{R}^{\mathbb{N}}$ is all
   of $\mathbb{R}^{\mathbb{N}}$. So if $F$ were pseudocomplete, the constant sequence
   $\mathbf{1}$ would lie in $G$. But $T(\mathbf{1})$ is the characteristic function of
   $X\setminus Z$, which is discontinuous because $Z$ is not open.

Full details are in the paper.

## Lean formalization

[`Question48.lean`](Question48.lean) proves the corollary in Lean 4 with Mathlib:

```lean
theorem question_4_8 {X : Type*} [TopologicalSpace X] [CompletelyRegularSpace X]
    (h : ∀ A : Set (Cp X), A.Countable → Pseudocomplete (closure A)) : IsPSpace X
```

* It compiles with **no `sorry`**, and `#print axioms` reports only Lean's standard
  axioms `propext`, `Classical.choice` and `Quot.sound`.
* `Cp`, `Pseudocomplete` and `IsPSpace` are defined at the top of the file to match the
  paper. `Cp X` uses the pointwise (product) topology, not Mathlib's compact-open
  `C(X, ℝ)`.
* The hypothesis on $X$ is complete regularity, slightly weaker than Tychonoff.
* **One difference from the paper.** Mathlib does not contain the Aarts–Lutzer
  characterization used in the paper's Lemma 2.1. The Lean file proves that lemma
  directly from Oxtoby's definition instead, for any metrizable topological group, by
  building nested sequences for $G$ and its translate $a+G$ at the same time. The proof
  is therefore fully self-contained and imports no unformalized theorem.

### Main components of the file

| Lean name | Content |
|---|---|
| `Pseudocomplete.of_homeomorph` | pseudocompleteness is a topological invariant |
| `Pseudocomplete.of_compactSpace` | compact spaces are pseudocomplete (non-degeneracy check) |
| `dense_pseudocomplete_subgroup` | Lemma 2.1: a dense pseudocomplete subgroup is everything |
| `exists_nonopen_zero_set` | a non-P-space has a non-open zero set |
| `ψ`, `ψ_at`, `ψ_pair_ge_one` | tent functions realizing the interpolation $u_a$ |
| `dense_range_fs` | finitely supported rational sequences are dense |
| `question_4_8` | the main theorem |

### Checking it yourself

Requires [elan](https://github.com/leanprover/elan). The toolchain (Lean 4.34.1) and
Mathlib version (`v4.34.1`) are pinned in `lean-toolchain` and `lake-manifest.json`.

```bash
git clone https://github.com/LucasAlves8Sp/dow-tkachuk-question-4-8.git
cd dow-tkachuk-question-4-8
lake exe cache get   # downloads precompiled Mathlib (optional, saves hours)
lake build
```

The build ends by printing:

```
'Question48.question_4_8' depends on axioms: [propext, Classical.choice, Quot.sound]
```

See [`verification/CERTIFICATE.md`](verification/CERTIFICATE.md) for versions, file hashes
and the raw output of the check.

## Disclosure of AI assistance

This work is **AI-assisted**.

* **Main idea (author, Lucas Alves de Almeida):** answer Question 4.8 by proving the
  stronger statement that every non-P-space $X$ yields a closed separable metrizable
  linear subspace of $C_p(X)$ that is not pseudocomplete (Theorem 1.1 of the paper),
  instead of arguing directly from the hypothesis on countable closures.
* **ChatGPT (Astra, OpenAI):** worked out the details and completed the argument.
* **Author:** edited the manuscript and checked the literature.
* **Claude Opus 5.5 (Anthropic):** assisted with reviewing the proof and typesetting, and
  produced the Lean 4 / Mathlib formalization in this repository.
* **Cost:** none beyond the author's existing US$20/month ChatGPT and Claude
  subscriptions.

The result has not yet been checked by a human expert.

## References

1. J. M. Aarts and D. J. Lutzer, *Pseudo-completeness and the product of Baire spaces*,
   Pacific J. Math. **48** (1973), 1–10.
2. A. Dow and V. V. Tkachuk, *Reflecting topological properties in closed separable
   subspaces*, Eur. J. Math. **11** (2025), Art. No. 5.
3. R. Engelking, *General Topology*, Heldermann, 1989.
4. J. C. Oxtoby, *Cartesian products of Baire spaces*, Fund. Math. **49** (1961), 157–166.
