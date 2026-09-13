# Constructive discretization in Lean 4 / Mathlib

A Lean 4 / Mathlib formalisation of the **generalized Batson–Spielman–Srivastava
sparsification theorem** of Chkifa, Dolbeault, Krieg and Ullrich, and of the
`L₂`-norm discretization inequality it yields. What the generalisation adds: the two
frame bounds may refer to two different families of functions, and the upper bound
depends on the *effective dimension* of the second family rather than on how many
functions it contains. The project builds without `sorry`, and every theorem uses only
the three axioms Mathlib relies on throughout (`propext`, `Classical.choice`,
`Quot.sound`).

* **Blueprint** (the mathematics, with the Lean name at every statement):
  <https://mario-ullrich.github.io/Lean-Discretization/>
* **Blueprint as PDF**:
  <https://mario-ullrich.github.io/Lean-Discretization/blueprint.pdf>
* **Dependency graph**:
  <https://mario-ullrich.github.io/Lean-Discretization/dep_graph_document.html>

GitHub Pages serves these three once the repository is public. Until then the same site
and PDF are downloadable from every run under *Actions* as the artifact
`blueprint-YYYYMMDD`.

## The question

Given a family of functions on a measure space, can one replace the integral
`∫ |f|² dμ` by a finite weighted sum `∑ wᵢ |f(xᵢ)|²` of point evaluations, with a
controlled loss in both directions? For a finite-dimensional space of functions this is
the problem of **norm discretization**, and the sharpest known answer of this type is
the sparsification theorem of Batson, Spielman and Srivastava. Letting the upper bound
depend on the effective dimension `M = Tr J / Λ` of the second family, rather than on
its size, is what makes the theorem applicable to infinite-dimensional reproducing
kernel Hilbert spaces, and it is the reason its constants beat those obtainable from
the Kadison–Singer theorem.

## The theorem

Let `(Ω, μ)` be a measure space, `ι` a finite nonempty index set with `m = card ι`
elements, and `κ` a second finite index set. Let

* `a : Ω → ι → ℂ` be square-integrable with Gram matrix `∫ a a* dμ = 1`, and
* `b : Ω → κ → ℂ` be square-integrable with Gram matrix `J = ∫ b b* dμ` positive
  definite and bounded by `Λ • 1`, of effective dimension `M = Tr J / Λ`.

Then for every `n ≥ m` there are points `x₁, …, xₙ ∈ Ω` and weights `w₁, …, wₙ > 0`
with

```
(1 - √((m-1)/n))² • 1  ≤  ∑ wᵢ a(xᵢ) a(xᵢ)*        (lower frame bound)
∑ wᵢ b(xᵢ) b(xᵢ)*      ≤  (1 + √((M-1)/n))² Λ • 1  (upper frame bound)
```

in the Loewner order, with no side condition. This is
`Discretization.bss_generalized_of_gram_eq_one'`.

## Main results

* **The potential argument** proves the theorem under the two side conditions `m ≥ 2`
  and `M ≥ 1 + 1/n` (`Discretization.bss_generalized_of_gram_eq_one`). Three further
  theorems cover the cases where one or both of them fail
  (`.bss_generalized_of_unique`, `.bss_generalized_of_small_dim`,
  `.bss_generalized_of_unique_of_small_dim`), and the four together give the statement
  above.
* **Without the normalisation** of the first family, the lower bound reads
  `(1 - √((m-1)/n))² • I` with `I = ∫ a a* dμ` (`Discretization.bss_generalized`); in
  eigenvalue form that is the factor `λ_min(I)` of the paper.
* **A countably infinite second family.** Then `b` maps into a Hilbert space, its Gram
  operator `J` is positive, injective and of finite trace, and the same two bounds hold
  with the second one in the order of operators
  (`Discretization.Infinite.bss_generalized_of_gram_eq_one`). The number of points does
  not change, because it is governed by `M = Tr J / Λ` and not by the size of the
  family.
* **The discretization inequality.** For every `f` in the span of the first family,
  `(1 - √((m-1)/n))² ∫ |f|² dμ ≤ ∑ wᵢ |f(xᵢ)|²`, and the weighted sum of every `g` in
  the span of the second family is at most `(1 + √((M-1)/n))² Λ ‖c‖²` in its
  coefficients `c` (`Discretization.exists_discretization`,
  `.Infinite.exists_discretization`). This is Corollary 4 of the paper; with `b` the
  singular basis of the embedding of a reproducing kernel Hilbert space into `L₂`, the
  coefficient norm is the norm of that space.
* **Barrier lemma.** A weight between the values of the two verifier functions keeps
  both matrices positive definite and lets neither potential increase
  (`Discretization.lowerPotential_update_le`, `.upperPotential_update_le`,
  `.Infinite.upperPotential_update_le`).
* **The verifiers pass on average**, which is where the measure space enters: an
  admissible point exists because the lower verifier exceeds the upper one on average
  (`Discretization.integral_lowerVerifier_gt`, `.integral_upperVerifier_lt`,
  `.exists_admissible_point`).
* **A bound on a potential is a bound on the matrix**: `Φ(A)⁻¹ • 1 ≼ A` and
  `Ψ_J(B)⁻¹ • J ≼ B` (`Matrix.PosDef.inv_re_trace_smul_one_le`,
  `.inv_re_trace_mul_smul_le`, `Discretization.Infinite.inv_upperPotential_smul_le`).
* **The trace of an operator** along a fixed Hilbert basis, `Tr T = ∑ₖ Re ⟪eₖ, T eₖ⟫`,
  with the cyclicity and the bound `T ≼ Tr(T) • 1` the argument needs
  (`ContinuousLinearMap.traceAlong`, `.tsum_inner_apply_comm`,
  `.le_traceAlong_smul_one`). Mathlib has no trace outside finite dimension.
* Three tools from `BasicResults` carry the steps above: Sherman–Morrison for a
  rank-one update, for matrices and for operators (`Matrix.inv_add_smul_vecMulVec`,
  `ContinuousLinearMap.inverse_add_smul_rankOne`), Cauchy–Schwarz for the trace
  (`Matrix.PosSemidef.norm_trace_mul_sq_le`), and `∫ a(x)* Q a(x) dμ = Tr (Q · gram a μ)`
  (`Discretization.integral_quadForm`, `ContinuousLinearMap.integral_re_inner_apply`).

Everything else is in the blueprint, with its Lean name at every statement.

## The proof

The proof is the potential-function argument of BSS, with the second potential weighted
by `J`. Two matrices `A` and `B` are carried along, and two real numbers measure how
close each is to failure: the **lower potential** `Φ(A) = Tr A⁻¹`, which is large when
`A` has a small eigenvalue, and the **upper potential** `Ψ_J(B) = Tr (J B⁻¹)`, which is
large when `B` is small where `J` is large. Each of the `n` steps first shifts `A` to
`A - δ • 1` and `B` to `B + ζ • J`, which costs an exactly computable amount of both
potentials, and the barrier lemma then says which weights at which point spend no more
than that. Averaging the verifiers over `μ` turns them into traces against the Gram
matrices, so such a point exists. After `n` steps both potentials are still below their
initial values, and reading a bound on a potential back as a bound on the matrix gives
the two frame bounds. For a countably infinite second family, `B` is a positive
invertible operator and the traces are sums along a fixed Hilbert basis; only the upper
side is redone, in `Discretization/Infinite/`.

## Organisation

Two libraries. `Discretization` holds the argument: the arithmetic of the parameters,
the two potentials and the verifiers, the barrier lemma, the averaging step, the
`n`-step iteration, the main theorem with its edge cases, the discretization
inequality, and under `Discretization/Infinite/` the same for a countably infinite
second family. `BasicResults` holds what the argument needs and Mathlib lacks:
comparisons in the Loewner order, traces of products and Cauchy–Schwarz for them,
Sherman–Morrison for rank-one updates of a matrix and of an operator, the trace of an
operator along a Hilbert basis, and the bridge from Bochner integrals to Gram matrices;
[MathlibCandidates.md](MathlibCandidates.md) lists what could be upstreamed.
`blueprint/` holds the LaTeX source of the blueprint and the script that points its
`\lean` links at this repository.

## What is left to do

* **The application to a reproducing kernel Hilbert space.** The theorem for a
  countable second family is proved; what is not formalised is the construction of the
  Gram operator from a kernel, that is the singular value decomposition of the
  embedding into `L₂` which supplies the family `b` and makes `J` diagonal.
* **The applications of the paper**: least-squares recovery, sampling numbers, and the
  discretization with equal weights via Kiefer–Wolfowitz.

## Building

Requires [`elan`](https://github.com/leanprover/elan). The Lean version is pinned in
`lean-toolchain` and Mathlib in `lake-manifest.json`, so a clone builds against Lean /
Mathlib `v4.33.1`:

```bash
lake exe cache get   # downloads the prebuilt Mathlib oleans
lake build           # builds the project
```

Run `lake` from inside this folder, since `elan` reads `lean-toolchain` from the
working directory, and do not run `lake update`: it re-resolves the dependencies and
makes the build non-reproducible.

The blueprint follows the
[leanblueprint](https://github.com/PatrickMassot/leanblueprint) convention and needs a
TeX installation, `graphviz` for the dependency graph, and the `leanblueprint` package:

```bash
leanblueprint pdf          # blueprint/print/print.pdf
leanblueprint web          # blueprint/web/index.html and the dependency graph
leanblueprint checkdecls   # checks that every \lean{Decl} resolves
```

GitHub Actions builds the project and the blueprint on every push to `main`, and
deploys the blueprint to GitHub Pages once the repository is public. Neither output is
committed.

## AI assistance

The formalisation was written with Claude Code. Every statement and proof was checked
by Lean; the mathematical design, the choice of statements and the review of what the
proofs actually say are the author's.

## License

Apache 2.0, the same as Mathlib. See [LICENSE](LICENSE).

## References

* A. Chkifa, M. Dolbeault, D. Krieg, M. Ullrich, *Constructive discretization and
  approximation in reproducing kernel Hilbert spaces*. Theorem 3 is the result
  formalised here, Corollary 4 the discretization inequality, and Section 4 the proof
  followed in `Discretization/`.
* J. Batson, D. A. Spielman, N. Srivastava, *Twice-Ramanujan sparsifiers*, SIAM Review
  **56** (2014), 315–334. The original potential-function argument.
