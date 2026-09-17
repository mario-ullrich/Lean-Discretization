# Constructive discretization in Lean 4 / Mathlib

A Lean 4 / Mathlib formalisation of two theorems that replace a norm by finitely many
point evaluations. The first is the **generalized Batson–Spielman–Srivastava
sparsification theorem** of Chkifa, Dolbeault, Krieg and Ullrich, with the `L₂`-norm
discretization inequality it yields; what the generalisation adds is that the two frame
bounds may refer to two different families of functions, and that the upper bound
depends on the *effective dimension* of the second family rather than on how many
functions it contains. The second is the **Kiefer–Wolfowitz theorem** in the form used
by Krieg, Pozharska, Ullrich and Ullrich for sampling projections: on an
`n`-dimensional space of bounded functions the uniform norm is dominated by the `L₂`
norm of a finitely supported probability measure, with the constant `√(n+ε)`. The
project builds without `sorry`, and every theorem uses only the three axioms Mathlib
relies on throughout (`propext`, `Classical.choice`, `Quot.sound`).

* **Blueprint** (the mathematics, with the Lean name at every statement):
  <https://mario-ullrich.github.io/Lean-Discretization/>
* **Blueprint as PDF**:
  <https://mario-ullrich.github.io/Lean-Discretization/blueprint.pdf>
* **Dependency graph**:
  <https://mario-ullrich.github.io/Lean-Discretization/dep_graph_document.html>

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

The second question is which measure to discretize in the first place. On an
`n`-dimensional space of functions one may ask for a measure for which the uniform norm
is already controlled by the `L₂` norm, and the answer of Kiefer and Wolfowitz is that a
measure maximising the determinant of the Gram matrix does this with the constant `√n`,
up to an arbitrarily small loss on a general domain. Applying the sparsification theorem
to such a measure is how one arrives at sampling projections with few points and small
norm.

## Main results

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

in the Loewner order, with no side condition
(`Discretization.bss_generalized_of_gram_eq_one'`). Four statements go with it:

* **The potential argument** gives the theorem under the two side conditions `m ≥ 2`
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
  with the second one in the order of operators, again with no side condition
  (`Discretization.Infinite.bss_generalized`). Underneath it are the same four cases as in
  finite dimension: the potential argument
  (`.Infinite.bss_generalized_of_gram_eq_one`) and the three edge cases
  (`.Infinite.bss_generalized_of_unique`, `.Infinite.bss_generalized_of_small_dim`,
  `.Infinite.bss_generalized_of_unique_of_small_dim`). The number of points does not
  change, because it is governed by `M = Tr J / Λ` and not by the size of the family.
* **The discretization inequality.** For every `f` in the span of the first family,
  `(1 - √((m-1)/n))² ∫ |f|² dμ ≤ ∑ wᵢ |f(xᵢ)|²`, and the weighted sum of every `g` in
  the span of the second family is at most `(1 + √((M-1)/n))² Λ ‖c‖²` in its
  coefficients `c` (`Discretization.exists_discretization`,
  `.Infinite.exists_discretization`, the second with a vector of the Hilbert space in
  place of `c`). This is Corollary 4 of the paper, in both cases without a side condition;
  with `b` the singular basis of the embedding of a reproducing kernel Hilbert space into
  `L₂`, the coefficient norm is the norm of that space.

For the second theorem, let `D` be any set, `ι` a finite nonempty index set with
`n = card ι` elements, and `a : D → ι → ℂ` a bounded family whose coordinate functions
are linearly independent. Then for every `ε > 0` there are points `x₁, …, x_N ∈ D` and
weights `w₁, …, w_N ≥ 0` summing to one such that

```
|f(y)|²  ≤  (n + ε) · ∑ wₖ |f(xₖ)|²
```

for every point `y ∈ D` and every `f` in the span of the family
(`Discretization.KieferWolfowitz.exists_design_kieferWolfowitz`). This is Proposition 9
of Krieg, Pozharska, Ullrich and Ullrich. Three variants of it are proved:

* **As a measure.** The points and weights are a finitely supported probability measure
  `ϱ = ∑ wₖ δ(xₖ)` with invertible Gram matrix, and the inequality reads
  `|f(y)|² ≤ (n + ε) ∫ |f|² dϱ`
  (`Discretization.KieferWolfowitz.exists_probabilityMeasure_kieferWolfowitz`). The Gram
  matrix of `ϱ` in the sense of `Discretization.gram` is the one of the points and
  weights (`.gram_designMeasure`), which is what lets the measure be handed to the
  sparsification theorem.
* **The sharp constant on a compact domain.** For continuous functions on a compact
  space the maximum of the determinant is attained, the `ε` disappears, and the constant
  is `√n` (`Discretization.KieferWolfowitz.exists_design_kieferWolfowitz_of_compact`).
* **At most `2n² + 1` points.** Every design can be replaced by one with at most
  `2n² + 1` points and the same Gram matrix, so both statements hold with that many
  points (`Discretization.KieferWolfowitz.exists_design_card_le`,
  `.exists_design_kieferWolfowitz_card_le`,
  `.exists_design_kieferWolfowitz_of_compact_card_le`).

Alongside these, a design decomposes the identity. Writing `t(y) = a(y)* G⁻¹ a(y)` for
the variance function, the weights `wₖ t(xₖ)` are nonnegative and sum to `n`
(`Discretization.KieferWolfowitz.sum_weight_quadForm_inv_eq_card`), and
`∑ₖ wₖ ⟪a(xₖ), z⟫ a(xₖ) = z` for every vector `z` in the inner product
`⟪u, z⟫ = u* G⁻¹ z` of the ellipsoid of `G`
(`.sum_weight_smul_quadForm_inv_eq_self`). This is John's decomposition of the identity,
the condition dual to the Kiefer–Wolfowitz bound: on a compact domain the bound
`t(y) ≤ n` and the average `n` together force `t(xₖ) = n` at every design point, making
the points contact points. The theorem for a general convex body is proved in the
companion project [Lean-SNumbers](https://github.com/mario-ullrich/Lean-SNumbers) as
`John.john_decomposition`.

## The proofs

The first proof is the potential-function argument of BSS, with the second potential
weighted by `J`. Two matrices `A` and `B` are carried along, and two real numbers
measure how close each is to failure: the **lower potential** `Φ(A) = Tr A⁻¹`, which is
large when `A` has a small eigenvalue, and the **upper potential** `Ψ_J(B) = Tr (J B⁻¹)`,
which is large when `B` is small where `J` is large. Each of the `n` steps first shifts
`A` to `A - δ • 1` and `B` to `B + ζ • J`, which costs an exactly computable amount of
both potentials, and the barrier lemma then says which weights at which point spend no
more than that. Averaging the verifiers over `μ` turns them into traces against the Gram
matrices, so such a point exists. After `n` steps both potentials are still below their
initial values, and reading a bound on a potential back as a bound on the matrix gives
the two frame bounds. For a countably infinite second family, `B` is a positive
invertible operator and the traces are sums along a fixed Hilbert basis; only the upper
side is redone, in `Discretization/Infinite/`. The edge cases and the removal of the
normalisation follow the finite argument there as well: both inductions consume the second
family only through a constant verifier of average `n`, so the lower half is the finite
lemma itself, and the crude bound `b b* ≼ ‖b‖² • 1` is all the upper half needs.

The second proof maximises a determinant. Among all finitely supported probability
measures one is chosen whose Gram matrix `G = ∑ wₖ a(xₖ) a(xₖ)*` has an almost maximal
determinant: the determinants are bounded above because the entries of `G` are, and one
of them is positive because the functions are linearly independent. Giving a further
point `y` the weight `α` yields such a measure again, and the matrix determinant lemma
says exactly what that does to the determinant, namely multiply it by
`(1-α)^(n-1) (1 + α (t - 1))` with `t = a(y)* G⁻¹ a(y)`. Almost maximality bounds that
factor, and Bernoulli's inequality with the explicit weight `α = (t-n)/(2n(t-1))` turns
the bound into `t ≤ n + ε`, uniformly in `y`. Subtracting `(n+ε)⁻¹ a(y) a(y)*` from `G`
then leaves a positive definite matrix, which read as an inequality between quadratic
forms is the theorem. On a compact domain the maximum is attained and the same argument
gives `t ≤ n`.

The steps the two arguments are built from:

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
* **The determinant of a rank-one mixture**,
  `det (β A + α u u*) = β^(n-1) det A (β + α u* A⁻¹ u)`, affine in `α` and so the
  substitute for the derivative of the determinant
  (`Matrix.det_smul_add_smul_vecMulVec`), together with the real estimate it feeds
  (`Discretization.KieferWolfowitz.exists_mix_ge`) and the uniform bound on the
  quadratic form that comes out (`.exists_design_quadForm_inv_le`). Mathlib has no
  Jacobi formula, and none is needed.
* **A design with an invertible Gram matrix** exists for linearly independent functions,
  which is what makes the determinant somewhere positive
  (`Discretization.KieferWolfowitz.exists_design_posDef`), and the Gram matrices of
  designs are the convex hull of the rank-one matrices `a(y) a(y)*`, which is where
  Carathéodory's theorem enters (`.designGram_mem_convexHull`,
  `.exists_design_of_mem_convexHull`).
* Three more tools from `BasicResults` recur throughout: Sherman–Morrison for a
  rank-one update, for matrices and for operators (`Matrix.inv_add_smul_vecMulVec`,
  `ContinuousLinearMap.inverse_add_smul_rankOne`), Cauchy–Schwarz for the trace
  (`Matrix.PosSemidef.norm_trace_mul_sq_le`), and `∫ a(x)* Q a(x) dμ = Tr (Q · gram a μ)`
  (`Discretization.integral_quadForm`, `ContinuousLinearMap.integral_re_inner_apply`).

Everything else is in the blueprint, with its Lean name at every statement.

## Organisation

Two libraries. `Discretization` holds the arguments: the arithmetic of the parameters,
the two potentials and the verifiers, the barrier lemma, the averaging step, the
`n`-step iteration, the main theorem with its edge cases, the discretization
inequality, under `Discretization/Infinite/` the same chain for a countably infinite
second family, and under `Discretization/KieferWolfowitz/` the maximisation of the
determinant
of a Gram matrix, the theorem it yields and John's decomposition of the identity beside
it. `BasicResults` holds what the arguments need
and Mathlib lacks: comparisons in the Loewner order, traces of products and
Cauchy–Schwarz for them, Sherman–Morrison for rank-one updates of a matrix and of an
operator, the trace of an operator along a Hilbert basis, the matrix determinant lemma,
the compactness of the convex hull of a compact set, and the bridge from Bochner
integrals to Gram matrices;
[MathlibCandidates.md](MathlibCandidates.md) lists what could be upstreamed.
`blueprint/` holds the LaTeX source of the blueprint and the script that points its
`\lean` links at this repository. `Palomar/` holds the submission surfaces for the
[Palomar registry](https://palomar-registry.org), one directory per registered result,
each with a `Challenge` module stating the advertised theorems and a `Solution` module
supplying their proofs from the development. The placeholder `sorry`s in the `Challenge`
modules are required by that format: a Challenge advertises statements and imports only
Mathlib, so a reader can audit what is claimed without reading the development. This
library sits outside `defaultTargets`; build it with `lake build Palomar`.

## What is left to do

* **The application to a reproducing kernel Hilbert space.** The theorem for a
  countable second family is proved; what is not formalised is the construction of the
  Gram operator from a kernel, that is the singular value decomposition of the
  embedding into `L₂` which supplies the family `b` and makes `J` diagonal.
* **Sampling projections in the uniform norm**: handing the Kiefer–Wolfowitz measure to
  the sparsification theorem, which is what yields a projection using `2n` points with
  norm of order `√n`.
* **The applications of the paper**: least-squares recovery and sampling numbers.

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

GitHub Actions builds the project and the blueprint on every push to `main`, and deploys
the blueprint to GitHub Pages. Neither output is committed.

## AI assistance

The formalisation was written with Claude Code. Every statement and proof was checked
by Lean; the mathematical design, the choice of statements and the review of what the
proofs actually say are the author's.

## License

Apache 2.0, the same as Mathlib. See [LICENSE](LICENSE).

## References

* A. Chkifa, M. Dolbeault, D. Krieg, M. Ullrich, *Constructive discretization and
  approximation in reproducing kernel Hilbert spaces*, preprint, 2026,
  [arxiv](https://arxiv.org/abs/2602.18719). Theorem 3 is the result formalised here,
  Corollary 4 the discretization inequality, and Section 4 the proof followed in
  `Discretization/`.
* J. Batson, D. A. Spielman, N. Srivastava, *Twice-Ramanujan sparsifiers*, SIAM Review
  **56** (2014), no. 2, 315–334, [doi](https://doi.org/10.1137/130949117),
  [arxiv](https://arxiv.org/abs/0808.0163). The original potential-function argument.
* D. Krieg, K. Pozharska, M. Ullrich, T. Ullrich, *Sampling projections in the uniform
  norm*, J. Math. Anal. Appl. **553** (2026), no. 2, Paper No. 129873,
  [arxiv](https://arxiv.org/abs/2401.02220). Proposition 9 is the Kiefer–Wolfowitz
  theorem formalised here, and its proof the one followed in
  `Discretization/KieferWolfowitz/`.
* J. Kiefer, J. Wolfowitz, *The equivalence of two extremum problems*, Canad. J. Math.
  **12** (1960), 363–366, [doi](https://doi.org/10.4153/CJM-1960-030-4). The original
  equivalence theorem for optimal designs.
