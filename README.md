# Norm discretization in Lean 4 / Mathlib

A Lean 4 / Mathlib formalisation of two theorems that replace a norm by finitely many
point evaluations. The first is the **discretization theorem** of Chkifa, Dolbeault,
Krieg and Ullrich, a generalization of the Batson–Spielman–Srivastava sparsification
theorem, with the `L₂`-norm discretization inequality it yields; what the generalisation
adds is that the two frame bounds may refer to two different families, the second one a
map into a Hilbert space, and that the upper bound depends on the *effective dimension*
of the second family rather than on its size. The second is the **Kiefer–Wolfowitz
theorem** in the form used by Krieg, Pozharska, Ullrich and Ullrich for sampling
projections: on an `m`-dimensional space of bounded functions the uniform norm is
dominated by the `L₂` norm of a finitely supported probability measure, with the
constant `√(m+ε)`. Thinned by the first theorem, the measure can be replaced by any
`n ≥ m` equally weighted points, at the price of the factor `(1 − √((m−1)/n))⁻²`. The project builds
without `sorry`, and every theorem uses only the
three axioms Mathlib relies on throughout (`propext`, `Classical.choice`, `Quot.sound`).

* **Blueprint** (a webpage explaining the mathematics):
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
`m`-dimensional space of functions one may ask for a measure for which the uniform norm
is already controlled by the `L₂` norm, and the answer of Kiefer and Wolfowitz is that a
measure maximising the determinant of the Gram matrix does this with the constant `√m`,
up to an arbitrarily small loss on a general domain. Applying the discretization theorem
to such a measure is how one arrives at sampling projections with few points and small
norm.

## Main results

### The discretization theorem

Let `(Ω, μ)` be a measure space, `ι` a finite nonempty index set with `m = card ι`
elements, and `H` a nonzero separable complex Hilbert space. Let

* `a : Ω → ι → ℂ` be square-integrable with positive definite Gram matrix
  `I = ∫ a a* dμ`, and
* `b : Ω → H` be square-integrable with injective Gram operator
  `J = ∫ b(x) b(x)* dμ(x)`, a Bochner integral, bounded by `Λ • 1`, and put
  `M = ∫ ‖b‖² dμ / Λ`, the effective dimension.

Then for every `n ≥ m` there are points `x₁, …, xₙ ∈ Ω` and weights `w₁, …, wₙ > 0`
with

```
(1 - √((m-1)/n))² • I  ≤  ∑ wᵢ a(xᵢ) a(xᵢ)*        (lower frame bound)
∑ wᵢ b(xᵢ) b(xᵢ)*      ≤  (1 + √((M-1)/n))² Λ • 1  (upper frame bound)
```

in the Loewner order, with no side condition (`Discretization.Infinite.bss_generalized`).
This is Theorem 3 of
[Chkifa, Dolbeault, Krieg and Ullrich](https://arxiv.org/abs/2602.18719); in eigenvalue
form the lower bound is their factor `λ_min(I)`. For `a = b` it is the sparsification
theorem of [Batson, Spielman and Srivastava](https://arxiv.org/abs/0808.0163) in a
slightly stronger form, with `√((m-1)/n)` in place of their `√(m/n)`. Positivity
of `J` and the finiteness of its trace follow from its definition, and both hypotheses on
`J` can be checked on `b`: `J ≤ Λ • 1` says `∫ |⟪u, b⟫|² dμ ≤ Λ ‖u‖²` for every `u ∈ H`,
and injectivity says that `⟪u, b(·)⟫ = 0` almost everywhere only for `u = 0`
(`ContinuousLinearMap.integral_rankOne_self_le_iff`,
`.integral_rankOne_self_injective_iff`). Five statements go with it:

* **A family of functions**, in the form of the paper. Let `b = (b_k)_{k ∈ κ}` be
  square-integrable functions indexed by a finite or countable set with
  `∑_k ‖b_k‖²_{L₂} < ∞`, whose Gram matrix `J = (∫ b_k b̄_l dμ)` is injective on `ℓ²(κ)`
  and bounded by `Λ • 1`, and put `M = ∑_k ‖b_k‖² / Λ`. Then the same two bounds hold,
  the second one as `∑ wᵢ |g(xᵢ)|² ≤ (1 + √((M-1)/n))² Λ ‖c‖²` for every `c ∈ ℓ²(κ)` and
  `g = ∑_k c_k b_k` (`Discretization.bss_generalized` for finite `κ`, proved with
  matrices; `Discretization.Countable.bss_generalized` for countable `κ`, the case
  `H = ℓ²(κ)`). Nothing pointwise is assumed: `∑_k |b_k(x)|² < ∞` holds almost
  everywhere, and the points are chosen where it holds. With `I = 1` the first bound
  reads `(1 - √((m-1)/n))² ∫ |f|² dμ ≤ ∑ wᵢ |f(xᵢ)|²` for every `f` in the span of the
  first family (`Discretization.exists_discretization`,
  `Discretization.Countable.exists_discretization`).
* **The special case `a = b`** is the sparsification theorem of Batson, Spielman and
  Srivastava (`Discretization.bss`): one family with Gram matrix the identity, squeezed
  between `(1 - √((m-1)/n))² • 1` and `(1 + √((m-1)/n))² • 1`. With the original
  `√(m/n)` and `n = d·m`, the ratio of the upper to the lower constant, the condition
  number, is `((√d + 1)/(√d - 1))²`. For finitely many vectors
  `v_k ∈ ℂ^m`, `k ∈ Ω`, with `∑ v_k v_k* = 1`, the form of the original theorem, it gives
  weights `s_k ≥ 0`, at most `n` of them nonzero, with `∑ s_k v_k v_k*` between the same two
  constants (`Discretization.bss_of_sum_eq_one`).
* **One-sided discretization.** On a probability space the lower frame bound holds with
  weights at most `1/n`: for every `n ≥ m` there are points `x₁, …, xₙ ∈ Ω`, not necessarily distinct, and
  weights `0 < wᵢ ≤ 1/n` with `(1 - √((m-1)/n))² • I ≤ ∑ wᵢ a(xᵢ) a(xᵢ)*`
  (`Discretization.bss_lower_le_one_div`), hence
  `(1 - √((m-1)/n))² ∫ |f|² dμ ≤ (1/n) ∑ |f(xᵢ)|²` for every `f` in the span of the first
  family (`Discretization.exists_one_sided_discretization`). This is the theorem for the
  constant second family `b ≡ 1` in `H = ℂ`, with `M = 1`: the construction for a small
  effective dimension compares the lower verifier with the constant `n` and so keeps every
  weight below `1/n`, while the upper bound of the theorem records the sum `∑ wᵢ ≤ 1`.
  Limonova and Temlyakov prove such a bound for spaces satisfying a Nikol'skii-type
  inequality, Bartel, Schäfer and Ullrich for arbitrary spaces up to constants; the form here
  is the case `p = 2` of Proposition 8 of the paper.
* **Discretization of the `L₂`-norm**, Corollary 4 of the paper. Let `H` be a separable
  Hilbert space of measurable functions on `Ω` with continuous point evaluations and
  reproducing kernel `K`, with `∫ K(x, x) dμ < ∞`; let `∫ |g|² dμ ≤ Λ ‖g‖²_H` for every
  `g ∈ H`, and let `g = 0` be the only function of `H` vanishing almost everywhere. With
  `I = 1` and `M = ∫ K(x, x) dμ / Λ`, the points and weights satisfy
  `(1 - √((m-1)/n))² ∫ |f|² dμ ≤ ∑ wᵢ |f(xᵢ)|²` for every `f` in the span of the first
  family and `∑ wᵢ |g(xᵢ)|² ≤ (1 + √((M-1)/n))² Λ ‖g‖²_H` for every `g ∈ H`
  (`Discretization.RKHS.exists_discretization`). The second family is the kernel
  sections `K(x, ·)`, so no basis of `H` and no singular value decomposition of the
  embedding into `L₂` enter. Every `b` with injective Gram operator leads to such a
  space: the functions `⟪u, b(·)⟫` with norm `‖u‖` and kernel `⟪b(x), b(y)⟫`. For it the
  bound reads `∑ wᵢ |⟪u, b(xᵢ)⟫|² ≤ (1 + √((M-1)/n))² Λ ‖u‖²` for every `u ∈ H`
  (`Discretization.Infinite.exists_discretization`). In the coordinates of an
  orthonormal basis of `H` it is the family form above.
* **The four cases underneath.** The potential argument gives the theorem under the two
  side conditions `m ≥ 2` and `M ≥ 1 + 1/n` (`Discretization.bss_generalized_of_gram_eq_one`
  for matrices, `Discretization.UpperBarrier.bss_generalized_of_gram_eq_one` for every
  upper state). Three further theorems cover the cases where one or both of them fail
  (`.bss_generalized_of_unique`, `.bss_generalized_of_small_dim`,
  `.bss_generalized_of_unique_of_small_dim`, each also under
  `Discretization.UpperBarrier`), and they are proved once for matrices and operators
  alike. For operators the normalized theorem is stated for a nonzero separable Hilbert
  space, with the same hypothesis `∫ b b* dμ = J` and the same
  `M = ∫ ‖b‖² dμ / Λ` (`Discretization.Infinite.bss_generalized_of_gram_eq_one'`). The
  number of points does not depend on the second family beyond `M`.

### The Kiefer–Wolfowitz theorem

Let `Ω` be any set, `ι` a finite nonempty index set with `m = card ι` elements, and
`a : Ω → ι → ℂ` a bounded family whose coordinate functions are linearly independent.
Then for every `ε > 0` there are points `x₁, …, xₙ ∈ Ω` and weights `w₁, …, wₙ ≥ 0`
summing to one such that

```
|f(y)|²  ≤  (m + ε) · ∑ wₖ |f(xₖ)|²
```

for every point `y ∈ Ω` and every `f` in the span of the family
(`Discretization.KieferWolfowitz.exists_design_kieferWolfowitz`). This is the theorem of
[Kiefer and Wolfowitz](https://doi.org/10.4153/CJM-1960-030-4), in the complex and
non-compact form of Proposition 9 of
[Krieg, Pozharska, Ullrich and Ullrich](https://arxiv.org/abs/2401.02220). Three variants
of it are proved:

* **As a measure.** The points and weights are a finitely supported probability measure
  `ϱ = ∑ wₖ δ(xₖ)` with invertible Gram matrix, and the inequality reads
  `|f(y)|² ≤ (m + ε) ∫ |f|² dϱ`
  (`Discretization.KieferWolfowitz.exists_probabilityMeasure_kieferWolfowitz`). The Gram
  matrix of `ϱ` in the sense of `Discretization.gram` is the one of the points and
  weights (`.gram_designMeasure`), which is what lets the measure be handed to the
  discretization theorem. On a compact domain this holds with `ε = 0` as well
  (`.exists_probabilityMeasure_kieferWolfowitz_of_compact`).
* **The sharp constant on a compact domain.** For continuous functions on a compact
  space the maximum of the determinant is attained, and the bound holds with `ε = 0`,
  that is with the constant `√m`
  (`Discretization.KieferWolfowitz.exists_design_kieferWolfowitz_of_compact`).
* **At most `2m² + 1` points.** Every design can be replaced by one with at most
  `2m² + 1` points and the same Gram matrix, so both statements hold with that many
  points (`Discretization.KieferWolfowitz.exists_design_card_le`,
  `.exists_design_kieferWolfowitz_card_le`,
  `.exists_design_kieferWolfowitz_of_compact_card_le`).

Alongside these, a design decomposes the identity. Writing `t(y) = a(y)* G⁻¹ a(y)` for
the variance function, the weights `wₖ t(xₖ)` are nonnegative and sum to `m`
(`Discretization.KieferWolfowitz.sum_weight_quadForm_inv_eq_card`), and
`∑ₖ wₖ ⟪a(xₖ), z⟫ a(xₖ) = z` for every vector `z` in the inner product
`⟪u, z⟫ = u* G⁻¹ z` of the ellipsoid of `G`
(`.sum_weight_smul_quadForm_inv_eq_self`). This is John's decomposition of the identity,
the condition dual to the Kiefer–Wolfowitz bound: on a compact domain the bound
`t(y) ≤ m` and the average `m` together force `t(xₖ) = m` at every design point, making
the points contact points. The theorem for a general convex body is proved in the
companion project [Lean-SNumbers](https://github.com/mario-ullrich/Lean-SNumbers) as
`John.john_decomposition`.

### The uniform norm with `n ≥ m` points

Under the same hypotheses, for every `ε > 0` and every `n ≥ m` there are points
`x₁, …, xₙ ∈ Ω`, not necessarily distinct, such that

```
|f(y)|²  ≤  (m + ε) / (1 − √((m−1)/n))² · (1/n) ∑ |f(xᵢ)|²
```

for every point `y ∈ Ω` and every `f` in the span of the family
(`Discretization.exists_uniform_discretization_by_l2`). For continuous functions on a compact
space the same holds with `ε = 0`
(`Discretization.exists_uniform_discretization_of_compact_by_l2`). The proof thins the
Kiefer–Wolfowitz design to `n` of its points by the one-sided discretization
(`Discretization.exists_one_sided_discretization`). This is the case `p = ∞` of
Proposition 8 of Chkifa, Dolbeault, Krieg and Ullrich. For `n = 2m` it gives
`‖f‖_∞ ≤ (1 + √2) √(1 + ε/m) (∑ᵢ₌₁²ᵐ |f(xᵢ)|²)^{1/2}`: the uniform norm on the span is
dominated by the Euclidean norm of `2m` sample values. Theorem 2 of
[Krieg, Pozharska, Ullrich and Ullrich](https://arxiv.org/abs/2401.02220) proves this with
the constant `42`, and Proposition 8 improves it to `1 + √2`. For `n = m` points the bound is
due to Novak, who obtains `‖f‖_∞ ≤ (m + ε) ((1/m) ∑ᵢ₌₁ᵐ |f(xᵢ)|²)^{1/2}` from a form of
Auerbach's lemma.

An average is at most its largest term, so the same points bound the uniform norm by the
largest sample value:

```
|f(y)|²  ≤  (m + ε) / (1 − √((m−1)/n))² · maxᵢ |f(xᵢ)|²
```

(`Discretization.exists_uniform_discretization_by_max`, and with `ε = 0` on a compact space
`Discretization.exists_uniform_discretization_of_compact_by_max`). For `n = 2m` this is
`‖f‖_∞ ≤ (2 + √2) √(m + ε) maxᵢ |f(xᵢ)|`, the bound that Chkifa, Dolbeault, Krieg and
Ullrich state with `√m`.

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
the two frame bounds. For a second family in a Hilbert space, `B` is a positive
invertible operator and the traces are sums along a Hilbert basis. Only the analysis
of `B` is redone, in `Discretization/Infinite/`: the construction, the read-off and the
edge cases use `B` through a handful of properties, collected in
`Discretization.UpperBarrier`, and are proved once for matrices and operators alike.

The second proof maximises a determinant. Among all finitely supported probability
measures one is chosen whose Gram matrix `G = ∑ wₖ a(xₖ) a(xₖ)*` has an almost maximal
determinant: the determinants are bounded above because the entries of `G` are, and one
of them is positive because the functions are linearly independent. Giving a further
point `y` the weight `α` yields such a measure again, and the matrix determinant lemma
says exactly what that does to the determinant, namely multiply it by
`(1-α)^(m-1) (1 + α (t - 1))` with `t = a(y)* G⁻¹ a(y)`. Almost maximality bounds that
factor, and Bernoulli's inequality with the explicit weight `α = (t-m)/(2m(t-1))` turns
the bound into `t ≤ m + ε`, uniformly in `y`. Subtracting `(m+ε)⁻¹ a(y) a(y)*` from `G`
then leaves a positive definite matrix, which read as an inequality between quadratic
forms is the theorem. On a compact domain the maximum is attained and the same argument
gives `t ≤ m`.

The steps the two arguments are built from:

* **Barrier lemma.** A weight between the values of the two verifier functions keeps
  both matrices positive definite and lets neither potential increase
  (`Discretization.lowerPotential_update_le`, `.upperPotential_update_le`,
  `.Infinite.upperPotential_update_le`).
* **The verifiers pass on average**, which is where the measure space enters: an
  admissible point exists because the lower verifier exceeds the upper one on average
  (`Discretization.integral_lowerVerifier_gt`, `.integral_upperVerifier_lt`,
  `.UpperBarrier.exists_admissible_point`).
* **One-sided constructions.** When one frame bound comes for free, the verifier on that side
  is replaced by a constant of average `n`, and only the other state is tracked
  (`Discretization.exists_points_weights_of_small_dim`,
  `.UpperBarrier.exists_points_weights_of_unique`, with the initial data of the lower half in
  `.exists_lower_initial_data`). The constant `n` as upper verifier is what bounds every
  weight by `1/n`.
* **A bound on a potential is a bound on the matrix**: `Φ(A)⁻¹ • 1 ≼ A` and
  `Ψ_J(B)⁻¹ • J ≼ B` (`Matrix.PosDef.inv_re_trace_smul_one_le`,
  `.inv_re_trace_mul_smul_le`, `Discretization.Infinite.inv_upperPotential_smul_le`).
* **The trace of a positive operator**, `Tr T = ∑ₖ Re ⟪eₖ, T eₖ⟫` along a Hilbert basis,
  which does not depend on the basis, with the cyclicity and the bound `T ≼ Tr(T) • 1` the
  argument needs (`ContinuousLinearMap.trace`, `.trace_eq_traceAlong`,
  `.tsum_inner_apply_comm`, `.le_traceAlong_smul_one`). In Lean the trace is computed along
  a basis chosen once. Mathlib has no trace outside finite dimension.
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
* **The Gram operator** `∫ b(x) b(x)* dμ(x)` as a Bochner integral, with its quadratic
  form `⟪u, J u⟫ = ∫ |⟪u, b(x)⟫|² dμ(x)` and the two readings of the hypotheses on it
  (`ContinuousLinearMap.inner_integral_rankOne_self`,
  `.le_smul_one_iff_of_inner_eq_integral`, `.injective_iff_of_inner_eq_integral`); on a
  separable space it is positive and of finite trace, with trace `∫ ‖b‖² dμ`
  (`Discretization.Infinite.isFiniteTracePos_of_integral_rankOne`,
  `.integral_norm_sq_eq_trace`).

Everything else is in the blueprint, with its Lean name at every statement.

## Organisation

Two libraries. `Discretization` holds the arguments: the arithmetic of the parameters,
the two potentials and the verifiers, the barrier lemma, the averaging step, the
`n`-step iteration, the potential argument with its edge cases under
`Discretization/EdgeCases/`, the discretization inequality, one-sided discretization
with equal weights, under `Discretization/Infinite/` the analysis of the upper state for a
second family in a Hilbert space with the theorem for it, a countable family and a
reproducing kernel Hilbert space, and under `Discretization/KieferWolfowitz/` the
maximisation of the determinant of a Gram matrix, the theorem it yields and John's
decomposition of the identity beside it, with its thinning to `n ≥ m` points by the
one-sided discretization at the top level. `BasicResults` holds what the arguments need and
Mathlib lacks: comparisons in the Loewner order, traces of products and Cauchy–Schwarz for
them, Sherman–Morrison for rank-one updates of a matrix and of an operator, the trace of
a positive operator on a Hilbert space, the Gram operator as a Bochner integral, the matrix
determinant lemma, the compactness of the convex hull of a compact set, and the bridge
from Bochner integrals to Gram matrices. The matrix facts lie under
`BasicResults/Matrix/`, their operator counterparts under `BasicResults/Operator/`, and
the general ones at the top level;
[MathlibCandidates.md](MathlibCandidates.md) lists what could be upstreamed.
`blueprint/` holds the LaTeX source of the blueprint and the scripts that point its
`\lean` links at this repository and order its dependency graph. `Palomar/` holds the submission surfaces for the
[Palomar registry](https://palomar-registry.org), one directory per registered result,
each with a `Challenge` module stating the advertised theorems and a `Solution` module
supplying their proofs from the development. The placeholder `sorry`s in the `Challenge`
modules are required by that format: a Challenge advertises statements and imports only
Mathlib, so a reader can audit what is claimed without reading the development. This
library sits outside `defaultTargets`; build it with `lake build Palomar`.

## What is left to do

* **Sampling projections in the uniform norm**: the weighted least-squares projection on
  the `2m` points of the uniform discretization, with norm of order `√m`.
* **The applications of the paper**: least-squares recovery and sampling numbers.

## Building

Requires [`elan`](https://github.com/leanprover/elan). The Lean version is pinned in
`lean-toolchain` and Mathlib in `lake-manifest.json`, so a clone builds against Lean /
Mathlib `v4.35.0-rc2`:

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
python blueprint/scripts/check_lean_decls.py   # checks that every \lean{Decl} resolves
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

* J. Batson, D. A. Spielman, N. Srivastava, *Twice-Ramanujan sparsifiers*, SIAM Review
  **56** (2014), no. 2, 315–334, [doi](https://doi.org/10.1137/130949117),
  [arxiv](https://arxiv.org/abs/0808.0163). The original potential-function argument.
* A. Chkifa, M. Dolbeault, D. Krieg, M. Ullrich, *Constructive discretization and
  approximation in reproducing kernel Hilbert spaces*, preprint, 2026,
  [arxiv](https://arxiv.org/abs/2602.18719). Theorem 3 is the result formalised here,
  Corollary 4 the discretization inequality, and its proof the one followed in
  `Discretization/`. Proposition 8 is the one-sided discretization for `p = 2` and the
  discretization of the uniform norm with `n ≥ m` points for `p = ∞`.
* J. Kiefer, J. Wolfowitz, *The equivalence of two extremum problems*, Canad. J. Math.
  **12** (1960), 363–366, [doi](https://doi.org/10.4153/CJM-1960-030-4). The original
  equivalence theorem for optimal designs.
* D. Krieg, K. Pozharska, M. Ullrich, T. Ullrich, *Sampling projections in the uniform
  norm*, J. Math. Anal. Appl. **553** (2026), no. 2, Paper No. 129873,
  [doi](https://doi.org/10.1016/j.jmaa.2025.129873),
  [arxiv](https://arxiv.org/abs/2401.02220). Proposition 9 is the Kiefer–Wolfowitz
  theorem formalised here, and its proof the one followed in
  `Discretization/KieferWolfowitz/`. Its Theorem 2 bounds the uniform norm by `2m` sample
  values with the constant `42`; the form with any `n ≥ m` points and the constant of
  Chkifa, Dolbeault, Krieg and Ullrich is in `Discretization/UniformDiscretization.lean`.
* F. Bartel, M. Schäfer, T. Ullrich, *Constructive subsampling of finite frames with
  applications in optimal function recovery*, Appl. Comput. Harmon. Anal. **65** (2023),
  209–248, [doi](https://doi.org/10.1016/j.acha.2023.02.004). One-sided discretization of
  the `L₂`-norm with equal weights on arbitrary spaces.
* I. Limonova, V. Temlyakov, *On sampling discretization in `L₂`*, J. Math. Anal. Appl.
  **515** (2022), no. 2, Paper No. 126457, [arxiv](https://arxiv.org/abs/2009.10789).
  Theorem 1.1 is a discretization of the `L₂`-norm with equal weights under a Nikol'skii-type
  inequality.
* E. Novak, *Deterministic and stochastic error bounds in numerical analysis*, Lecture Notes
  in Mathematics **1349**, Springer-Verlag, 1988. Lemma 1.2.2, Auerbach's lemma with
  function values, discretizes the uniform norm with `n = m` points.
