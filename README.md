# Norm discretization in Lean 4 / Mathlib

A Lean 4 / Mathlib formalisation of two theorems that replace a norm on an
`m`-dimensional space of functions by `n ≥ m` point evaluations. The **discretization
theorem** of Chkifa, Dolbeault, Krieg and Ullrich does this for the `L₂`-norm: a
weighted sum `∑ wᵢ |f(xᵢ)|²` bounds `∫ |f|² dμ` from below, and the same weighted sum
for the functions of a second, possibly infinite-dimensional family is bounded from
above in terms of its effective dimension. For a single family this is the
Batson–Spielman–Srivastava sparsification theorem. The **Kiefer–Wolfowitz theorem**
gives a measure whose `L₂`-norm bounds the uniform norm up to the factor `√(m+ε)`, and
discretizing that measure gives `n ≥ m` points that control the uniform norm.

* **Blueprint** (a webpage explaining the mathematics):
  <https://mario-ullrich.github.io/Lean-Discretization/>
* **Blueprint as PDF**:
  <https://mario-ullrich.github.io/Lean-Discretization/blueprint.pdf>
* **Dependency graph**:
  <https://mario-ullrich.github.io/Lean-Discretization/dep_graph_document.html>

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

in the Loewner order (`Discretization.Infinite.bss_generalized`). This is Theorem 3 of
[Chkifa, Dolbeault, Krieg and Ullrich](https://arxiv.org/abs/2602.18719). Both hypotheses
on `J` are conditions on `b`: `J ≤ Λ • 1` says `∫ |⟪u, b⟫|² dμ ≤ Λ ‖u‖²` for every
`u ∈ H`, and `J` is injective when `⟪u, b(·)⟫ = 0` almost everywhere only for `u = 0`.
Four consequences:

* **Sparsification**, the case `a = b`. The theorem of
  [Batson, Spielman and Srivastava](https://arxiv.org/abs/0808.0163), with `√((m-1)/n)`
  in place of their `√(m/n)`: for vectors `v_k ∈ ℂ^m` with `∑ v_k v_k* = 1` there are
  weights `s_k ≥ 0`, at most `n` of them nonzero, with
  `(1 - √((m-1)/n))² • 1 ≤ ∑ s_k v_k v_k* ≤ (1 + √((m-1)/n))² • 1`
  (`Discretization.bss_of_sum_eq_one`, and `Discretization.bss` on a measure space).
* **A countable family** `b = (b_k)_{k ∈ κ}` with `∑_k ‖b_k‖²_{L₂} < ∞`, the form of the
  paper: `J` is the Gram matrix `(∫ b_k b̄_l dμ)` on `ℓ²(κ)`, `M = ∑_k ‖b_k‖² / Λ`, and the
  upper bound reads `∑ wᵢ |∑_k c_k b_k(xᵢ)|² ≤ (1 + √((M-1)/n))² Λ ‖c‖²` for every
  `c ∈ ℓ²(κ)` (`Discretization.Countable.bss_generalized`, for finite `κ`
  `Discretization.bss_generalized`).
* **Discretization of the `L₂`-norm**, Corollary 4 of the paper. Let `H` be a separable
  Hilbert space of measurable functions on `Ω` with reproducing kernel `K` and
  `∫ K(x, x) dμ < ∞`, whose embedding into `L₂(μ)` is injective with squared norm at most
  `Λ`, and put `M = ∫ K(x, x) dμ / Λ`. Then
  `(1 - √((m-1)/n))² ∫ |f|² dμ ≤ ∑ wᵢ |f(xᵢ)|²` for every `f` in the span of the first
  family and `∑ wᵢ |g(xᵢ)|² ≤ (1 + √((M-1)/n))² Λ ‖g‖²_H` for every `g ∈ H`
  (`Discretization.RKHS.exists_discretization`).
* **One-sided discretization with equal weights.** On a probability space, for every
  `n ≥ m` there are points `x₁, …, xₙ`, not necessarily distinct, with
  `(1 - √((m-1)/n))² ∫ |f|² dμ ≤ (1/n) ∑ |f(xᵢ)|²` for every `f` in the span of the first
  family (`Discretization.exists_one_sided_discretization`). This is the case `p = 2` of
  Proposition 8 of the paper; [Limonova and Temlyakov](https://arxiv.org/abs/2009.10789)
  prove such a bound under a Nikol'skii-type inequality, and
  [Bartel, Schäfer and Ullrich](https://doi.org/10.1016/j.acha.2023.02.004) for arbitrary
  spaces up to constants.

### The Kiefer–Wolfowitz theorem

Let `Ω` be any set, `ι` a finite nonempty index set with `m = card ι` elements, and
`a : Ω → ι → ℂ` a bounded family whose coordinate functions are linearly independent.
Then for every `ε > 0` there are points `x₁, …, xₙ ∈ Ω` and weights `w₁, …, wₙ ≥ 0`
summing to one such that

```
‖f‖_∞²  ≤  (m + ε) · ∑ wₖ |f(xₖ)|²
```

for every `f` in the span of the family, where `‖f‖_∞ = sup_{y ∈ Ω} |f(y)|`
(`Discretization.KieferWolfowitz.exists_optimal_design`). This is the theorem of
[Kiefer and Wolfowitz](https://doi.org/10.4153/CJM-1960-030-4), in the complex and
non-compact form of Proposition 9 of
[Krieg, Pozharska, Ullrich and Ullrich](https://arxiv.org/abs/2401.02220). For continuous
functions on a compact space it holds with `ε = 0`
(`.exists_optimal_design_of_compact`), and both forms hold with at most `m² + 1` points
(`.exists_optimal_design_card_le`, `.exists_optimal_design_of_compact_card_le`). Read as a
finitely supported probability measure `ϱ = ∑ wₖ δ(xₖ)`, the bound is
`‖f‖_∞² ≤ (m + ε) ∫ |f|² dϱ` (`.exists_optimal_measure`), the form in which the design
enters the discretization theorem.

A design also decomposes the identity, as in John's theorem: with
`t(y) = a(y)* G⁻¹ a(y)` for the Gram matrix `G` of the design, the weights `wₖ t(xₖ)` sum
to `m`, and `∑ₖ wₖ ⟪a(xₖ), z⟫ a(xₖ) = z` in the inner product `⟪u, z⟫ = u* G⁻¹ z`
(`.sum_weight_quadForm_inv_eq_card`, `.sum_weight_smul_quadForm_inv_eq_self`). John's
theorem for a general convex body is `John.john_decomposition` in the companion project
[Lean-SNumbers](https://github.com/mario-ullrich/Lean-SNumbers).

### The uniform norm with `n ≥ m` points

Under the same hypotheses, for every `ε > 0` and every `n ≥ m` there are points
`x₁, …, xₙ ∈ Ω`, not necessarily distinct, such that

```
‖f‖_∞  ≤  √(m + ε) / (1 − √((m−1)/n)) · ((1/n) ∑ |f(xᵢ)|²)^{1/2}
```

for every `f` in the span of the family
(`Discretization.exists_uniform_discretization_by_l2`), and with `ε = 0` for continuous
functions on a compact space (`.exists_uniform_discretization_of_compact_by_l2`). This is
the case `p = ∞` of Proposition 8 of Chkifa, Dolbeault, Krieg and Ullrich, obtained by
thinning the Kiefer–Wolfowitz design with the one-sided discretization. For `n = 2m` it
gives `‖f‖_∞ ≤ (1 + √2) √(1 + ε/m) (∑ᵢ₌₁²ᵐ |f(xᵢ)|²)^{1/2}`; Theorem 2 of
[Krieg, Pozharska, Ullrich and Ullrich](https://arxiv.org/abs/2401.02220) has the
constant `42` in place of `1 + √2`.

An average is at most its largest term, so the same points bound the uniform norm by the
largest sample value:

```
‖f‖_∞  ≤  √(m + ε) / (1 − √((m−1)/n)) · maxᵢ |f(xᵢ)|
```

(`.exists_uniform_discretization_by_max`, `.exists_uniform_discretization_of_compact_by_max`).
For `n = m` points Novak obtains `‖f‖_∞ ≤ (m + ε) maxᵢ |f(xᵢ)|` from a form of Auerbach's
lemma.

### The `L_p`-norms with `n ≥ m` points

Let `(Ω, μ)` be a probability space and `a : Ω → ι → ℂ` a bounded measurable family of
`m = card ι` functions with positive definite Gram matrix `∫ a a* dμ`. Then for every
`n ≥ m` there are points `x₁, …, xₙ ∈ Ω`, not necessarily distinct, such that

```
κ ‖f‖_{L_p(μ)}  ≤  m^(1/2 − 1/p) · ((2/n) ∑ |f(xᵢ)|²)^(1/2),    κ = max(1 − √(m/n), 1/(2m)),
```

for every `f` in the span of the family and every `2 ≤ p ≤ ∞`, with one set of points for
all `p` (`Discretization.exists_lp_discretization`). This is Proposition 8 of Chkifa,
Dolbeault, Krieg and Ullrich, whose `2n` points, `n` for `μ` and `n` for the
Kiefer–Wolfowitz measure, are replaced here by `n` points with the same weight `2/n` each,
chosen for the mixture of the two measures. For `n = 2m` it gives
`‖f‖_p ≤ (2 + √2) m^(1/2 − 1/p) ((1/m) ∑ᵢ₌₁²ᵐ |f(xᵢ)|²)^(1/2)`.

## Palomar registry

The [Palomar registry](https://palomar-registry.org) re-checks a registered proof at a
fixed commit. The sparsification theorem of Batson, Spielman and Srivastava is registered
as [PALOMAR-2026-10-14-000002](https://palomar-registry.org/entry?id=PALOMAR-2026-10-14-000002&version=1),
checked at commit
[`209d4bf`](https://github.com/mario-ullrich/Lean-Discretization/tree/209d4bf72bec56fa7b181a24dacb8570b10a6986).

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

The `L_p`-norms combine the two. For the Kiefer–Wolfowitz measure `ϱ` of a suitable `ε`,
the one-sided discretization of the mixture `(μ + ϱ)/2` gives `n` points with
`(1 − r)² (A + B) ≤ X`, where `A` and `B` are the averages of `|f|²` for `μ` and for `ϱ`,
`X = (2/n) ∑ᵢ |f(xᵢ)|²` and `r = √((m−1)/n)`. Since `|f|² ≤ (m + ε) B` everywhere,
`∫ |f|^p dμ ≤ ((m + ε) B)^(p/2 − 1) A`, and `B^q A ≤ (A + B)^(q+1)` finishes. The factor `κ`
lies strictly below `1 − r`, and the choice `ε = m ((1 − r)²/κ² − 1)` makes this gap absorb
the `ε`.

The steps the arguments are built from:

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
one-sided discretization and the discretization of the `L_p`-norms at the top level.
`BasicResults` holds what the arguments need and Mathlib lacks: comparisons in the Loewner
order, traces of products and Cauchy–Schwarz for
them, Sherman–Morrison for rank-one updates of a matrix and of an operator, the trace of
a positive operator on a Hilbert space, the Gram operator as a Bochner integral, the matrix
determinant lemma, the compactness of the convex hull of a compact set, and the bridge
from Bochner integrals to Gram matrices. The matrix facts lie under
`BasicResults/Matrix/`, their operator counterparts under `BasicResults/Operator/`, and
the general ones at the top level;
[MathlibCandidates.md](MathlibCandidates.md) lists what could be upstreamed.
`blueprint/` holds the LaTeX source of the blueprint and the scripts that point its
`\lean` links at this repository, order its dependency graph, let it zoom and give every
result with dependencies its Uses button.
`Palomar/` holds the registry submissions, one directory per entry: a `Challenge` module
states the registered theorems on Mathlib alone, with `sorry` in place of the proofs as
the registry format requires, and a `Solution` module proves them from the development.
Build it separately with `lake build Palomar`.

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
  `Discretization/`. Proposition 8 is the one-sided discretization for `p = 2`, the
  discretization of all `L_p`-norms, `2 ≤ p ≤ ∞`, with one set of `n ≥ m` points, and the
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
