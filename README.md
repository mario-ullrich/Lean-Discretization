# Constructive discretization — Lean 4 / Mathlib formalisation

## The question

Given a family of functions on a measure space, can one replace the integral
`∫ |f|² dμ` by a finite weighted sum `∑ wᵢ |f(xᵢ)|²` of point evaluations, with a controlled
loss in both directions?  For a finite-dimensional space of functions this is the problem of
**norm discretization**, and the sharpest known answer of this type is the sparsification
theorem of Batson, Spielman and Srivastava (BSS).

This project formalises the generalisation of that theorem proved by Chkifa, Dolbeault,
Krieg and Ullrich, in which

* the two frame bounds are allowed to refer to **two different families** of functions, and
* the upper bound depends on the **effective dimension** `M = Tr J / Λ` of the second
  family, not on how many functions it contains.

The second point is what makes the result applicable to infinite-dimensional reproducing
kernel Hilbert spaces, and it is the reason the constants beat those obtainable from the
Kadison–Singer theorem.

## The theorem

Let `(Ω, μ)` be a measure space, `ι` a finite index set with `m = card ι ≥ 2` elements, and
`κ` a second finite index set.  Let

* `a : Ω → ι → ℂ` be square-integrable with Gram matrix `∫ a a* dμ = 1`, and
* `b : Ω → κ → ℂ` be square-integrable with Gram matrix `J = ∫ b b* dμ` positive definite,
  `J ≤ Λ • 1`, and effective dimension `M = Tr J / Λ ≥ 1 + 1/n`.

Then for every `n ≥ m` there are points `x₁, …, xₙ ∈ Ω` and weights `w₁, …, wₙ > 0` with

```
(1 - √((m-1)/n))² • 1  ≤  ∑ wᵢ a(xᵢ) a(xᵢ)*        (lower frame bound)
∑ wᵢ b(xᵢ) b(xᵢ)*      ≤  (1 + √((M-1)/n))² Λ • 1  (upper frame bound)
```

in the Loewner order.  This is `Discretization.bss_generalized_of_gram_eq_one`.  Without the
normalisation of the first family the lower bound reads `(1 - √((m-1)/n))² • I` with
`I = ∫ a a* dμ`, which is `Discretization.bss_generalized`; in eigenvalue form that is the
factor `λ_min(I)` of the paper.

The proof is the potential-function argument of BSS.  Two matrices are carried along, a
small one for the lower bound and a large one for the upper one; the two **potentials**
`Φ(A) = Re Tr A⁻¹` and `Ψ_J(B) = Re Tr (J B⁻¹)` measure how close they are to failure; each
step shifts the matrices, which makes both potentials worse by a computable amount, and then
spends that budget on one new sampling point chosen so that neither potential increases.

## What is formalised

Legend: ✅ proved unconditionally.  There is no `sorry` anywhere in this project, and
`#print axioms Discretization.bss_generalized_of_gram_eq_one` reports only `propext`,
`Classical.choice` and `Quot.sound`.

### Matrix analysis (`BasicResults`)

| Result | Lean name | Status |
|---|---|---|
| A Hermitian matrix is below `c • 1` if `c` bounds its eigenvalues | `Matrix.IsHermitian.le_smul_one` | ✅ |
| Conjugating by a Hermitian matrix preserves positivity | `Matrix.PosSemidef.mul_mul_same_of_isHermitian`, `Matrix.PosDef.mul_mul_same_of_isHermitian` | ✅ |
| `A ≼ (Tr A) • 1` for `A ≽ 0` | `Matrix.PosSemidef.le_trace_smul_one` | ✅ |
| The inverse is antitone | `Matrix.PosDef.inv_le_inv_of_le`, `Matrix.PosDef.smul_one_le_of_inv_le` | ✅ |
| `Φ(A)⁻¹ • 1 ≼ A` | `Matrix.PosDef.inv_re_trace_smul_one_le` | ✅ |
| `Ψ_J(B)⁻¹ • J ≼ B` | `Matrix.PosDef.inv_re_trace_mul_smul_le` | ✅ |
| `A - δ • 1` stays positive definite for `δ < Φ(A)⁻¹` | `Matrix.PosDef.sub_smul_one` | ✅ |
| `Tr (P Q) ≥ 0`, and `> 0` for positive definite factors | `Matrix.PosSemidef.trace_mul_nonneg`, `Matrix.PosDef.re_trace_mul_pos` | ✅ |
| `Tr (P Q)` is real for Hermitian `P`, `Q` | `Matrix.IsHermitian.ofReal_re_trace_mul` | ✅ |
| Cauchy–Schwarz for the trace | `Matrix.PosSemidef.norm_trace_mul_sq_le`, `.re_trace_mul_sq_le` | ✅ |
| Sherman–Morrison for a rank-one update | `Matrix.inv_add_smul_vecMulVec` | ✅ |
| The same with a real weight, added and subtracted | `Matrix.PosDef.inv_add_smul_vecMulVec`, `.inv_sub_smul_vecMulVec` | ✅ |
| The trace of a rank-one update | `Matrix.trace_inv_add_smul_vecMulVec` | ✅ |
| Positive definiteness under `A ± w a a*` | `Matrix.PosDef.add_smul_vecMulVec`, `.sub_smul_vecMulVec` | ✅ |

### The trace of an operator (`BasicResults.OperatorTrace`)

For the passage to a countably infinite second family, where the Gram matrix `J` becomes a
positive operator of finite trace on `ℓ₂`.  Mathlib has no trace-class theory, so the trace
is defined along a fixed Hilbert basis `e` as `Tr T = ∑ₖ Re ⟪eₖ, T eₖ⟫`.

| Result | Lean name | Status |
|---|---|---|
| Parseval's identity along a Hilbert basis | `Discretization.hasSum_norm_sq_inner` | ✅ |
| The trace along a basis | `Discretization.traceAlong` | ✅ |
| `Re ⟪x, T x⟫ = ‖√T x‖²`, so `Tr T` is a squared Hilbert–Schmidt norm | `Discretization.re_inner_apply_eq_norm_sq_sqrt`, `.traceAlong_eq_tsum_norm_sq_sqrt` | ✅ |
| `Tr T ≥ 0` for `T ≥ 0` | `Discretization.traceAlong_nonneg` | ✅ |
| The Hilbert–Schmidt sum is invariant under adjoints | `Discretization.tsum_ofReal_norm_sq_adjoint`, `.summable_norm_sq_adjoint_iff`, `.tsum_norm_sq_adjoint` | ✅ |
| **Cyclicity** `∑ₖ ⟪S eₖ, T eₖ⟫ = ∑ₖ ⟪T* eₖ, S* eₖ⟫` | `Discretization.tsum_inner_apply_comm` | ✅ |
| **The crude bound** `T ≼ Tr(T) • 1` | `Discretization.le_traceAlong_smul_one` | ✅ |
| `Tr (P Q) = Tr (√P Q √P)`, and its sign | `Discretization.traceAlong_mul`, `.traceAlong_mul_nonneg`, `.traceAlong_mul_pos` | ✅ |
| A positive operator with vanishing trace is zero | `Discretization.eq_zero_of_traceAlong_eq_zero` | ✅ |
| `Tr (T u u*) = ⟪u, T u⟫` | `Discretization.traceAlong_mul_rankOne` | ✅ |
| Linearity, and existence of `Tr (P Q)` | `Discretization.traceAlong_add`, `.traceAlong_smul`, `.summable_re_inner_apply_mul` | ✅ |

### Rank-one updates of an operator (`BasicResults.OperatorShermanMorrison`)

| Result | Lean name | Status |
|---|---|---|
| **Sherman–Morrison for operators** | `Discretization.inverse_add_smul_rankOne` | ✅ |
| A rank-one update of a unit is a unit | `Discretization.isUnit_add_smul_rankOne` | ✅ |
| The same with a real weight, added and subtracted | `Discretization.inverse_add_smul_rankOne_of_nonneg`, `.inverse_sub_smul_rankOne_of_nonneg` | ✅ |
| Strict positivity under `A ± w u u*` | `Discretization.isStrictlyPositive_add_smul_rankOne`, `.isStrictlyPositive_sub_smul_rankOne` | ✅ |
| The inverse of a strictly positive operator | `Discretization.isStrictlyPositive_inverse`, `.isSelfAdjoint_inverse` | ✅ |

### Averages of operator quadratic forms (`BasicResults.OperatorQuadraticForm`)

| Result | Lean name | Status |
|---|---|---|
| **`∫ Re ⟪b x, Q (b x)⟫ dμ = Tr (J Q)`** | `Discretization.integral_re_inner_apply` | ✅ |
| `Tr (J Q) = ∑ₖ Re ⟪√Q eₖ, J (√Q eₖ)⟫` | `Discretization.traceAlong_mul_eq_tsum_sqrt` | ✅ |
| `√Q √J` is Hilbert–Schmidt | `Discretization.summable_norm_sq_sqrt_mul_sqrt` | ✅ |
| Integrability of the quadratic form | `Discretization.integrable_re_inner_apply` | ✅ |

### The bridge to measure theory (`BasicResults.IntegralQuadraticForm`)

| Result | Lean name | Status |
|---|---|---|
| The Gram matrix of a square-integrable family | `Discretization.gram` | ✅ |
| `∫ a(x)* Q a(x) dμ = Tr (Q · gram a μ)` | `Discretization.integral_quadForm`, `.integral_re_quadForm` | ✅ |
| Integrability of the quadratic form | `Discretization.integrable_quadForm` | ✅ |
| A point where `g ≤ f` exists if `∫ g < ∫ f` | `Discretization.exists_lt_of_integral_lt` | ✅ |

### The construction (`Discretization`)

| Result | Lean name | Status |
|---|---|---|
| The arithmetic of the parameters `r`, `s`, `δ`, `ζ` | `Discretization.one_div_le_sqrt_div`, `.eq_mul_sq_sqrt_div_add_one`, `.one_div_add_div_eq`, `.lt_inv_of_le_one_div_sub` | ✅ |
| The two potentials and their positivity | `Discretization.lowerPotential`, `.upperPotential` | ✅ |
| Effect of the shifts on the potentials | `Discretization.lowerPotential_sub_eq`, `.upperPotential_sub_eq` | ✅ |
| The potential of a rank-one update, in closed form | `Discretization.lowerPotential_add_smul_vecMulVec`, `.upperPotential_sub_smul_vecMulVec` | ✅ |
| The verifiers | `Discretization.lowerVerifier`, `.upperVerifier` | ✅ |
| **Barrier lemma** | `Discretization.lowerPotential_update_le`, `.upperPotential_update_le` | ✅ |
| The inequality each half of it rests on | `Discretization.lower_barrier_ineq`, `.upper_barrier_ineq` | ✅ |
| The verifiers pass on average | `Discretization.integral_lowerVerifier_gt`, `.integral_upperVerifier_lt` | ✅ |
| An admissible point exists | `Discretization.exists_admissible_point` | ✅ |
| The `n`-step construction | `Discretization.exists_points_weights` | ✅ |
| Reading off the frame bounds | `Discretization.lower_bound_of_state`, `.upper_bound_of_state` | ✅ |
| The frame bounds with the parameters inserted | `Discretization.lower_frame_bound`, `.upper_frame_bound` | ✅ |
| **The theorem, normalized first family** | `Discretization.bss_generalized_of_gram_eq_one` | ✅ |
| Gram matrix of a linearly transformed family | `Discretization.gram_mulVec` | ✅ |
| **The theorem, general first family** | `Discretization.bss_generalized` | ✅ |
| A quadratic form is a weighted sum of squares | `Discretization.re_dotProduct_sum_mulVec`, `.integral_norm_sq_combination` | ✅ |
| **The discretization inequality for the `L₂`-norm** | `Discretization.exists_discretization` | ✅ |
| Edge case `m = 1`: constant lower verifier | `Discretization.bss_generalized_of_unique` | ✅ |
| Edge case `M ≤ 1 + 1/n`: constant upper verifier | `Discretization.bss_generalized_of_small_dim` | ✅ |
| A rank-one matrix is below `‖u‖² • 1` | `Matrix.vecMulVec_le_norm_sq_smul_one` | ✅ |

### Towards a countably infinite second family (`Discretization.Infinite`)

| Result | Lean name | Status |
|---|---|---|
| Positive, injective, of finite trace | `Discretization.Infinite.IsFiniteTracePos` | ✅ |
| `J S J` is again such an operator | `Discretization.Infinite.IsFiniteTracePos.conj` | ✅ |
| The upper potential `Ψ_J(B) = Tr (J B⁻¹)` and its positivity | `Discretization.Infinite.upperPotential`, `.upperPotential_pos` | ✅ |
| The resolvent identity | `Discretization.Infinite.inverse_sub_inverse_add_smul` | ✅ |
| Effect of the shift on the potential | `Discretization.Infinite.upperPotential_sub_eq` | ✅ |
| Growing `B` decreases the potential strictly | `Discretization.Infinite.upperPotential_add_smul_lt` | ✅ |

## What is left to do

* **The two edge cases together**, `m = 1` and `M ≤ 1 + 1/n` at the same time; each is
  proved only under the assumption that the other side is regular.
* **Countably infinite second family**, which is what makes the theorem apply to a
  reproducing kernel Hilbert space with finite trace.  The operator analogues of the general
  ingredients are in place, as is the upper potential with the effect of the shift on it.
  The verifier, the barrier lemma, the averaging step and the construction are not.
* **The applications of the paper**: least-squares recovery, sampling numbers, and the
  discretization with equal weights via Kiefer–Wolfowitz.

## Candidates for Mathlib

Everything in `BasicResults` is stated for a general `RCLike` field wherever the C⋆-algebra
structure is not needed, and none of it is currently in Mathlib:

* `Matrix.PosSemidef.trace_mul_nonneg` and `Matrix.PosDef.re_trace_mul_pos` — the trace of a
  product of positive semidefinite matrices;
* `Matrix.PosSemidef.le_trace_smul_one` and `Matrix.IsHermitian.le_smul_one`;
* `Matrix.PosDef.inv_le_inv_of_le` — antitonicity of the inverse in the Loewner order,
  packaged for matrices;
* `Matrix.inv_add_smul_vecMulVec`, `Matrix.trace_inv_add_smul_vecMulVec` and the real-weight
  forms `Matrix.PosDef.inv_add_smul_vecMulVec`, `Matrix.PosDef.inv_sub_smul_vecMulVec` —
  Sherman–Morrison for rank-one updates written with `Matrix.vecMulVec` (Mathlib has only the
  block form, `Matrix.add_mul_mul_inv_eq_sub`);
* `Matrix.PosSemidef.mul_mul_same_of_isHermitian` and `Matrix.PosDef.mul_mul_same_of_isHermitian`
  — conjugation by a Hermitian matrix, the form of
  `Matrix.PosSemidef.conjTranspose_mul_mul_same` that arises in practice;
* `Matrix.PosSemidef.norm_trace_mul_sq_le` — Cauchy–Schwarz for the trace semi-inner product
  (Mathlib's own construction of that inner product is `private`);
* `Matrix.IsHermitian.ofReal_re_trace` and `RCLike.ofReal_re_of_nonneg` — the trace of a
  Hermitian matrix and any nonnegative scalar are real;
* `Discretization.integral_quadForm` — the average of a quadratic form is a trace against the
  Gram matrix;
* the whole of `BasicResults.OperatorTrace`: Mathlib has no trace of an operator, and the
  invariance of the Hilbert–Schmidt norm under adjoints, the cyclicity
  `∑ₖ ⟪S eₖ, T eₖ⟫ = ∑ₖ ⟪T* eₖ, S* eₖ⟫` and the bound `T ≼ Tr(T) • 1` are general facts;
* `Discretization.inverse_add_smul_rankOne` — Sherman–Morrison for operators, which Mathlib
  has in no form;
* `Discretization.integral_re_inner_apply` — the average of an operator quadratic form along
  a square-integrable family is a trace against its Gram operator.

## Layout

```
BasicResults.lean                        ← root of the general library
BasicResults/
  OperatorTrace.lean                     ← the trace of an operator along a Hilbert basis
  OperatorShermanMorrison.lean           ← rank-one updates of an operator
  OperatorQuadraticForm.lean             ← averages of quadratic forms as traces
  LoewnerOrder.lean                      ← comparisons with multiples of the identity
  TraceInequalities.lean                 ← traces of products, Cauchy–Schwarz
  PotentialBounds.lean                   ← Ψ(B)⁻¹ • J ≼ B, via the square root of B
  ShermanMorrison.lean                   ← rank-one updates of inverse and trace
  IntegralQuadraticForm.lean             ← Gram matrices and averages of quadratic forms
Discretization.lean                      ← root of the theory
Discretization/
  Parameters.lean                        ← the arithmetic of r, s, δ, ζ
  Potentials.lean                        ← the two potentials and the effect of the shifts
  Barrier.lean                           ← verifiers and the barrier lemma
  Averages.lean                          ← the verifiers pass on average
  Iteration.lean                         ← the n-step construction
  MainTheorem.lean                       ← initial data, frame bounds, the theorem
  GeneralGram.lean                       ← removing the normalisation of the first family
  NormDiscretization.lean                ← the discretization inequality for the L₂-norm
  Infinite/
    Potentials.lean                      ← the upper potential of an operator
  CardOne.lean                           ← the edge case of a one-element first family
  SmallEffectiveDim.lean                 ← the edge case of a small effective dimension
lakefile.toml                            ← package `discretization`, two libraries
lean-toolchain                           ← leanprover/lean4:v4.33.1
lake-manifest.json                       ← Mathlib pinned to the v4.33.1 tag
```

The dependencies live **outside** the repository, in `../lake-packages/v4.33.1`, so that all
projects of this workspace that pin the same toolchain share one built Mathlib.  The
`packagesDir` line of `lakefile.toml` says so, and the folder is named after the version it
holds, which lets several Mathlib versions coexist.

## Building

```
lake exe cache get   # only if ../lake-packages/v4.33.1 does not exist yet
lake build
```

Do **not** run `lake update`: it re-resolves the dependencies and makes the build
non-reproducible.  Run `lake` from inside this folder, since `elan` reads `lean-toolchain`
from the working directory.

## References

A. Chkifa, M. Dolbeault, D. Krieg, M. Ullrich, *Constructive discretization and approximation
in reproducing kernel Hilbert spaces* — Theorem 3 is the result formalised here, and
Section 4 is the proof followed in `Discretization/`.

J. Batson, D. A. Spielman, N. Srivastava, *Twice-Ramanujan sparsifiers*, SIAM Review 56
(2014), 315–334 — the original potential-function argument.

## AI assistance

The formalisation was written with Claude Code.  Every statement and proof was checked by
Lean; the mathematical design, the choice of statements and the review of what the proofs
actually say are the author's.
