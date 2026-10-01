/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import Discretization.NormDiscretization
public import Discretization.Infinite.GeneralGram

/-!
# The discretization inequality with a second family in a Hilbert space

The theorems `Discretization.Infinite.bss_generalized_of_hilbertBasis` and
`Discretization.Infinite.bss_generalized` read as inequalities between norms, the operator
counterpart of `Discretization.exists_discretization`.

For a coefficient vector `c` the function `f(x) = ⟪c, a(x)⟫` lies in the span of the first
family, and the lower frame bound says

`(1 - r)² ∫ |f|² dμ ≤ ∑ᵢ wᵢ |f(xᵢ)|²`.

On the upper side a vector `u : H` plays the role of a coefficient vector: the function
`g(x) = ⟪u, b(x)⟫` is the general element of the space spanned by the second family, and the
upper frame bound says

`∑ᵢ wᵢ |g(xᵢ)|² ≤ (1 + s)² Λ ‖u‖²`.

Both statements hold uniformly, with the same points and weights.  This is Corollary 4 of
the paper: if `b` is the singular basis of the embedding of a reproducing kernel Hilbert
space into `L₂`, that is, an orthonormal basis of the space that is orthogonal in `L₂`, then
the right-hand side is the squared norm of `g` in that space.

The dictionary is the same as in finite dimension, with the quadratic form of a weighted sum
of rank-one operators (`ContinuousLinearMap.re_inner_sum_rankOne`) in place of the quadratic
form of a sum of rank-one matrices.  The lower half is the finite
`Discretization.mul_integral_norm_sq_le_sum`, the upper half
`Discretization.Infinite.sum_mul_norm_sq_inner_le`.

As for the frame bounds, there are two forms: along a given Hilbert basis
(`Discretization.Infinite.exists_discretization_of_hilbertBasis`), and without a basis in
the statement for a separable space, where the Gram operator is `J = ∫ b(x) b(x)* dμ(x)`,
the only hypothesis on it besides `J ≤ Λ • 1` is injectivity, and `M = ∫ ‖b‖² dμ / Λ`
(`Discretization.Infinite.exists_discretization`).
-/

@[expose] public section

open Matrix MeasureTheory
open scoped InnerProductSpace ComplexOrder MatrixOrder
open InnerProductSpace
open ContinuousLinearMap

namespace Discretization

namespace Infinite

variable {ι κ Ω H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {e : HilbertBasis κ ℂ H} {J : H →L[ℂ] H}

/-! ### The quadratic form of a multiple of the identity -/

/-- The quadratic form of a multiple of the identity is the squared norm. -/
theorem re_inner_smul_one (c : ℝ) (u : H) :
    RCLike.re ⟪u, (c • (1 : H →L[ℂ] H)) u⟫_ℂ = c * ‖u‖ ^ 2 := by
  rw [show (c • (1 : H →L[ℂ] H)) u = c • u from rfl, RCLike.real_smul_eq_coe_smul (K := ℂ),
    inner_smul_real_right, RCLike.smul_re, inner_self_eq_norm_sq]

/-- **An upper frame bound between operators is a bound on quadratic forms.**  If the
weighted sum of the rank-one operators `b(xᵢ) b(xᵢ)*` is at most `C • 1`, then

`∑ᵢ wᵢ |⟪u, b(xᵢ)⟫|² ≤ C ‖u‖²`  for every `u ∈ H`. -/
theorem sum_mul_norm_sq_inner_le [CompleteSpace H] {n : ℕ} {x : Fin n → Ω} {w : Fin n → ℝ}
    {b : Ω → H} {C : ℝ} (h : ∑ i, w i • rankOne ℂ (b (x i)) (b (x i)) ≤ C • (1 : H →L[ℂ] H))
    (u : H) : ∑ i, w i * ‖⟪u, b (x i)⟫_ℂ‖ ^ 2 ≤ C * ‖u‖ ^ 2 := by
  calc ∑ i, w i * ‖⟪u, b (x i)⟫_ℂ‖ ^ 2
      = RCLike.re ⟪u, (∑ i, w i • rankOne ℂ (b (x i)) (b (x i))) u⟫_ℂ :=
        (re_inner_sum_rankOne x w b u).symm
    _ ≤ RCLike.re ⟪u, (C • (1 : H →L[ℂ] H)) u⟫_ℂ := re_inner_le_of_le h u
    _ = C * ‖u‖ ^ 2 := re_inner_smul_one C u

/-! ### The discretization inequality -/

variable [Fintype ι] [DecidableEq ι] [CompleteSpace H] [MeasurableSpace Ω] {μ : Measure Ω}

/-- **Discretization of the `L₂`-norm, with a countable second family.**

Under the hypotheses of `Discretization.Infinite.bss_generalized_of_gram_eq_one'`, the `n`
points and weights discretize the norm of every function in the span of the first family
from below,

`(1 - √((m-1)/n))² · ∫ |f|² dμ ≤ ∑ᵢ wᵢ |f(xᵢ)|²`,

and bound the weighted sum for every function in the span of the second family from above,

`∑ᵢ wᵢ |⟪u, b(xᵢ)⟫|² ≤ (1 + √((M-1)/n))² Λ · ‖u‖²`.

This is Corollary 4 of the paper for an infinite-dimensional second family: what controls
the number of points is the effective dimension `M = Tr J / Λ`, and there is no side
condition beyond `n ≥ m`. -/
theorem exists_discretization_of_hilbertBasis [Nonempty ι] [Nonempty κ] [Countable κ]
    (hJ : IsFiniteTracePos e J) {Λ : ℝ} (hΛ : 0 < Λ)
    (hJΛ : J ≤ Λ • (1 : H →L[ℂ] H)) {a : Ω → ι → ℂ} {b : Ω → H}
    (ha : ∀ k, MemLp (fun x => a x k) 2 μ) (hb : MemLp b 2 μ) (hgrama : gram a μ = 1)
    (hgramb : ∀ u, RCLike.re ⟪u, J u⟫_ℂ = ∫ x, ‖⟪u, b x⟫_ℂ‖ ^ 2 ∂μ)
    {n : ℕ} (hmn : Fintype.card ι ≤ n) :
    ∃ (x : Fin n → Ω) (w : Fin n → ℝ), (∀ i, 0 < w i) ∧
      (∀ c : ι → ℂ, (1 - Real.sqrt ((Fintype.card ι - 1) / n)) ^ 2
            * ∫ y, ‖star c ⬝ᵥ a y‖ ^ 2 ∂μ
          ≤ ∑ i, w i * ‖star c ⬝ᵥ a (x i)‖ ^ 2) ∧
      (∀ u : H, ∑ i, w i * ‖⟪u, b (x i)⟫_ℂ‖ ^ 2
          ≤ (1 + Real.sqrt ((traceAlong e J / Λ - 1) / n)) ^ 2 * Λ * ‖u‖ ^ 2) := by
  obtain ⟨x, w, hwpos, hlow, hup⟩ :=
    bss_generalized_of_gram_eq_one' hJ hΛ hJΛ ha hb hgrama hgramb hmn
  exact ⟨x, w, hwpos, mul_integral_norm_sq_le_sum ha (by rwa [hgrama]),
    sum_mul_norm_sq_inner_le hup⟩

/-- **Discretization of the `L₂`-norm for a second family with values in a separable Hilbert
space**, with no basis in the statement.

Let `a` be a family of square-integrable functions indexed by a finite nonempty set `ι` of
`m` elements with Gram matrix `1`, and let `b : Ω → H` be square-integrable, with values in a
nonzero separable Hilbert space, with injective Gram operator `J = ∫ b(x) b(x)* dμ(x)`
satisfying `J ≤ Λ • 1`.  Put `M = ∫ ‖b‖² dμ / Λ`.  Then for every `n ≥ m` there are `n`
points and positive weights with

`(1 - √((m-1)/n))² · ∫ |f|² dμ ≤ ∑ᵢ wᵢ |f(xᵢ)|²`  for every `f` in the span of `a`, and
`∑ᵢ wᵢ |⟪u, b(xᵢ)⟫|² ≤ (1 + √((M-1)/n))² Λ · ‖u‖²`  for every `u ∈ H`. -/
theorem exists_discretization [Nonempty ι] [TopologicalSpace.SeparableSpace H]
    [Nontrivial H] {Λ : ℝ} (hΛ : 0 < Λ) (hJΛ : J ≤ Λ • (1 : H →L[ℂ] H))
    (hJinj : ∀ v, J v = 0 → v = 0) {a : Ω → ι → ℂ} {b : Ω → H}
    (ha : ∀ k, MemLp (fun x => a x k) 2 μ) (hb : MemLp b 2 μ) (hgrama : gram a μ = 1)
    (hgramb : ∫ x, rankOne ℂ (b x) (b x) ∂μ = J)
    {n : ℕ} (hmn : Fintype.card ι ≤ n) :
    ∃ (x : Fin n → Ω) (w : Fin n → ℝ), (∀ i, 0 < w i) ∧
      (∀ c : ι → ℂ, (1 - Real.sqrt ((Fintype.card ι - 1) / n)) ^ 2
            * ∫ y, ‖star c ⬝ᵥ a y‖ ^ 2 ∂μ
          ≤ ∑ i, w i * ‖star c ⬝ᵥ a (x i)‖ ^ 2) ∧
      (∀ u : H, ∑ i, w i * ‖⟪u, b (x i)⟫_ℂ‖ ^ 2
          ≤ (1 + Real.sqrt (((∫ y, ‖b y‖ ^ 2 ∂μ) / Λ - 1) / n)) ^ 2 * Λ * ‖u‖ ^ 2) := by
  obtain ⟨x, w, hwpos, hlow, hup⟩ :=
    bss_generalized hΛ hJΛ hJinj ha hb (by rw [hgrama]; exact Matrix.PosDef.one) hgramb hmn
  exact ⟨x, w, hwpos, mul_integral_norm_sq_le_sum ha hlow, sum_mul_norm_sq_inner_le hup⟩

end Infinite

end Discretization
