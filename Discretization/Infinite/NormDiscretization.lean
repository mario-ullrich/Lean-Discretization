/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
import Discretization.NormDiscretization
import Discretization.Infinite.BothEdgeCases

/-!
# The discretization inequality with a countable second family

The theorem `Discretization.Infinite.bss_generalized_of_gram_eq_one'` read as an inequality
between norms, the operator counterpart of `Discretization.exists_discretization`.

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
form of a sum of rank-one matrices.
-/

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
theorem exists_discretization [Nonempty ι] [Nonempty κ] [Countable κ]
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
  refine ⟨x, w, hwpos, fun c => ?_, fun u => ?_⟩
  · -- the lower half is the finite statement
    have h1 : RCLike.re (star c ⬝ᵥ ((1 : Matrix ι ι ℂ) *ᵥ c)) = ∑ k, ‖c k‖ ^ 2 := by
      simpa using re_quadForm_smul_one (ι := ι) 1 c
    calc (1 - Real.sqrt ((Fintype.card ι - 1) / n)) ^ 2 * ∫ y, ‖star c ⬝ᵥ a y‖ ^ 2 ∂μ
        = RCLike.re (star c ⬝ᵥ
            (((1 - Real.sqrt ((Fintype.card ι - 1) / n)) ^ 2 • (1 : Matrix ι ι ℂ)) *ᵥ c)) := by
          rw [re_quadForm_smul_one, integral_norm_sq_combination ha c, hgrama, h1]
      _ ≤ RCLike.re (star c ⬝ᵥ
            ((∑ i, w i • Matrix.vecMulVec (a (x i)) (star (a (x i)))) *ᵥ c)) :=
          re_quadForm_le_of_le hlow c
      _ = ∑ i, w i * ‖star c ⬝ᵥ a (x i)‖ ^ 2 := re_dotProduct_sum_mulVec x w c a
  · -- the upper half, read through the operator order
    calc ∑ i, w i * ‖⟪u, b (x i)⟫_ℂ‖ ^ 2
        = RCLike.re ⟪u, (∑ i, w i • rankOne ℂ (b (x i)) (b (x i))) u⟫_ℂ :=
          (re_inner_sum_rankOne x w b u).symm
      _ ≤ RCLike.re ⟪u, (((1 + Real.sqrt ((traceAlong e J / Λ - 1) / n)) ^ 2 * Λ)
            • (1 : H →L[ℂ] H)) u⟫_ℂ := re_inner_le_of_le hup u
      _ = (1 + Real.sqrt ((traceAlong e J / Λ - 1) / n)) ^ 2 * Λ * ‖u‖ ^ 2 :=
          re_inner_smul_one _ u

end Infinite

end Discretization
