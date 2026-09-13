/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
import BasicResults.LoewnerOrder

/-!
# Quadratic forms and sums of squares

The dictionary between matrices and functions.  A coefficient vector `c` gives the function
`f(x) = ⟪c, a(x)⟫ = ∑ conj (cₖ) aₖ(x)`, and the three facts below turn statements about the
matrices `a(x) a(x)*` into statements about the numbers `|f(x)|²`:

* `Discretization.re_dotProduct_vecMulVec_mulVec`: the quadratic form of a rank-one matrix
  is a squared modulus, `c* (u u*) c = |⟪c, u⟫|²`;
* `Discretization.re_dotProduct_sum_mulVec`: hence the quadratic form of a weighted sum of
  rank-one matrices is the corresponding weighted sum of squared moduli,
  `c* (∑ wᵢ a(xᵢ) a(xᵢ)*) c = ∑ wᵢ |f(xᵢ)|²`;
* `Discretization.re_quadForm_le_of_le`: the quadratic form is monotone for the Loewner
  order, so a Loewner inequality between matrices is exactly an inequality between
  quadratic forms, uniformly in the coefficient vector.

Nothing here mentions integrals, and the points `xᵢ` are drawn from a bare type, so the
three facts serve both the sparsification theorem and the Kiefer–Wolfowitz theorem.
-/

open Matrix
open scoped ComplexOrder MatrixOrder

namespace Discretization

variable {ι Ω : Type*} [Fintype ι]

/-- The quadratic form of a rank-one matrix is a squared modulus:
`c* (u u*) c = |⟪c, u⟫|²`. -/
theorem re_dotProduct_vecMulVec_mulVec (u c : ι → ℂ) :
    RCLike.re (star c ⬝ᵥ ((vecMulVec u (star u)) *ᵥ c)) = ‖star c ⬝ᵥ u‖ ^ 2 := by
  rw [Matrix.vecMulVec_mulVec, dotProduct_smul, op_smul_eq_mul, Matrix.star_dotProduct u c,
    RCLike.star_def, RCLike.mul_conj]
  norm_cast

/-- The quadratic form of a weighted sum of rank-one matrices is the corresponding weighted
sum of squared moduli. -/
theorem re_dotProduct_sum_mulVec {k : ℕ} (x : Fin k → Ω) (w : Fin k → ℝ) (c : ι → ℂ)
    (a : Ω → ι → ℂ) :
    RCLike.re (star c ⬝ᵥ ((∑ i, w i • vecMulVec (a (x i)) (star (a (x i)))) *ᵥ c))
      = ∑ i, w i * ‖star c ⬝ᵥ a (x i)‖ ^ 2 := by
  simp only [Matrix.sum_mulVec, dotProduct_sum, map_sum, Matrix.smul_mulVec,
    dotProduct_smul, RCLike.smul_re, re_dotProduct_vecMulVec_mulVec]

/-- The quadratic form is monotone for the Loewner order. -/
theorem re_quadForm_le_of_le {A B : Matrix ι ι ℂ} (h : A ≤ B) (c : ι → ℂ) :
    RCLike.re (star c ⬝ᵥ (A *ᵥ c)) ≤ RCLike.re (star c ⬝ᵥ (B *ᵥ c)) := by
  have hd := (Matrix.le_iff.1 h).re_dotProduct_nonneg c
  rw [Matrix.sub_mulVec, dotProduct_sub, map_sub] at hd
  linarith

end Discretization
