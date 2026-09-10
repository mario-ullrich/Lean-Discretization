/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
import BasicResults.LoewnerOrder
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Function.LpSeminorm.Monotonicity
import Mathlib.Data.ENNReal.Holder

/-!
# From integrals of quadratic forms to Gram matrices

The link between the analytic side of the problem (functions on a measure space) and the
matrix algebra of the previous files is a single identity.  For a finite family of
square-integrable functions, assembled into a vector-valued map `a : D → ι → ℂ`, and its
**Gram matrix**

`gram a μ k l = ∫ aₖ(x) · conj (aₗ(x)) dμ(x)`,

every matrix `Q` satisfies

`∫ a(x)* Q a(x) dμ(x) = Tr (Q · gram a μ)`.

Read from left to right this computes the average of a quadratic form along the family;
read from right to left it says that the trace of `Q` against the Gram matrix is an
average, which is how the potential-function argument finds a good sampling point.

The file also records the two auxiliary facts that go with it: the integrand is integrable
(Cauchy–Schwarz for `L₂` functions, `MeasureTheory.MemLp.integrable_mul`), and if the
average of `g` is smaller than the average of `f`, then `g x ≤ f x` at some point
(`Discretization.exists_lt_of_integral_lt`).  The latter replaces the "set of positive
measure" formulation of the paper: for our purposes one single good point is enough.
-/

open Matrix MeasureTheory
open scoped ComplexOrder MatrixOrder

namespace Discretization

variable {ι D : Type*} [Fintype ι] [MeasurableSpace D] {μ : Measure D} {a : D → ι → ℂ}

/-- The **Gram matrix** of a finite family of functions `a : D → ι → ℂ`, with entries
`∫ aₖ · conj aₗ dμ`.  In the notation of the paper this is `∫ a(x) a(x)* dμ(x)`. -/
noncomputable def gram (a : D → ι → ℂ) (μ : Measure D) : Matrix ι ι ℂ :=
  Matrix.of fun k l => ∫ x, a x k * star (a x l) ∂μ

omit [Fintype ι] in
@[simp]
theorem gram_apply (a : D → ι → ℂ) (μ : Measure D) (k l : ι) :
    gram a μ k l = ∫ x, a x k * star (a x l) ∂μ := rfl

omit [Fintype ι] in
/-- The Gram matrix is Hermitian: swapping the two indices conjugates the entry. -/
theorem isHermitian_gram (a : D → ι → ℂ) (μ : Measure D) : (gram a μ).IsHermitian := by
  ext k l
  rw [Matrix.conjTranspose_apply, gram_apply, gram_apply, RCLike.star_def, ← integral_conj]
  exact integral_congr_ae (Filter.Eventually.of_forall fun x => by simp [mul_comm])

omit [Fintype ι] in
/-- The product of two members of the family is integrable, by Cauchy–Schwarz for
`L₂`-functions. -/
theorem integrable_mul_star (ha : ∀ k, MemLp (fun x => a x k) 2 μ) (k l : ι) :
    Integrable (fun x => a x k * star (a x l)) μ :=
  (ha k).integrable_mul (ha l).star

omit [MeasurableSpace D] in
/-- The quadratic form `a(x)* Q a(x)` written as a double sum. -/
theorem quadForm_eq_sum (Q : Matrix ι ι ℂ) (x : D) :
    star (a x) ⬝ᵥ (Q *ᵥ a x) = ∑ k, ∑ l, Q k l * (a x l * star (a x k)) := by
  simp only [dotProduct, Matrix.mulVec, Pi.star_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring

/-- The quadratic form of a fixed matrix along the family is integrable. -/
theorem integrable_quadForm (ha : ∀ k, MemLp (fun x => a x k) 2 μ) (Q : Matrix ι ι ℂ) :
    Integrable (fun x => star (a x) ⬝ᵥ (Q *ᵥ a x)) μ := by
  have hint : ∀ k l, Integrable (fun x => Q k l * (a x l * star (a x k))) μ := fun k l =>
    (integrable_mul_star ha l k).const_mul _
  refine (integrable_congr (Filter.Eventually.of_forall fun x => quadForm_eq_sum Q x)).2 ?_
  exact integrable_finsetSum _ fun k _ => integrable_finsetSum _ fun l _ => hint k l

/-- **The average of a quadratic form is a trace against the Gram matrix:**
`∫ a(x)* Q a(x) dμ(x) = Tr (Q · gram a μ)`. -/
theorem integral_quadForm (ha : ∀ k, MemLp (fun x => a x k) 2 μ) (Q : Matrix ι ι ℂ) :
    ∫ x, star (a x) ⬝ᵥ (Q *ᵥ a x) ∂μ = (Q * gram a μ).trace := by
  have hint : ∀ k l, Integrable (fun x => Q k l * (a x l * star (a x k))) μ := fun k l =>
    (integrable_mul_star ha l k).const_mul _
  calc ∫ x, star (a x) ⬝ᵥ (Q *ᵥ a x) ∂μ
      = ∫ x, ∑ k, ∑ l, Q k l * (a x l * star (a x k)) ∂μ :=
        integral_congr_ae (Filter.Eventually.of_forall fun x => quadForm_eq_sum Q x)
    _ = ∑ k, ∑ l, ∫ x, Q k l * (a x l * star (a x k)) ∂μ := by
        rw [integral_finsetSum _ fun k _ => integrable_finsetSum _ fun l _ => hint k l]
        exact Finset.sum_congr rfl fun k _ => integral_finsetSum _ fun l _ => hint k l
    _ = ∑ k, ∑ l, Q k l * gram a μ l k := by
        simp only [integral_const_mul, gram_apply]
    _ = (Q * gram a μ).trace := by
        simp [Matrix.trace, Matrix.diag, Matrix.mul_apply]

/-- The real-valued form of `Discretization.integral_quadForm`, which is what the verifiers
of the construction use. -/
theorem integral_re_quadForm (ha : ∀ k, MemLp (fun x => a x k) 2 μ) (Q : Matrix ι ι ℂ) :
    ∫ x, RCLike.re (star (a x) ⬝ᵥ (Q *ᵥ a x)) ∂μ = RCLike.re ((Q * gram a μ).trace) := by
  rw [← integral_quadForm ha Q, integral_re (integrable_quadForm ha Q)]

/-- **One good point suffices.**  If the average of `g` is strictly smaller than the average
of `f`, then `g x < f x` for at least one `x`.

This is the form in which the existence of an admissible sampling point is used.  The paper
states that the set of admissible points has positive measure; that is true but not needed.
The conclusion is strict, which is what makes the weight of the new point finite. -/
theorem exists_lt_of_integral_lt {f g : D → ℝ} (hf : Integrable f μ) (hg : Integrable g μ)
    (h : ∫ x, g x ∂μ < ∫ x, f x ∂μ) : ∃ x, g x < f x := by
  by_contra hcon
  simp only [not_exists, not_lt] at hcon
  exact absurd h (not_lt.2 (integral_mono hf hg fun x => hcon x))

end Discretization
