/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
import Discretization.MainTheorem

/-!
# The discretization inequality

The main theorem is a statement about matrices.  This file translates it into the statement
about functions that motivates it: for a function `f` in the span of the first family, the
integral `∫ |f|² dμ` is bounded by a weighted sum of `|f(xᵢ)|²`, and for a function `g` in the
span of the second family the weighted sum is bounded by the squared coefficient norm.

The dictionary is elementary.  A coefficient vector `c` gives the function
`f(x) = ⟪c, a(x)⟫ = ∑ conj (cₖ) aₖ(x)`, and

* `∑ wᵢ |f(xᵢ)|² = c* G c` for the accumulated matrix `G = ∑ wᵢ a(xᵢ) a(xᵢ)*`
  (`Discretization.re_dotProduct_sum_mulVec`),
* `∫ |f|² dμ = c* (gram a μ) c` (`Discretization.integral_norm_sq_combination`),
* `c* A c ≤ c* B c` whenever `A ≤ B` in the Loewner order
  (`Discretization.re_quadForm_le_of_le`).

So a Loewner inequality between matrices is exactly an inequality between quadratic forms,
uniformly in the coefficient vector.  The result is
`Discretization.exists_discretization`.
-/

open Matrix MeasureTheory
open scoped ComplexOrder MatrixOrder

namespace Discretization

variable {ι κ Ω : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  [MeasurableSpace Ω] {μ : Measure Ω}

/-! ### Quadratic forms and sums of squares -/

omit [DecidableEq ι] in
/-- The quadratic form of a rank-one matrix is a squared modulus:
`c* (u u*) c = |⟪c, u⟫|²`. -/
theorem re_dotProduct_vecMulVec_mulVec (u c : ι → ℂ) :
    RCLike.re (star c ⬝ᵥ ((vecMulVec u (star u)) *ᵥ c)) = ‖star c ⬝ᵥ u‖ ^ 2 := by
  have hz : (star c ⬝ᵥ u) * (starRingEnd ℂ) (star c ⬝ᵥ u)
      = star c ⬝ᵥ ((vecMulVec u (star u)) *ᵥ c) := by
    simp only [dotProduct, Matrix.mulVec, Matrix.vecMulVec_apply, Pi.star_apply, map_sum,
      map_mul, RCLike.star_def, Complex.conj_conj]
    rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun l _ => by ring
  rw [← hz, RCLike.mul_conj]
  norm_cast

omit [DecidableEq ι] [MeasurableSpace Ω] in
/-- The quadratic form of a weighted sum of rank-one matrices is the corresponding weighted
sum of squared moduli. -/
theorem re_dotProduct_sum_mulVec {k : ℕ} (x : Fin k → Ω) (w : Fin k → ℝ) (c : ι → ℂ)
    (a : Ω → ι → ℂ) :
    RCLike.re (star c ⬝ᵥ ((∑ i, w i • vecMulVec (a (x i)) (star (a (x i)))) *ᵥ c))
      = ∑ i, w i * ‖star c ⬝ᵥ a (x i)‖ ^ 2 := by
  simp only [Matrix.sum_mulVec, dotProduct_sum, map_sum, Matrix.smul_mulVec,
    dotProduct_smul, RCLike.smul_re, re_dotProduct_vecMulVec_mulVec]

omit [DecidableEq ι] in
/-- The quadratic form is monotone for the Loewner order. -/
theorem re_quadForm_le_of_le {A B : Matrix ι ι ℂ} (h : A ≤ B) (c : ι → ℂ) :
    RCLike.re (star c ⬝ᵥ (A *ᵥ c)) ≤ RCLike.re (star c ⬝ᵥ (B *ᵥ c)) := by
  have hd := (Matrix.le_iff.1 h).re_dotProduct_nonneg c
  rw [Matrix.sub_mulVec, dotProduct_sub, map_sub] at hd
  linarith

/-- The quadratic form of a multiple of the identity is the squared norm of the coefficient
vector. -/
theorem re_quadForm_smul_one (α : ℝ) (c : ι → ℂ) :
    RCLike.re (star c ⬝ᵥ ((α • (1 : Matrix ι ι ℂ)) *ᵥ c)) = α * ∑ k, ‖c k‖ ^ 2 := by
  rw [Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul, RCLike.smul_re]
  congr 1
  simp only [dotProduct, Pi.star_apply, map_sum, RCLike.star_def]
  exact Finset.sum_congr rfl fun k _ => by rw [RCLike.conj_mul]; norm_cast

omit [DecidableEq ι] in
/-- The average of `|f|²` for the function `f` with coefficient vector `c` is the quadratic
form of the Gram matrix. -/
theorem integral_norm_sq_combination {a : Ω → ι → ℂ}
    (ha : ∀ k, MemLp (fun x => a x k) 2 μ) (c : ι → ℂ) :
    ∫ y, ‖star c ⬝ᵥ a y‖ ^ 2 ∂μ = RCLike.re (star c ⬝ᵥ ((gram a μ) *ᵥ c)) := by
  have h1 : ∀ y, ‖star c ⬝ᵥ a y‖ ^ 2
      = RCLike.re (star (a y) ⬝ᵥ ((vecMulVec c (star c)) *ᵥ a y)) := by
    intro y
    rw [re_dotProduct_vecMulVec_mulVec]
    have h2 : star (a y) ⬝ᵥ c = (starRingEnd ℂ) (star c ⬝ᵥ a y) := by
      simp only [dotProduct, Pi.star_apply, map_sum, map_mul, RCLike.star_def,
        Complex.conj_conj]
      exact Finset.sum_congr rfl fun k _ => by ring
    rw [h2, RCLike.norm_conj]
  rw [integral_congr_ae (Filter.Eventually.of_forall h1), integral_re_quadForm ha,
    Matrix.trace_mul_comm, Matrix.trace_mul_vecMulVec_self_star]

/-! ### The discretization inequality -/

set_option maxHeartbeats 1000000 in
/-- **Discretization of the `L₂`-norm.**

Under the hypotheses of `Discretization.bss_generalized_of_gram_eq_one`, the `n` points and
weights discretize the norm of every function in the span of the first family from below,

`(1 - √((m-1)/n))² · ∫ |f|² dμ ≤ ∑ wᵢ |f(xᵢ)|²`,

and bound the weighted sum for every function in the span of the second family from above,

`∑ wᵢ |g(xᵢ)|² ≤ (1 + √((M-1)/n))² Λ · ‖c‖²`,

where `c` is the coefficient vector of `g`.  Both statements hold uniformly: the same points
and weights work for all coefficient vectors.

This is Corollary 4 of the paper, for finite families.  With the second family taken to be
the singular basis of the embedding of a reproducing kernel Hilbert space `H` into `L₂`, the
coefficient norm on the right is the `H`-norm of `g` and `Λ` is the norm of the
embedding. -/
theorem exists_discretization [Nonempty ι] [Nonempty κ]
    {J : Matrix κ κ ℂ} (hJ : J.PosDef) {Λ : ℝ} (hΛ : 0 < Λ)
    (hJΛ : J ≤ Λ • (1 : Matrix κ κ ℂ)) {a : Ω → ι → ℂ} {b : Ω → κ → ℂ}
    (ha : ∀ k, MemLp (fun x => a x k) 2 μ) (hb : ∀ k, MemLp (fun x => b x k) 2 μ)
    (hgrama : gram a μ = 1) (hgramb : gram b μ = J)
    {n : ℕ} (hm : 2 ≤ Fintype.card ι) (hmn : Fintype.card ι ≤ n)
    (hM : 1 + 1 / (n : ℝ) ≤ RCLike.re J.trace / Λ) :
    ∃ (x : Fin n → Ω) (w : Fin n → ℝ), (∀ i, 0 < w i) ∧
      (∀ c : ι → ℂ, (1 - Real.sqrt ((Fintype.card ι - 1) / n)) ^ 2
            * ∫ y, ‖star c ⬝ᵥ a y‖ ^ 2 ∂μ
          ≤ ∑ i, w i * ‖star c ⬝ᵥ a (x i)‖ ^ 2) ∧
      (∀ c : κ → ℂ, ∑ i, w i * ‖star c ⬝ᵥ b (x i)‖ ^ 2
          ≤ (1 + Real.sqrt ((RCLike.re J.trace / Λ - 1) / n)) ^ 2 * Λ
              * ∑ k, ‖c k‖ ^ 2) := by
  obtain ⟨x, w, hwpos, hlow, hup⟩ :=
    bss_generalized_of_gram_eq_one hJ hΛ hJΛ ha hb hgrama hgramb hm hmn hM
  refine ⟨x, w, hwpos, fun c => ?_, fun c => ?_⟩
  · have h1 : RCLike.re (star c ⬝ᵥ ((1 : Matrix ι ι ℂ) *ᵥ c)) = ∑ k, ‖c k‖ ^ 2 := by
      simpa using re_quadForm_smul_one (ι := ι) 1 c
    calc (1 - Real.sqrt ((Fintype.card ι - 1) / n)) ^ 2 * ∫ y, ‖star c ⬝ᵥ a y‖ ^ 2 ∂μ
        = RCLike.re (star c ⬝ᵥ
            (((1 - Real.sqrt ((Fintype.card ι - 1) / n)) ^ 2 • (1 : Matrix ι ι ℂ)) *ᵥ c)) := by
          rw [re_quadForm_smul_one, integral_norm_sq_combination ha c, hgrama, h1]
      _ ≤ RCLike.re (star c ⬝ᵥ
            ((∑ i, w i • vecMulVec (a (x i)) (star (a (x i)))) *ᵥ c)) :=
          re_quadForm_le_of_le hlow c
      _ = ∑ i, w i * ‖star c ⬝ᵥ a (x i)‖ ^ 2 := re_dotProduct_sum_mulVec x w c a
  · calc ∑ i, w i * ‖star c ⬝ᵥ b (x i)‖ ^ 2
        = RCLike.re (star c ⬝ᵥ
            ((∑ i, w i • vecMulVec (b (x i)) (star (b (x i)))) *ᵥ c)) :=
          (re_dotProduct_sum_mulVec x w c b).symm
      _ ≤ RCLike.re (star c ⬝ᵥ
            ((((1 + Real.sqrt ((RCLike.re J.trace / Λ - 1) / n)) ^ 2 * Λ)
              • (1 : Matrix κ κ ℂ)) *ᵥ c)) := re_quadForm_le_of_le hup c
      _ = (1 + Real.sqrt ((RCLike.re J.trace / Λ - 1) / n)) ^ 2 * Λ * ∑ k, ‖c k‖ ^ 2 :=
          re_quadForm_smul_one _ c

end Discretization
