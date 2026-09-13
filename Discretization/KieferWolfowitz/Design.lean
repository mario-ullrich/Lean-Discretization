/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
import BasicResults.QuadraticForm
import BasicResults.RankOneDeterminant

/-!
# Designs and their Gram matrices

A **design** is a finitely supported probability measure on the domain: finitely many points
`x₁, …, x_N` with nonnegative weights `w₁, …, w_N` summing to one.  Its **Gram matrix** with
respect to a family `a₁, …, a_n` of functions is

`G = ∑ₖ wₖ · a(xₖ) a(xₖ)*`,   that is   `Gᵢⱼ = ∑ₖ wₖ aᵢ(xₖ) conj (aⱼ(xₖ))`,

the matrix of inner products `⟪aᵢ, aⱼ⟫` in `L₂` of that measure.  This is the same weighted
sum of rank-one matrices that the sparsification theorem accumulates, so the definition
`Discretization.KieferWolfowitz.designGram` agrees with the matrix produced there.  No
measure appears yet: a finitely supported measure *is* a list of points with weights, and
keeping it in that form avoids all measurability side conditions.  The passage to an actual
`MeasureTheory.Measure` is made once, at the very end of the development.

The file collects what the maximisation of the determinant needs:

* `designGram_posSemidef`: a Gram matrix is positive semidefinite;
* `re_quadForm_designGram`: its quadratic form is `∑ₖ wₖ |f(xₖ)|²` for the function `f` with
  coefficient vector `c`;
* `designGram_snoc` and the two accompanying facts about the weights: mixing a new point `y`
  into a design with weight `α` produces a design again, whose Gram matrix is
  `(1-α) G + α a(y) a(y)*`.  This is the perturbation whose determinant the matrix
  determinant lemma computes;
* `norm_designGram_apply_le`: for a uniformly bounded family the entries of every Gram
  matrix are bounded by the same constant, whatever the design.  This is what bounds the set
  of determinants and so gives it a supremum.
-/

open Matrix
open scoped ComplexOrder MatrixOrder

namespace Discretization.KieferWolfowitz

variable {Ω ι : Type*} [Fintype ι]

/-- **The Gram matrix of a design.**  For points `x₁, …, x_N` with weights `w₁, …, w_N`,

`designGram a x w = ∑ₖ wₖ · a(xₖ) a(xₖ)*`.

If the weights are nonnegative and sum to one this is the matrix of the inner products
`⟪aᵢ, aⱼ⟫` in `L₂` of the measure `∑ₖ wₖ δ(xₖ)`. -/
noncomputable def designGram (a : Ω → ι → ℂ) {N : ℕ} (x : Fin N → Ω) (w : Fin N → ℝ) :
    Matrix ι ι ℂ :=
  ∑ k, w k • vecMulVec (a (x k)) (star (a (x k)))

/-- A Gram matrix with nonnegative weights is positive semidefinite, being a nonnegative
combination of the positive semidefinite rank-one matrices `a(xₖ) a(xₖ)*`. -/
theorem designGram_posSemidef (a : Ω → ι → ℂ) {N : ℕ} (x : Fin N → Ω) {w : Fin N → ℝ}
    (hw : ∀ k, 0 ≤ w k) : (designGram a x w).PosSemidef :=
  posSemidef_sum _ fun k _ => (posSemidef_vecMulVec_self_star _).smul (hw k)

/-- **The quadratic form of a Gram matrix is the weighted sum of squared values.**  For the
function `f(y) = ⟪c, a(y)⟫` with coefficient vector `c`,

`c* G c = ∑ₖ wₖ |f(xₖ)|²`. -/
theorem re_quadForm_designGram (a : Ω → ι → ℂ) {N : ℕ} (x : Fin N → Ω) (w : Fin N → ℝ)
    (c : ι → ℂ) :
    RCLike.re (star c ⬝ᵥ (designGram a x w *ᵥ c)) = ∑ k, w k * ‖star c ⬝ᵥ a (x k)‖ ^ 2 :=
  re_dotProduct_sum_mulVec x w c a

/-! ### Mixing in one more point -/

/-- The weights of the mixture that gives a new point the weight `α`: the old weights are
scaled by `1-α`, and `α` is appended. -/
def snocWeights {N : ℕ} (w : Fin N → ℝ) (α : ℝ) : Fin (N + 1) → ℝ :=
  Fin.snoc (fun k => (1 - α) * w k) α

omit [Fintype ι] in
/-- **The Gram matrix of a mixture.**  Appending the point `y` with weight `α` and scaling the
old weights by `1-α` turns the Gram matrix `G` into `(1-α) G + α a(y) a(y)*`. -/
theorem designGram_snoc (a : Ω → ι → ℂ) {N : ℕ} (x : Fin N → Ω) (w : Fin N → ℝ) (y : Ω)
    (α : ℝ) :
    designGram a (Fin.snoc x y) (snocWeights w α)
      = (1 - α) • designGram a x w + α • vecMulVec (a y) (star (a y)) := by
  rw [designGram, Fin.sum_univ_castSucc, snocWeights]
  simp only [Fin.snoc_castSucc, Fin.snoc_last]
  rw [designGram, Finset.smul_sum]
  congr 1
  exact Finset.sum_congr rfl fun k _ => by rw [← smul_smul]

/-- The weights of a mixture are again nonnegative. -/
theorem snocWeights_nonneg {N : ℕ} {w : Fin N → ℝ} (hw : ∀ k, 0 ≤ w k) {α : ℝ} (hα0 : 0 ≤ α)
    (hα1 : α ≤ 1) (k : Fin (N + 1)) : 0 ≤ snocWeights w α k := by
  induction k using Fin.lastCases with
  | last => simpa [snocWeights] using hα0
  | cast k => simpa [snocWeights] using mul_nonneg (by linarith) (hw k)

/-- The weights of a mixture again sum to one. -/
theorem sum_snocWeights {N : ℕ} {w : Fin N → ℝ} (hw1 : ∑ k, w k = 1) (α : ℝ) :
    ∑ k, snocWeights w α k = 1 := by
  rw [Fin.sum_univ_castSucc, snocWeights]
  simp only [Fin.snoc_castSucc, Fin.snoc_last]
  rw [← Finset.mul_sum, hw1]
  ring

/-! ### A uniform bound on the entries -/

omit [Fintype ι] in
/-- **The entries of every Gram matrix of a bounded family are bounded by `C²`**, uniformly
in the design.  The weights are a probability vector, so no growth in the number of points
occurs. -/
theorem norm_designGram_apply_le {a : Ω → ι → ℂ} {C : ℝ} (h0 : 0 ≤ C)
    (hC : ∀ y i, ‖a y i‖ ≤ C) {N : ℕ} {x : Fin N → Ω} {w : Fin N → ℝ} (hw : ∀ k, 0 ≤ w k)
    (hw1 : ∑ k, w k = 1) (i j : ι) : ‖designGram a x w i j‖ ≤ C ^ 2 := by
  have hstep : ‖designGram a x w i j‖ ≤ ∑ k, w k * C ^ 2 := by
    rw [designGram, Matrix.sum_apply]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
    rw [Matrix.smul_apply, Matrix.vecMulVec_apply, Pi.star_apply, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (hw k), norm_mul, norm_star, sq]
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul (hC _ _) (hC _ _) (norm_nonneg _) h0) (hw k)
  rwa [← Finset.sum_mul, hw1, one_mul] at hstep

end Discretization.KieferWolfowitz
