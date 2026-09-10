/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
import Discretization.MainTheorem

/-!
# Removing the normalisation of the first family

The main theorem assumes that the Gram matrix of the first family is the identity.  The
general case reduces to it, as in the original proof of Batson, Spielman and Srivastava:
replace `a` by `I^{-1/2} a`, where `I = ∫ a a* dμ`, so that the new family is orthonormal,
and conjugate the resulting frame bound back by `I^{1/2}`.

The two ingredients are the behaviour of the Gram matrix under a linear change of the family,

`gram (S a) μ = S · (gram a μ) · S*`  (`Discretization.gram_mulVec`),

and the fact that conjugation by a positive matrix preserves the Loewner order, which is
Mathlib's `conjugate_le_conjugate_of_nonneg` for the C⋆-algebra of matrices.

The result is `Discretization.bss_generalized`: the lower frame bound becomes
`(1 - √((m-1)/n))² • I` instead of `(1 - √((m-1)/n))² • 1`.  In eigenvalue form this is the
factor `λ_min(I)` of the paper.
-/

open Matrix MeasureTheory
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace Discretization

variable {ι κ Ω : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  [MeasurableSpace Ω] {μ : Measure Ω}

/-! ### A linear change of the family -/

omit [DecidableEq ι] in
/-- A linearly transformed family is still square-integrable. -/
theorem memLp_mulVec (S : Matrix ι ι ℂ) {a : Ω → ι → ℂ}
    (ha : ∀ k, MemLp (fun x => a x k) 2 μ) (k : ι) :
    MemLp (fun x => (S *ᵥ a x) k) 2 μ := by
  have h : (fun x => (S *ᵥ a x) k) = fun x => ∑ p, S k p * a x p := by
    funext x; simp [Matrix.mulVec, dotProduct]
  rw [h]
  exact memLp_finsetSum _ fun p _ => (ha p).const_mul _

omit [DecidableEq ι] in
/-- **The Gram matrix of a linearly transformed family**: `gram (S a) μ = S (gram a μ) S*`. -/
theorem gram_mulVec (S : Matrix ι ι ℂ) {a : Ω → ι → ℂ}
    (ha : ∀ k, MemLp (fun x => a x k) 2 μ) :
    gram (fun x => S *ᵥ a x) μ = S * gram a μ * Sᴴ := by
  ext k l
  have hint : ∀ p q, Integrable (fun x => S k p * star (S l q) * (a x p * star (a x q))) μ :=
    fun p q => (integrable_mul_star ha p q).const_mul _
  rw [gram_apply]
  calc ∫ x, (S *ᵥ a x) k * star ((S *ᵥ a x) l) ∂μ
      = ∫ x, ∑ p, ∑ q, S k p * star (S l q) * (a x p * star (a x q)) ∂μ := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, RCLike.star_def]
        rw [Finset.sum_mul_sum]
        exact Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => by ring
    _ = ∑ p, ∑ q, S k p * star (S l q) * ∫ x, a x p * star (a x q) ∂μ := by
        rw [integral_finsetSum _ fun p _ => integrable_finsetSum _ fun q _ => hint p q]
        exact Finset.sum_congr rfl fun p _ => by
          rw [integral_finsetSum _ fun q _ => hint p q]
          exact Finset.sum_congr rfl fun q _ => integral_const_mul _ _
    _ = (S * gram a μ * Sᴴ) k l := by
        simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, gram_apply, RCLike.star_def]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun q _ => by
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl fun p _ => by ring

omit [DecidableEq ι] [MeasurableSpace Ω] in
/-- The rank-one matrix of a transformed vector is the conjugated rank-one matrix. -/
theorem vecMulVec_mulVec_self_star (S : Matrix ι ι ℂ) (u : ι → ℂ) :
    vecMulVec (S *ᵥ u) (star (S *ᵥ u)) = S * vecMulVec u (star u) * Sᴴ := by
  rw [← Matrix.mul_vecMulVec, Matrix.star_mulVec, ← Matrix.vecMulVec_mul, ← mul_assoc]

omit [MeasurableSpace Ω] in
/-- Conjugation commutes with weighted sums. -/
theorem sum_smul_conj (S : Matrix ι ι ℂ) {k : ℕ} (w : Fin k → ℝ)
    (R : Fin k → Matrix ι ι ℂ) :
    ∑ i, w i • (S * R i * Sᴴ) = S * (∑ i, w i • R i) * Sᴴ := by
  rw [Matrix.mul_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun i _ => by rw [mul_smul_comm, smul_mul_assoc]

/-! ### The theorem without normalisation -/

/-- **Generalized sparsification theorem** (Chkifa–Dolbeault–Krieg–Ullrich, Theorem 3), for
finite families.

Let `a` be a family of square-integrable functions indexed by a finite set `ι` of `m ≥ 2`
elements with positive definite Gram matrix `I = ∫ a a* dμ`, and let `b` be a second family
whose Gram matrix `J` is positive definite and bounded by `Λ • 1`, with effective dimension
`M = Tr J / Λ ≥ 1 + 1/n`.  Then for every `n ≥ m` there are `n` points and positive weights
with

`(1 - √((m-1)/n))² • I ≤ ∑ wᵢ a(xᵢ) a(xᵢ)*`  and
`∑ wᵢ b(xᵢ) b(xᵢ)* ≤ (1 + √((M-1)/n))² Λ • 1`.

The first bound is the Loewner form of the paper's `(1 - √((m-1)/n))² λ_min(I)`. -/
theorem bss_generalized [Nonempty ι] [Nonempty κ]
    {J : Matrix κ κ ℂ} (hJ : J.PosDef) {Λ : ℝ} (hΛ : 0 < Λ)
    (hJΛ : J ≤ Λ • (1 : Matrix κ κ ℂ)) {a : Ω → ι → ℂ} {b : Ω → κ → ℂ}
    (ha : ∀ k, MemLp (fun x => a x k) 2 μ) (hb : ∀ k, MemLp (fun x => b x k) 2 μ)
    (hI : (gram a μ).PosDef) (hgramb : gram b μ = J)
    {n : ℕ} (hm : 2 ≤ Fintype.card ι) (hmn : Fintype.card ι ≤ n)
    (hM : 1 + 1 / (n : ℝ) ≤ RCLike.re J.trace / Λ) :
    ∃ (x : Fin n → Ω) (w : Fin n → ℝ), (∀ i, 0 < w i) ∧
      (1 - Real.sqrt ((Fintype.card ι - 1) / n)) ^ 2 • gram a μ
        ≤ ∑ i, w i • vecMulVec (a (x i)) (star (a (x i))) ∧
      ∑ i, w i • vecMulVec (b (x i)) (star (b (x i)))
        ≤ ((1 + Real.sqrt ((RCLike.re J.trace / Λ - 1) / n)) ^ 2 * Λ)
            • (1 : Matrix κ κ ℂ) := by
  -- the square root of the Gram matrix and its inverse
  set T := CFC.sqrt (gram a μ) with hTdef
  have hT0 : (0 : Matrix ι ι ℂ) ≤ T := CFC.sqrt_nonneg _
  have hTpsd : T.PosSemidef := Matrix.nonneg_iff_posSemidef.1 hT0
  have hTT : T * T = gram a μ := CFC.sqrt_mul_sqrt_self _ hI.posSemidef.nonneg
  have hTdet : IsUnit T.det := hI.isUnit_det_sqrt
  have hTS : T * T⁻¹ = 1 := mul_nonsing_inv _ hTdet
  have hST : T⁻¹ * T = 1 := nonsing_inv_mul _ hTdet
  have hSherm : (T⁻¹)ᴴ = T⁻¹ := hTpsd.inv.isHermitian.eq
  -- the normalized family
  have hgram' : gram (fun x => T⁻¹ *ᵥ a x) μ = 1 := by
    rw [gram_mulVec _ ha, hSherm, ← hTT, ← mul_assoc, hST, one_mul, hTS]
  obtain ⟨x, w, hwpos, hlow, hup⟩ :=
    bss_generalized_of_gram_eq_one hJ hΛ hJΛ (memLp_mulVec T⁻¹ ha) hb hgram' hgramb hm hmn hM
  refine ⟨x, w, hwpos, ?_, hup⟩
  -- conjugate the lower bound back by `T`
  have hsum : ∑ i, w i • vecMulVec (T⁻¹ *ᵥ a (x i)) (star (T⁻¹ *ᵥ a (x i)))
      = T⁻¹ * (∑ i, w i • vecMulVec (a (x i)) (star (a (x i)))) * (T⁻¹)ᴴ := by
    rw [← sum_smul_conj]
    exact Finset.sum_congr rfl fun i _ => by rw [vecMulVec_mulVec_self_star]
  rw [hsum, hSherm] at hlow
  have hconj := conjugate_le_conjugate_of_nonneg hlow hT0
  have hleft : T * ((1 - Real.sqrt ((Fintype.card ι - 1) / n)) ^ 2 • (1 : Matrix ι ι ℂ)) * T
      = (1 - Real.sqrt ((Fintype.card ι - 1) / n)) ^ 2 • gram a μ := by
    rw [mul_smul_comm, smul_mul_assoc, mul_one, hTT]
  have hright : T * (T⁻¹ * (∑ i, w i • vecMulVec (a (x i)) (star (a (x i)))) * T⁻¹) * T
      = ∑ i, w i • vecMulVec (a (x i)) (star (a (x i))) := by
    calc T * (T⁻¹ * (∑ i, w i • vecMulVec (a (x i)) (star (a (x i)))) * T⁻¹) * T
        = (T * T⁻¹) * (∑ i, w i • vecMulVec (a (x i)) (star (a (x i)))) * (T⁻¹ * T) := by
          simp [mul_assoc]
      _ = ∑ i, w i • vecMulVec (a (x i)) (star (a (x i))) := by
          rw [hTS, hST, one_mul, mul_one]
  rwa [hleft, hright] at hconj

end Discretization
