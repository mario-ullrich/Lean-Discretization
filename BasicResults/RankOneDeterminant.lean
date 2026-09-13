/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
import BasicResults.ShermanMorrison
import Mathlib.LinearAlgebra.Matrix.SchurComplement

/-!
# Determinants of rank-one mixtures

Three facts about determinants, all needed for the maximisation of `det` over the Gram
matrices of a finitely supported measure:

* `Matrix.det_add_vecMulVec`: the **matrix determinant lemma** in the shape used here,
  `det (A + v w*) = det A · (1 + w* A⁻¹ v)` for invertible `A`.  Mathlib states it for the
  product of a column and a row (`Matrix.det_add_replicateCol_mul_replicateRow`);
  `Matrix.vecMulVec` is the spelling used throughout this project, so the translation is
  made once.
* `Matrix.det_smul_add_smul_vecMulVec`: the determinant of `β A + α u u*` for invertible
  `A`.  Because `u u*` has rank one the determinant is not merely bounded but computed
  exactly,

  `det (β A + α u u*) = β^(n-1) · det A · (β + α · u* A⁻¹ u)`,

  a polynomial of degree `n` in `β` and of degree *one* in `α`.  This identity is what
  replaces the derivative of the determinant: the first-order condition at a maximum of
  `det` is read off from it, rather than from Jacobi's formula, which Mathlib does not
  have.  The exponent `n-1` is spelled by assuming `Fintype.card n = m + 1`, so that no
  truncated subtraction of natural numbers occurs.
  `Matrix.PosDef.re_det_smul_add_smul_vecMulVec` is the real form of the same identity, for
  real scalars and positive definite `A`, where every quantity involved is a real number.
* `Matrix.norm_det_le_of_norm_apply_le`: the crude bound `|det A| ≤ n! · C^n` for a matrix
  whose entries are bounded by `C`, read off from the Leibniz formula.  It is what makes
  the set of determinants of Gram matrices bounded above, so that its supremum exists.
-/

open scoped ComplexOrder MatrixOrder

namespace Matrix

variable {𝕜 n : Type*} [RCLike 𝕜] [Fintype n] [DecidableEq n]

/-- **The matrix determinant lemma.**  For an invertible `A`,

`det (A + v w*) = det A · (1 + w* A⁻¹ v)`.

Factoring `A` out of `A + v w*` leaves `1 + (A⁻¹ v) w*`, whose determinant is
`1 + w* A⁻¹ v` because the matrix that was added has rank one. -/
theorem det_add_vecMulVec {A : Matrix n n 𝕜} (hA : IsUnit A.det) (v w : n → 𝕜) :
    (A + vecMulVec v w).det = A.det * (1 + w ⬝ᵥ (A⁻¹ *ᵥ v)) := by
  have hAv : A *ᵥ (A⁻¹ *ᵥ v) = v := by
    rw [mulVec_mulVec, mul_nonsing_inv _ hA, one_mulVec]
  have h1 : A * (1 + vecMulVec (A⁻¹ *ᵥ v) w) = A + vecMulVec v w := by
    rw [Matrix.mul_add, Matrix.mul_one, mul_vecMulVec, hAv]
  rw [← h1, det_mul, vecMulVec_eq (ι := Unit), det_one_add_replicateCol_mul_replicateRow]

/-- **The determinant of a rank-one mixture.**  For an invertible `A`, a nonzero scalar `β`
and an arbitrary scalar `α`,

`det (β A + α u u*) = β^m · det A · (β + α · u* A⁻¹ u)`,   where `n = m + 1`.

The dependence on `α` is affine: adding a rank-one matrix changes the determinant only to
first order.  This exact identity is the substitute for differentiating the determinant. -/
theorem det_smul_add_smul_vecMulVec {A : Matrix n n 𝕜} (hA : IsUnit A.det) {β : 𝕜}
    (hβ : β ≠ 0) (α : 𝕜) (u : n → 𝕜) {m : ℕ} (hm : Fintype.card n = m + 1) :
    (β • A + α • vecMulVec u (star u)).det
      = β ^ m * A.det * (β + α * (star u ⬝ᵥ (A⁻¹ *ᵥ u))) := by
  have hsplit : β • A + α • vecMulVec u (star u)
      = β • (A + vecMulVec ((β⁻¹ * α) • u) (star u)) := by
    rw [smul_vecMulVec, smul_add, smul_smul, ← mul_assoc, mul_inv_cancel₀ hβ, one_mul]
  rw [hsplit, det_smul, hm, det_add_vecMulVec hA, mulVec_smul, dotProduct_smul, smul_eq_mul]
  field_simp
  ring

/-- The real form of `Matrix.det_smul_add_smul_vecMulVec`.  For positive definite `A` and
real scalars `β ≠ 0` and `α`, both the determinant of `A` and the quadratic form
`u* A⁻¹ u` are nonnegative reals, so the identity can be stated entirely in `ℝ`:

`Re det (β A + α u u*) = β^m · (β + α · Re (u* A⁻¹ u)) · Re det A`. -/
theorem PosDef.re_det_smul_add_smul_vecMulVec {A : Matrix n n ℂ} (hA : A.PosDef) {β : ℝ}
    (hβ : β ≠ 0) (α : ℝ) (u : n → ℂ) {m : ℕ} (hm : Fintype.card n = m + 1) :
    RCLike.re (β • A + α • vecMulVec u (star u)).det
      = β ^ m * (β + α * RCLike.re (star u ⬝ᵥ (A⁻¹ *ᵥ u))) * RCLike.re A.det := by
  -- name the two real quantities, so that rewriting cannot loop back into their real parts
  obtain ⟨d, hdre, hdc⟩ : ∃ d : ℝ, RCLike.re A.det = d ∧ (d : ℂ) = A.det :=
    ⟨_, rfl, RCLike.ofReal_re_of_nonneg hA.det_pos.le⟩
  obtain ⟨q, hqre, hqc⟩ : ∃ q : ℝ, RCLike.re (star u ⬝ᵥ (A⁻¹ *ᵥ u)) = q ∧
      (q : ℂ) = star u ⬝ᵥ (A⁻¹ *ᵥ u) :=
    ⟨_, rfl, RCLike.ofReal_re_of_nonneg (hA.inv.posSemidef.dotProduct_mulVec_nonneg u)⟩
  have hAdet : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det _).1 hA.isUnit
  rw [hdre, hqre, real_smul_eq_complex_smul, real_smul_eq_complex_smul,
    det_smul_add_smul_vecMulVec hAdet (by exact_mod_cast hβ) _ u hm, ← hdc, ← hqc]
  norm_cast
  rw [RCLike.re_to_complex, Complex.ofReal_re]
  ring

/-- **A crude bound on a determinant by the size of its entries:** `|det A| ≤ n! · C^n`.

The Leibniz formula writes `det A` as a sum of `n!` signed products of `n` entries, and the
signs have modulus one. -/
theorem norm_det_le_of_norm_apply_le {A : Matrix n n 𝕜} {C : ℝ} (hC : ∀ i j, ‖A i j‖ ≤ C) :
    ‖A.det‖ ≤ (Fintype.card n).factorial * C ^ Fintype.card n := by
  classical
  have hterm : ∀ σ : Equiv.Perm n,
      ‖((Equiv.Perm.sign σ : ℤ) : 𝕜) * ∏ i, A (σ i) i‖ ≤ C ^ Fintype.card n := by
    intro σ
    have hsign : ‖((Equiv.Perm.sign σ : ℤ) : 𝕜)‖ = 1 := by
      rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> rw [h] <;> simp
    rw [norm_mul, hsign, one_mul, norm_prod]
    calc ∏ i, ‖A (σ i) i‖ ≤ ∏ _i : n, C :=
          Finset.prod_le_prod (fun i _ => norm_nonneg _) fun i _ => hC _ _
      _ = C ^ Fintype.card n := by rw [Finset.prod_const, Finset.card_univ]
  calc ‖A.det‖ = ‖∑ σ : Equiv.Perm n, ((Equiv.Perm.sign σ : ℤ) : 𝕜) * ∏ i, A (σ i) i‖ := by
        rw [det_apply']
    _ ≤ ∑ _σ : Equiv.Perm n, C ^ Fintype.card n :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum fun σ _ => hterm σ)
    _ = (Fintype.card n).factorial * C ^ Fintype.card n := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, nsmul_eq_mul]

end Matrix
