/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
import Discretization.Potentials

/-!
# Verifiers and the barrier lemma

A candidate sampling point `x` is admissible if adding the rank-one matrix `w a(x) a(x)*` to
the shrunk matrix `A - δ • 1` does not increase the lower potential, and subtracting
`w b(x) b(x)*` from the grown matrix `B + ζ • J` does not increase the upper potential.  Both
conditions can be checked pointwise, without recomputing any inverse, through the two
**verifiers**

* `Discretization.lowerVerifier A δ a = (a* Z² a) / (Φ(A - δ • 1) - Φ(A)) - a* Z a`, where
  `Z = (A - δ • 1)⁻¹`, and
* `Discretization.upperVerifier J B ζ b = (b* X J X b) / (Ψ_J(B) - Ψ_J(B + ζ • J)) + b* X b`,
  where `X = (B + ζ • J)⁻¹`.

The **barrier lemma** (`Discretization.lowerPotential_update_le` and
`Discretization.upperPotential_update_le`) says that a weight `w` with
`upperVerifier ≤ 1/w ≤ lowerVerifier` keeps both potentials from increasing, and keeps both
matrices positive definite.  This is Lemma 3.3/3.4 of Batson–Spielman–Srivastava in the form
used by Chkifa–Dolbeault–Krieg–Ullrich.

The exact effect of an update on the potentials is computed first, in
`Discretization.lowerPotential_add_smul_vecMulVec` and
`Discretization.upperPotential_sub_smul_vecMulVec`; after that the barrier lemma is
elementary algebra with real numbers.
-/

open Matrix
open scoped ComplexOrder MatrixOrder

namespace Discretization

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- **The lower potential after a rank-one update**, in closed form:
`Φ(N + w a a*) = Φ(N) - w / (1 + w a* N⁻¹ a) · a* N⁻² a`.

Every quantity on the right is real and nonnegative, so adding a rank-one matrix can only
decrease the lower potential; the point of the formula is to say by how much. -/
theorem lowerPotential_add_smul_vecMulVec {N : Matrix ι ι ℂ} (hN : N.PosDef) (a : ι → ℂ)
    {w : ℝ} (hw : 0 ≤ w) :
    lowerPotential (N + w • vecMulVec a (star a))
      = lowerPotential N - (w / (1 + w * RCLike.re (star a ⬝ᵥ (N⁻¹ *ᵥ a))))
          * RCLike.re (star a ⬝ᵥ ((N⁻¹ * N⁻¹) *ᵥ a)) := by
  have hNdet : IsUnit N.det := (Matrix.isUnit_iff_isUnit_det _).1 hN.isUnit
  have hZZ : (N⁻¹ * N⁻¹).PosSemidef := by
    have h := Matrix.posSemidef_conjTranspose_mul_self (N⁻¹)
    rwa [hN.inv.isHermitian.eq] at h
  set qr := RCLike.re (star a ⬝ᵥ (N⁻¹ *ᵥ a)) with hqr
  set sr := RCLike.re (star a ⬝ᵥ ((N⁻¹ * N⁻¹) *ᵥ a)) with hsr
  have hqre : ((qr : ℝ) : ℂ) = star a ⬝ᵥ (N⁻¹ *ᵥ a) :=
    RCLike.ofReal_re_of_nonneg (hN.inv.posSemidef.dotProduct_mulVec_nonneg a)
  have hsre : ((sr : ℝ) : ℂ) = star a ⬝ᵥ ((N⁻¹ * N⁻¹) *ᵥ a) :=
    RCLike.ofReal_re_of_nonneg (hZZ.dotProduct_mulVec_nonneg a)
  have hq0 : 0 ≤ qr := hN.inv.posSemidef.re_dotProduct_nonneg a
  have hden : 0 < 1 + w * qr := by have := mul_nonneg hw hq0; linarith
  have hdenC : (1 : ℂ) + (w : ℂ) * (star a ⬝ᵥ (N⁻¹ *ᵥ a)) ≠ 0 := by
    rw [← hqre, show (1 : ℂ) + (w : ℂ) * ((qr : ℝ) : ℂ) = ((1 + w * qr : ℝ) : ℂ) by
      push_cast; ring]
    exact_mod_cast hden.ne'
  have hkey : RCLike.re (((w : ℂ) / (1 + (w : ℂ) * (star a ⬝ᵥ (N⁻¹ *ᵥ a))))
      * (star a ⬝ᵥ ((N⁻¹ * N⁻¹) *ᵥ a))) = (w / (1 + w * qr)) * sr := by
    rw [← hqre, ← hsre, show ((w : ℂ) / (1 + (w : ℂ) * ((qr : ℝ) : ℂ))) * ((sr : ℝ) : ℂ)
        = (((w / (1 + w * qr)) * sr : ℝ) : ℂ) by push_cast; ring]
    exact RCLike.ofReal_re _
  rw [lowerPotential, lowerPotential, Matrix.real_smul_eq_complex_smul,
    Matrix.trace_inv_add_smul_vecMulVec hN.isHermitian hNdet a (w : ℂ) hdenC, map_sub, hkey]

/-- **The upper potential after a rank-one downdate**, in closed form:
`Ψ_J(M - w b b*) = Ψ_J(M) + w / (1 - w b* M⁻¹ b) · b* M⁻¹ J M⁻¹ b`,
valid as long as the Sherman–Morrison denominator `1 - w b* M⁻¹ b` is positive. -/
theorem upperPotential_sub_smul_vecMulVec {J M : Matrix κ κ ℂ} (hJ : J.PosDef)
    (hM : M.PosDef) (b : κ → ℂ) {w : ℝ}
    (hden : 0 < 1 - w * RCLike.re (star b ⬝ᵥ (M⁻¹ *ᵥ b))) :
    upperPotential J (M - w • vecMulVec b (star b))
      = upperPotential J M + (w / (1 - w * RCLike.re (star b ⬝ᵥ (M⁻¹ *ᵥ b))))
          * RCLike.re (star b ⬝ᵥ ((M⁻¹ * J * M⁻¹) *ᵥ b)) := by
  have hMdet : IsUnit M.det := (Matrix.isUnit_iff_isUnit_det _).1 hM.isUnit
  have hconj : (M⁻¹ * J * M⁻¹).PosSemidef := by
    have h := hJ.posSemidef.conjTranspose_mul_mul_same (M⁻¹)
    rwa [hM.inv.isHermitian.eq] at h
  set pr := RCLike.re (star b ⬝ᵥ (M⁻¹ *ᵥ b)) with hpr
  set rr := RCLike.re (star b ⬝ᵥ ((M⁻¹ * J * M⁻¹) *ᵥ b)) with hrr
  have hpre : ((pr : ℝ) : ℂ) = star b ⬝ᵥ (M⁻¹ *ᵥ b) :=
    RCLike.ofReal_re_of_nonneg (hM.inv.posSemidef.dotProduct_mulVec_nonneg b)
  have hrre : ((rr : ℝ) : ℂ) = star b ⬝ᵥ ((M⁻¹ * J * M⁻¹) *ᵥ b) :=
    RCLike.ofReal_re_of_nonneg (hconj.dotProduct_mulVec_nonneg b)
  have hdenC : (1 : ℂ) + (-(w : ℂ)) * (star b ⬝ᵥ (M⁻¹ *ᵥ b)) ≠ 0 := by
    rw [← hpre, show (1 : ℂ) + (-(w : ℂ)) * ((pr : ℝ) : ℂ) = ((1 - w * pr : ℝ) : ℂ) by
      push_cast; ring]
    exact_mod_cast hden.ne'
  have hsub : M - w • vecMulVec b (star b) = M + (-(w : ℂ)) • vecMulVec b (star b) := by
    rw [Matrix.real_smul_eq_complex_smul, neg_smul, ← sub_eq_add_neg]
  have hkey : RCLike.re (((-(w : ℂ)) / (1 + (-(w : ℂ)) * (star b ⬝ᵥ (M⁻¹ *ᵥ b))))
      * (star b ⬝ᵥ ((M⁻¹ * J * M⁻¹) *ᵥ b))) = -((w / (1 - w * pr)) * rr) := by
    rw [← hpre, ← hrre,
      show ((-(w : ℂ)) / (1 + (-(w : ℂ)) * ((pr : ℝ) : ℂ))) * ((rr : ℝ) : ℂ)
        = ((-((w / (1 - w * pr)) * rr) : ℝ) : ℂ) by push_cast; ring]
    exact RCLike.ofReal_re _
  rw [upperPotential, upperPotential, hsub,
    Matrix.inv_add_smul_vecMulVec hM.isHermitian hMdet b _ hdenC, Matrix.mul_sub,
    Matrix.mul_smul, Matrix.trace_sub, Matrix.trace_smul, smul_eq_mul,
    Matrix.trace_mul_vecMulVec_self_star,
    Matrix.dotProduct_conj_mulVec hM.inv.isHermitian, map_sub, hkey]
  ring

/-- The **lower verifier** of a candidate vector `a`, measuring how much of the gap opened by
the shift `A ↦ A - δ • 1` the rank-one update `w a a*` would consume. -/
noncomputable def lowerVerifier (A : Matrix ι ι ℂ) (δ : ℝ) (a : ι → ℂ) : ℝ :=
  RCLike.re (star a ⬝ᵥ (((A - δ • (1 : Matrix ι ι ℂ))⁻¹ * (A - δ • (1 : Matrix ι ι ℂ))⁻¹)
      *ᵥ a)) / (lowerPotential (A - δ • (1 : Matrix ι ι ℂ)) - lowerPotential A)
    - RCLike.re (star a ⬝ᵥ ((A - δ • (1 : Matrix ι ι ℂ))⁻¹ *ᵥ a))

/-- The **upper verifier** of a candidate vector `b`. -/
noncomputable def upperVerifier (J B : Matrix κ κ ℂ) (ζ : ℝ) (b : κ → ℂ) : ℝ :=
  RCLike.re (star b ⬝ᵥ (((B + ζ • J)⁻¹ * J * (B + ζ • J)⁻¹) *ᵥ b))
      / (upperPotential J B - upperPotential J (B + ζ • J))
    + RCLike.re (star b ⬝ᵥ ((B + ζ • J)⁻¹ *ᵥ b))

/-- **Barrier lemma, lower half.**  If the weight `w` satisfies `1/w ≤ lowerVerifier A δ a`,
then the updated matrix `A - δ • 1 + w a a*` is again positive definite and its lower
potential has not increased. -/
theorem lowerPotential_update_le [Nonempty ι] {A : Matrix ι ι ℂ} (hA : A.PosDef) {δ : ℝ}
    (hδ : 0 < δ) (hδ' : δ < (lowerPotential A)⁻¹) (a : ι → ℂ) {w : ℝ} (hw : 0 < w)
    (hcond : 1 / w ≤ lowerVerifier A δ a) :
    (A - δ • (1 : Matrix ι ι ℂ) + w • vecMulVec a (star a)).PosDef ∧
      lowerPotential (A - δ • (1 : Matrix ι ι ℂ) + w • vecMulVec a (star a))
        ≤ lowerPotential A := by
  have hN : (A - δ • (1 : Matrix ι ι ℂ)).PosDef := hA.sub_smul_one hδ'
  refine ⟨hN.add_smul_vecMulVec a hw.le, ?_⟩
  have hDpos : lowerPotential A < lowerPotential (A - δ • (1 : Matrix ι ι ℂ)) :=
    lowerPotential_lt_sub_smul_one hA hδ hδ'
  rw [lowerPotential_add_smul_vecMulVec hN a hw.le]
  simp only [lowerVerifier] at hcond
  set D := lowerPotential (A - δ • (1 : Matrix ι ι ℂ)) - lowerPotential A with hDdef
  set qr := RCLike.re (star a ⬝ᵥ ((A - δ • (1 : Matrix ι ι ℂ))⁻¹ *ᵥ a)) with hqr
  set sr := RCLike.re (star a ⬝ᵥ (((A - δ • (1 : Matrix ι ι ℂ))⁻¹
    * (A - δ • (1 : Matrix ι ι ℂ))⁻¹) *ᵥ a)) with hsr
  have hD : 0 < D := by simp only [hDdef]; linarith
  have hq0 : 0 ≤ qr := hN.inv.posSemidef.re_dotProduct_nonneg a
  have hden : 0 < 1 + w * qr := by have := mul_nonneg hw.le hq0; linarith
  have hc : (w / (1 + w * qr)) * (1 + w * qr) = w := by field_simp
  have hgoal : D * (1 + w * qr) ≤ w * sr := by
    have h2 : D * (1 / w) ≤ D * (sr / D - qr) := mul_le_mul_of_nonneg_left hcond hD.le
    have h3 : D * (sr / D - qr) = sr - D * qr := by field_simp
    rw [h3] at h2
    have h5 := mul_le_mul_of_nonneg_left h2 hw.le
    have h4 : w * (D * (1 / w)) = D := by field_simp
    rw [h4] at h5
    nlinarith [h5]
  have hkey : D ≤ (w / (1 + w * qr)) * sr := by
    refine le_of_mul_le_mul_right ?_ hden
    calc D * (1 + w * qr) ≤ w * sr := hgoal
      _ = ((w / (1 + w * qr)) * (1 + w * qr)) * sr := by rw [hc]
      _ = (w / (1 + w * qr)) * sr * (1 + w * qr) := by ring
  simp only [hDdef] at hkey
  linarith

/-- **Barrier lemma, upper half.**  If the weight `w` satisfies
`upperVerifier J B ζ b ≤ 1/w`, then the updated matrix `B + ζ • J - w b b*` is again positive
definite and its upper potential has not increased. -/
theorem upperPotential_update_le [Nonempty κ] {J B : Matrix κ κ ℂ} (hJ : J.PosDef)
    (hB : B.PosDef) {ζ : ℝ} (hζ : 0 < ζ) (b : κ → ℂ) {w : ℝ} (hw : 0 < w)
    (hcond : upperVerifier J B ζ b ≤ 1 / w) :
    (B + ζ • J - w • vecMulVec b (star b)).PosDef ∧
      upperPotential J (B + ζ • J - w • vecMulVec b (star b)) ≤ upperPotential J B := by
  have hM : (B + ζ • J).PosDef := hB.add_smul_posDef hJ hζ
  have hEpos : upperPotential J (B + ζ • J) < upperPotential J B :=
    upperPotential_add_smul_lt hJ hB hζ
  have hMinvUnit : IsUnit ((B + ζ • J)⁻¹) := Matrix.isUnit_nonsing_inv_iff.2 hM.isUnit
  have hconjPD : ((B + ζ • J)⁻¹ * J * (B + ζ • J)⁻¹).PosDef := by
    have h := hJ.conjTranspose_mul_mul_same (B := (B + ζ • J)⁻¹)
      (Matrix.mulVec_injective_iff_isUnit.2 hMinvUnit)
    rwa [hM.inv.isHermitian.eq] at h
  simp only [upperVerifier] at hcond
  set E := upperPotential J B - upperPotential J (B + ζ • J) with hEdef
  set pr := RCLike.re (star b ⬝ᵥ ((B + ζ • J)⁻¹ *ᵥ b)) with hpr
  set rr := RCLike.re (star b ⬝ᵥ (((B + ζ • J)⁻¹ * J * (B + ζ • J)⁻¹) *ᵥ b)) with hrr
  have hE : 0 < E := by simp only [hEdef]; linarith
  have hp0 : 0 ≤ pr := hM.inv.posSemidef.re_dotProduct_nonneg b
  have hr0 : 0 ≤ rr := hconjPD.posSemidef.re_dotProduct_nonneg b
  have hstrict : 0 < 1 - w * pr := by
    rcases eq_or_ne b 0 with rfl | hb
    · simp only [hpr]
      simp
    · have hrpos : 0 < rr := by
        simp only [hrr]
        exact hconjPD.re_dotProduct_pos hb
      have hdiv : 0 < rr / E := div_pos hrpos hE
      have hwinv : w * (1 / w) = 1 := by field_simp
      nlinarith [hcond, hdiv, hw, hwinv]
  refine ⟨hM.sub_smul_vecMulVec b hw.le hstrict, ?_⟩
  rw [upperPotential_sub_smul_vecMulVec hJ hM b hstrict]
  have hc : (w / (1 - w * pr)) * (1 - w * pr) = w := by field_simp
  have hgoal : w * rr ≤ E * (1 - w * pr) := by
    have h2 : E * (rr / E + pr) ≤ E * (1 / w) := mul_le_mul_of_nonneg_left hcond hE.le
    have h3 : E * (rr / E + pr) = rr + E * pr := by field_simp
    rw [h3] at h2
    have h5 := mul_le_mul_of_nonneg_left h2 hw.le
    have h4 : w * (E * (1 / w)) = E := by field_simp
    rw [h4] at h5
    nlinarith [h5]
  have hkey : (w / (1 - w * pr)) * rr ≤ E := by
    refine le_of_mul_le_mul_right ?_ hstrict
    calc (w / (1 - w * pr)) * rr * (1 - w * pr)
        = ((w / (1 - w * pr)) * (1 - w * pr)) * rr := by ring
      _ = w * rr := by rw [hc]
      _ ≤ E * (1 - w * pr) := hgoal
  simp only [hEdef] at hkey
  linarith

/-- The upper verifier is nonnegative: both of its summands are, the numerator because
`X J X` is positive semidefinite and the denominator because growing `B` lowers the upper
potential. -/
theorem upperVerifier_nonneg [Nonempty κ] {J B : Matrix κ κ ℂ} (hJ : J.PosDef)
    (hB : B.PosDef) {ζ : ℝ} (hζ : 0 < ζ) (b : κ → ℂ) : 0 ≤ upperVerifier J B ζ b := by
  have hM : (B + ζ • J).PosDef := hB.add_smul_posDef hJ hζ
  have hconj : ((B + ζ • J)⁻¹ * J * (B + ζ • J)⁻¹).PosSemidef := by
    have h := hJ.posSemidef.conjTranspose_mul_mul_same ((B + ζ • J)⁻¹)
    rwa [hM.inv.isHermitian.eq] at h
  have h1 : 0 ≤ RCLike.re (star b ⬝ᵥ (((B + ζ • J)⁻¹ * J * (B + ζ • J)⁻¹) *ᵥ b)) :=
    hconj.re_dotProduct_nonneg b
  have h2 : 0 ≤ RCLike.re (star b ⬝ᵥ ((B + ζ • J)⁻¹ *ᵥ b)) :=
    hM.inv.posSemidef.re_dotProduct_nonneg b
  have h3 : 0 < upperPotential J B - upperPotential J (B + ζ • J) := by
    have := upperPotential_add_smul_lt hJ hB hζ
    linarith
  simp only [upperVerifier]
  exact add_nonneg (div_nonneg h1 h3.le) h2

end Discretization
