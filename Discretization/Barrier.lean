/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
import BasicResults.ShermanMorrison
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

The effect of an update on the potentials is computed exactly
(`Discretization.lowerPotential_add_smul_vecMulVec`,
`Discretization.upperPotential_sub_smul_vecMulVec`).  The barrier lemma then follows from two
inequalities between real numbers (`Discretization.lower_barrier_ineq`,
`Discretization.upper_barrier_ineq`).
-/

open Matrix
open scoped ComplexOrder MatrixOrder

namespace Discretization

/-! ### The arithmetic of the two barriers

Once the potentials are computed in closed form, each half of the barrier lemma is one
inequality between real numbers. -/

/-- **The inequality behind the lower barrier.**  If the reciprocal weight `1/w` does not
exceed `s/D - q`, then the decrease `w/(1 + w q) · s` of the lower potential is at least the
increase `D` caused by the shift.  Here `D > 0` is that increase, `q ≥ 0` the quadratic form
of the shifted inverse and `s` the quadratic form of its square. -/
theorem lower_barrier_ineq {D w q s : ℝ} (hD : 0 < D) (hw : 0 < w) (hq : 0 ≤ q)
    (h : 1 / w ≤ s / D - q) : D ≤ (w / (1 + w * q)) * s := by
  have hden : 0 < 1 + w * q := by positivity
  rw [div_mul_eq_mul_div, le_div_iff₀ hden]
  have h1 := (div_le_iff₀ hw).1 h
  have h2 : D * (s / D - q) = s - D * q := by field_simp
  nlinarith

/-- **The inequality behind the upper barrier.**  If `r/E + p` does not exceed the reciprocal
weight `1/w`, then the increase `w/(1 - w p) · r` of the upper potential is at most the
decrease `E` caused by the shift.  Here `E > 0` is that decrease, `p` the quadratic form of
the shifted inverse and `r` the quadratic form of its `J`-conjugate; the hypothesis
`1 - w p > 0` is the Sherman–Morrison denominator. -/
theorem upper_barrier_ineq {E w p r : ℝ} (hE : 0 < E) (hw : 0 < w) (hden : 0 < 1 - w * p)
    (h : r / E + p ≤ 1 / w) : (w / (1 - w * p)) * r ≤ E := by
  rw [div_mul_eq_mul_div, div_le_iff₀ hden]
  have h1 := (le_div_iff₀ hw).1 h
  have h2 : E * (r / E + p) = r + E * p := by field_simp
  nlinarith

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
  rw [lowerPotential, lowerPotential, hN.inv_add_smul_vecMulVec a hw, Matrix.trace_sub,
    map_sub, Matrix.trace_smul, RCLike.smul_re, Matrix.trace_vecMulVec,
    Matrix.dotProduct_mulVec_self_star hN.inv.isHermitian]

/-- **The upper potential after a rank-one downdate**, in closed form:
`Ψ_J(M - w b b*) = Ψ_J(M) + w / (1 - w b* M⁻¹ b) · b* M⁻¹ J M⁻¹ b`,
valid as long as the Sherman–Morrison denominator `1 - w b* M⁻¹ b` is positive.

The identity holds for an arbitrary `J`; positivity of `J` is what makes the correction
term nonnegative. -/
theorem upperPotential_sub_smul_vecMulVec {J M : Matrix κ κ ℂ} (hM : M.PosDef)
    (b : κ → ℂ) {w : ℝ}
    (hden : 0 < 1 - w * RCLike.re (star b ⬝ᵥ (M⁻¹ *ᵥ b))) :
    upperPotential J (M - w • vecMulVec b (star b))
      = upperPotential J M + (w / (1 - w * RCLike.re (star b ⬝ᵥ (M⁻¹ *ᵥ b))))
          * RCLike.re (star b ⬝ᵥ ((M⁻¹ * J * M⁻¹) *ᵥ b)) := by
  rw [upperPotential, upperPotential, hM.inv_sub_smul_vecMulVec b hden, Matrix.mul_add,
    Matrix.mul_smul, Matrix.trace_add, map_add, Matrix.trace_smul, RCLike.smul_re,
    Matrix.trace_mul_vecMulVec_self_star, Matrix.dotProduct_conj_mulVec hM.inv.isHermitian]

/-- The **lower verifier** of a candidate vector `a`, measuring how much of the gap opened by
the shift `A ↦ A - δ • 1` the rank-one update `w a a*` would consume. -/
noncomputable def lowerVerifier (A : Matrix ι ι ℂ) (δ : ℝ) (a : ι → ℂ) : ℝ :=
  RCLike.re (star a ⬝ᵥ (((A - δ • (1 : Matrix ι ι ℂ))⁻¹ * (A - δ • (1 : Matrix ι ι ℂ))⁻¹)
      *ᵥ a)) / (lowerPotential (A - δ • (1 : Matrix ι ι ℂ)) - lowerPotential A)
    - RCLike.re (star a ⬝ᵥ ((A - δ • (1 : Matrix ι ι ℂ))⁻¹ *ᵥ a))

/-- The **upper verifier** of a candidate vector `b`, measuring how much of the gap opened by
the shift `B ↦ B + ζ • J` the rank-one update `w b b*` would consume.  Here
`X = (B + ζ • J)⁻¹`, and the two summands are `b* X J X b / (Ψ_J(B) - Ψ_J(B + ζ • J))` and
`b* X b`. -/
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
  have hkey : D ≤ (w / (1 + w * qr)) * sr := lower_barrier_ineq hD hw hq0 hcond
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
  have hconjPD : ((B + ζ • J)⁻¹ * J * (B + ζ • J)⁻¹).PosDef :=
    hJ.mul_mul_same_of_isHermitian hM.inv.isHermitian
      (Matrix.isUnit_nonsing_inv_iff.2 hM.isUnit)
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
  rw [upperPotential_sub_smul_vecMulVec hM b hstrict]
  have hkey : (w / (1 - w * pr)) * rr ≤ E := upper_barrier_ineq hE hw hstrict hcond
  simp only [hEdef] at hkey
  linarith

/-- The upper verifier is nonnegative: both of its summands are, the numerator because
`X J X` is positive semidefinite for `X = (B + ζ • J)⁻¹`, and the denominator because growing
`B` lowers the upper potential. -/
theorem upperVerifier_nonneg [Nonempty κ] {J B : Matrix κ κ ℂ} (hJ : J.PosDef)
    (hB : B.PosDef) {ζ : ℝ} (hζ : 0 < ζ) (b : κ → ℂ) : 0 ≤ upperVerifier J B ζ b := by
  have hM : (B + ζ • J).PosDef := hB.add_smul_posDef hJ hζ
  have hconj : ((B + ζ • J)⁻¹ * J * (B + ζ • J)⁻¹).PosSemidef :=
    hJ.posSemidef.mul_mul_same_of_isHermitian hM.inv.isHermitian
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
