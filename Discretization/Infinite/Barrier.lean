/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
import Discretization.Barrier
import Discretization.Infinite.Potentials

/-!
# The upper verifier and the barrier lemma for operators

The upper half of the barrier lemma, transcribed from `Discretization.Barrier` to operators.
A candidate point `u` is tested by the **upper verifier**

`U_B^ζ(u) = ⟪u, X J X u⟫ / (Ψ_J(B) - Ψ_J(B + ζ • J)) + ⟪u, X u⟫`,  `X = (B + ζ • J)⁻¹`,

and `Discretization.Infinite.upperPotential_update_le` says that a weight `w` with
`U_B^ζ(u) ≤ 1/w` keeps the grown operator strictly positive after the rank-one downdate and
does not increase the upper potential.

The real-number inequality behind it is shared with the finite-dimensional proof: it is
`Discretization.upper_barrier_ineq`.  What has to be redone is the closed form of the
potential after a rank-one downdate, which now rests on
`Discretization.inverse_sub_smul_rankOne_of_nonneg`, and the positivity of the numerator,
which rests on the injectivity of `J`.
-/

open scoped InnerProductSpace ComplexOrder
open InnerProductSpace

namespace Discretization

namespace Infinite

variable {κ H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {e : HilbertBasis κ ℂ H} {J : H →L[ℂ] H}

/-! ### Quadratic forms of a positive injective operator -/

/-- **The quadratic form of a positive injective operator is positive on nonzero vectors.**

This is the substitute for positive definiteness: the eigenvalues of `J` accumulate at zero,
but the quadratic form still does not vanish anywhere except at `0`. -/
theorem IsFiniteTracePos.re_inner_pos (hJ : IsFiniteTracePos e J) {y : H} (hy : y ≠ 0) :
    0 < RCLike.re ⟪y, J y⟫_ℂ := by
  have hsq : CFC.sqrt J * CFC.sqrt J = J := CFC.sqrt_mul_sqrt_self J hJ.nonneg
  rw [re_inner_apply_eq_norm_sq_sqrt hJ.nonneg y]
  rcases eq_or_lt_of_le (norm_nonneg (CFC.sqrt J y)) with h0 | h0
  · exfalso
    have hzero : CFC.sqrt J y = 0 := norm_eq_zero.1 h0.symm
    refine hy (hJ.injective y ?_)
    calc J y = CFC.sqrt J (CFC.sqrt J y) :=
          congrArg (fun S : H →L[ℂ] H => S y) hsq.symm
      _ = CFC.sqrt J 0 := by rw [hzero]
      _ = 0 := map_zero _
  · positivity

/-- The conjugate `X J X` of a positive injective operator by an invertible self-adjoint one
has a positive quadratic form on nonzero vectors. -/
theorem re_inner_conj_pos (hJ : IsFiniteTracePos e J) {X : H →L[ℂ] H}
    (hX : IsStrictlyPositive X) {u : H} (hu : u ≠ 0) :
    0 < RCLike.re ⟪u, (X * J * X) u⟫_ℂ := by
  have hXadj : ContinuousLinearMap.adjoint X = X := hX.nonneg.isSelfAdjoint.star_eq
  have hXu : X u ≠ 0 := by
    intro h
    obtain ⟨v, hv⟩ := hX.isUnit
    refine hu ?_
    have h1 : ((↑v⁻¹ : H →L[ℂ] H) * (↑v : H →L[ℂ] H)) u = u := by rw [v.inv_mul]; rfl
    have h2 : (↑v : H →L[ℂ] H) u = 0 := by rw [hv]; exact h
    calc u = ((↑v⁻¹ : H →L[ℂ] H) * (↑v : H →L[ℂ] H)) u := h1.symm
      _ = (↑v⁻¹ : H →L[ℂ] H) ((↑v : H →L[ℂ] H) u) := rfl
      _ = (↑v⁻¹ : H →L[ℂ] H) 0 := by rw [h2]
      _ = 0 := map_zero _
  have hmove : ⟪u, (X * J * X) u⟫_ℂ = ⟪X u, J (X u)⟫_ℂ := by
    have h := ContinuousLinearMap.adjoint_inner_right X u (J (X u))
    rw [hXadj] at h
    rw [show (X * J * X) u = X (J (X u)) from rfl, h]
  rw [hmove]
  exact hJ.re_inner_pos hXu

/-! ### The potential after a rank-one downdate -/

/-- **The upper potential after a rank-one downdate**, in closed form:
`Ψ_J(M - w u u*) = Ψ_J(M) + w / (1 - w ⟪u, M⁻¹ u⟫) · ⟪u, M⁻¹ J M⁻¹ u⟫`,
valid as long as the Sherman–Morrison denominator is positive. -/
theorem upperPotential_sub_smul_rankOne (hJ : IsFiniteTracePos e J) {M : H →L[ℂ] H}
    (hM : IsStrictlyPositive M) (u : H) {w : ℝ} (hw : 0 ≤ w)
    (hden : 0 < 1 - w * RCLike.re ⟪u, Ring.inverse M u⟫_ℂ) :
    upperPotential e J (M - w • rankOne ℂ u u)
      = upperPotential e J M
        + (w / (1 - w * RCLike.re ⟪u, Ring.inverse M u⟫_ℂ))
          * RCLike.re ⟪u, (Ring.inverse M * J * Ring.inverse M) u⟫_ℂ := by
  have hMinv : IsStrictlyPositive (Ring.inverse M) := isStrictlyPositive_inverse hM
  have hWadj : ContinuousLinearMap.adjoint (Ring.inverse M) = Ring.inverse M :=
    hMinv.nonneg.isSelfAdjoint.star_eq
  have hc0 : 0 ≤ w / (1 - w * RCLike.re ⟪u, Ring.inverse M u⟫_ℂ) := div_nonneg hw hden.le
  have hinv := inverse_sub_smul_rankOne_of_nonneg hM u hden
  have hR0 : (0 : H →L[ℂ] H)
      ≤ (w / (1 - w * RCLike.re ⟪u, Ring.inverse M u⟫_ℂ))
        • rankOne ℂ (Ring.inverse M u) (Ring.inverse M u) :=
    smul_nonneg hc0 (nonneg_rankOne_self _)
  have h₁ : Summable fun k => RCLike.re ⟪e k, (J * Ring.inverse M) (e k)⟫_ℂ :=
    summable_re_inner_apply_mul e hJ.nonneg hMinv.nonneg hJ.summableTrace
  have h₂ : Summable fun k => RCLike.re ⟪e k,
      (J * ((w / (1 - w * RCLike.re ⟪u, Ring.inverse M u⟫_ℂ))
        • rankOne ℂ (Ring.inverse M u) (Ring.inverse M u))) (e k)⟫_ℂ :=
    summable_re_inner_apply_mul e hJ.nonneg hR0 hJ.summableTrace
  have hform : RCLike.re ⟪Ring.inverse M u, J (Ring.inverse M u)⟫_ℂ
      = RCLike.re ⟪u, (Ring.inverse M * J * Ring.inverse M) u⟫_ℂ := by
    have h := ContinuousLinearMap.adjoint_inner_right (Ring.inverse M) u
      (J (Ring.inverse M u))
    rw [hWadj] at h
    rw [← h, show Ring.inverse M (J (Ring.inverse M u))
      = (Ring.inverse M * J * Ring.inverse M) u from rfl]
  rw [upperPotential, upperPotential, hinv, mul_add, traceAlong_add e h₁ h₂, mul_smul_comm,
    traceAlong_smul, traceAlong_mul_rankOne, hform]

/-! ### The verifier and the barrier lemma -/

/-- The **upper verifier** of a candidate vector `u`, testing how much of the gap opened by
the shift `B ↦ B + ζ • J` the rank-one downdate `w u u*` would consume. -/
noncomputable def upperVerifier (e : HilbertBasis κ ℂ H) (J B : H →L[ℂ] H) (ζ : ℝ) (u : H) :
    ℝ :=
  RCLike.re ⟪u, (Ring.inverse (B + ζ • J) * J * Ring.inverse (B + ζ • J)) u⟫_ℂ
      / (upperPotential e J B - upperPotential e J (B + ζ • J))
    + RCLike.re ⟪u, Ring.inverse (B + ζ • J) u⟫_ℂ

/-- The upper verifier is nonnegative: both summands are, the numerator because `X J X` is
positive and the denominator because growing `B` lowers the potential. -/
theorem upperVerifier_nonneg [Nonempty κ] (hJ : IsFiniteTracePos e J) {B : H →L[ℂ] H}
    (hB : IsStrictlyPositive B) {ζ : ℝ} (hζ : 0 < ζ) (u : H) :
    0 ≤ upperVerifier e J B ζ u := by
  have hM : IsStrictlyPositive (B + ζ • J) := isStrictlyPositive_add_smul hJ.nonneg hB hζ.le
  have hMinv : IsStrictlyPositive (Ring.inverse (B + ζ • J)) := isStrictlyPositive_inverse hM
  have h₁ : 0 ≤ RCLike.re ⟪u,
      (Ring.inverse (B + ζ • J) * J * Ring.inverse (B + ζ • J)) u⟫_ℂ :=
    ((ContinuousLinearMap.nonneg_iff_isPositive _).1
      (nonneg_conj hMinv.nonneg hJ.nonneg)).re_inner_nonneg_right u
  have h₂ : 0 ≤ RCLike.re ⟪u, Ring.inverse (B + ζ • J) u⟫_ℂ :=
    ((ContinuousLinearMap.nonneg_iff_isPositive _).1 hMinv.nonneg).re_inner_nonneg_right u
  have h₃ : 0 < upperPotential e J B - upperPotential e J (B + ζ • J) := by
    have := upperPotential_add_smul_lt hJ hB hζ
    linarith
  exact add_nonneg (div_nonneg h₁ h₃.le) h₂

/-- **Barrier lemma for operators, upper half.**  If the weight `w` satisfies
`U_B^ζ(u) ≤ 1/w`, then the updated operator `B + ζ • J - w u u*` is again strictly positive
and its upper potential has not increased.

The real arithmetic is `Discretization.upper_barrier_ineq`, shared verbatim with the
finite-dimensional proof. -/
theorem upperPotential_update_le [Nonempty κ] (hJ : IsFiniteTracePos e J) {B : H →L[ℂ] H}
    (hB : IsStrictlyPositive B) {ζ : ℝ} (hζ : 0 < ζ) (u : H) {w : ℝ} (hw : 0 < w)
    (hcond : upperVerifier e J B ζ u ≤ 1 / w) :
    IsStrictlyPositive (B + ζ • J - w • rankOne ℂ u u) ∧
      upperPotential e J (B + ζ • J - w • rankOne ℂ u u) ≤ upperPotential e J B := by
  have hM : IsStrictlyPositive (B + ζ • J) := isStrictlyPositive_add_smul hJ.nonneg hB hζ.le
  have hMinv : IsStrictlyPositive (Ring.inverse (B + ζ • J)) := isStrictlyPositive_inverse hM
  have hEpos : upperPotential e J (B + ζ • J) < upperPotential e J B :=
    upperPotential_add_smul_lt hJ hB hζ
  simp only [upperVerifier] at hcond
  set E := upperPotential e J B - upperPotential e J (B + ζ • J) with hEdef
  set p := RCLike.re ⟪u, Ring.inverse (B + ζ • J) u⟫_ℂ with hpdef
  set r := RCLike.re ⟪u,
    (Ring.inverse (B + ζ • J) * J * Ring.inverse (B + ζ • J)) u⟫_ℂ with hrdef
  have hE : 0 < E := by simp only [hEdef]; linarith
  have hp0 : 0 ≤ p := ((ContinuousLinearMap.nonneg_iff_isPositive _).1
    hMinv.nonneg).re_inner_nonneg_right u
  -- the Sherman–Morrison denominator is positive
  have hstrict : 0 < 1 - w * p := by
    rcases eq_or_ne u 0 with rfl | hu
    · simp only [hpdef]
      simp
    · have hrpos : 0 < r := by
        simp only [hrdef]
        exact re_inner_conj_pos hJ hMinv hu
      have hdiv : 0 < r / E := div_pos hrpos hE
      have hwinv : w * (1 / w) = 1 := by field_simp
      nlinarith [hcond, hdiv, hw, hwinv]
  refine ⟨isStrictlyPositive_sub_smul_rankOne hM u hw.le hstrict, ?_⟩
  rw [upperPotential_sub_smul_rankOne hJ hM u hw.le hstrict]
  have hkey : (w / (1 - w * p)) * r ≤ E := upper_barrier_ineq hE hw hstrict hcond
  simp only [hEdef] at hkey
  linarith

end Infinite

end Discretization
