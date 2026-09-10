/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
import BasicResults

/-!
# The upper potential of an operator

The upper half of the construction, for a second family indexed by a countable set, runs on
the same potential as in finite dimension,

`Ψ_J(B) = Tr (J B⁻¹)`,

now with `J` a positive operator of finite trace, `B` a strictly positive operator, and the
trace taken along a fixed Hilbert basis.  This file provides the potential, the exact effect
of the shift `B ↦ B + ζ • J` on it, and the resulting strict decrease.

Three hypotheses on `J` recur, and they are bundled as `Discretization.Infinite.IsFiniteTracePos`:
`J` is positive, its trace along the basis converges, and it is injective.  Injectivity is
what replaces positive definiteness of the Gram matrix: a positive operator of finite trace
on an infinite-dimensional space is compact, so it is never bounded away from zero, and
injectivity is exactly what the strict inequalities of the argument need.

For `B` the right notion is Mathlib's `IsStrictlyPositive`, positivity together with
invertibility, and the inverse is `Ring.inverse`.  The resolvent identity is Mathlib's
`Ring.inverse_sub_inverse`, valid in any ring, and the antitonicity of the inverse is
`CStarAlgebra.ringInverse_le_ringInverse`.
-/

open scoped InnerProductSpace ComplexOrder

namespace Discretization

namespace Infinite

variable {κ H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ### Positive operators of finite trace -/

/-- The hypotheses carried by the Gram operator of the second family: it is **positive**, its
**trace** along the basis `e` converges, and it is **injective**.

The first two say that `J` is a positive trace-class operator; the third replaces the
positive definiteness of the finite-dimensional Gram matrix.  In the application `J` is
diagonal with strictly positive entries, so all three are immediate. -/
structure IsFiniteTracePos (e : HilbertBasis κ ℂ H) (J : H →L[ℂ] H) : Prop where
  /-- `J` is a positive operator. -/
  nonneg : 0 ≤ J
  /-- The trace of `J` along `e` converges. -/
  summableTrace : Summable fun k => RCLike.re ⟪e k, J (e k)⟫_ℂ
  /-- `J` is injective. -/
  injective : ∀ v : H, J v = 0 → v = 0

variable {e : HilbertBasis κ ℂ H} {J : H →L[ℂ] H}

/-- A positive operator of finite trace is Hilbert–Schmidt: `∑ₖ ‖J eₖ‖² < ∞`.

Indeed `J eₖ = √J (√J eₖ)`, so `‖J eₖ‖ ≤ ‖√J‖ · ‖√J eₖ‖`, and the squares of the latter are
the terms of the trace. -/
theorem IsFiniteTracePos.summable_norm_sq_apply (hJ : IsFiniteTracePos e J) :
    Summable fun k => ‖J (e k)‖ ^ 2 := by
  have hS : Summable fun k => ‖CFC.sqrt J (e k)‖ ^ 2 :=
    (summable_norm_sq_sqrt_iff e hJ.nonneg).2 hJ.summableTrace
  have hsq : CFC.sqrt J * CFC.sqrt J = J := CFC.sqrt_mul_sqrt_self J hJ.nonneg
  refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_)
    (hS.mul_left (‖CFC.sqrt J‖ ^ 2))
  have happ : J (e k) = CFC.sqrt J (CFC.sqrt J (e k)) :=
    congrArg (fun S : H →L[ℂ] H => S (e k)) hsq.symm
  have h := (CFC.sqrt J).le_opNorm (CFC.sqrt J (e k))
  have h0 : (0 : ℝ) ≤ ‖J (e k)‖ := norm_nonneg _
  have h1 : (0 : ℝ) ≤ ‖CFC.sqrt J‖ * ‖CFC.sqrt J (e k)‖ := by positivity
  calc ‖J (e k)‖ ^ 2 = ‖CFC.sqrt J (CFC.sqrt J (e k))‖ ^ 2 := by rw [happ]
    _ ≤ (‖CFC.sqrt J‖ * ‖CFC.sqrt J (e k)‖) ^ 2 := by
        have h2 : ‖CFC.sqrt J (CFC.sqrt J (e k))‖ ≤ ‖CFC.sqrt J‖ * ‖CFC.sqrt J (e k)‖ := h
        nlinarith [norm_nonneg (CFC.sqrt J (CFC.sqrt J (e k)))]
    _ = ‖CFC.sqrt J‖ ^ 2 * ‖CFC.sqrt J (e k)‖ ^ 2 := by ring

/-- Conjugating a positive operator by a self-adjoint one keeps it positive: `J S J ≽ 0`. -/
theorem nonneg_conj {S : H →L[ℂ] H} (hJ : 0 ≤ J) (hS : 0 ≤ S) : (0 : H →L[ℂ] H) ≤ J * S * J := by
  have hJadj : ContinuousLinearMap.adjoint J = J := hJ.isSelfAdjoint.star_eq
  have h := ((ContinuousLinearMap.nonneg_iff_isPositive S).1 hS).adjoint_conj J
  rw [hJadj] at h
  rw [ContinuousLinearMap.nonneg_iff_isPositive]
  simpa [ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_assoc] using h

/-- **The conjugate `J S J` of a positive operator of finite trace is again one**, provided
the conjugating operator `S` is strictly positive.

Positivity and the finiteness of the trace only need `S` positive and bounded; injectivity is
where invertibility of `S` enters, through the injectivity of `√S`. -/
theorem IsFiniteTracePos.conj (hJ : IsFiniteTracePos e J) {S : H →L[ℂ] H}
    (hS : IsStrictlyPositive S) : IsFiniteTracePos e (J * S * J) := by
  refine ⟨nonneg_conj hJ.nonneg hS.nonneg, ?_, ?_⟩
  · -- `Re ⟪eₖ, J S J eₖ⟫ = Re ⟪J eₖ, S (J eₖ)⟫ ≤ ‖S‖ ‖J eₖ‖²`
    have hJadj : ContinuousLinearMap.adjoint J = J := hJ.nonneg.isSelfAdjoint.star_eq
    have hterm : ∀ k, RCLike.re ⟪e k, (J * S * J) (e k)⟫_ℂ
        = RCLike.re ⟪J (e k), S (J (e k))⟫_ℂ := fun k => by
      have h := ContinuousLinearMap.adjoint_inner_right J (e k) (S (J (e k)))
      rw [hJadj] at h
      rw [show (J * S * J) (e k) = J (S (J (e k))) from rfl, h]
    refine Summable.of_nonneg_of_le (fun k => ?_) (fun k => ?_)
      (hJ.summable_norm_sq_apply.mul_left (‖S‖))
    · rw [hterm k]
      exact ((ContinuousLinearMap.nonneg_iff_isPositive S).1 hS.nonneg).re_inner_nonneg_right _
    · rw [hterm k]
      have h1 : ‖RCLike.re ⟪J (e k), S (J (e k))⟫_ℂ‖ ≤ ‖⟪J (e k), S (J (e k))⟫_ℂ‖ :=
        RCLike.abs_re_le_norm _
      have h2 : ‖⟪J (e k), S (J (e k))⟫_ℂ‖ ≤ ‖J (e k)‖ * ‖S (J (e k))‖ :=
        norm_inner_le_norm _ _
      have h3 : ‖S (J (e k))‖ ≤ ‖S‖ * ‖J (e k)‖ := S.le_opNorm _
      have h4 : (0 : ℝ) ≤ ‖J (e k)‖ := norm_nonneg _
      have h5 : RCLike.re ⟪J (e k), S (J (e k))⟫_ℂ ≤ ‖J (e k)‖ * ‖S (J (e k))‖ :=
        le_trans (le_abs_self _) (h1.trans h2)
      nlinarith
  · -- injectivity, through the injectivity of `√S`
    intro v hv
    have hSsqrt : IsUnit (CFC.sqrt S) := (CFC.isUnit_sqrt_iff S hS.nonneg).2 hS.isUnit
    obtain ⟨w, hw⟩ := hSsqrt
    have hinjS : ∀ y : H, CFC.sqrt S y = 0 → y = 0 := fun y hy => by
      have h1 : ((↑w⁻¹ : H →L[ℂ] H) * (↑w : H →L[ℂ] H)) y = y := by rw [w.inv_mul]; rfl
      have h2 : (↑w : H →L[ℂ] H) y = 0 := by rw [hw]; exact hy
      calc y = ((↑w⁻¹ : H →L[ℂ] H) * (↑w : H →L[ℂ] H)) y := h1.symm
        _ = (↑w⁻¹ : H →L[ℂ] H) ((↑w : H →L[ℂ] H) y) := rfl
        _ = (↑w⁻¹ : H →L[ℂ] H) 0 := by rw [h2]
        _ = 0 := map_zero _
    have hJadj : ContinuousLinearMap.adjoint J = J := hJ.nonneg.isSelfAdjoint.star_eq
    have hzero : RCLike.re ⟪J v, S (J v)⟫_ℂ = 0 := by
      have h := ContinuousLinearMap.adjoint_inner_right J v (S (J v))
      rw [hJadj] at h
      rw [← h, show J (S (J v)) = (J * S * J) v from rfl, hv]
      simp
    rw [re_inner_apply_eq_norm_sq_sqrt hS.nonneg (J v)] at hzero
    have : CFC.sqrt S (J v) = 0 := by
      have h0 := norm_nonneg (CFC.sqrt S (J v))
      have : ‖CFC.sqrt S (J v)‖ = 0 := by nlinarith
      exact norm_eq_zero.1 this
    exact hJ.injective v (hinjS _ this)

/-! ### The upper potential -/

/-- The **upper potential** `Ψ_J(B) = Tr (J B⁻¹)` of a strictly positive operator `B`
relative to a positive operator `J` of finite trace. -/
noncomputable def upperPotential (e : HilbertBasis κ ℂ H) (J B : H →L[ℂ] H) : ℝ :=
  traceAlong e (J * Ring.inverse B)

/-- The upper potential is nonnegative. -/
theorem upperPotential_nonneg (hJ : IsFiniteTracePos e J) {B : H →L[ℂ] H}
    (hB : IsStrictlyPositive B) : 0 ≤ upperPotential e J B :=
  traceAlong_mul_nonneg e hJ.nonneg (isStrictlyPositive_inverse hB).nonneg hJ.summableTrace

/-- **The upper potential is positive.**  It vanishes only if `J` does, which injectivity
forbids as soon as the space is nonzero. -/
theorem upperPotential_pos [Nonempty κ] (hJ : IsFiniteTracePos e J) {B : H →L[ℂ] H}
    (hB : IsStrictlyPositive B) : 0 < upperPotential e J B := by
  obtain ⟨k⟩ := ‹Nonempty κ›
  have hek : e k ≠ 0 := by
    intro h
    have : ‖e k‖ = 1 := e.orthonormal.1 k
    rw [h, norm_zero] at this
    exact absurd this (by norm_num)
  have hJ0 : J ≠ 0 := fun h => hek (hJ.injective (e k) (by rw [h]; rfl))
  exact traceAlong_mul_pos e hJ.nonneg (isStrictlyPositive_inverse hB).nonneg
    (isStrictlyPositive_inverse hB).isUnit hJ.summableTrace hJ0

/-! ### The effect of the shift -/

/-- Growing `B` by `ζ • J` keeps it strictly positive. -/
theorem isStrictlyPositive_add_smul (hJ : 0 ≤ J) {B : H →L[ℂ] H} (hB : IsStrictlyPositive B)
    {ζ : ℝ} (hζ : 0 ≤ ζ) : IsStrictlyPositive (B + ζ • J) := by
  have hle : B ≤ B + ζ • J := by
    have h : (0 : H →L[ℂ] H) ≤ ζ • J := smul_nonneg hζ hJ
    simpa using add_le_add_left h B
  exact ⟨hB.nonneg.trans hle, CStarAlgebra.isUnit_of_le B hle hB⟩

/-- **The resolvent identity** for the shift by a multiple of `J`:
`B⁻¹ - (B + ζ • J)⁻¹ = ζ • (B⁻¹ J (B + ζ • J)⁻¹)`.

This is Mathlib's `Ring.inverse_sub_inverse`, which holds in any ring. -/
theorem inverse_sub_inverse_add_smul (hJ : 0 ≤ J) {B : H →L[ℂ] H} (hB : IsStrictlyPositive B)
    {ζ : ℝ} (hζ : 0 ≤ ζ) :
    Ring.inverse B - Ring.inverse (B + ζ • J)
      = ζ • (Ring.inverse B * J * Ring.inverse (B + ζ • J)) := by
  have hM : IsStrictlyPositive (B + ζ • J) := isStrictlyPositive_add_smul hJ hB hζ
  rw [Ring.inverse_sub_inverse (iff_of_true hB.isUnit hM.isUnit)]
  have hdiff : B + ζ • J - B = ζ • J := by abel
  rw [hdiff, mul_smul_comm, smul_mul_assoc]

/-- The shifted inverse is below the original one: `(B + ζ • J)⁻¹ ≼ B⁻¹`. -/
theorem inverse_add_smul_le (hJ : 0 ≤ J) {B : H →L[ℂ] H} (hB : IsStrictlyPositive B)
    {ζ : ℝ} (hζ : 0 ≤ ζ) : Ring.inverse (B + ζ • J) ≤ Ring.inverse B := by
  have hle : B ≤ B + ζ • J := by
    have h : (0 : H →L[ℂ] H) ≤ ζ • J := smul_nonneg hζ hJ
    simpa using add_le_add_left h B
  exact CStarAlgebra.ringInverse_le_ringInverse hle hB

/-- **The gain of the upper potential under the shift:**
`Ψ_J(B) - Ψ_J(B + ζ • J) = ζ · Tr ((J B⁻¹ J) (B + ζ • J)⁻¹)`.

The right-hand side is a trace of a product of two positive operators, the first of finite
trace, so it is nonnegative — and positive, which is the content of
`Discretization.Infinite.upperPotential_add_smul_lt`. -/
theorem upperPotential_sub_eq (hJ : IsFiniteTracePos e J) {B : H →L[ℂ] H}
    (hB : IsStrictlyPositive B) {ζ : ℝ} (hζ : 0 ≤ ζ) :
    upperPotential e J B - upperPotential e J (B + ζ • J)
      = ζ * traceAlong e ((J * Ring.inverse B * J) * Ring.inverse (B + ζ • J)) := by
  have hM : IsStrictlyPositive (B + ζ • J) := isStrictlyPositive_add_smul hJ.nonneg hB hζ
  have hres := inverse_sub_inverse_add_smul hJ.nonneg hB hζ
  have hXW : (0 : H →L[ℂ] H) ≤ Ring.inverse B - Ring.inverse (B + ζ • J) :=
    sub_nonneg.2 (inverse_add_smul_le hJ.nonneg hB hζ)
  -- split the trace of `J B⁻¹` along `B⁻¹ = (B + ζ • J)⁻¹ + (B⁻¹ - (B + ζ • J)⁻¹)`
  have hsplit : J * Ring.inverse B
      = J * Ring.inverse (B + ζ • J)
        + J * (Ring.inverse B - Ring.inverse (B + ζ • J)) := by
    rw [mul_sub]; abel
  have h₁ : Summable fun k => RCLike.re ⟪e k, (J * Ring.inverse (B + ζ • J)) (e k)⟫_ℂ :=
    summable_re_inner_apply_mul e hJ.nonneg (isStrictlyPositive_inverse hM).nonneg
      hJ.summableTrace
  have h₂ : Summable fun k =>
      RCLike.re ⟪e k, (J * (Ring.inverse B - Ring.inverse (B + ζ • J))) (e k)⟫_ℂ :=
    summable_re_inner_apply_mul e hJ.nonneg hXW hJ.summableTrace
  have hmul : J * (Ring.inverse B - Ring.inverse (B + ζ • J))
      = ζ • ((J * Ring.inverse B * J) * Ring.inverse (B + ζ • J)) := by
    rw [hres, mul_smul_comm]
    congr 1
  rw [upperPotential, upperPotential]
  conv_lhs => rw [hsplit]
  rw [traceAlong_add e h₁ h₂, hmul, traceAlong_smul]
  ring

/-- **Growing `B` decreases the upper potential strictly.** -/
theorem upperPotential_add_smul_lt [Nonempty κ] (hJ : IsFiniteTracePos e J) {B : H →L[ℂ] H}
    (hB : IsStrictlyPositive B) {ζ : ℝ} (hζ : 0 < ζ) :
    upperPotential e J (B + ζ • J) < upperPotential e J B := by
  have hM : IsStrictlyPositive (B + ζ • J) := isStrictlyPositive_add_smul hJ.nonneg hB hζ.le
  have hconj : IsFiniteTracePos e (J * Ring.inverse B * J) :=
    hJ.conj (isStrictlyPositive_inverse hB)
  obtain ⟨k⟩ := ‹Nonempty κ›
  have hek : e k ≠ 0 := by
    intro h
    have : ‖e k‖ = 1 := e.orthonormal.1 k
    rw [h, norm_zero] at this
    exact absurd this (by norm_num)
  have hne : J * Ring.inverse B * J ≠ 0 := fun h =>
    hek (hconj.injective (e k) (by rw [h]; rfl))
  have hpos : 0 < traceAlong e ((J * Ring.inverse B * J) * Ring.inverse (B + ζ • J)) :=
    traceAlong_mul_pos e hconj.nonneg (isStrictlyPositive_inverse hM).nonneg
      (isStrictlyPositive_inverse hM).isUnit hconj.summableTrace hne
  have heq := upperPotential_sub_eq hJ hB hζ.le
  nlinarith [heq, hpos, hζ]

end Infinite

end Discretization
