/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import BasicResults.Operator.ShermanMorrison
public import BasicResults.Operator.Trace

/-!
# The upper potential of an operator

The upper half of the construction, for a second family with values in a separable Hilbert
space, runs on the same potential as in finite dimension,

`Ψ_J(B) = Tr (J B⁻¹)`,

with `J` a positive operator of finite trace, `B` a strictly positive operator, and the
trace `ContinuousLinearMap.trace`, computed along a Hilbert basis chosen once and for all
(`HilbertBasis.chosen`).  This file provides the potential, the exact effect
of the shift `B ↦ B + ζ • J` on it, and the resulting strict decrease.

Three hypotheses on `J` recur, and they are collected in
`Discretization.Infinite.IsFiniteTracePos`: `J` is positive, of finite trace, and
injective.  Injectivity stands in for positive definiteness of the Gram
matrix.  A positive operator of finite trace on an infinite-dimensional space is compact, so
it is never bounded away from zero, and injectivity is exactly what the strict inequalities
of the argument need.

For `B` the right notion is Mathlib's `IsStrictlyPositive`, positivity together with
invertibility, and the inverse is `Ring.inverse`.  How that inverse reacts to the shift is
`BasicResults.Operator.ShermanMorrison`.
-/

@[expose] public section

open scoped InnerProductSpace ComplexOrder
open ContinuousLinearMap

namespace Discretization

namespace Infinite

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The Hilbert basis chosen once and for all, along which traces are computed. -/
local notation "e₀" => HilbertBasis.chosen H

/-! ### Positive operators of finite trace -/

/-- The hypotheses carried by the Gram operator of the second family: it is **positive**, of
**finite trace**, and **injective**.  The trace is computed along the chosen basis
`HilbertBasis.chosen H`; for a positive operator its finiteness does not depend on the basis
(`ContinuousLinearMap.summable_re_inner_chosen_iff`).

The first two say that `J` is a positive trace-class operator; the third replaces the
positive definiteness of the finite-dimensional Gram matrix.  In the application `J` is the
Gram operator `∫ b b* dμ`, which has all three by
`Discretization.Infinite.isFiniteTracePos_of_integral_rankOne`. -/
structure IsFiniteTracePos (J : H →L[ℂ] H) : Prop where
  /-- `J` is a positive operator. -/
  nonneg : 0 ≤ J
  /-- The trace of `J` converges. -/
  summableTrace : Summable fun k => RCLike.re ⟪e₀ k, J (e₀ k)⟫_ℂ
  /-- `J` is injective. -/
  injective : ∀ v : H, J v = 0 → v = 0

variable {J : H →L[ℂ] H}

/-- A positive operator of finite trace is Hilbert–Schmidt: `∑ₖ ‖J eₖ‖² < ∞`.

Indeed `J eₖ = √J (√J eₖ)`, so `‖J eₖ‖ ≤ ‖√J‖ · ‖√J eₖ‖`, and the squares of the latter are
the terms of the trace. -/
theorem IsFiniteTracePos.summable_norm_sq_apply (hJ : IsFiniteTracePos J) :
    Summable fun k => ‖J (e₀ k)‖ ^ 2 := by
  have hsq : CFC.sqrt J * CFC.sqrt J = J := CFC.sqrt_mul_sqrt_self J hJ.nonneg
  refine (summable_norm_sq_comp e₀ (CFC.sqrt J)
    ((summable_norm_sq_sqrt_iff e₀ hJ.nonneg).2 hJ.summableTrace)).congr fun k => ?_
  rw [show CFC.sqrt J (CFC.sqrt J (e₀ k)) = J (e₀ k) from
    congrArg (fun S : H →L[ℂ] H => S (e₀ k)) hsq]

/-- **The conjugate `J S J` of a positive operator of finite trace is again one**, provided
`S` is strictly positive.

Positivity and the finiteness of the trace only need `S` positive and bounded; injectivity is
where invertibility of `S` enters, through the injectivity of `√S`. -/
theorem IsFiniteTracePos.conj (hJ : IsFiniteTracePos J) {S : H →L[ℂ] H}
    (hS : IsStrictlyPositive S) : IsFiniteTracePos (J * S * J) := by
  refine ⟨nonneg_conj hJ.nonneg hS.nonneg, ?_, ?_⟩
  · -- `Re ⟪eₖ, J S J eₖ⟫ = Re ⟪J eₖ, S (J eₖ)⟫ ≤ ‖S‖ ‖J eₖ‖²`
    have hterm : ∀ k, RCLike.re ⟪e₀ k, (J * S * J) (e₀ k)⟫_ℂ
        = RCLike.re ⟪J (e₀ k), S (J (e₀ k))⟫_ℂ := fun k =>
      re_inner_conj_apply hJ.nonneg.isSelfAdjoint S (e₀ k)
    refine Summable.of_nonneg_of_le (fun k => ?_) (fun k => ?_)
      (hJ.summable_norm_sq_apply.mul_left (‖S‖))
    · rw [hterm k]
      exact ((ContinuousLinearMap.nonneg_iff_isPositive (f := S)).1
        hS.nonneg).re_inner_nonneg_right _
    · rw [hterm k]
      have h1 : ‖RCLike.re ⟪J (e₀ k), S (J (e₀ k))⟫_ℂ‖ ≤ ‖⟪J (e₀ k), S (J (e₀ k))⟫_ℂ‖ :=
        RCLike.abs_re_le_norm _
      have h2 : ‖⟪J (e₀ k), S (J (e₀ k))⟫_ℂ‖ ≤ ‖J (e₀ k)‖ * ‖S (J (e₀ k))‖ :=
        norm_inner_le_norm _ _
      have h3 : ‖S (J (e₀ k))‖ ≤ ‖S‖ * ‖J (e₀ k)‖ := S.le_opNorm _
      have h4 : (0 : ℝ) ≤ ‖J (e₀ k)‖ := norm_nonneg _
      have h5 : RCLike.re ⟪J (e₀ k), S (J (e₀ k))⟫_ℂ ≤ ‖J (e₀ k)‖ * ‖S (J (e₀ k))‖ :=
        le_trans (le_abs_self _) (h1.trans h2)
      nlinarith
  · -- injectivity, through the injectivity of `√S`
    intro v hv
    have hinjS : ∀ y : H, CFC.sqrt S y = 0 → y = 0 := fun y hy =>
      (ContinuousLinearMap.isUnit_iff_bijective.1
        ((CFC.isUnit_sqrt_iff S hS.nonneg).2 hS.isUnit)).1 (by rw [hy, map_zero])
    have hzero : RCLike.re ⟪J v, S (J v)⟫_ℂ = 0 := by
      rw [← re_inner_conj_apply hJ.nonneg.isSelfAdjoint S v, hv]
      simp
    rw [re_inner_apply_eq_norm_sq_sqrt hS.nonneg (J v)] at hzero
    have : CFC.sqrt S (J v) = 0 := by
      have h0 := norm_nonneg (CFC.sqrt S (J v))
      have : ‖CFC.sqrt S (J v)‖ = 0 := by nlinarith
      exact norm_eq_zero.1 this
    exact hJ.injective v (hinjS _ this)

/-- **The trace of a positive injective operator of finite trace is positive** on a nonzero
space.  A vanishing trace would force `J` itself to vanish, which injectivity forbids. -/
theorem IsFiniteTracePos.trace_pos [Nontrivial H] (hJ : IsFiniteTracePos J) :
    0 < trace J := by
  obtain ⟨k⟩ := (inferInstance : Nonempty (HilbertBasis.chosenIndex H))
  have hJ0 : J ≠ 0 := fun h => (e₀).ne_zero k (hJ.injective (e₀ k) (by rw [h]; rfl))
  refine lt_of_le_of_ne (traceAlong_nonneg e₀ hJ.nonneg) fun h => hJ0 ?_
  exact eq_zero_of_traceAlong_eq_zero e₀ hJ.nonneg hJ.summableTrace h.symm

/-! ### The upper potential -/

/-- The **upper potential** `Ψ_J(B) = Tr (J B⁻¹)` of a strictly positive operator `B`
relative to a positive operator `J` of finite trace, the trace computed along the chosen basis
(`Discretization.Infinite.upperPotential_eq_trace`). -/
noncomputable def upperPotential (J B : H →L[ℂ] H) : ℝ :=
  traceAlong e₀ (J * Ring.inverse B)

/-- The upper potential is the trace `Tr (J B⁻¹)`. -/
theorem upperPotential_eq_trace (J B : H →L[ℂ] H) :
    upperPotential J B = trace (J * Ring.inverse B) := rfl

/-- **The upper potential is positive.**  It vanishes only if `J` does, which injectivity
forbids as soon as the space is nonzero. -/
theorem upperPotential_pos [Nontrivial H] (hJ : IsFiniteTracePos J) {B : H →L[ℂ] H}
    (hB : IsStrictlyPositive B) : 0 < upperPotential J B := by
  obtain ⟨k⟩ := (inferInstance : Nonempty (HilbertBasis.chosenIndex H))
  have hJ0 : J ≠ 0 := fun h =>
    (e₀).ne_zero k (hJ.injective (e₀ k) (by rw [h]; rfl))
  exact traceAlong_mul_pos e₀ hJ.nonneg (hB.ringInverse).nonneg
    (hB.ringInverse).isUnit hJ.summableTrace hJ0

/-! ### The effect of the shift -/

/-- **The gain of the upper potential under the shift:**
`Ψ_J(B) - Ψ_J(B + ζ • J) = ζ · Tr ((J B⁻¹ J) (B + ζ • J)⁻¹)`.

The right-hand side is a trace of a product of two positive operators, the first of finite
trace, so it is nonnegative.  It is even positive, which is the content of
`Discretization.Infinite.upperPotential_add_smul_lt`. -/
theorem upperPotential_sub_eq (hJ : IsFiniteTracePos J) {B : H →L[ℂ] H}
    (hB : IsStrictlyPositive B) {ζ : ℝ} (hζ : 0 ≤ ζ) :
    upperPotential J B - upperPotential J (B + ζ • J)
      = ζ * traceAlong e₀ ((J * Ring.inverse B * J) * Ring.inverse (B + ζ • J)) := by
  have hM : IsStrictlyPositive (B + ζ • J) := isStrictlyPositive_add_smul hJ.nonneg hB hζ
  have hres := inverse_sub_inverse_add_smul hJ.nonneg hB hζ
  have hXW : (0 : H →L[ℂ] H) ≤ Ring.inverse B - Ring.inverse (B + ζ • J) :=
    sub_nonneg.2 (inverse_add_smul_le hJ.nonneg hB hζ)
  -- split the trace of `J B⁻¹` along `B⁻¹ = (B + ζ • J)⁻¹ + (B⁻¹ - (B + ζ • J)⁻¹)`
  have hsplit : J * Ring.inverse B
      = J * Ring.inverse (B + ζ • J)
        + J * (Ring.inverse B - Ring.inverse (B + ζ • J)) := by
    rw [mul_sub]; abel
  have h₁ : Summable fun k => RCLike.re ⟪e₀ k, (J * Ring.inverse (B + ζ • J)) (e₀ k)⟫_ℂ :=
    summable_re_inner_apply_mul e₀ hJ.nonneg (hM.ringInverse).nonneg
      hJ.summableTrace
  have h₂ : Summable fun k =>
      RCLike.re ⟪e₀ k, (J * (Ring.inverse B - Ring.inverse (B + ζ • J))) (e₀ k)⟫_ℂ :=
    summable_re_inner_apply_mul e₀ hJ.nonneg hXW hJ.summableTrace
  have hmul : J * (Ring.inverse B - Ring.inverse (B + ζ • J))
      = ζ • ((J * Ring.inverse B * J) * Ring.inverse (B + ζ • J)) := by
    rw [hres, mul_smul_comm]
    congr 1
  rw [upperPotential, upperPotential]
  conv_lhs => rw [hsplit]
  rw [traceAlong_add e₀ h₁ h₂, hmul, traceAlong_smul]
  ring

/-- **Growing `B` decreases the upper potential strictly.** -/
theorem upperPotential_add_smul_lt [Nontrivial H] (hJ : IsFiniteTracePos J) {B : H →L[ℂ] H}
    (hB : IsStrictlyPositive B) {ζ : ℝ} (hζ : 0 < ζ) :
    upperPotential J (B + ζ • J) < upperPotential J B := by
  have hM : IsStrictlyPositive (B + ζ • J) := isStrictlyPositive_add_smul hJ.nonneg hB hζ.le
  have hconj : IsFiniteTracePos (J * Ring.inverse B * J) :=
    hJ.conj (hB.ringInverse)
  obtain ⟨k⟩ := (inferInstance : Nonempty (HilbertBasis.chosenIndex H))
  have hne : J * Ring.inverse B * J ≠ 0 := fun h =>
    (e₀).ne_zero k (hconj.injective (e₀ k) (by rw [h]; rfl))
  have hpos : 0 < traceAlong e₀ ((J * Ring.inverse B * J) * Ring.inverse (B + ζ • J)) :=
    traceAlong_mul_pos e₀ hconj.nonneg (hM.ringInverse).nonneg
      (hM.ringInverse).isUnit hconj.summableTrace hne
  have heq := upperPotential_sub_eq hJ hB hζ.le
  nlinarith [heq, hpos, hζ]

/-! ### Multiples of the identity -/

omit [CompleteSpace H] in
/-- The inverse of a positive multiple of the identity. -/
theorem inverse_smul_one {c : ℝ} (hc : c ≠ 0) :
    Ring.inverse (c • (1 : H →L[ℂ] H)) = c⁻¹ • (1 : H →L[ℂ] H) := by
  refine Ring.inverse_eq_of_mul_eq_one ?_ ?_ <;>
    rw [smul_mul_assoc, one_mul, smul_smul]
  · rw [mul_inv_cancel₀ hc, one_smul]
  · rw [inv_mul_cancel₀ hc, one_smul]

/-- A positive multiple of the identity is strictly positive. -/
theorem isStrictlyPositive_smul_one {c : ℝ} (hc : 0 < c) :
    IsStrictlyPositive (c • (1 : H →L[ℂ] H)) := by
  refine ⟨smul_nonneg hc.le zero_le_one, ⟨⟨c • 1, c⁻¹ • 1, ?_, ?_⟩, rfl⟩⟩ <;>
    rw [smul_mul_assoc, one_mul, smul_smul]
  · rw [mul_inv_cancel₀ hc.ne', one_smul]
  · rw [inv_mul_cancel₀ hc.ne', one_smul]

/-- `Ψ_J(c • 1) = Tr J / c`. -/
theorem upperPotential_smul_one {c : ℝ} (hc : c ≠ 0) :
    upperPotential J (c • (1 : H →L[ℂ] H)) = trace J / c := by
  rw [upperPotential, trace, inverse_smul_one hc, mul_smul_comm, mul_one, traceAlong_smul,
    div_eq_inv_mul]

end Infinite

end Discretization
