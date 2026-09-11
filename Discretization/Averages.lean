/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
import Discretization.Barrier

/-!
# Averages of the verifiers

The verifiers of the previous file decide whether a single point is admissible.  This file
shows that on average they are, which is why an admissible point exists at all.

Let `a : Ω → ι → ℂ` be a family of square-integrable functions whose Gram matrix is the
identity, and `b : Ω → κ → ℂ` one whose Gram matrix is `J`.  Then

* `Discretization.integral_lowerVerifier_gt`: `∫ lowerVerifier A δ (a x) dμ > 1/δ - Φ(A)`,
* `Discretization.integral_upperVerifier_lt`: `∫ upperVerifier J B ζ (b x) dμ < 1/ζ + Ψ_J(B)`.

So as soon as `1/δ - Φ(A) ≥ 1/ζ + Ψ_J(B)`, the lower verifier exceeds the upper one on
average, hence at some point `x` (`Discretization.exists_admissible_point`).  Any weight `w`
between the two reciprocals is then admissible for both barriers.

The averages are computed with `Discretization.integral_re_quadForm`, which turns the
average of a quadratic form into a trace against the Gram matrix.  The estimate of the lower
average then rests on the Cauchy–Schwarz inequality for the trace
(`Matrix.PosSemidef.re_trace_mul_sq_le`), and the estimate of the upper average on the
antitonicity of the matrix inverse (`Matrix.PosDef.inv_le_inv_of_le`).
-/

open Matrix MeasureTheory
open scoped ComplexOrder MatrixOrder

namespace Discretization

variable {ι κ Ω : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  [MeasurableSpace Ω] {μ : Measure Ω}

/-- **The average of the lower verifier exceeds `1/δ - Φ(A)`.**

Writing `Y = A⁻¹`, `Z = (A - δ • 1)⁻¹`, `t = Re Tr (Y Z)` and `u = Re Tr (Y Z²)`, the average
equals `Re Tr (Z²) / (δ t) - Re Tr Z = 1/δ + u/t - Φ(A) - δ t`, so the claim amounts to
`δ t² < u`.  That is exactly what Cauchy–Schwarz gives: `t² ≤ Φ(A) · u` and `δ · Φ(A) < 1`. -/
theorem integral_lowerVerifier_gt [Nonempty ι] {A : Matrix ι ι ℂ} (hA : A.PosDef) {δ : ℝ}
    (hδ : 0 < δ) (hδ' : δ < (lowerPotential A)⁻¹) {a : Ω → ι → ℂ}
    (ha : ∀ k, MemLp (fun x => a x k) 2 μ) (hgram : gram a μ = 1) :
    1 / δ - lowerPotential A < ∫ x, lowerVerifier A δ (a x) ∂μ := by
  have hN : (A - δ • (1 : Matrix ι ι ℂ)).PosDef := hA.sub_smul_one hδ'
  -- split the average into two traces
  have hZZint : Integrable (fun x => RCLike.re (star (a x) ⬝ᵥ
      (((A - δ • (1 : Matrix ι ι ℂ))⁻¹ * (A - δ • (1 : Matrix ι ι ℂ))⁻¹) *ᵥ a x))) μ :=
    (integrable_quadForm ha _).re
  have hZint : Integrable (fun x => RCLike.re (star (a x) ⬝ᵥ
      ((A - δ • (1 : Matrix ι ι ℂ))⁻¹ *ᵥ a x))) μ := (integrable_quadForm ha _).re
  have hsplit : ∫ x, lowerVerifier A δ (a x) ∂μ
      = RCLike.re (((A - δ • (1 : Matrix ι ι ℂ))⁻¹ * (A - δ • (1 : Matrix ι ι ℂ))⁻¹).trace)
          / (lowerPotential (A - δ • (1 : Matrix ι ι ℂ)) - lowerPotential A)
        - lowerPotential (A - δ • (1 : Matrix ι ι ℂ)) := by
    simp only [lowerVerifier, lowerPotential]
    rw [integral_sub (hZZint.div_const _) hZint, integral_div,
      integral_re_quadForm ha _, integral_re_quadForm ha _, hgram, mul_one, mul_one]
  -- the resolvent identity, and the trace identities it implies
  have hres : (A - δ • (1 : Matrix ι ι ℂ))⁻¹ - A⁻¹
      = δ • ((A - δ • (1 : Matrix ι ι ℂ))⁻¹ * A⁻¹) :=
    Matrix.inv_sub_smul_one_sub_inv hA.isUnit hN.isUnit
  have hcyc : ((A - δ • (1 : Matrix ι ι ℂ))⁻¹ * A⁻¹
      * (A - δ • (1 : Matrix ι ι ℂ))⁻¹).trace
      = (A⁻¹ * (A - δ • (1 : Matrix ι ι ℂ))⁻¹ * (A - δ • (1 : Matrix ι ι ℂ))⁻¹).trace := by
    rw [Matrix.trace_mul_cycle, Matrix.trace_mul_cycle]
  have hSt : RCLike.re (((A - δ • (1 : Matrix ι ι ℂ))⁻¹
        * (A - δ • (1 : Matrix ι ι ℂ))⁻¹).trace)
      - RCLike.re ((A⁻¹ * (A - δ • (1 : Matrix ι ι ℂ))⁻¹).trace)
      = δ * RCLike.re ((A⁻¹ * (A - δ • (1 : Matrix ι ι ℂ))⁻¹
        * (A - δ • (1 : Matrix ι ι ℂ))⁻¹).trace) := by
    have h := congrArg
      (fun M => RCLike.re (Matrix.trace (M * (A - δ • (1 : Matrix ι ι ℂ))⁻¹))) hres
    simp only [Matrix.sub_mul, Matrix.trace_sub, map_sub, Matrix.smul_mul, Matrix.trace_smul,
      RCLike.smul_re, hcyc] at h
    exact h
  have hD : lowerPotential (A - δ • (1 : Matrix ι ι ℂ)) - lowerPotential A
      = δ * RCLike.re ((A⁻¹ * (A - δ • (1 : Matrix ι ι ℂ))⁻¹).trace) := by
    rw [lowerPotential_sub_eq hA hδ', Matrix.trace_mul_comm]
  have hCS := hA.inv.posSemidef.re_trace_mul_sq_le hN.inv.isHermitian
  have ht0 : 0 < RCLike.re ((A⁻¹ * (A - δ • (1 : Matrix ι ι ℂ))⁻¹).trace) :=
    hA.inv.re_trace_mul_pos hN.inv
  have hy0 : 0 < lowerPotential A := lowerPotential_pos hA
  -- from here on everything is real algebra
  rw [hsplit]
  simp only [lowerPotential] at hD hy0 hδ' ⊢
  set y := RCLike.re (A⁻¹).trace with hy
  set z := RCLike.re (((A - δ • (1 : Matrix ι ι ℂ))⁻¹).trace) with hz
  set S := RCLike.re (((A - δ • (1 : Matrix ι ι ℂ))⁻¹
    * (A - δ • (1 : Matrix ι ι ℂ))⁻¹).trace) with hS
  set t := RCLike.re ((A⁻¹ * (A - δ • (1 : Matrix ι ι ℂ))⁻¹).trace) with ht
  set u := RCLike.re ((A⁻¹ * (A - δ • (1 : Matrix ι ι ℂ))⁻¹
    * (A - δ • (1 : Matrix ι ι ℂ))⁻¹).trace) with hu
  have hδ0 : δ ≠ 0 := hδ.ne'
  have ht0' : t ≠ 0 := ht0.ne'
  have hδy : δ * y < 1 := by
    have h := mul_lt_mul_of_pos_right hδ' hy0
    rwa [inv_mul_cancel₀ hy0.ne'] at h
  have hu0 : 0 < u := by nlinarith [hCS, ht0, hy0]
  have hut : δ * t ^ 2 < u := by nlinarith [hCS, hδy, hu0, hδ.le]
  have hzt : z = y + δ * t := by linarith
  have hSeq : S = t + δ * u := by linarith
  have hfrac : S / (z - y) = 1 / δ + u / t := by
    rw [hSeq, hD]; field_simp
  rw [hfrac, hzt]
  have hut' : δ * t < u / t := by
    refine lt_of_mul_lt_mul_right ?_ ht0.le
    have hv : u / t * t = u := by field_simp
    rw [hv]; nlinarith [hut]
  linarith

/-- **The average of the upper verifier stays below `1/ζ + Ψ_J(B)`.**

Writing `W = B⁻¹` and `X = (B + ζ • J)⁻¹`, the average equals
`Re Tr (J X J X) / E + Ψ_J(B + ζ • J)` with `E = ζ · Re Tr (J W J X)`.  Since `X ≤ W` the
numerator is at most `Re Tr (J W J X) = E / ζ`, so the first summand is at most `1/ζ`, and
the second is smaller than `Ψ_J(B)`. -/
theorem integral_upperVerifier_lt [Nonempty κ] {J B : Matrix κ κ ℂ} (hJ : J.PosDef)
    (hB : B.PosDef) {ζ : ℝ} (hζ : 0 < ζ) {b : Ω → κ → ℂ}
    (hb : ∀ k, MemLp (fun x => b x k) 2 μ) (hgram : gram b μ = J) :
    ∫ x, upperVerifier J B ζ (b x) ∂μ < 1 / ζ + upperPotential J B := by
  have hM : (B + ζ • J).PosDef := hB.add_smul_posDef hJ hζ
  -- split the average into two traces
  have hQint : Integrable (fun x => RCLike.re (star (b x) ⬝ᵥ
      (((B + ζ • J)⁻¹ * J * (B + ζ • J)⁻¹) *ᵥ b x))) μ := (integrable_quadForm hb _).re
  have hXint : Integrable (fun x => RCLike.re (star (b x) ⬝ᵥ ((B + ζ • J)⁻¹ *ᵥ b x))) μ :=
    (integrable_quadForm hb _).re
  have hcyc : ((B + ζ • J)⁻¹ * J * (B + ζ • J)⁻¹ * J).trace
      = (J * (B + ζ • J)⁻¹ * J * (B + ζ • J)⁻¹).trace := by
    rw [Matrix.trace_mul_cycle, ← mul_assoc]
  have hsplit : ∫ x, upperVerifier J B ζ (b x) ∂μ
      = RCLike.re ((J * (B + ζ • J)⁻¹ * J * (B + ζ • J)⁻¹).trace)
          / (upperPotential J B - upperPotential J (B + ζ • J))
        + upperPotential J (B + ζ • J) := by
    simp only [upperVerifier, upperPotential]
    rw [integral_add (hQint.div_const _) hXint, integral_div,
      integral_re_quadForm hb _, integral_re_quadForm hb _, hgram, hcyc,
      Matrix.trace_mul_comm ((B + ζ • J)⁻¹) J]
  -- the numerator is bounded by the gain of the potential, divided by `ζ`
  have hBM : B ≤ B + ζ • J := by
    rw [Matrix.le_iff, add_sub_cancel_left]
    exact hJ.posSemidef.smul hζ.le
  have hXW : (B + ζ • J)⁻¹ ≤ B⁻¹ := hB.inv_le_inv_of_le hM hBM
  have hconjle : J * (B + ζ • J)⁻¹ * J ≤ J * B⁻¹ * J :=
    conjugate_le_conjugate_of_nonneg hXW hJ.posSemidef.nonneg
  have htrle : RCLike.re ((J * (B + ζ • J)⁻¹ * J) * (B + ζ • J)⁻¹).trace
      ≤ RCLike.re ((J * B⁻¹ * J) * (B + ζ • J)⁻¹).trace := by
    have h := (Matrix.le_iff.1 hconjle).re_trace_mul_nonneg hM.inv.posSemidef
    rw [Matrix.sub_mul, Matrix.trace_sub, map_sub] at h
    linarith
  have hE := upperPotential_sub_eq hJ hB hζ
  have hG0 : 0 < RCLike.re ((J * B⁻¹ * J) * (B + ζ • J)⁻¹).trace :=
    (posDef_conj_inv hJ hB).re_trace_mul_pos hM.inv
  have hlt : upperPotential J (B + ζ • J) < upperPotential J B :=
    upperPotential_add_smul_lt hJ hB hζ
  rw [hsplit]
  -- real algebra
  set E := upperPotential J B - upperPotential J (B + ζ • J) with hEdef
  set G := RCLike.re ((J * B⁻¹ * J) * (B + ζ • J)⁻¹).trace with hGdef
  set P := RCLike.re ((J * (B + ζ • J)⁻¹ * J) * (B + ζ • J)⁻¹).trace with hPdef
  have hE0 : 0 < E := by simp only [hEdef]; linarith
  have hPE : P / E ≤ 1 / ζ := by
    calc P / E ≤ G / E := by gcongr
      _ = 1 / ζ := by rw [hE]; field_simp
  have : upperPotential J (B + ζ • J) < upperPotential J B := hlt
  linarith

/-- The lower verifier of a square-integrable family is integrable. -/
theorem integrable_lowerVerifier {A : Matrix ι ι ℂ} {δ : ℝ} {a : Ω → ι → ℂ}
    (ha : ∀ k, MemLp (fun x => a x k) 2 μ) :
    Integrable (fun x => lowerVerifier A δ (a x)) μ := by
  simp only [lowerVerifier]
  exact ((integrable_quadForm ha _).re.div_const _).sub (integrable_quadForm ha _).re

/-- The upper verifier of a square-integrable family is integrable. -/
theorem integrable_upperVerifier {J B : Matrix κ κ ℂ} {ζ : ℝ} {b : Ω → κ → ℂ}
    (hb : ∀ k, MemLp (fun x => b x k) 2 μ) :
    Integrable (fun x => upperVerifier J B ζ (b x)) μ := by
  simp only [upperVerifier]
  exact ((integrable_quadForm hb _).re.div_const _).add (integrable_quadForm hb _).re

/-- **An admissible point exists.**  If the gap opened by the two shifts is large enough,
`1/δ - Φ(A) ≥ 1/ζ + Ψ_J(B)`, then some point passes the test of the two verifiers. -/
theorem exists_admissible_point [Nonempty ι] [Nonempty κ] {A : Matrix ι ι ℂ}
    (hA : A.PosDef) {J B : Matrix κ κ ℂ} (hJ : J.PosDef) (hB : B.PosDef) {δ ζ : ℝ}
    (hδ : 0 < δ) (hδ' : δ < (lowerPotential A)⁻¹) (hζ : 0 < ζ)
    {a : Ω → ι → ℂ} {b : Ω → κ → ℂ}
    (ha : ∀ k, MemLp (fun x => a x k) 2 μ) (hb : ∀ k, MemLp (fun x => b x k) 2 μ)
    (hgrama : gram a μ = 1) (hgramb : gram b μ = J)
    (hgap : 1 / ζ + upperPotential J B ≤ 1 / δ - lowerPotential A) :
    ∃ x, upperVerifier J B ζ (b x) < lowerVerifier A δ (a x) := by
  have hlow := integral_lowerVerifier_gt hA hδ hδ' ha hgrama
  have hup := integral_upperVerifier_lt hJ hB hζ hb hgramb
  refine exists_lt_of_integral_lt (μ := μ) (f := fun x => lowerVerifier A δ (a x))
    (g := fun x => upperVerifier J B ζ (b x)) ?_ ?_ ?_
  · exact integrable_lowerVerifier ha
  · exact integrable_upperVerifier hb
  · linarith

end Discretization
