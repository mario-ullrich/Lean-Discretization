/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import BasicResults.Operator.QuadraticForm
public import BasicResults.Operator.GramOperator
public import Discretization.Averages
public import Discretization.Infinite.Barrier

/-!
# The upper verifier passes the test on average

The operator counterpart of the upper half of `Discretization.Averages`.  For a
square-integrable family `b` with injective Gram operator `J = ∫ b(x) b(x)* dμ(x)`,

`∫ U_B^ζ(b x) dμ(x) < 1/ζ + Ψ_J(B)`   (`Discretization.Infinite.integral_upperVerifier_lt`),

so a point at which the upper verifier is small exists as soon as the lower verifier is
large on average.  Since the first family stays finite, the lower verifier is a matrix
quantity and the upper one an operator quantity; both are real functions on `Ω`, and the
conclusion is `Discretization.UpperBarrier.exists_admissible_point` for the operator
upper barrier of `Discretization.Infinite.UpperBarrier`.  This file also proves that on a
separable space the Gram operator is positive and of finite trace
(`Discretization.Infinite.isFiniteTracePos_of_integral_rankOne`), with
`∫ ‖b‖² dμ = Tr J` (`Discretization.Infinite.integral_norm_sq_eq_trace`, and along any
countable Hilbert basis `Discretization.Infinite.integral_norm_sq_eq_traceAlong`).

Two ingredients do the work.  The average of a quadratic form is a trace
(`ContinuousLinearMap.integral_re_inner_apply`).  With `W = B⁻¹` and `X = (B + ζ • J)⁻¹` it turns
the average of the verifier into `Tr (J X J X) / E + Ψ_J(B + ζ • J)`, where
`E = ζ Tr (J W J X)` is the gain of the potential.  Then `X ≤ W` bounds the numerator by
`E/ζ`.
-/

@[expose] public section

open MeasureTheory
open scoped InnerProductSpace ComplexOrder
open InnerProductSpace
open ContinuousLinearMap

namespace Discretization

namespace Infinite

variable {κ Ω H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [MeasurableSpace Ω] {μ : Measure Ω} {J : H →L[ℂ] H}

/-- The Hilbert basis chosen once and for all, along which traces are computed. -/
local notation "e₀" => HilbertBasis.chosen H

/-! ### Monotonicity of the trace of a product -/

/-- **The trace of a product is monotone in the factor of finite trace:** `P₁ ≼ P₂` implies
`Tr (P₁ Q) ≤ Tr (P₂ Q)` for positive `Q`.

The difference `P₂ - P₁` is positive with summable trace, so the trace of its product with
`Q` is nonnegative. -/
theorem traceAlong_mul_le_of_le {e : HilbertBasis κ ℂ H} {P₁ P₂ Q : H →L[ℂ] H}
    (h₁ : Summable fun k => RCLike.re ⟪e k, P₁ (e k)⟫_ℂ)
    (h₂ : Summable fun k => RCLike.re ⟪e k, P₂ (e k)⟫_ℂ) (hP₁ : 0 ≤ P₁) (hle : P₁ ≤ P₂)
    (hQ : 0 ≤ Q) : traceAlong e (P₁ * Q) ≤ traceAlong e (P₂ * Q) := by
  have hdiff : (0 : H →L[ℂ] H) ≤ P₂ - P₁ := sub_nonneg.2 hle
  have hdsum : Summable fun k => RCLike.re ⟪e k, (P₂ - P₁) (e k)⟫_ℂ := by
    refine (h₂.sub h₁).congr fun k => ?_
    rw [show (P₂ - P₁) (e k) = P₂ (e k) - P₁ (e k) from rfl, inner_sub_right, map_sub]
  have hnn : 0 ≤ traceAlong e ((P₂ - P₁) * Q) := traceAlong_mul_nonneg e hdiff hQ hdsum
  have hsplit : P₂ * Q = P₁ * Q + (P₂ - P₁) * Q := by rw [sub_mul]; abel
  have hs₁ : Summable fun k => RCLike.re ⟪e k, (P₁ * Q) (e k)⟫_ℂ :=
    summable_re_inner_apply_mul e hP₁ hQ h₁
  have hs₂ : Summable fun k => RCLike.re ⟪e k, ((P₂ - P₁) * Q) (e k)⟫_ℂ :=
    summable_re_inner_apply_mul e hdiff hQ hdsum
  rw [hsplit, traceAlong_add e hs₁ hs₂]
  linarith

/-! ### The Gram operator -/

/-- The quadratic form of the Gram operator `J = ∫ b(x) b(x)* dμ(x)`:
`⟪u, J u⟫ = ∫ |⟪u, b(x)⟫|² dμ(x)` (`ContinuousLinearMap.inner_integral_rankOne_self`). -/
theorem inner_eq_integral_of_integral_rankOne {b : Ω → H} (hb : MemLp b 2 μ)
    (hJ : ∫ x, rankOne ℂ (b x) (b x) ∂μ = J) (u : H) :
    ⟪u, J u⟫_ℂ = ((∫ x, ‖⟪u, b x⟫_ℂ‖ ^ 2 ∂μ : ℝ) : ℂ) := by
  rw [← hJ]
  exact inner_integral_rankOne_self hb u

/-- **On a separable space the Gram operator is positive and of finite trace**, and so, once
injective, satisfies `IsFiniteTracePos`: positivity is that of its quadratic form
(`ContinuousLinearMap.nonneg_of_inner_eq_integral`); along the chosen basis, which is
countable, the finite trace `∑ₖ Re ⟪eₖ, J eₖ⟫ = ∫ ‖b‖² dμ` is Tonelli and Parseval
(`ContinuousLinearMap.summable_re_inner_of_gram`). -/
theorem isFiniteTracePos_of_integral_rankOne [TopologicalSpace.SeparableSpace H]
    {b : Ω → H} (hb : MemLp b 2 μ) (hJ : ∫ x, rankOne ℂ (b x) (b x) ∂μ = J)
    (hinj : ∀ v, J v = 0 → v = 0) : IsFiniteTracePos J :=
  ⟨nonneg_of_inner_eq_integral (inner_eq_integral_of_integral_rankOne hb hJ),
    summable_re_inner_of_gram e₀ hb
      (re_inner_eq_integral (inner_eq_integral_of_integral_rankOne hb hJ)), hinj⟩

/-! ### The average of the upper verifier -/

/-- The upper verifier of a square-integrable family is integrable. -/
theorem integrable_upperVerifier {b : Ω → H} (hb : MemLp b 2 μ) (J B : H →L[ℂ] H) (ζ : ℝ) :
    Integrable (fun x => upperVerifier J B ζ (b x)) μ := by
  simp only [upperVerifier]
  exact ((integrable_re_inner_apply hb _).div_const _).add (integrable_re_inner_apply hb _)

/-- **The average of the upper verifier stays below `1/ζ + Ψ_J(B)`.**

Writing `W = B⁻¹` and `X = (B + ζ • J)⁻¹`, the average equals
`Tr (J X J X) / E + Ψ_J(B + ζ • J)` with `E = ζ · Tr (J W J X)`.  Since `X ≼ W` the
numerator is at most `Tr (J W J X) = E/ζ`, so the first summand is at most `1/ζ`, and the
second is strictly smaller than `Ψ_J(B)`. -/
theorem integral_upperVerifier_lt [Nontrivial H] [TopologicalSpace.SeparableSpace H]
    {b : Ω → H} (hb : MemLp b 2 μ)
    (hJb : ∫ x, rankOne ℂ (b x) (b x) ∂μ = J) (hinj : ∀ v, J v = 0 → v = 0)
    {B : H →L[ℂ] H} (hB : IsStrictlyPositive B) {ζ : ℝ} (hζ : 0 < ζ) :
    ∫ x, upperVerifier J B ζ (b x) ∂μ < 1 / ζ + upperPotential J B := by
  have hJ := isFiniteTracePos_of_integral_rankOne hb hJb hinj
  have hgram := re_inner_eq_integral (inner_eq_integral_of_integral_rankOne hb hJb)
  have hM : IsStrictlyPositive (B + ζ • J) := isStrictlyPositive_add_smul hJ.nonneg hB hζ.le
  have hX : IsStrictlyPositive (Ring.inverse (B + ζ • J)) := hM.ringInverse
  have hW : IsStrictlyPositive (Ring.inverse B) := hB.ringInverse
  have hXW : Ring.inverse (B + ζ • J) ≤ Ring.inverse B :=
    inverse_add_smul_le hJ.nonneg hB hζ.le
  have hconjX : (0 : H →L[ℂ] H)
      ≤ Ring.inverse (B + ζ • J) * J * Ring.inverse (B + ζ • J) :=
    nonneg_conj hX.nonneg hJ.nonneg
  -- the average splits into two traces
  have hint₁ : Integrable (fun x => RCLike.re ⟪b x,
      (Ring.inverse (B + ζ • J) * J * Ring.inverse (B + ζ • J)) (b x)⟫_ℂ) μ :=
    integrable_re_inner_apply hb _
  have hint₂ : Integrable
      (fun x => RCLike.re ⟪b x, Ring.inverse (B + ζ • J) (b x)⟫_ℂ) μ :=
    integrable_re_inner_apply hb _
  have hsplit : ∫ x, upperVerifier J B ζ (b x) ∂μ
      = traceAlong e₀ (J * (Ring.inverse (B + ζ • J) * J * Ring.inverse (B + ζ • J)))
          / (upperPotential J B - upperPotential J (B + ζ • J))
        + upperPotential J (B + ζ • J) := by
    simp only [upperVerifier, upperPotential]
    rw [integral_add (hint₁.div_const _) hint₂, integral_div,
      integral_re_inner_apply e₀ hJ.nonneg hconjX hJ.summableTrace hb hgram,
      integral_re_inner_apply e₀ hJ.nonneg hX.nonneg hJ.summableTrace hb hgram]
  -- the numerator is at most the gain of the potential, divided by `ζ`
  have hassoc : J * (Ring.inverse (B + ζ • J) * J * Ring.inverse (B + ζ • J))
      = (J * Ring.inverse (B + ζ • J) * J) * Ring.inverse (B + ζ • J) := by
    simp only [mul_assoc]
  have hle : traceAlong e₀ (J * (Ring.inverse (B + ζ • J) * J * Ring.inverse (B + ζ • J)))
      ≤ traceAlong e₀ ((J * Ring.inverse B * J) * Ring.inverse (B + ζ • J)) := by
    rw [hassoc]
    exact traceAlong_mul_le_of_le (hJ.conj hX).summableTrace (hJ.conj hW).summableTrace
      (hJ.conj hX).nonneg (conjugate_le_conjugate_of_nonneg hXW hJ.nonneg) hX.nonneg
  have hE := upperPotential_sub_eq hJ hB hζ.le
  have hlt : upperPotential J (B + ζ • J) < upperPotential J B :=
    upperPotential_add_smul_lt hJ hB hζ
  rw [hsplit]
  -- real algebra
  set E := upperPotential J B - upperPotential J (B + ζ • J) with hEdef
  set G := traceAlong e₀ ((J * Ring.inverse B * J) * Ring.inverse (B + ζ • J)) with hGdef
  set P := traceAlong e₀ (J * (Ring.inverse (B + ζ • J) * J * Ring.inverse (B + ζ • J)))
    with hPdef
  have hE0 : 0 < E := by simp only [hEdef]; linarith
  have hPE : P / E ≤ 1 / ζ := by
    rw [div_le_iff₀ hE0, hE, show 1 / ζ * (ζ * G) = G by field_simp]
    exact hle
  linarith

/-! ### The trace as an average -/

/-- **The trace of the Gram operator is the average of `‖b‖²`**, `∫ ‖b x‖² dμ(x) = Tr J`.

This is `ContinuousLinearMap.integral_re_inner_apply` with `Q = 1`, and it is the form in
which the finite-trace assumption of the paper is used here.  Injectivity is not needed. -/
theorem integral_norm_sq_eq_traceAlong [Countable κ] (e : HilbertBasis κ ℂ H) {b : Ω → H}
    (hb : MemLp b 2 μ) (hJ : ∫ x, rankOne ℂ (b x) (b x) ∂μ = J) :
    ∫ x, ‖b x‖ ^ 2 ∂μ = traceAlong e J := by
  have hq := inner_eq_integral_of_integral_rankOne hb hJ
  have hgramb := re_inner_eq_integral hq
  have h1 := integral_re_inner_apply e (nonneg_of_inner_eq_integral hq) zero_le_one
    (summable_re_inner_of_gram e hb hgramb) hb hgramb
  rw [mul_one] at h1
  rw [← h1]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  show ‖b x‖ ^ 2 = RCLike.re ⟪b x, b x⟫_ℂ
  exact (inner_self_eq_norm_sq (b x)).symm

/-- **The trace of the Gram operator is the average of `‖b‖²`**, `∫ ‖b x‖² dμ(x) = Tr J`, on a
separable space: `Discretization.Infinite.integral_norm_sq_eq_traceAlong` along the chosen
basis, which is countable. -/
theorem integral_norm_sq_eq_trace [TopologicalSpace.SeparableSpace H] {b : Ω → H}
    (hb : MemLp b 2 μ) (hJ : ∫ x, rankOne ℂ (b x) (b x) ∂μ = J) :
    ∫ x, ‖b x‖ ^ 2 ∂μ = trace J :=
  integral_norm_sq_eq_traceAlong e₀ hb hJ

end Infinite

end Discretization
