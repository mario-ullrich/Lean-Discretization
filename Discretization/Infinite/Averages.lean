/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
import Discretization.Averages
import Discretization.Infinite.Barrier

/-!
# The upper verifier passes the test on average

The operator counterpart of the upper half of `Discretization.Averages`.  For a
square-integrable family `b` whose Gram operator is `J`,

`∫ U_B^ζ(b x) dμ(x) < 1/ζ + Ψ_J(B)`   (`Discretization.Infinite.integral_upperVerifier_lt`),

so a point at which the upper verifier is small exists as soon as the lower verifier is
large on average.  Since the first family stays finite, the lower verifier is a matrix
quantity and the upper one an operator quantity; both are real functions on `Ω`, and the
conclusion is `Discretization.Infinite.exists_admissible_point`.

Two ingredients do the work.  The average of a quadratic form is a trace
(`Discretization.integral_re_inner_apply`).  With `W = B⁻¹` and `X = (B + ζ • J)⁻¹` it turns
the average of the verifier into `Tr (J X J X) / E + Ψ_J(B + ζ • J)`, where
`E = ζ Tr (J W J X)` is the gain of the potential.  Then `X ≤ W` bounds the numerator by
`E/ζ`.
-/

open MeasureTheory
open scoped InnerProductSpace ComplexOrder
open InnerProductSpace

namespace Discretization

namespace Infinite

variable {κ Ω H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [MeasurableSpace Ω] {μ : Measure Ω} {e : HilbertBasis κ ℂ H} {J : H →L[ℂ] H}

/-! ### Monotonicity of the trace of a product -/

/-- **The trace of a product is monotone in the factor of finite trace:** `P₁ ≼ P₂` implies
`Tr (P₁ Q) ≤ Tr (P₂ Q)` for positive `Q`.

The difference `P₂ - P₁` is positive with summable trace, so the trace of its product with
`Q` is nonnegative. -/
theorem traceAlong_mul_le_of_le {P₁ P₂ Q : H →L[ℂ] H}
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

/-! ### The average of the upper verifier -/

omit [CompleteSpace H] in
/-- The upper verifier of a square-integrable family is integrable. -/
theorem integrable_upperVerifier {b : Ω → H} (hb : MemLp b 2 μ) (J B : H →L[ℂ] H) (ζ : ℝ) :
    Integrable (fun x => upperVerifier e J B ζ (b x)) μ := by
  simp only [upperVerifier]
  exact ((integrable_re_inner_apply hb _).div_const _).add (integrable_re_inner_apply hb _)

/-- **The average of the upper verifier stays below `1/ζ + Ψ_J(B)`.**

Writing `W = B⁻¹` and `X = (B + ζ • J)⁻¹`, the average equals
`Tr (J X J X) / E + Ψ_J(B + ζ • J)` with `E = ζ · Tr (J W J X)`.  Since `X ≼ W` the
numerator is at most `Tr (J W J X) = E/ζ`, so the first summand is at most `1/ζ`, and the
second is strictly smaller than `Ψ_J(B)`. -/
theorem integral_upperVerifier_lt [Nonempty κ] [Countable κ] (hJ : IsFiniteTracePos e J)
    {B : H →L[ℂ] H} (hB : IsStrictlyPositive B) {ζ : ℝ} (hζ : 0 < ζ) {b : Ω → H}
    (hb : MemLp b 2 μ)
    (hgram : ∀ u, RCLike.re ⟪u, J u⟫_ℂ = ∫ x, ‖⟪u, b x⟫_ℂ‖ ^ 2 ∂μ) :
    ∫ x, upperVerifier e J B ζ (b x) ∂μ < 1 / ζ + upperPotential e J B := by
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
  have hsplit : ∫ x, upperVerifier e J B ζ (b x) ∂μ
      = traceAlong e (J * (Ring.inverse (B + ζ • J) * J * Ring.inverse (B + ζ • J)))
          / (upperPotential e J B - upperPotential e J (B + ζ • J))
        + upperPotential e J (B + ζ • J) := by
    simp only [upperVerifier, upperPotential]
    rw [integral_add (hint₁.div_const _) hint₂, integral_div,
      integral_re_inner_apply e hJ.nonneg hconjX hJ.summableTrace hb hgram,
      integral_re_inner_apply e hJ.nonneg hX.nonneg hJ.summableTrace hb hgram]
  -- the numerator is at most the gain of the potential, divided by `ζ`
  have hassoc : J * (Ring.inverse (B + ζ • J) * J * Ring.inverse (B + ζ • J))
      = (J * Ring.inverse (B + ζ • J) * J) * Ring.inverse (B + ζ • J) := by
    simp only [mul_assoc]
  have hle : traceAlong e (J * (Ring.inverse (B + ζ • J) * J * Ring.inverse (B + ζ • J)))
      ≤ traceAlong e ((J * Ring.inverse B * J) * Ring.inverse (B + ζ • J)) := by
    rw [hassoc]
    exact traceAlong_mul_le_of_le (hJ.conj hX).summableTrace (hJ.conj hW).summableTrace
      (hJ.conj hX).nonneg (conjugate_le_conjugate_of_nonneg hXW hJ.nonneg) hX.nonneg
  have hE := upperPotential_sub_eq hJ hB hζ.le
  have hlt : upperPotential e J (B + ζ • J) < upperPotential e J B :=
    upperPotential_add_smul_lt hJ hB hζ
  rw [hsplit]
  -- real algebra
  set E := upperPotential e J B - upperPotential e J (B + ζ • J) with hEdef
  set G := traceAlong e ((J * Ring.inverse B * J) * Ring.inverse (B + ζ • J)) with hGdef
  set P := traceAlong e (J * (Ring.inverse (B + ζ • J) * J * Ring.inverse (B + ζ • J)))
    with hPdef
  have hE0 : 0 < E := by simp only [hEdef]; linarith
  have hPE : P / E ≤ 1 / ζ := by
    rw [div_le_iff₀ hE0, hE, show 1 / ζ * (ζ * G) = G by field_simp]
    exact hle
  linarith

/-! ### An admissible point exists -/

/-- **An admissible point exists.**  If the gap opened by the two shifts is large enough,
`1/δ - Φ(A) ≥ 1/ζ + Ψ_J(B)`, then some point passes the test of both verifiers, the lower
one for the finite first family and the upper one for the operator second family. -/
theorem exists_admissible_point {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    [Nonempty κ] [Countable κ] {A : Matrix ι ι ℂ} (hA : A.PosDef) {δ : ℝ} (hδ : 0 < δ)
    (hδ' : δ < (lowerPotential A)⁻¹) {a : Ω → ι → ℂ}
    (ha : ∀ k, MemLp (fun x => a x k) 2 μ) (hgrama : gram a μ = 1)
    (hJ : IsFiniteTracePos e J) {B : H →L[ℂ] H} (hB : IsStrictlyPositive B) {ζ : ℝ}
    (hζ : 0 < ζ) {b : Ω → H} (hb : MemLp b 2 μ)
    (hgramb : ∀ u, RCLike.re ⟪u, J u⟫_ℂ = ∫ x, ‖⟪u, b x⟫_ℂ‖ ^ 2 ∂μ)
    (hgap : 1 / ζ + upperPotential e J B ≤ 1 / δ - lowerPotential A) :
    ∃ x, upperVerifier e J B ζ (b x) < lowerVerifier A δ (a x) := by
  have hlow := integral_lowerVerifier_gt hA hδ hδ' ha hgrama
  have hup := integral_upperVerifier_lt hJ hB hζ hb hgramb
  refine exists_lt_of_integral_lt (μ := μ) (f := fun x => lowerVerifier A δ (a x))
    (g := fun x => upperVerifier e J B ζ (b x)) (integrable_lowerVerifier ha)
    (integrable_upperVerifier hb J B ζ) ?_
  linarith

end Infinite

end Discretization
