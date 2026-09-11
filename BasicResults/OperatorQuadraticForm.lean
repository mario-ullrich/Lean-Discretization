/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
import BasicResults.OperatorTrace
import Mathlib.MeasureTheory.Function.L2Space

/-!
# From averages of quadratic forms to traces

This is the operator counterpart of `BasicResults.IntegralQuadraticForm`, and the only place
in the infinite-dimensional development where measure theory meets the trace.

The second family is a single square-integrable map `b : Ω → H` into a Hilbert space, and
its Gram operator is a positive operator `J` of finite trace, tied to `b` by

`Re ⟪u, J u⟫ = ∫ |⟪u, b x⟫|² dμ(x)`   for every `u`.

The identity to be proved is that averaging the quadratic form of a positive operator `Q`
along `b` gives the trace of `J Q`:

`∫ Re ⟪b x, Q (b x)⟫ dμ(x) = Tr (J Q)`   (`ContinuousLinearMap.integral_re_inner_apply`).

Both sides are computed through square roots and Parseval's identity.  Pointwise,
`Re ⟪b, Q b⟫ = ‖√Q b‖² = ∑ₖ |⟪√Q eₖ, b⟫|²`.  Sum and integral may be interchanged because all
terms are nonnegative, and the Gram identity turns the result into
`∑ₖ Re ⟪√Q eₖ, J (√Q eₖ)⟫ = Tr (√Q J √Q)`.  This equals `Tr (J Q)` because both are the
squared Hilbert–Schmidt norm of `√Q √J`, once read through the operator and once through its
adjoint (`ContinuousLinearMap.tsum_norm_sq_adjoint`).

Countability of the index set of the basis enters here for the first time: the interchange of
sum and integral is `MeasureTheory.integral_tsum_of_summable_integral_norm`, which needs a
countable index.
-/

open MeasureTheory
open scoped InnerProductSpace ComplexOrder

namespace ContinuousLinearMap

variable {κ Ω H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [MeasurableSpace Ω] {μ : Measure Ω}

/-! ### The two symmetrizations of `Tr (J Q)` -/

/-- The adjoint of `√Q √J` is `√J √Q`; the square root of any operator is self-adjoint,
because `CFC.sqrt` is nonnegative by construction. -/
private theorem adjoint_sqrt_mul_sqrt (J Q : H →L[ℂ] H) :
    ContinuousLinearMap.adjoint (CFC.sqrt Q * CFC.sqrt J) = CFC.sqrt J * CFC.sqrt Q := by
  rw [← ContinuousLinearMap.star_eq_adjoint, star_mul,
    (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg J)).star_eq,
    (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg Q)).star_eq]

/-- The composition `√Q √J` is Hilbert–Schmidt as soon as `J` has finite trace, because `√J`
is Hilbert–Schmidt and `√Q` is bounded. -/
theorem summable_norm_sq_sqrt_mul_sqrt (e : HilbertBasis κ ℂ H) {J Q : H →L[ℂ] H} (hJ : 0 ≤ J)
    (hsum : Summable fun k => RCLike.re ⟪e k, J (e k)⟫_ℂ) :
    Summable fun k => ‖CFC.sqrt Q (CFC.sqrt J (e k))‖ ^ 2 :=
  summable_norm_sq_comp e (CFC.sqrt Q) ((summable_norm_sq_sqrt_iff e hJ).2 hsum)

/-- **The trace of `J Q`, symmetrized on the other side:**
`Tr (J Q) = ∑ₖ Re ⟪√Q eₖ, J (√Q eₖ)⟫`.

Both this and `ContinuousLinearMap.traceAlong_mul` express the trace as a squared
Hilbert–Schmidt norm of `√Q √J`, the two readings differing by an adjoint.  The averaging
step produces this form; the potential argument uses the form of
`ContinuousLinearMap.traceAlong_mul`. -/
theorem traceAlong_mul_eq_tsum_sqrt (e : HilbertBasis κ ℂ H) {J Q : H →L[ℂ] H} (hJ : 0 ≤ J)
    (hQ : 0 ≤ Q) (hsum : Summable fun k => RCLike.re ⟪e k, J (e k)⟫_ℂ) :
    traceAlong e (J * Q) = ∑' k, RCLike.re ⟪CFC.sqrt Q (e k), J (CFC.sqrt Q (e k))⟫_ℂ := by
  have hcomm := tsum_norm_sq_adjoint e (CFC.sqrt Q * CFC.sqrt J)
    (summable_norm_sq_sqrt_mul_sqrt e hJ hsum)
  rw [adjoint_sqrt_mul_sqrt J Q] at hcomm
  calc traceAlong e (J * Q)
      = ∑' k, RCLike.re ⟪CFC.sqrt J (e k), Q (CFC.sqrt J (e k))⟫_ℂ :=
        traceAlong_mul e hJ hQ hsum
    _ = ∑' k, ‖CFC.sqrt Q (CFC.sqrt J (e k))‖ ^ 2 :=
        tsum_congr fun k => re_inner_apply_eq_norm_sq_sqrt hQ _
    _ = ∑' k, ‖CFC.sqrt J (CFC.sqrt Q (e k))‖ ^ 2 := hcomm.symm
    _ = ∑' k, RCLike.re ⟪CFC.sqrt Q (e k), J (CFC.sqrt Q (e k))⟫_ℂ :=
        tsum_congr fun k => (re_inner_apply_eq_norm_sq_sqrt hJ _).symm

/-! ### Averages along a square-integrable family -/

omit [CompleteSpace H] in
/-- The quadratic form of a bounded operator along a square-integrable family is
integrable. -/
theorem integrable_re_inner_apply {b : Ω → H} (hb : MemLp b 2 μ) (Q : H →L[ℂ] H) :
    Integrable (fun x => RCLike.re ⟪b x, Q (b x)⟫_ℂ) μ := by
  have hcont : Continuous fun y : H => RCLike.re ⟪y, Q y⟫_ℂ :=
    RCLike.continuous_re.comp (continuous_inner.comp (continuous_id.prodMk Q.continuous))
  have hmeas : AEStronglyMeasurable (fun x => RCLike.re ⟪b x, Q (b x)⟫_ℂ) μ :=
    hcont.comp_aestronglyMeasurable hb.aestronglyMeasurable
  refine Integrable.mono' ((hb.norm.integrable_sq).const_mul (‖Q‖)) hmeas ?_
  refine Filter.Eventually.of_forall fun x => ?_
  have h1 : ‖RCLike.re ⟪b x, Q (b x)⟫_ℂ‖ ≤ ‖⟪b x, Q (b x)⟫_ℂ‖ := RCLike.abs_re_le_norm _
  have h2 : ‖⟪b x, Q (b x)⟫_ℂ‖ ≤ ‖b x‖ * ‖Q (b x)‖ := norm_inner_le_norm _ _
  have h3 : ‖Q (b x)‖ ≤ ‖Q‖ * ‖b x‖ := Q.le_opNorm _
  have h4 : (0 : ℝ) ≤ ‖b x‖ := norm_nonneg _
  calc ‖RCLike.re ⟪b x, Q (b x)⟫_ℂ‖ ≤ ‖b x‖ * ‖Q (b x)‖ := h1.trans h2
    _ ≤ ‖b x‖ * (‖Q‖ * ‖b x‖) := by nlinarith
    _ = ‖Q‖ * ‖b x‖ ^ 2 := by ring

omit [CompleteSpace H] in
/-- Each coefficient of the family is square-integrable. -/
theorem integrable_norm_sq_inner {b : Ω → H} (hb : MemLp b 2 μ) (u : H) :
    Integrable (fun x => ‖⟪u, b x⟫_ℂ‖ ^ 2) μ :=
  ((hb.continuousLinearMap_comp (innerSL ℂ u)).norm).integrable_sq

/-- **The average of a quadratic form is a trace.**

For a square-integrable family `b` with Gram operator `J` of finite trace and any positive
bounded operator `Q`,

`∫ Re ⟪b x, Q (b x)⟫ dμ(x) = Tr (J Q)`.

This is the operator form of `Discretization.integral_re_quadForm`. -/
theorem integral_re_inner_apply [Countable κ] (e : HilbertBasis κ ℂ H) {J Q : H →L[ℂ] H}
    (hJ : 0 ≤ J) (hQ : 0 ≤ Q) (hsum : Summable fun k => RCLike.re ⟪e k, J (e k)⟫_ℂ)
    {b : Ω → H} (hb : MemLp b 2 μ)
    (hgram : ∀ u, RCLike.re ⟪u, J u⟫_ℂ = ∫ x, ‖⟪u, b x⟫_ℂ‖ ^ 2 ∂μ) :
    ∫ x, RCLike.re ⟪b x, Q (b x)⟫_ℂ ∂μ = traceAlong e (J * Q) := by
  have hQadj : ContinuousLinearMap.adjoint (CFC.sqrt Q) = CFC.sqrt Q :=
    (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg Q)).star_eq
  -- the coefficients of `√Q b` along the basis
  set g : κ → Ω → ℝ := fun k x => ‖⟪CFC.sqrt Q (e k), b x⟫_ℂ‖ ^ 2 with hg
  have hgint : ∀ k, Integrable (g k) μ := fun k => integrable_norm_sq_inner hb _
  have hgval : ∀ k, ∫ x, g k x ∂μ = RCLike.re ⟪CFC.sqrt Q (e k), J (CFC.sqrt Q (e k))⟫_ℂ :=
    fun k => (hgram _).symm
  have hgsum : Summable fun k => ∫ x, ‖g k x‖ ∂μ := by
    have hterm : ∀ k, ∫ x, ‖g k x‖ ∂μ = ‖CFC.sqrt J (CFC.sqrt Q (e k))‖ ^ 2 := fun k => by
      rw [integral_congr_ae (Filter.Eventually.of_forall fun x =>
          Real.norm_of_nonneg (show (0 : ℝ) ≤ g k x by rw [hg]; positivity)),
        hgval k, re_inner_apply_eq_norm_sq_sqrt hJ]
    have hadj := summable_norm_sq_adjoint_iff e (CFC.sqrt Q * CFC.sqrt J)
    rw [adjoint_sqrt_mul_sqrt J Q] at hadj
    have h1 : Summable fun k => ‖CFC.sqrt J (CFC.sqrt Q (e k))‖ ^ 2 :=
      hadj.2 (summable_norm_sq_sqrt_mul_sqrt e hJ hsum)
    exact h1.congr fun k => (hterm k).symm
  -- pointwise Parseval, then interchange of sum and integral
  have hpoint : ∀ x, RCLike.re ⟪b x, Q (b x)⟫_ℂ = ∑' k, g k x := fun x => by
    rw [re_inner_apply_eq_norm_sq_sqrt hQ (b x),
      ← (e.hasSum_norm_sq_inner (CFC.sqrt Q (b x))).tsum_eq]
    refine tsum_congr fun k => ?_
    rw [hg]
    congr 1
    rw [← hQadj, ContinuousLinearMap.adjoint_inner_left, hQadj]
  calc ∫ x, RCLike.re ⟪b x, Q (b x)⟫_ℂ ∂μ = ∫ x, ∑' k, g k x ∂μ :=
        integral_congr_ae (Filter.Eventually.of_forall hpoint)
    _ = ∑' k, ∫ x, g k x ∂μ := (integral_tsum_of_summable_integral_norm hgint hgsum).symm
    _ = ∑' k, RCLike.re ⟪CFC.sqrt Q (e k), J (CFC.sqrt Q (e k))⟫_ℂ := tsum_congr hgval
    _ = traceAlong e (J * Q) := (traceAlong_mul_eq_tsum_sqrt e hJ hQ hsum).symm

end ContinuousLinearMap
