/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
import Discretization.Infinite.Potentials

/-!
# A bound on the upper potential is a bound on the operator

The whole point of the potential is that controlling it controls the operator:

`Ψ_J(B)⁻¹ • J ≼ B`   (`Discretization.Infinite.inv_upperPotential_smul_le`),

the operator analogue of `Matrix.PosDef.inv_re_trace_mul_smul_le`.  This is what turns the
final bound on the potential into the upper frame bound of the theorem.

The proof conjugates by the square root `S = √B`.  The operator `S⁻¹ J S⁻¹` is positive, and
its trace is again `Ψ_J(B)`: expanding `Tr (J B⁻¹)` through the square root of `B⁻¹`, which
is `S⁻¹` by `CFC.sqrt_ringInverse`, gives exactly `∑ₖ Re ⟪S⁻¹ eₖ, J (S⁻¹ eₖ)⟫`.  Hence the
crude bound `Discretization.le_traceAlong_smul_one` applies to it, and conjugating back by
`S` turns `S⁻¹ J S⁻¹ ≼ Ψ_J(B) • 1` into `J ≼ Ψ_J(B) • B`.
-/

open scoped InnerProductSpace ComplexOrder

namespace Discretization

namespace Infinite

variable {κ H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {e : HilbertBasis κ ℂ H} {J : H →L[ℂ] H}

/-- Moving a self-adjoint operator across the inner product: `⟪x, S J S x⟫ = ⟪S x, J (S x)⟫`. -/
private theorem re_inner_conj_apply {S : H →L[ℂ] H} (hS : IsSelfAdjoint S) (T : H →L[ℂ] H)
    (x : H) : RCLike.re ⟪x, (S * T * S) x⟫_ℂ = RCLike.re ⟪S x, T (S x)⟫_ℂ := by
  have hSadj : ContinuousLinearMap.adjoint S = S := hS.star_eq
  have h := ContinuousLinearMap.adjoint_inner_right S x (T (S x))
  rw [hSadj] at h
  rw [show (S * T * S) x = S (T (S x)) from rfl, h]

/-- **The conjugate of `J` by the inverse square root of `B` has the upper potential as its
trace:** `Tr (B^{-1/2} J B^{-1/2}) = Ψ_J(B)`. -/
theorem traceAlong_conj_inv_sqrt (hJ : IsFiniteTracePos e J) {B : H →L[ℂ] H}
    (hB : IsStrictlyPositive B) :
    traceAlong e (Ring.inverse (CFC.sqrt B) * J * Ring.inverse (CFC.sqrt B))
      = upperPotential e J B := by
  have hBinv : IsStrictlyPositive (Ring.inverse B) := isStrictlyPositive_inverse hB
  have hsqrtinv : CFC.sqrt (Ring.inverse B) = Ring.inverse (CFC.sqrt B) := CFC.sqrt_ringInverse
  have hsa : IsSelfAdjoint (Ring.inverse (CFC.sqrt B)) := by
    rw [← hsqrtinv]
    exact IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg _)
  rw [upperPotential, traceAlong_mul_eq_tsum_sqrt e hJ.nonneg hBinv.nonneg hJ.summableTrace,
    hsqrtinv, traceAlong]
  exact tsum_congr fun k => re_inner_conj_apply hsa J (e k)

/-- The conjugate `B^{-1/2} J B^{-1/2}` is positive and its trace converges. -/
theorem summable_trace_conj_inv_sqrt (hJ : IsFiniteTracePos e J) {B : H →L[ℂ] H}
    (hB : IsStrictlyPositive B) :
    Summable fun k => RCLike.re ⟪e k,
      (Ring.inverse (CFC.sqrt B) * J * Ring.inverse (CFC.sqrt B)) (e k)⟫_ℂ := by
  have hBinv : IsStrictlyPositive (Ring.inverse B) := isStrictlyPositive_inverse hB
  have hsqrtinv : CFC.sqrt (Ring.inverse B) = Ring.inverse (CFC.sqrt B) := CFC.sqrt_ringInverse
  have hsa : IsSelfAdjoint (Ring.inverse (CFC.sqrt B)) := by
    rw [← hsqrtinv]
    exact IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg _)
  have hterm : ∀ k, RCLike.re ⟪e k,
      (Ring.inverse (CFC.sqrt B) * J * Ring.inverse (CFC.sqrt B)) (e k)⟫_ℂ
      = ‖CFC.sqrt J (Ring.inverse (CFC.sqrt B) (e k))‖ ^ 2 := fun k => by
    rw [re_inner_conj_apply hsa J (e k), re_inner_apply_eq_norm_sq_sqrt hJ.nonneg]
  refine Summable.congr ?_ fun k => (hterm k).symm
  -- `√J S⁻¹` is Hilbert–Schmidt because its adjoint `S⁻¹ √J` is
  have hadj : ContinuousLinearMap.adjoint
      (CFC.sqrt J * Ring.inverse (CFC.sqrt B)) = Ring.inverse (CFC.sqrt B) * CFC.sqrt J := by
    rw [← ContinuousLinearMap.star_eq_adjoint, star_mul, hsa.star_eq,
      (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg J)).star_eq]
  have hother : Summable fun k => ‖ContinuousLinearMap.adjoint
      (CFC.sqrt J * Ring.inverse (CFC.sqrt B)) (e k)‖ ^ 2 := by
    simp only [hadj]
    have hS : Summable fun k => ‖CFC.sqrt J (e k)‖ ^ 2 :=
      (summable_norm_sq_sqrt_iff e hJ.nonneg).2 hJ.summableTrace
    refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_)
      (hS.mul_left (‖Ring.inverse (CFC.sqrt B)‖ ^ 2))
    have h := (Ring.inverse (CFC.sqrt B)).le_opNorm (CFC.sqrt J (e k))
    have h0 : (0 : ℝ) ≤ ‖Ring.inverse (CFC.sqrt B) (CFC.sqrt J (e k))‖ := norm_nonneg _
    have h1 : (0 : ℝ) ≤ ‖Ring.inverse (CFC.sqrt B)‖ * ‖CFC.sqrt J (e k)‖ := by positivity
    calc ‖(Ring.inverse (CFC.sqrt B) * CFC.sqrt J) (e k)‖ ^ 2
        = ‖Ring.inverse (CFC.sqrt B) (CFC.sqrt J (e k))‖ ^ 2 := rfl
      _ ≤ (‖Ring.inverse (CFC.sqrt B)‖ * ‖CFC.sqrt J (e k)‖) ^ 2 := by nlinarith
      _ = ‖Ring.inverse (CFC.sqrt B)‖ ^ 2 * ‖CFC.sqrt J (e k)‖ ^ 2 := by ring
  exact (summable_norm_sq_adjoint_iff e (CFC.sqrt J * Ring.inverse (CFC.sqrt B))).1 hother

/-- **A bound on the upper potential is a bound on the operator:** `Ψ_J(B)⁻¹ • J ≼ B`.

Equivalently `J ≼ Ψ_J(B) • B`: a small upper potential forces `B` to be large in the
directions where `J` is large.  This is the operator form of
`Matrix.PosDef.inv_re_trace_mul_smul_le`. -/
theorem inv_upperPotential_smul_le [Nonempty κ] (hJ : IsFiniteTracePos e J) {B : H →L[ℂ] H}
    (hB : IsStrictlyPositive B) : (upperPotential e J B)⁻¹ • J ≤ B := by
  have hΨ : 0 < upperPotential e J B := upperPotential_pos hJ hB
  have hS0 : (0 : H →L[ℂ] H) ≤ CFC.sqrt B := CFC.sqrt_nonneg B
  have hSS : CFC.sqrt B * CFC.sqrt B = B := CFC.sqrt_mul_sqrt_self B hB.nonneg
  have hSunit : IsUnit (CFC.sqrt B) := (CFC.isUnit_sqrt_iff B hB.nonneg).2 hB.isUnit
  have hSinv : CFC.sqrt B * Ring.inverse (CFC.sqrt B) = 1 :=
    Ring.mul_inverse_cancel _ hSunit
  have hSinv' : Ring.inverse (CFC.sqrt B) * CFC.sqrt B = 1 :=
    Ring.inverse_mul_cancel _ hSunit
  -- the conjugated operator is positive, with trace the potential
  have hPpos : (0 : H →L[ℂ] H)
      ≤ Ring.inverse (CFC.sqrt B) * J * Ring.inverse (CFC.sqrt B) :=
    nonneg_conj (isStrictlyPositive_inverse ⟨hS0, hSunit⟩).nonneg hJ.nonneg
  have hP : Ring.inverse (CFC.sqrt B) * J * Ring.inverse (CFC.sqrt B)
      ≤ (upperPotential e J B) • (1 : H →L[ℂ] H) := by
    have h := le_traceAlong_smul_one e hPpos (summable_trace_conj_inv_sqrt hJ hB)
    rwa [traceAlong_conj_inv_sqrt hJ hB] at h
  -- conjugating back by `√B`
  have hconj := conjugate_le_conjugate_of_nonneg hP hS0
  have hlhs : CFC.sqrt B * (Ring.inverse (CFC.sqrt B) * J * Ring.inverse (CFC.sqrt B))
      * CFC.sqrt B = J := by
    calc CFC.sqrt B * (Ring.inverse (CFC.sqrt B) * J * Ring.inverse (CFC.sqrt B)) * CFC.sqrt B
        = (CFC.sqrt B * Ring.inverse (CFC.sqrt B)) * J
            * (Ring.inverse (CFC.sqrt B) * CFC.sqrt B) := by
          simp only [mul_assoc]
      _ = J := by rw [hSinv, hSinv', one_mul, mul_one]
  have hrhs : CFC.sqrt B * ((upperPotential e J B) • (1 : H →L[ℂ] H)) * CFC.sqrt B
      = (upperPotential e J B) • B := by
    rw [mul_smul_comm, smul_mul_assoc, mul_one, hSS]
  rw [hlhs, hrhs] at hconj
  -- and dividing by the potential
  have h := smul_le_smul_of_nonneg_left hconj (inv_nonneg.2 hΨ.le)
  rwa [smul_smul, inv_mul_cancel₀ hΨ.ne', one_smul] at h

end Infinite

end Discretization
