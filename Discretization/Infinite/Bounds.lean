/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
import BasicResults.OperatorQuadraticForm
import BasicResults.SqrtConjugation
import Discretization.Infinite.Potentials

/-!
# A bound on the upper potential is a bound on the operator

The whole point of the potential is that controlling it controls the operator:

`Ψ_J(B)⁻¹ • J ≼ B`   (`Discretization.Infinite.inv_upperPotential_smul_le`),

the operator analogue of `Matrix.PosDef.inv_re_trace_mul_smul_le`.  This is what turns the
final bound on the potential into the upper frame bound of the theorem.

The proof conjugates by the square root `S = √B`.  The operator `S⁻¹ J S⁻¹` is positive, and
its trace is again `Ψ_J(B)`: the square root of `B⁻¹` is `S⁻¹` (`CFC.sqrt_ringInverse`), so
`Tr (J B⁻¹)` expands to `∑ₖ Re ⟪S⁻¹ eₖ, J (S⁻¹ eₖ)⟫`.  Hence the bound
`ContinuousLinearMap.le_traceAlong_smul_one` gives `S⁻¹ J S⁻¹ ≼ Ψ_J(B) • 1`, and conjugating back
by `S` turns this into `J ≼ Ψ_J(B) • B`.
-/

open scoped InnerProductSpace ComplexOrder
open ContinuousLinearMap

namespace Discretization

namespace Infinite

variable {κ H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {e : HilbertBasis κ ℂ H} {J : H →L[ℂ] H}

/-- **The conjugate of `J` by the inverse square root of `B` has the upper potential as its
trace:** `Tr (B^{-1/2} J B^{-1/2}) = Ψ_J(B)`. -/
theorem traceAlong_conj_inv_sqrt (hJ : IsFiniteTracePos e J) {B : H →L[ℂ] H}
    (hB : IsStrictlyPositive B) :
    traceAlong e (Ring.inverse (CFC.sqrt B) * J * Ring.inverse (CFC.sqrt B))
      = upperPotential e J B := by
  have hBinv : IsStrictlyPositive (Ring.inverse B) := hB.ringInverse
  have hsqrtinv : CFC.sqrt (Ring.inverse B) = Ring.inverse (CFC.sqrt B) := CFC.sqrt_ringInverse
  have hsa : IsSelfAdjoint (Ring.inverse (CFC.sqrt B)) :=
    (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg B)).ringInverse
  rw [upperPotential, traceAlong_mul_eq_tsum_sqrt e hJ.nonneg hBinv.nonneg hJ.summableTrace,
    hsqrtinv, traceAlong]
  exact tsum_congr fun k => re_inner_conj_apply hsa J (e k)

/-- The trace of the conjugate `B^{-1/2} J B^{-1/2}` converges.  No hypothesis on `B` is
needed: whatever `B` is, `B^{-1/2}` is a bounded operator, and composing with a bounded
operator preserves the Hilbert–Schmidt property. -/
theorem summable_trace_conj_inv_sqrt (hJ : IsFiniteTracePos e J) (B : H →L[ℂ] H) :
    Summable fun k => RCLike.re ⟪e k,
      (Ring.inverse (CFC.sqrt B) * J * Ring.inverse (CFC.sqrt B)) (e k)⟫_ℂ := by
  have hsa : IsSelfAdjoint (Ring.inverse (CFC.sqrt B)) :=
    (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg B)).ringInverse
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
    exact summable_norm_sq_comp e (Ring.inverse (CFC.sqrt B))
      ((summable_norm_sq_sqrt_iff e hJ.nonneg).2 hJ.summableTrace)
  exact (summable_norm_sq_adjoint_iff e (CFC.sqrt J * Ring.inverse (CFC.sqrt B))).1 hother

/-- **A bound on the upper potential is a bound on the operator:** `Ψ_J(B)⁻¹ • J ≼ B`.

Equivalently `J ≼ Ψ_J(B) • B`: a small upper potential forces `B` to be large in the
directions where `J` is large.  This is the operator form of
`Matrix.PosDef.inv_re_trace_mul_smul_le`. -/
theorem inv_upperPotential_smul_le [Nonempty κ] (hJ : IsFiniteTracePos e J) {B : H →L[ℂ] H}
    (hB : IsStrictlyPositive B) : (upperPotential e J B)⁻¹ • J ≤ B := by
  have hΨ : 0 < upperPotential e J B := upperPotential_pos hJ hB
  have hS0 : (0 : H →L[ℂ] H) ≤ CFC.sqrt B := CFC.sqrt_nonneg B
  have hSunit : IsUnit (CFC.sqrt B) := (CFC.isUnit_sqrt_iff B hB.nonneg).2 hB.isUnit
  -- the conjugated operator is positive, with trace the potential
  have hPpos : (0 : H →L[ℂ] H)
      ≤ Ring.inverse (CFC.sqrt B) * J * Ring.inverse (CFC.sqrt B) :=
    nonneg_conj (IsStrictlyPositive.ringInverse ⟨hS0, hSunit⟩).nonneg hJ.nonneg
  have hP : Ring.inverse (CFC.sqrt B) * J * Ring.inverse (CFC.sqrt B)
      ≤ (upperPotential e J B) • (1 : H →L[ℂ] H) := by
    have h := le_traceAlong_smul_one e hPpos (summable_trace_conj_inv_sqrt hJ B)
    rwa [traceAlong_conj_inv_sqrt hJ hB] at h
  -- conjugating back by `√B` and dividing by the potential
  exact CStarAlgebra.inv_smul_le_of_conj_inv_sqrt_le hB.nonneg hB.isUnit hΨ hP

end Infinite

end Discretization
