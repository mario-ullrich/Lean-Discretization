/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order

/-!
# Conjugating a bound by the square root

One step recurs on both sides of the potential argument.  An element `X` is first compared
with a multiple of the identity after conjugation by the inverse square root of a positive
invertible `B`, and that comparison is then carried back to `X` and `B` themselves:

`B^{-1/2} X B^{-1/2} ≤ t • 1`   gives   `t⁻¹ • X ≤ B`.

Conjugating the hypothesis by `B^{1/2}` cancels the two inverse square roots on the left and
turns `t • 1` into `t • B` on the right; dividing by `t` gives the claim.

Neither matrices nor operators enter, only the order of a C⋆-algebra, so the statement is
made once and serves `Matrix.PosDef.inv_re_trace_mul_smul_le` in finite dimension and
`Discretization.Infinite.inv_upperPotential_smul_le` for operators.  It is the step that
turns a bound on a potential into a bound on the object the potential measures.
-/

namespace CStarAlgebra

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- **A bound on the conjugate by the inverse square root is a bound on the element.**

For a positive invertible `B` and a positive real `t`, the bound
`B^{-1/2} X B^{-1/2} ≤ t • 1` gives `t⁻¹ • X ≤ B`. -/
theorem inv_smul_le_of_conj_inv_sqrt_le {B X : A} (hB : 0 ≤ B) (hu : IsUnit B) {t : ℝ}
    (ht : 0 < t)
    (h : Ring.inverse (CFC.sqrt B) * X * Ring.inverse (CFC.sqrt B) ≤ t • (1 : A)) :
    t⁻¹ • X ≤ B := by
  have hS0 : (0 : A) ≤ CFC.sqrt B := CFC.sqrt_nonneg B
  have hSS : CFC.sqrt B * CFC.sqrt B = B := CFC.sqrt_mul_sqrt_self B hB
  have hSunit : IsUnit (CFC.sqrt B) := (CFC.isUnit_sqrt_iff B hB).2 hu
  have hSinv : CFC.sqrt B * Ring.inverse (CFC.sqrt B) = 1 := Ring.mul_inverse_cancel _ hSunit
  have hSinv' : Ring.inverse (CFC.sqrt B) * CFC.sqrt B = 1 := Ring.inverse_mul_cancel _ hSunit
  -- conjugating the hypothesis by the square root
  have hconj := conjugate_le_conjugate_of_nonneg h hS0
  have hlhs : CFC.sqrt B * (Ring.inverse (CFC.sqrt B) * X * Ring.inverse (CFC.sqrt B))
      * CFC.sqrt B = X := by
    calc CFC.sqrt B * (Ring.inverse (CFC.sqrt B) * X * Ring.inverse (CFC.sqrt B)) * CFC.sqrt B
        = CFC.sqrt B * Ring.inverse (CFC.sqrt B) * X
            * (Ring.inverse (CFC.sqrt B) * CFC.sqrt B) := by
          simp only [mul_assoc]
      _ = X := by rw [hSinv, hSinv', one_mul, mul_one]
  have hrhs : CFC.sqrt B * (t • (1 : A)) * CFC.sqrt B = t • B := by
    rw [mul_smul_comm, smul_mul_assoc, mul_one, hSS]
  rw [hlhs, hrhs] at hconj
  -- and dividing by `t`
  have h2 := smul_le_smul_of_nonneg_left hconj (inv_nonneg.2 ht.le)
  rwa [smul_smul, inv_mul_cancel₀ ht.ne', one_smul] at h2

end CStarAlgebra
