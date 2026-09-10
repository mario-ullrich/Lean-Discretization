/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
import BasicResults.LoewnerOrder
import BasicResults.TraceInequalities

/-!
# Lower bounds by the reciprocal of a potential

The Batson–Spielman–Srivastava argument controls a positive definite matrix through the two
quantities

* `Φ(A) = Re Tr A⁻¹`, the **lower potential**, and
* `Ψ(B) = Re Tr (J B⁻¹)`, the **upper potential** relative to a positive definite `J`.

Their whole point is that a bound on the potential is a bound on the matrix:
`Φ(A)⁻¹ • 1 ≤ A` (already proved in `BasicResults.LoewnerOrder` as
`Matrix.PosDef.inv_re_trace_smul_one_le`) and `Ψ(B)⁻¹ • J ≤ B`, proved here as
`Matrix.PosDef.inv_re_trace_mul_smul_le`.

The `J`-weighted statement is the one that makes the upper frame bound of the main theorem
dimension-free.  Its proof conjugates by the positive square root `S = B^{1/2}`: the matrix
`S⁻¹ J S⁻¹` is positive semidefinite with trace `Tr (J B⁻¹) = Ψ(B)`, hence is bounded by
`Ψ(B) • 1`, and conjugating that inequality back by `S` turns it into `J ≤ Ψ(B) • B`.

Square roots of matrices are Mathlib's `CFC.sqrt`, from the continuous functional calculus;
they require the C⋆-algebra structure of `Matrix n n ℂ`, whose norm is scoped in
`Matrix.Norms.L2Operator`.
-/

open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **The positive square root of a positive definite matrix is invertible.**  This is
Mathlib's `CFC.isUnit_sqrt_iff`, which says that `√a` is a unit exactly when `a` is. -/
theorem PosDef.isUnit_sqrt {B : Matrix n n ℂ} (hB : B.PosDef) : IsUnit (CFC.sqrt B) :=
  (CFC.isUnit_sqrt_iff B hB.posSemidef.nonneg).2 hB.isUnit

/-- The determinant of the positive square root of a positive definite matrix is a unit. -/
theorem PosDef.isUnit_det_sqrt {B : Matrix n n ℂ} (hB : B.PosDef) :
    IsUnit (CFC.sqrt B).det :=
  (Matrix.isUnit_iff_isUnit_det _).1 hB.isUnit_sqrt

/-- **A positive definite matrix dominates the reciprocal of its upper potential times `J`.**

For positive definite `B` and `J`, the upper potential `Ψ(B) = Re Tr (J B⁻¹)` satisfies
`Ψ(B)⁻¹ • J ≤ B`.  Equivalently `J ≤ Ψ(B) • B`: a small upper potential forces `B` to be
large in the directions where `J` is large.

Together with `Matrix.PosDef.inv_re_trace_smul_one_le` this is the reason potentials control
frame bounds: at the end of the construction the two potentials have not increased, and the
inequalities above convert that into the eigenvalue bounds of the main theorem. -/
theorem PosDef.inv_re_trace_mul_smul_le [Nonempty n] {B J : Matrix n n ℂ} (hB : B.PosDef)
    (hJ : J.PosDef) : (RCLike.re (J * B⁻¹).trace)⁻¹ • J ≤ B := by
  -- the positive square root of `B` and its elementary properties
  set S := CFC.sqrt B with hSdef
  have hS0 : (0 : Matrix n n ℂ) ≤ S := CFC.sqrt_nonneg B
  have hSS : S * S = B := CFC.sqrt_mul_sqrt_self B hB.posSemidef.nonneg
  have hdet : IsUnit S.det := hB.isUnit_det_sqrt
  have hSinv : S * S⁻¹ = 1 := mul_nonsing_inv _ hdet
  have hSinv' : S⁻¹ * S = 1 := nonsing_inv_mul _ hdet
  have hBinv : B⁻¹ = S⁻¹ * S⁻¹ := by rw [← hSS, mul_inv_rev]
  -- the conjugated matrix `S⁻¹ J S⁻¹` is positive semidefinite with trace `Ψ(B)`
  have hSpsd : S.PosSemidef := Matrix.nonneg_iff_posSemidef.1 hS0
  have hPpsd : (S⁻¹ * J * S⁻¹).PosSemidef :=
    hJ.posSemidef.mul_mul_same_of_isHermitian hSpsd.inv.isHermitian
  have htrace : (S⁻¹ * J * S⁻¹).trace = (J * B⁻¹).trace := by
    rw [trace_mul_cycle, trace_mul_comm, ← hBinv]
  have hΨpos : 0 < RCLike.re (J * B⁻¹).trace := hJ.re_trace_mul_pos hB.inv
  have hreal := IsHermitian.ofReal_re_trace_mul hJ.isHermitian hB.inv.isHermitian
  have hP : S⁻¹ * J * S⁻¹ ≤ (RCLike.re (J * B⁻¹).trace) • (1 : Matrix n n ℂ) := by
    rw [RCLike.real_smul_eq_coe_smul (K := ℂ)]
    have h := hPpsd.le_trace_smul_one
    rwa [htrace, ← hreal] at h
  -- conjugating back by `S` turns this into `J ≤ Ψ(B) • B`
  have hconj := conjugate_le_conjugate_of_nonneg hP hS0
  have hlhs : S * (S⁻¹ * J * S⁻¹) * S = J := by
    calc S * (S⁻¹ * J * S⁻¹) * S = S * S⁻¹ * J * (S⁻¹ * S) := by simp [mul_assoc]
      _ = J := by rw [hSinv, hSinv', one_mul, mul_one]
  have hrhs : S * ((RCLike.re (J * B⁻¹).trace) • (1 : Matrix n n ℂ)) * S
      = (RCLike.re (J * B⁻¹).trace) • B := by
    rw [mul_smul_comm, smul_mul_assoc, mul_one, hSS]
  rw [hlhs, hrhs] at hconj
  -- and dividing by the (positive) potential gives the claim
  have h := smul_le_smul_of_nonneg_left hconj (inv_nonneg.2 hΨpos.le)
  rwa [smul_smul, inv_mul_cancel₀ hΨpos.ne', one_smul] at h

omit [Fintype n] [DecidableEq n] in
/-- Adding a positive multiple of a positive definite matrix keeps positive definiteness.
This is the increment step `B ↦ B + ζ • J` of the construction. -/
theorem PosDef.add_smul_posDef {B J : Matrix n n ℂ} (hB : B.PosDef) (hJ : J.PosDef) {ζ : ℝ}
    (hζ : 0 < ζ) : (B + ζ • J).PosDef :=
  hB.add (hJ.smul hζ)

end Matrix
