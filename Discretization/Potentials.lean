/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
import BasicResults

/-!
# Potentials

The construction of Batson, Spielman and Srivastava keeps track of two matrices, a small
one `A` controlling the lower frame bound and a large one `B` controlling the upper one, and
of two real numbers attached to them:

* the **lower potential** `Φ(A) = Re Tr A⁻¹`, which is large when `A` has a small
  eigenvalue, and
* the **upper potential** `Ψ_J(B) = Re Tr (J B⁻¹)`, which is large when `B` is small in the
  directions where `J` is large.

Before each step of the construction, `A` is shrunk by `δ • 1` and `B` is grown by `ζ • J`.
Both shifts move the potentials in the unfavourable direction, and the exact amount is
computed here:

* `Discretization.lowerPotential_sub_eq` — `Φ(A - δ • 1) - Φ(A) = δ · Re Tr ((A - δ • 1)⁻¹ A⁻¹)`,
* `Discretization.upperPotential_sub_eq` — `Ψ_J(B) - Ψ_J(B + ζ • J) = ζ · Re Tr (J B⁻¹ J (B + ζ • J)⁻¹)`.

Both right-hand sides are positive, so shrinking increases the lower potential and growing
decreases the upper one; the gap this opens is what a new sampling point is allowed to
consume.  Both identities come from Mathlib's resolvent identity `Matrix.inv_sub_inv`, and
the sign from the positivity of the trace of a product of positive definite matrices
(`Matrix.PosDef.re_trace_mul_pos`).
-/

open Matrix
open scoped ComplexOrder MatrixOrder

namespace Matrix

variable {𝕜 n : Type*} [RCLike 𝕜] [Fintype n] [DecidableEq n]

/-- The resolvent identity for a shift by a multiple of the identity:
`(A - δ • 1)⁻¹ - A⁻¹ = δ • ((A - δ • 1)⁻¹ A⁻¹)`. -/
theorem inv_sub_smul_one_sub_inv {A : Matrix n n 𝕜} (hA : IsUnit A) {δ : ℝ}
    (hN : IsUnit (A - δ • (1 : Matrix n n 𝕜))) :
    (A - δ • (1 : Matrix n n 𝕜))⁻¹ - A⁻¹
      = δ • ((A - δ • (1 : Matrix n n 𝕜))⁻¹ * A⁻¹) := by
  have hAN : A - (A - δ • (1 : Matrix n n 𝕜)) = δ • 1 := by abel
  rw [Matrix.inv_sub_inv (iff_of_true hN hA), hAN, mul_smul_comm, mul_one, smul_mul_assoc]

/-- The resolvent identity for a shift by a multiple of a fixed matrix:
`B⁻¹ - (B + ζ • J)⁻¹ = ζ • (B⁻¹ J (B + ζ • J)⁻¹)`. -/
theorem inv_sub_inv_add_smul {B J : Matrix n n 𝕜} (hB : IsUnit B) {ζ : ℝ}
    (hA : IsUnit (B + ζ • J)) :
    B⁻¹ - (B + ζ • J)⁻¹ = ζ • (B⁻¹ * J * (B + ζ • J)⁻¹) := by
  have hAN : B + ζ • J - B = ζ • J := by abel
  rw [Matrix.inv_sub_inv (iff_of_true hB hA), hAN, mul_smul_comm, smul_mul_assoc]

end Matrix

namespace Discretization

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- The **lower potential** `Φ(A) = Re Tr A⁻¹`. -/
noncomputable def lowerPotential (A : Matrix ι ι ℂ) : ℝ := RCLike.re (A⁻¹).trace

/-- The **upper potential** `Ψ_J(B) = Re Tr (J B⁻¹)` of `B` relative to `J`. -/
noncomputable def upperPotential (J B : Matrix κ κ ℂ) : ℝ := RCLike.re (J * B⁻¹).trace

/-- The lower potential of a positive definite matrix is positive. -/
theorem lowerPotential_pos [Nonempty ι] {A : Matrix ι ι ℂ} (hA : A.PosDef) :
    0 < lowerPotential A :=
  (RCLike.pos_iff.mp hA.inv.trace_pos).1

/-- The upper potential of a positive definite matrix is positive. -/
theorem upperPotential_pos [Nonempty κ] {J B : Matrix κ κ ℂ} (hJ : J.PosDef)
    (hB : B.PosDef) : 0 < upperPotential J B :=
  hJ.re_trace_mul_pos hB.inv

/-- **The gain of the lower potential under a shift.**
`Φ(A - δ • 1) - Φ(A) = δ · Re Tr ((A - δ • 1)⁻¹ A⁻¹)`. -/
theorem lowerPotential_sub_eq [Nonempty ι] {A : Matrix ι ι ℂ} (hA : A.PosDef) {δ : ℝ}
    (hδ' : δ < (lowerPotential A)⁻¹) :
    lowerPotential (A - δ • (1 : Matrix ι ι ℂ)) - lowerPotential A
      = δ * RCLike.re ((A - δ • (1 : Matrix ι ι ℂ))⁻¹ * A⁻¹).trace := by
  have hN : (A - δ • (1 : Matrix ι ι ℂ)).PosDef := hA.sub_smul_one hδ'
  have hid := Matrix.inv_sub_smul_one_sub_inv hA.isUnit (δ := δ) hN.isUnit
  have h := congrArg (fun M => RCLike.re (Matrix.trace M)) hid
  simpa [lowerPotential, Matrix.trace_sub, map_sub, Matrix.trace_smul, RCLike.smul_re] using h

/-- **The gain of the upper potential under a shift.**
`Ψ_J(B) - Ψ_J(B + ζ • J) = ζ · Re Tr ((J B⁻¹ J) (B + ζ • J)⁻¹)`. -/
theorem upperPotential_sub_eq {J B : Matrix κ κ ℂ} (hJ : J.PosDef) (hB : B.PosDef) {ζ : ℝ}
    (hζ : 0 < ζ) :
    upperPotential J B - upperPotential J (B + ζ • J)
      = ζ * RCLike.re ((J * B⁻¹ * J) * (B + ζ • J)⁻¹).trace := by
  have hA : (B + ζ • J).PosDef := hB.add_smul_posDef hJ hζ
  have hid := Matrix.inv_sub_inv_add_smul hB.isUnit (ζ := ζ) hA.isUnit
  have h := congrArg (fun M => RCLike.re (Matrix.trace (J * M))) hid
  simpa [upperPotential, Matrix.mul_sub, Matrix.trace_sub, map_sub, Matrix.mul_smul,
    Matrix.trace_smul, RCLike.smul_re, mul_assoc] using h

/-- The matrix `J B⁻¹ J` is positive definite for positive definite `J` and `B`. -/
theorem posDef_conj_inv {J B : Matrix κ κ ℂ} (hJ : J.PosDef) (hB : B.PosDef) :
    (J * B⁻¹ * J).PosDef := by
  have hJinj : Function.Injective J.mulVec := Matrix.mulVec_injective_iff_isUnit.2 hJ.isUnit
  have h := hB.inv.conjTranspose_mul_mul_same (B := J) hJinj
  rwa [hJ.isHermitian.eq] at h

/-- **Shrinking increases the lower potential**: `Φ(A) < Φ(A - δ • 1)`. -/
theorem lowerPotential_lt_sub_smul_one [Nonempty ι] {A : Matrix ι ι ℂ} (hA : A.PosDef)
    {δ : ℝ} (hδ : 0 < δ) (hδ' : δ < (lowerPotential A)⁻¹) :
    lowerPotential A < lowerPotential (A - δ • (1 : Matrix ι ι ℂ)) := by
  have hN : (A - δ • (1 : Matrix ι ι ℂ)).PosDef := hA.sub_smul_one hδ'
  have htr := lowerPotential_sub_eq hA hδ'
  have hpos : 0 < RCLike.re ((A - δ • (1 : Matrix ι ι ℂ))⁻¹ * A⁻¹).trace :=
    hN.inv.re_trace_mul_pos hA.inv
  nlinarith [htr, hpos, hδ]

/-- **Growing decreases the upper potential**: `Ψ_J(B + ζ • J) < Ψ_J(B)`. -/
theorem upperPotential_add_smul_lt [Nonempty κ] {J B : Matrix κ κ ℂ} (hJ : J.PosDef)
    (hB : B.PosDef) {ζ : ℝ} (hζ : 0 < ζ) :
    upperPotential J (B + ζ • J) < upperPotential J B := by
  have hA : (B + ζ • J).PosDef := hB.add_smul_posDef hJ hζ
  have htr := upperPotential_sub_eq hJ hB hζ
  have hpos : 0 < RCLike.re ((J * B⁻¹ * J) * (B + ζ • J)⁻¹).trace :=
    (posDef_conj_inv hJ hB).re_trace_mul_pos hA.inv
  nlinarith [htr, hpos, hζ]

end Discretization
