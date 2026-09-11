/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order

/-!
# Rank-one updates of an operator

The construction of sampling points changes the operator of the upper bound by a rank-one
operator at a time, so the whole argument rests on knowing how the inverse reacts.  This
file is the operator counterpart of `BasicResults.ShermanMorrison`.

Two notations differ from the matrix case.  The rank-one operator `u u*` is Mathlib's
`InnerProductSpace.rankOne ℂ u u`, which sends `z` to `⟪u, z⟫ • u`.  The inverse is
`Ring.inverse`, which is defined for every operator and is the inverse whenever the operator
is invertible.  The formula itself is the same:

`(A + t u u*)⁻¹ = A⁻¹ - t / (1 + t ⟪u, A⁻¹ u⟫) · (A⁻¹u)(A⁻¹u)*`,

and so is its proof, a direct verification that the right-hand side is a two-sided inverse.

The formula is also recorded with a **real** weight, added
(`Discretization.inverse_add_smul_rankOne_of_nonneg`) or subtracted
(`Discretization.inverse_sub_smul_rankOne_of_nonneg`); then the quadratic form `⟪u, A⁻¹ u⟫`
in the denominator is real.  Both updates keep the operator positive and invertible, the
second one as long as the Sherman–Morrison denominator stays positive.

A last section collects the facts about the order that the shift `B ↦ B + ζ • J` needs: it
keeps `B` strictly positive, the inverse follows by a resolvent identity, and it can only
lower that inverse.

Positivity here is Mathlib's `IsStrictlyPositive`, which is positivity together with
invertibility.  That is the right notion in infinite dimension: a positive operator need not
be bounded away from zero, and it is exactly invertibility that the potential argument uses
in place of positive definiteness.
-/

open scoped InnerProductSpace ComplexOrder
open InnerProductSpace

namespace Discretization

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **A two-sided inverse computes `Ring.inverse`.**

In a noncommutative ring one product does not suffice, but two do: they exhibit `x` as a
unit with inverse `y`.  Mathlib has the two cancellation laws `Ring.mul_inverse_cancel` and
`Ring.inverse_mul_cancel` but not this converse. -/
theorem inverse_eq_of_mul_eq_one {R : Type*} [Ring R] {x y : R} (h₁ : x * y = 1)
    (h₂ : y * x = 1) : Ring.inverse x = y := by
  simpa using Ring.inverse_unit (⟨x, y, h₁, h₂⟩ : Rˣ)

/-- The two products that identify the Sherman–Morrison candidate as a two-sided inverse.

Both products collapse to
`1 + (t - c - t c q) · u v*`, with `c` the Sherman–Morrison coefficient and
`q = ⟪u, A⁻¹ u⟫`, and that scalar vanishes by the choice of `c`. -/
private theorem mul_eq_one_add_smul_rankOne {A : H →L[ℂ] H} (hA : IsUnit A)
    (hsa : IsSelfAdjoint A) (u : H) (t : ℂ) (ht : 1 + t * ⟪u, Ring.inverse A u⟫_ℂ ≠ 0) :
    (A + t • rankOne ℂ u u)
        * (Ring.inverse A - (t / (1 + t * ⟪u, Ring.inverse A u⟫_ℂ))
            • rankOne ℂ (Ring.inverse A u) (Ring.inverse A u)) = 1 ∧
      (Ring.inverse A - (t / (1 + t * ⟪u, Ring.inverse A u⟫_ℂ))
            • rankOne ℂ (Ring.inverse A u) (Ring.inverse A u))
        * (A + t • rankOne ℂ u u) = 1 := by
  have hAadj : ContinuousLinearMap.adjoint A = A := hsa.star_eq
  have hWadj : ContinuousLinearMap.adjoint (Ring.inverse A) = Ring.inverse A :=
    hsa.ringInverse.star_eq
  have hAW : A * Ring.inverse A = 1 := Ring.mul_inverse_cancel A hA
  have hWA : Ring.inverse A * A = 1 := Ring.inverse_mul_cancel A hA
  set W := Ring.inverse A with hWdef
  set v := W u with hvdef
  set q := ⟪u, v⟫_ℂ with hqdef
  set c := t / (1 + t * q) with hcdef
  have hAv : A v = u := by
    rw [hvdef, show A (W u) = (A * W) u from rfl, hAW]; rfl
  have hvu : ⟪v, u⟫_ℂ = q := by
    rw [hqdef, hvdef, ← hWadj, ContinuousLinearMap.adjoint_inner_left, hWadj]
  have hkey : t - c - t * c * q = 0 := by rw [hcdef]; field_simp; ring
  have e₁ : (rankOne ℂ u u : H →L[ℂ] H) * W = rankOne ℂ u v := by
    rw [ContinuousLinearMap.mul_def, rankOne_comp, hWadj, hvdef]
  have e₂ : A * (rankOne ℂ v v : H →L[ℂ] H) = rankOne ℂ u v := by
    rw [ContinuousLinearMap.mul_def, comp_rankOne, hAv]
  have e₃ : (rankOne ℂ u u : H →L[ℂ] H) * rankOne ℂ v v = q • rankOne ℂ u v := by
    rw [ContinuousLinearMap.mul_def, rankOne_comp_rankOne, hqdef]
  have f₁ : W * (rankOne ℂ u u : H →L[ℂ] H) = rankOne ℂ v u := by
    rw [ContinuousLinearMap.mul_def, comp_rankOne, hvdef]
  have f₂ : (rankOne ℂ v v : H →L[ℂ] H) * A = rankOne ℂ v u := by
    rw [ContinuousLinearMap.mul_def, rankOne_comp, hAadj, hAv]
  have f₃ : (rankOne ℂ v v : H →L[ℂ] H) * rankOne ℂ u u = q • rankOne ℂ v u := by
    rw [ContinuousLinearMap.mul_def, rankOne_comp_rankOne, hvu]
  constructor
  · have expand : (A + t • rankOne ℂ u u) * (W - c • rankOne ℂ v v)
        = 1 + (t - c - t * c * q) • rankOne ℂ u v := by
      simp only [add_mul, mul_sub, smul_mul_assoc, mul_smul_comm, hAW, e₁, e₂, e₃, smul_smul]
      module
    rw [expand, hkey, zero_smul, add_zero]
  · have expand : (W - c • rankOne ℂ v v) * (A + t • rankOne ℂ u u)
        = 1 + (t - c - t * c * q) • rankOne ℂ v u := by
      simp only [sub_mul, mul_add, smul_mul_assoc, mul_smul_comm, hWA, f₁, f₂, f₃, smul_smul]
      module
    rw [expand, hkey, zero_smul, add_zero]

/-- **A rank-one update of a self-adjoint unit is a unit**, as long as the Sherman–Morrison
denominator does not vanish. -/
theorem isUnit_add_smul_rankOne {A : H →L[ℂ] H} (hA : IsUnit A) (hsa : IsSelfAdjoint A)
    (u : H) (t : ℂ) (ht : 1 + t * ⟪u, Ring.inverse A u⟫_ℂ ≠ 0) :
    IsUnit (A + t • rankOne ℂ u u) :=
  let h := mul_eq_one_add_smul_rankOne hA hsa u t ht
  ⟨⟨_, _, h.1, h.2⟩, rfl⟩

/-- **Sherman–Morrison formula for a rank-one update of an operator.**

For a self-adjoint invertible `A`, a vector `u` and a scalar `t` with
`1 + t ⟪u, A⁻¹ u⟫ ≠ 0`,

`(A + t u u*)⁻¹ = A⁻¹ - t / (1 + t ⟪u, A⁻¹ u⟫) · (A⁻¹u)(A⁻¹u)*`.

Self-adjointness of `A` is what makes the correction term a rank-one operator built from the
single vector `A⁻¹ u`. -/
theorem inverse_add_smul_rankOne {A : H →L[ℂ] H} (hA : IsUnit A) (hsa : IsSelfAdjoint A)
    (u : H) (t : ℂ) (ht : 1 + t * ⟪u, Ring.inverse A u⟫_ℂ ≠ 0) :
    Ring.inverse (A + t • rankOne ℂ u u)
      = Ring.inverse A - (t / (1 + t * ⟪u, Ring.inverse A u⟫_ℂ))
          • rankOne ℂ (Ring.inverse A u) (Ring.inverse A u) :=
  let h := mul_eq_one_add_smul_rankOne hA hsa u t ht
  inverse_eq_of_mul_eq_one h.1 h.2

/-! ### Real weights, and positivity -/

omit [CompleteSpace H] in
/-- Scaling an operator by a real number is scaling it by the corresponding complex number,
with the real number written as `Complex.ofReal r`, the spelling used throughout this file. -/
private theorem real_smul_eq_complex_smul (r : ℝ) (X : H →L[ℂ] H) : r • X = (r : ℂ) • X :=
  RCLike.real_smul_eq_coe_smul (K := ℂ) r X

omit [CompleteSpace H] in
/-- A rank-one operator `u u*` is positive. -/
theorem nonneg_rankOne_self (u : H) : (0 : H →L[ℂ] H) ≤ rankOne ℂ u u := by
  rw [ContinuousLinearMap.nonneg_iff_isPositive]
  exact InnerProductSpace.isPositive_rankOne_self u

/-- The quadratic form of the inverse of a strictly positive operator is nonnegative. -/
theorem re_inner_inverse_nonneg {A : H →L[ℂ] H} (hA : IsStrictlyPositive A) (u : H) :
    0 ≤ RCLike.re ⟪u, Ring.inverse A u⟫_ℂ :=
  ((ContinuousLinearMap.nonneg_iff_isPositive _).1
    hA.ringInverse.nonneg).re_inner_nonneg_right u

/-- The quadratic form of the inverse of a strictly positive operator is real, being
nonnegative. -/
theorem ofReal_re_inner_inverse {A : H →L[ℂ] H} (hA : IsStrictlyPositive A) (u : H) :
    ((RCLike.re ⟪u, Ring.inverse A u⟫_ℂ : ℝ) : ℂ) = ⟪u, Ring.inverse A u⟫_ℂ := by
  have h0 : (0 : ℂ) ≤ ⟪u, Ring.inverse A u⟫_ℂ :=
    ((ContinuousLinearMap.nonneg_iff_isPositive _).1
      hA.ringInverse.nonneg).inner_nonneg_right u
  have h : ⟪u, Ring.inverse A u⟫_ℂ = (⟪u, Ring.inverse A u⟫_ℂ).re :=
    Complex.eq_re_of_ofReal_le (r := 0) (by rw [Complex.ofReal_zero]; exact h0)
  rw [h]
  norm_cast

/-- **Adding a nonnegative multiple of a rank-one operator preserves strict positivity.** -/
theorem isStrictlyPositive_add_smul_rankOne {A : H →L[ℂ] H} (hA : IsStrictlyPositive A)
    (u : H) {w : ℝ} (hw : 0 ≤ w) : IsStrictlyPositive (A + w • rankOne ℂ u u) := by
  have hle : A ≤ A + w • rankOne ℂ u u := by
    have h : (0 : H →L[ℂ] H) ≤ w • rankOne ℂ u u := smul_nonneg hw (nonneg_rankOne_self u)
    simpa using add_le_add_left h A
  exact ⟨hA.nonneg.trans hle, CStarAlgebra.isUnit_of_le A hle hA⟩

/-- **Sherman–Morrison with a real weight, added.**

For a strictly positive `A` and a weight `w ≥ 0`,
`(A + w u u*)⁻¹ = A⁻¹ - w/(1 + w ⟪u, A⁻¹ u⟫) · (A⁻¹u)(A⁻¹u)*`, with every scalar real: the
quadratic form is nonnegative, so the denominator is at least one and in particular nonzero. -/
theorem inverse_add_smul_rankOne_of_nonneg {A : H →L[ℂ] H} (hA : IsStrictlyPositive A)
    (u : H) {w : ℝ} (hw : 0 ≤ w) :
    Ring.inverse (A + w • rankOne ℂ u u)
      = Ring.inverse A - (w / (1 + w * RCLike.re ⟪u, Ring.inverse A u⟫_ℂ))
          • rankOne ℂ (Ring.inverse A u) (Ring.inverse A u) := by
  have hp0 : 0 ≤ RCLike.re ⟪u, Ring.inverse A u⟫_ℂ := re_inner_inverse_nonneg hA u
  have hre := ofReal_re_inner_inverse hA u
  set p : ℝ := RCLike.re ⟪u, Ring.inverse A u⟫_ℂ with hpdef
  have hden : 0 < 1 + w * p := by positivity
  have hcast : (1 : ℂ) + (w : ℂ) * ⟪u, Ring.inverse A u⟫_ℂ = ((1 + w * p : ℝ) : ℂ) := by
    rw [← hre]; push_cast; ring
  have hne : (1 : ℂ) + (w : ℂ) * ⟪u, Ring.inverse A u⟫_ℂ ≠ 0 := by
    rw [hcast]; exact_mod_cast hden.ne'
  have hcoef : (w : ℂ) / (1 + (w : ℂ) * ⟪u, Ring.inverse A u⟫_ℂ)
      = ((w / (1 + w * p) : ℝ) : ℂ) := by
    rw [hcast]; push_cast; ring
  rw [real_smul_eq_complex_smul w,
    inverse_add_smul_rankOne hA.isUnit hA.isSelfAdjoint u _ hne,
    real_smul_eq_complex_smul (w / (1 + w * p)), hcoef]

/-- **Sherman–Morrison with a real weight, subtracted.**

For a strictly positive `A` and a weight `w` small enough that the Sherman–Morrison
denominator `1 - w ⟪u, A⁻¹ u⟫` stays positive,
`(A - w u u*)⁻¹ = A⁻¹ + w/(1 - w ⟪u, A⁻¹ u⟫) · (A⁻¹u)(A⁻¹u)*`.

The correction has a plus sign: removing mass from `A` makes its inverse larger. -/
theorem inverse_sub_smul_rankOne_of_nonneg {A : H →L[ℂ] H} (hA : IsStrictlyPositive A)
    (u : H) {w : ℝ} (hden : 0 < 1 - w * RCLike.re ⟪u, Ring.inverse A u⟫_ℂ) :
    Ring.inverse (A - w • rankOne ℂ u u)
      = Ring.inverse A + (w / (1 - w * RCLike.re ⟪u, Ring.inverse A u⟫_ℂ))
          • rankOne ℂ (Ring.inverse A u) (Ring.inverse A u) := by
  have hre := ofReal_re_inner_inverse hA u
  set p : ℝ := RCLike.re ⟪u, Ring.inverse A u⟫_ℂ with hpdef
  have hcast : (1 : ℂ) + (-(w : ℂ)) * ⟪u, Ring.inverse A u⟫_ℂ = ((1 - w * p : ℝ) : ℂ) := by
    rw [← hre]; push_cast; ring
  have hne : (1 : ℂ) + (-(w : ℂ)) * ⟪u, Ring.inverse A u⟫_ℂ ≠ 0 := by
    rw [hcast]; exact_mod_cast hden.ne'
  have hcoef : -((-(w : ℂ)) / (1 + (-(w : ℂ)) * ⟪u, Ring.inverse A u⟫_ℂ))
      = ((w / (1 - w * p) : ℝ) : ℂ) := by
    rw [hcast]; push_cast; ring
  have hsub : A - w • rankOne ℂ u u = A + (-(w : ℂ)) • rankOne ℂ u u := by
    rw [real_smul_eq_complex_smul, neg_smul, ← sub_eq_add_neg]
  rw [hsub, inverse_add_smul_rankOne hA.isUnit hA.isSelfAdjoint u _ hne, sub_eq_add_neg,
    ← neg_smul, hcoef, ← real_smul_eq_complex_smul]

/-- **Subtracting a rank-one operator preserves strict positivity** as long as the
Sherman–Morrison denominator stays positive.

The inverse of `A - w u u*` is a strictly positive operator plus a positive one, and an
operator whose inverse is positive is itself positive
(`CFC.ringInverse_nonneg_iff_nonneg_of_isUnit`). -/
theorem isStrictlyPositive_sub_smul_rankOne {A : H →L[ℂ] H} (hA : IsStrictlyPositive A)
    (u : H) {w : ℝ} (hw : 0 ≤ w)
    (hden : 0 < 1 - w * RCLike.re ⟪u, Ring.inverse A u⟫_ℂ) :
    IsStrictlyPositive (A - w • rankOne ℂ u u) := by
  have hre := ofReal_re_inner_inverse hA u
  have hcast : (1 : ℂ) + (-(w : ℂ)) * ⟪u, Ring.inverse A u⟫_ℂ
      = ((1 - w * RCLike.re ⟪u, Ring.inverse A u⟫_ℂ : ℝ) : ℂ) := by
    conv_lhs => rw [← hre]
    push_cast
    ring
  have hne : (1 : ℂ) + (-(w : ℂ)) * ⟪u, Ring.inverse A u⟫_ℂ ≠ 0 := by
    rw [hcast]; exact_mod_cast hden.ne'
  have hsub : A - w • rankOne ℂ u u = A + (-(w : ℂ)) • rankOne ℂ u u := by
    rw [real_smul_eq_complex_smul, neg_smul, ← sub_eq_add_neg]
  have hunit : IsUnit (A - w • rankOne ℂ u u) := by
    rw [hsub]; exact isUnit_add_smul_rankOne hA.isUnit hA.isSelfAdjoint u _ hne
  refine ⟨(CFC.ringInverse_nonneg_iff_nonneg_of_isUnit hunit).1 ?_, hunit⟩
  rw [inverse_sub_smul_rankOne_of_nonneg hA u hden]
  exact add_nonneg hA.ringInverse.nonneg
    (smul_nonneg (div_nonneg hw hden.le) (nonneg_rankOne_self _))

/-! ### Order and inverses

Two operators are shifted against each other in the construction, `B ↦ B + ζ • J`, and the
inverse has to follow.  These facts are about the order alone, with no rank-one operator in
sight. -/

/-- The product `J S J` of two positive operators `J` and `S` is positive. -/
theorem nonneg_conj {J S : H →L[ℂ] H} (hJ : 0 ≤ J) (hS : 0 ≤ S) :
    (0 : H →L[ℂ] H) ≤ J * S * J := by
  have hJadj : ContinuousLinearMap.adjoint J = J := hJ.isSelfAdjoint.star_eq
  have h := ((ContinuousLinearMap.nonneg_iff_isPositive S).1 hS).adjoint_conj J
  rw [hJadj] at h
  rw [ContinuousLinearMap.nonneg_iff_isPositive]
  simpa [ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_assoc] using h

/-- Growing `B` by a nonnegative multiple of a positive operator keeps it strictly
positive. -/
theorem isStrictlyPositive_add_smul {J B : H →L[ℂ] H} (hJ : 0 ≤ J)
    (hB : IsStrictlyPositive B) {ζ : ℝ} (hζ : 0 ≤ ζ) : IsStrictlyPositive (B + ζ • J) := by
  have hle : B ≤ B + ζ • J := by
    have h : (0 : H →L[ℂ] H) ≤ ζ • J := smul_nonneg hζ hJ
    simpa using add_le_add_left h B
  exact ⟨hB.nonneg.trans hle, CStarAlgebra.isUnit_of_le B hle hB⟩

/-- **The resolvent identity** for the shift by a multiple of `J`:
`B⁻¹ - (B + ζ • J)⁻¹ = ζ • (B⁻¹ J (B + ζ • J)⁻¹)`.

This is an instance of Mathlib's `Ring.inverse_sub_inverse`. -/
theorem inverse_sub_inverse_add_smul {J B : H →L[ℂ] H} (hJ : 0 ≤ J)
    (hB : IsStrictlyPositive B) {ζ : ℝ} (hζ : 0 ≤ ζ) :
    Ring.inverse B - Ring.inverse (B + ζ • J)
      = ζ • (Ring.inverse B * J * Ring.inverse (B + ζ • J)) := by
  have hM : IsStrictlyPositive (B + ζ • J) := isStrictlyPositive_add_smul hJ hB hζ
  rw [Ring.inverse_sub_inverse (iff_of_true hB.isUnit hM.isUnit)]
  have hdiff : B + ζ • J - B = ζ • J := by abel
  rw [hdiff, mul_smul_comm, smul_mul_assoc]

/-- The shifted inverse is below the original one: `(B + ζ • J)⁻¹ ≼ B⁻¹`. -/
theorem inverse_add_smul_le {J B : H →L[ℂ] H} (hJ : 0 ≤ J) (hB : IsStrictlyPositive B)
    {ζ : ℝ} (hζ : 0 ≤ ζ) : Ring.inverse (B + ζ • J) ≤ Ring.inverse B := by
  have hle : B ≤ B + ζ • J := by
    have h : (0 : H →L[ℂ] H) ≤ ζ • J := smul_nonneg hζ hJ
    simpa using add_le_add_left h B
  exact CStarAlgebra.ringInverse_le_ringInverse hle hB

end Discretization
