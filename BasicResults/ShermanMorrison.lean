/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
import BasicResults.LoewnerOrder

/-!
# Rank-one updates: the Sherman–Morrison formula

The construction of sampling points adds one rank-one matrix `w a a*` at a time, and the
whole argument rests on knowing how the inverse and its trace react.  This file provides:

* `Matrix.inv_add_smul_vecMulVec`: the **Sherman–Morrison formula**
  `(A + t a a*)⁻¹ = A⁻¹ - t / (1 + t a* A⁻¹ a) · (A⁻¹ a)(A⁻¹ a)*`;
* `Matrix.trace_inv_add_smul_vecMulVec`: its trace,
  `Tr (A + t a a*)⁻¹ = Tr A⁻¹ - t / (1 + t a* A⁻¹ a) · a* A⁻² a`, which is the identity
  behind the lower verifier;
* `Matrix.PosDef.inv_add_smul_vecMulVec` and `Matrix.PosDef.inv_sub_smul_vecMulVec`: the
  same formula for a positive definite matrix and a **real** weight, where the quadratic
  form in the denominator is automatically real;
* `Matrix.PosDef.add_smul_vecMulVec` and `Matrix.PosDef.sub_smul_vecMulVec`: positive
  definiteness is preserved when a rank-one matrix is added with a nonnegative weight, and
  when it is subtracted with a weight small enough to keep the Sherman–Morrison denominator
  `1 - w a* A⁻¹ a` positive.

Mathlib has the Woodbury identity for block updates
(`Matrix.add_mul_mul_inv_eq_sub`), but not the rank-one case in terms of
`Matrix.vecMulVec`, and it has nothing on the trace of an update.  The proof below is a
direct verification: with `q = a* A⁻¹ a` and `c = t / (1 + t q)`, the product of `A + t a a*`
with the claimed inverse collapses to `1 + (t - c - t c q) · a (A⁻¹ a)*`, and the scalar
factor vanishes by the choice of `c`.
-/

open scoped ComplexOrder MatrixOrder

/-- A nonnegative element of an `RCLike` field is the image of its own real part.  (Mathlib
has `RCLike.re_eq_self_of_le`, phrased with the norm instead of the order.) -/
theorem RCLike.ofReal_re_of_nonneg {𝕜 : Type*} [RCLike 𝕜] {z : 𝕜} (hz : 0 ≤ z) :
    ((RCLike.re z : ℝ) : 𝕜) = z :=
  RCLike.conj_eq_iff_re.mp (RCLike.conj_eq_iff_im.mpr (RCLike.nonneg_iff.mp hz).2)

namespace Matrix

variable {𝕜 n : Type*} [RCLike 𝕜] [Fintype n] [DecidableEq n]

/-- **Sherman–Morrison formula for a rank-one update.**

For an invertible Hermitian `A`, a vector `a` and a scalar `t` with
`1 + t · a* A⁻¹ a ≠ 0`,
`(A + t a a*)⁻¹ = A⁻¹ - t / (1 + t a* A⁻¹ a) · (A⁻¹ a)(A⁻¹ a)*`.

The Hermitian hypothesis is only used to identify the row vector `a* A⁻¹` with `(A⁻¹ a)*`,
so that the correction term is a rank-one matrix built from the single vector `A⁻¹ a`. -/
theorem inv_add_smul_vecMulVec {A : Matrix n n 𝕜} (hA : A.IsHermitian) (hdet : IsUnit A.det)
    (a : n → 𝕜) (t : 𝕜) (ht : 1 + t * (star a ⬝ᵥ (A⁻¹ *ᵥ a)) ≠ 0) :
    (A + t • vecMulVec a (star a))⁻¹
      = A⁻¹ - (t / (1 + t * (star a ⬝ᵥ (A⁻¹ *ᵥ a)))) •
          vecMulVec (A⁻¹ *ᵥ a) (star (A⁻¹ *ᵥ a)) := by
  set u := A⁻¹ *ᵥ a with hu
  set q := star a ⬝ᵥ u with hq
  set c := t / (1 + t * q) with hc
  have hAM : A * A⁻¹ = 1 := mul_nonsing_inv _ hdet
  have hAu : A *ᵥ u = a := by rw [hu, mulVec_mulVec, hAM, one_mulVec]
  have hstar : star u = star a ᵥ* A⁻¹ := by rw [hu, star_mulVec, hA.inv.eq]
  have e2 : A * vecMulVec u (star u) = vecMulVec a (star u) := by rw [mul_vecMulVec, hAu]
  have e3 : vecMulVec a (star a) * A⁻¹ = vecMulVec a (star u) := by
    rw [vecMulVec_mul, ← hstar]
  have e4 : vecMulVec a (star a) * vecMulVec u (star u) = q • vecMulVec a (star u) := by
    rw [vecMulVec_mul_vecMulVec, vecMulVec_smul]
  have key : t - c - t * c * q = 0 := by
    rw [hc]; field_simp; ring
  refine Matrix.inv_eq_right_inv ?_
  have expand : (A + t • vecMulVec a (star a)) * (A⁻¹ - c • vecMulVec u (star u))
      = 1 + (t - c - t * c * q) • vecMulVec a (star u) := by
    simp only [mul_sub, add_mul, Matrix.mul_smul, Matrix.smul_mul, hAM, e2, e3, e4, smul_smul]
    module
  rw [expand, key, zero_smul, add_zero]

omit [DecidableEq n] in
/-- For a Hermitian `A`, the squared length of `A a` is the quadratic form of `A²`:
`(A a) ⬝ᵥ star (A a) = a* A² a`. -/
theorem dotProduct_mulVec_self_star {A : Matrix n n 𝕜} (hA : A.IsHermitian) (a : n → 𝕜) :
    (A *ᵥ a) ⬝ᵥ star (A *ᵥ a) = star a ⬝ᵥ ((A * A) *ᵥ a) := by
  rw [star_mulVec, hA.eq, dotProduct_comm, dotProduct_mulVec, vecMul_vecMul,
    ← dotProduct_mulVec]

/-- **The trace of a rank-one update.**

`Tr (A + t a a*)⁻¹ = Tr A⁻¹ - t / (1 + t a* A⁻¹ a) · a* A⁻² a`.

Read with `t = w` this says: adding `w a a*` decreases the lower potential `Tr A⁻¹` by
exactly `a* A⁻² a / (1/w + a* A⁻¹ a)`, which is why the lower verifier of the
Batson–Spielman–Srivastava argument has that shape. -/
theorem trace_inv_add_smul_vecMulVec {A : Matrix n n 𝕜} (hA : A.IsHermitian)
    (hdet : IsUnit A.det) (a : n → 𝕜) (t : 𝕜)
    (ht : 1 + t * (star a ⬝ᵥ (A⁻¹ *ᵥ a)) ≠ 0) :
    ((A + t • vecMulVec a (star a))⁻¹).trace
      = (A⁻¹).trace - (t / (1 + t * (star a ⬝ᵥ (A⁻¹ *ᵥ a)))) *
          (star a ⬝ᵥ ((A⁻¹ * A⁻¹) *ᵥ a)) := by
  rw [inv_add_smul_vecMulVec hA hdet a t ht, trace_sub, trace_smul, smul_eq_mul,
    trace_vecMulVec, dotProduct_mulVec_self_star hA.inv]

omit [DecidableEq n] in
/-- Adding a nonnegative multiple of a rank-one matrix preserves positive definiteness. -/
theorem PosDef.add_smul_vecMulVec {A : Matrix n n 𝕜} (hA : A.PosDef) (a : n → 𝕜) {w : ℝ}
    (hw : 0 ≤ w) : (A + w • vecMulVec a (star a)).PosDef :=
  hA.add_posSemidef ((posSemidef_vecMulVec_self_star a).smul hw)

/-- **Sherman–Morrison with a real weight, added.**

For a positive definite `A`, a vector `a` and a weight `w ≥ 0`,
`(A + w a a*)⁻¹ = A⁻¹ - w/(1 + w · a* A⁻¹ a) · (A⁻¹a)(A⁻¹a)*`.

Every scalar here is real: `a* A⁻¹ a` is a nonnegative quadratic form, so the denominator is
at least one and in particular nonzero, and no hypothesis beyond `w ≥ 0` is needed.  This is
the form in which the potential argument uses the formula. -/
theorem PosDef.inv_add_smul_vecMulVec {A : Matrix n n ℂ} (hA : A.PosDef) (a : n → ℂ) {w : ℝ}
    (hw : 0 ≤ w) :
    (A + w • vecMulVec a (star a))⁻¹
      = A⁻¹ - (w / (1 + w * RCLike.re (star a ⬝ᵥ (A⁻¹ *ᵥ a))))
          • vecMulVec (A⁻¹ *ᵥ a) (star (A⁻¹ *ᵥ a)) := by
  have hAdet : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det _).1 hA.isUnit
  set q := star a ⬝ᵥ (A⁻¹ *ᵥ a) with hqdef
  set p := RCLike.re q with hp
  have hq0 : (0 : ℂ) ≤ q := hA.inv.posSemidef.dotProduct_mulVec_nonneg a
  have hp0 : 0 ≤ p := hA.inv.posSemidef.re_dotProduct_nonneg a
  have hqre : ((p : ℝ) : ℂ) = q := RCLike.ofReal_re_of_nonneg hq0
  have hden : 0 < 1 + w * p := by positivity
  have hcast : (1 : ℂ) + (w : ℂ) * q = ((1 + w * p : ℝ) : ℂ) := by
    rw [← hqre]; push_cast; ring
  have hdenC : (1 : ℂ) + (w : ℂ) * q ≠ 0 := by
    rw [hcast]; exact_mod_cast hden.ne'
  have hcoef : (w : ℂ) / (1 + (w : ℂ) * q) = ((w / (1 + w * p) : ℝ) : ℂ) := by
    rw [hcast]; push_cast; ring
  rw [real_smul_eq_complex_smul w,
    _root_.Matrix.inv_add_smul_vecMulVec hA.isHermitian hAdet a _ hdenC,
    real_smul_eq_complex_smul (w / (1 + w * p)), hcoef]

/-- **Sherman–Morrison with a real weight, subtracted.**

For a positive definite `A` and a weight `w` small enough that the denominator
`1 - w · a* A⁻¹ a` stays positive,
`(A - w a a*)⁻¹ = A⁻¹ + w/(1 - w · a* A⁻¹ a) · (A⁻¹a)(A⁻¹a)*`.

The correction has a plus sign: removing mass from `A` makes its inverse larger. -/
theorem PosDef.inv_sub_smul_vecMulVec {A : Matrix n n ℂ} (hA : A.PosDef) (a : n → ℂ) {w : ℝ}
    (hden : 0 < 1 - w * RCLike.re (star a ⬝ᵥ (A⁻¹ *ᵥ a))) :
    (A - w • vecMulVec a (star a))⁻¹
      = A⁻¹ + (w / (1 - w * RCLike.re (star a ⬝ᵥ (A⁻¹ *ᵥ a))))
          • vecMulVec (A⁻¹ *ᵥ a) (star (A⁻¹ *ᵥ a)) := by
  have hAdet : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det _).1 hA.isUnit
  set q := star a ⬝ᵥ (A⁻¹ *ᵥ a) with hqdef
  set p := RCLike.re q with hp
  have hq0 : (0 : ℂ) ≤ q := hA.inv.posSemidef.dotProduct_mulVec_nonneg a
  have hqre : ((p : ℝ) : ℂ) = q := RCLike.ofReal_re_of_nonneg hq0
  have hcast : (1 : ℂ) + (-(w : ℂ)) * q = ((1 - w * p : ℝ) : ℂ) := by
    rw [← hqre]; push_cast; ring
  have hdenC : (1 : ℂ) + (-(w : ℂ)) * q ≠ 0 := by
    rw [hcast]; exact_mod_cast hden.ne'
  have hcoef : -((-(w : ℂ)) / (1 + (-(w : ℂ)) * q)) = ((w / (1 - w * p) : ℝ) : ℂ) := by
    rw [hcast]; push_cast; ring
  have hsub : A - w • vecMulVec a (star a) = A + (-(w : ℂ)) • vecMulVec a (star a) := by
    rw [real_smul_eq_complex_smul, neg_smul, ← sub_eq_add_neg]
  rw [hsub, _root_.Matrix.inv_add_smul_vecMulVec hA.isHermitian hAdet a _ hdenC,
    sub_eq_add_neg, ← neg_smul, hcoef, ← real_smul_eq_complex_smul]

/-- **Subtracting a rank-one matrix preserves positive definiteness** as long as the weight
is nonnegative and the Sherman–Morrison denominator stays positive, that is `w · a* A⁻¹ a < 1`.

The inverse of `A - w a a*` is a positive definite matrix plus a positive semidefinite one,
and a matrix whose inverse is positive definite is itself positive definite
(`Matrix.posDef_inv_iff`). -/
theorem PosDef.sub_smul_vecMulVec {A : Matrix n n ℂ} (hA : A.PosDef) (a : n → ℂ) {w : ℝ}
    (hw : 0 ≤ w) (hden : 0 < 1 - w * RCLike.re (star a ⬝ᵥ (A⁻¹ *ᵥ a))) :
    (A - w • vecMulVec a (star a)).PosDef := by
  refine Matrix.posDef_inv_iff.1 ?_
  rw [hA.inv_sub_smul_vecMulVec a hden]
  exact hA.inv.add_posSemidef
    ((posSemidef_vecMulVec_self_star _).smul (div_nonneg hw hden.le))

omit [DecidableEq n] in
/-- For a Hermitian `X`, the quadratic form of `J` at `X b` is the quadratic form of
`X J X` at `b`: `(X b)* J (X b) = b* (X J X) b`. -/
theorem dotProduct_conj_mulVec {X J : Matrix n n 𝕜} (hX : X.IsHermitian) (b : n → 𝕜) :
    star (X *ᵥ b) ⬝ᵥ (J *ᵥ (X *ᵥ b)) = star b ⬝ᵥ ((X * J * X) *ᵥ b) := by
  rw [star_mulVec, hX.eq, mulVec_mulVec, dotProduct_mulVec, vecMul_vecMul,
    ← dotProduct_mulVec, ← mul_assoc]

end Matrix
