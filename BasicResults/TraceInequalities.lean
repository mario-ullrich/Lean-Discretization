/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
import BasicResults.LoewnerOrder
import Mathlib.Analysis.InnerProductSpace.Positive

/-!
# Traces of products of positive semidefinite matrices

Facts about the bilinear form `(P, Q) ↦ Tr (P * Q)` on Hermitian matrices, none of them in
Mathlib, all of them needed for the potential-function argument:

* `Matrix.PosSemidef.trace_mul_nonneg`: `Tr (P * Q) ≥ 0` for positive semidefinite `P`
  and `Q`, with the strict version `Matrix.PosDef.re_trace_mul_pos` for positive definite
  matrices;
* `Matrix.IsHermitian.ofReal_re_trace_mul`: `Tr (P * Q)` is real for Hermitian `P` and `Q`,
  even though the product itself need not be Hermitian;
* `Matrix.PosSemidef.norm_trace_mul_sq_le`: the **Cauchy–Schwarz inequality**
  `|Tr (Z * Y)|² ≤ Re Tr Y · Re Tr (Z * Y * Zᴴ)` for the semi-inner product
  `⟪P, Q⟫ = Tr (Q * Y * Pᴴ)` attached to a positive semidefinite `Y`.

The file also records that a rank-one matrix is bounded by its norm,
`u u* ≤ ‖u‖² • 1` (`Matrix.vecMulVec_le_norm_sq_smul_one`).

The proofs of the first two rest on the representation of a positive semidefinite matrix as
a sum of rank-one matrices `v v*` (`Matrix.posSemidef_iff_eq_sum_vecMulVec`), for which
`Matrix.trace_mul_vecMulVec_self_star` computes the trace.  The Cauchy–Schwarz inequality is
Mathlib's `InnerProductSpace.Core.inner_mul_inner_self_le` for the semi-inner product above,
which is set up on the spot.
-/

open scoped ComplexOrder MatrixOrder

namespace Matrix

variable {𝕜 n : Type*} [RCLike 𝕜] [Fintype n]

/-- The trace of `P` against a rank-one matrix is a quadratic form:
`Tr (P * a a*) = a* P a`. -/
theorem trace_mul_vecMulVec_self_star (P : Matrix n n 𝕜) (a : n → 𝕜) :
    (P * vecMulVec a (star a)).trace = star a ⬝ᵥ (P *ᵥ a) := by
  rw [mul_vecMulVec, trace_vecMulVec, dotProduct_comm]

/-- **The trace of a product of two positive semidefinite matrices is nonnegative.**

Writing `Q = ∑ vᵢ vᵢ*` as a sum of rank-one matrices turns `Tr (P * Q)` into the sum of the
quadratic forms `vᵢ* P vᵢ`, all of which are nonnegative. -/
theorem PosSemidef.trace_mul_nonneg {P Q : Matrix n n 𝕜} (hP : P.PosSemidef)
    (hQ : Q.PosSemidef) : 0 ≤ (P * Q).trace := by
  obtain ⟨m, v, rfl⟩ := posSemidef_iff_eq_sum_vecMulVec.mp hQ
  rw [Finset.mul_sum, trace_sum]
  refine Finset.sum_nonneg fun i _ => ?_
  rw [trace_mul_vecMulVec_self_star]
  exact hP.dotProduct_mulVec_nonneg _

/-- The real part of `Tr (P * Q)` is nonnegative for positive semidefinite `P` and `Q`. -/
theorem PosSemidef.re_trace_mul_nonneg {P Q : Matrix n n 𝕜} (hP : P.PosSemidef)
    (hQ : Q.PosSemidef) : 0 ≤ RCLike.re (P * Q).trace :=
  (RCLike.nonneg_iff.mp (hP.trace_mul_nonneg hQ)).1

/-- **The trace of a product of two positive definite matrices is positive**, provided the
index type is nonempty.

The decomposition `Q = ∑ vᵢ vᵢ*` has at least one nonzero vector (otherwise `Q = 0`, which a
positive definite matrix is not), and the corresponding quadratic form `vᵢ* P vᵢ` is
strictly positive. -/
theorem PosDef.re_trace_mul_pos [Nonempty n] {P Q : Matrix n n 𝕜} (hP : P.PosDef)
    (hQ : Q.PosDef) : 0 < RCLike.re (P * Q).trace := by
  obtain ⟨m, v, hv⟩ := posSemidef_iff_eq_sum_vecMulVec.mp hQ.posSemidef
  have hQ0 : Q ≠ 0 := by
    intro h
    obtain ⟨i⟩ := ‹Nonempty n›
    have hd := hQ.diag_pos (i := i)
    rw [h] at hd
    simp at hd
  obtain ⟨i₀, hi₀⟩ : ∃ i, v i ≠ 0 := by
    by_contra hcon
    simp only [not_exists, not_not] at hcon
    exact hQ0 (by simp [hv, hcon])
  have hre : RCLike.re (P * Q).trace
      = ∑ i, RCLike.re (star (v i) ⬝ᵥ (P *ᵥ v i)) := by
    rw [hv, Finset.mul_sum, trace_sum, map_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [trace_mul_vecMulVec_self_star]
  rw [hre]
  refine Finset.sum_pos' (fun i _ => hP.posSemidef.re_dotProduct_nonneg _) ⟨i₀, ?_, ?_⟩
  · exact Finset.mem_univ i₀
  · exact hP.re_dotProduct_pos hi₀

/-- **The trace of a product of two Hermitian matrices is real.**

The product `P * Q` of two Hermitian matrices is in general not Hermitian, but its trace
still equals its own conjugate, because `Tr ((P * Q)ᴴ) = Tr (Q * P) = Tr (P * Q)`. -/
theorem IsHermitian.ofReal_re_trace_mul {P Q : Matrix n n 𝕜} (hP : P.IsHermitian)
    (hQ : Q.IsHermitian) : ((RCLike.re (P * Q).trace : ℝ) : 𝕜) = (P * Q).trace := by
  refine RCLike.conj_eq_iff_re.mp ?_
  rw [← RCLike.star_def, ← trace_conjTranspose, conjTranspose_mul, hP.eq, hQ.eq, trace_mul_comm]

/-- **Cauchy–Schwarz inequality for the trace.**

A positive semidefinite matrix `Y` induces the semi-inner product
`⟪P, Q⟫ = Tr (Q * Y * Pᴴ)` on matrices.  Cauchy–Schwarz applied to the pair `1`, `Z` reads
`|Tr (Z * Y)|² ≤ Re Tr Y · Re Tr (Z * Y * Zᴴ)`.

No commutation of `Y` and `Z` is required.  For Hermitian `Z` the right-hand side is
`Tr Y · Tr (Y * Z * Z)`, see `Matrix.PosSemidef.re_trace_mul_sq_le`. -/
theorem PosSemidef.norm_trace_mul_sq_le [DecidableEq n] {Y : Matrix n n 𝕜} (hY : Y.PosSemidef)
    (Z : Matrix n n 𝕜) :
    ‖(Z * Y).trace‖ ^ 2 ≤ RCLike.re Y.trace * RCLike.re (Z * Y * Zᴴ).trace := by
  let core : PreInnerProductSpace.Core 𝕜 (Matrix n n 𝕜) :=
    { inner := fun x y => (y * Y * xᴴ).trace
      conj_inner_symm := fun _ _ => by
        simp only [mul_assoc, starRingEnd_apply, ← trace_conjTranspose, conjTranspose_mul,
          conjTranspose_conjTranspose, hY.isHermitian.eq]
      re_inner_nonneg := fun x =>
        (RCLike.nonneg_iff.mp (hY.mul_mul_conjTranspose_same x).trace_nonneg).1
      add_left := by simp [mul_add]
      smul_left := by simp }
  have key : ‖(Z * Y * (1 : Matrix n n 𝕜)ᴴ).trace‖ * ‖((1 : Matrix n n 𝕜) * Y * Zᴴ).trace‖
      ≤ RCLike.re ((1 : Matrix n n 𝕜) * Y * (1 : Matrix n n 𝕜)ᴴ).trace *
        RCLike.re (Z * Y * Zᴴ).trace :=
    InnerProductSpace.Core.inner_mul_inner_self_le (𝕜 := 𝕜) (1 : Matrix n n 𝕜) Z
  have hstar : star ((Z * Y).trace) = (Y * Zᴴ).trace := by
    rw [← trace_conjTranspose, conjTranspose_mul, hY.isHermitian.eq]
  calc ‖(Z * Y).trace‖ ^ 2 = ‖(Z * Y).trace‖ * ‖(Y * Zᴴ).trace‖ := by
        rw [← hstar, norm_star, sq]
    _ ≤ RCLike.re Y.trace * RCLike.re (Z * Y * Zᴴ).trace := by
        simpa using key

/-- The form of Cauchy–Schwarz used for the lower potential: for a positive semidefinite `Y`
and a Hermitian `Z`,
`(Re Tr (Y * Z))² ≤ Re Tr Y · Re Tr (Y * Z * Z)`. -/
theorem PosSemidef.re_trace_mul_sq_le [DecidableEq n] {Y Z : Matrix n n 𝕜} (hY : Y.PosSemidef)
    (hZ : Z.IsHermitian) :
    (RCLike.re (Y * Z).trace) ^ 2 ≤ RCLike.re Y.trace * RCLike.re (Y * Z * Z).trace := by
  have h₁ : RCLike.re (Y * Z).trace ^ 2 ≤ ‖(Z * Y).trace‖ ^ 2 := by
    rw [trace_mul_comm Y Z]
    exact sq_le_sq' (neg_le_of_abs_le (RCLike.abs_re_le_norm _))
      (le_of_abs_le (RCLike.abs_re_le_norm _))
  refine h₁.trans ?_
  have h₂ : (Z * Y * Zᴴ).trace = (Y * Z * Z).trace := by
    rw [hZ.eq, mul_assoc, trace_mul_comm]
  rw [← h₂]
  exact hY.norm_trace_mul_sq_le Z

/-- The trace of a rank-one matrix is the squared euclidean norm of its vector. -/
theorem trace_vecMulVec_self_star (u : n → ℂ) :
    (vecMulVec u (star u)).trace = ((∑ k, ‖u k‖ ^ 2 : ℝ) : ℂ) := by
  rw [trace_vecMulVec, dotProduct]
  push_cast
  exact Finset.sum_congr rfl fun k _ => by
    rw [Pi.star_apply, RCLike.star_def, RCLike.mul_conj]
    norm_cast

/-- **A rank-one matrix is bounded by its squared norm times the identity.**  This is the
crude bound used when the effective dimension of the second family is too small for the
potential argument. -/
theorem vecMulVec_le_norm_sq_smul_one [DecidableEq n] (u : n → ℂ) :
    vecMulVec u (star u) ≤ (∑ k, ‖u k‖ ^ 2) • (1 : Matrix n n ℂ) := by
  have h := PosSemidef.le_trace_smul_one (posSemidef_vecMulVec_self_star u)
  rwa [trace_vecMulVec_self_star, ← real_smul_eq_complex_smul] at h

end Matrix
