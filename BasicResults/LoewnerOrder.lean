/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order

/-!
# Comparing matrices with multiples of the identity

Mathlib's Loewner order on `Matrix n n 𝕜` is `A ≤ B ↔ (B - A).PosSemidef`
(`Matrix.le_iff`), available after `open scoped MatrixOrder`.  Positivity of complex
numbers is itself scoped, so `open scoped ComplexOrder` is needed as well.

This file collects the elementary comparisons with multiples of the identity that the
potential-function argument uses over and over:

* `Matrix.IsHermitian.le_smul_one` — a Hermitian matrix is dominated by `c • 1` as soon as
  `c` dominates every eigenvalue;
* `Matrix.PosSemidef.le_trace_smul_one` — a positive semidefinite matrix is dominated by
  its own trace times the identity, since the trace is the sum of the (nonnegative)
  eigenvalues;
* `Matrix.smul_le_smul_of_nonneg` and `Matrix.re_trace_le_re_trace_of_le` — the order is
  compatible with multiplication by a nonnegative real and with taking traces.

All four are stated for a general `RCLike` field, and none of them is in Mathlib.
-/

open scoped ComplexOrder MatrixOrder
open Unitary

namespace Matrix

variable {𝕜 n : Type*} [RCLike 𝕜] [Fintype n]

/-- **A multiple of the identity dominating all eigenvalues dominates the matrix.**

If `A` is Hermitian and `c` is at least every eigenvalue of `A`, then `A ≤ c • 1` in the
Loewner order.  Diagonalizing `A = U D U*` turns the claim into the statement that the
diagonal matrix `c • 1 - D` has nonnegative entries, which is the hypothesis.

The bound `c` lives in `𝕜`; the eigenvalues are real and are compared after the canonical
embedding `ℝ → 𝕜`. -/
theorem IsHermitian.le_smul_one [DecidableEq n] {A : Matrix n n 𝕜} (hA : A.IsHermitian)
    {c : 𝕜} (hc : ∀ i, (hA.eigenvalues i : 𝕜) ≤ c) : A ≤ c • (1 : Matrix n n 𝕜) := by
  rw [Matrix.le_iff]
  have h : c • (1 : Matrix n n 𝕜) - A
      = conjStarAlgAut 𝕜 _ hA.eigenvectorUnitary
          (c • (1 : Matrix n n 𝕜) - diagonal (RCLike.ofReal ∘ hA.eigenvalues)) := by
    rw [map_sub, map_smul, map_one, ← hA.spectral_theorem]
  rw [h, conjStarAlgAut_apply,
    Matrix.IsUnit.posSemidef_star_right_conjugate_iff (isUnit_coe (U := hA.eigenvectorUnitary)),
    smul_one_eq_diagonal, diagonal_sub, posSemidef_diagonal_iff]
  intro i
  simpa [sub_nonneg] using hc i

/-- **A positive semidefinite matrix is dominated by its trace times the identity.**

For `A ≽ 0` we have `A ≤ (Tr A) • 1`.  Indeed the trace is the sum of the eigenvalues of
`A`, all of which are nonnegative, so every single eigenvalue is at most the trace; now
apply `Matrix.IsHermitian.le_smul_one`.

This is the crude bound `‖A‖ ≤ Tr A` for positive semidefinite `A`, written as a matrix
inequality. -/
theorem PosSemidef.le_trace_smul_one [DecidableEq n] {A : Matrix n n 𝕜} (hA : A.PosSemidef) :
    A ≤ A.trace • (1 : Matrix n n 𝕜) := by
  refine hA.isHermitian.le_smul_one fun i => ?_
  rw [hA.isHermitian.trace_eq_sum_eigenvalues, ← RCLike.ofReal_sum]
  exact_mod_cast Finset.single_le_sum (f := hA.isHermitian.eigenvalues)
    (fun j _ => hA.eigenvalues_nonneg j) (Finset.mem_univ i)

omit [Fintype n] in
/-- Multiplying both sides of a Loewner inequality by a nonnegative real preserves it. -/
theorem smul_le_smul_of_nonneg {A B : Matrix n n 𝕜} (h : A ≤ B) {c : ℝ} (hc : 0 ≤ c) :
    c • A ≤ c • B := by
  rw [Matrix.le_iff, ← smul_sub]
  exact (Matrix.le_iff.1 h).smul hc

omit [Fintype n] in
/-- Scaling a fixed positive semidefinite matrix by a larger factor gives a larger matrix:
`α ≤ β` implies `α • A ≤ β • A` for `A ≽ 0`. -/
theorem PosSemidef.smul_le_smul_of_le {A : Matrix n n 𝕜} (hA : A.PosSemidef) {α β : ℝ}
    (h : α ≤ β) : α • A ≤ β • A := by
  rw [Matrix.le_iff, ← sub_smul]
  exact hA.smul (by linarith)

/-- The trace is monotone for the Loewner order: `A ≤ B` forces `Re Tr A ≤ Re Tr B`,
because `Tr (B - A) ≥ 0` for a positive semidefinite difference. -/
theorem re_trace_le_re_trace_of_le {A B : Matrix n n 𝕜} (h : A ≤ B) :
    RCLike.re A.trace ≤ RCLike.re B.trace := by
  have h₁ : (0 : 𝕜) ≤ B.trace - A.trace := by
    simpa [trace_sub] using (Matrix.le_iff.1 h).trace_nonneg
  have h₂ : 0 ≤ RCLike.re (B.trace - A.trace) := (RCLike.nonneg_iff.mp h₁).1
  rw [map_sub] at h₂
  linarith

/-- The trace of a Hermitian matrix is real: it agrees with the image of its own real part.
This is the bridge used whenever a potential, defined as a real number, has to be fed back
into a matrix identity. -/
theorem IsHermitian.ofReal_re_trace {A : Matrix n n 𝕜} (hA : A.IsHermitian) :
    ((RCLike.re A.trace : ℝ) : 𝕜) = A.trace := by
  have h : (starRingEnd 𝕜) A.trace = A.trace := by
    rw [← RCLike.star_def, ← trace_conjTranspose, hA.eq]
  exact RCLike.conj_eq_iff_re.mp h

omit [Fintype n] in
/-- **Anything above a positive definite matrix is positive definite.**  Writing
`B = A + (B - A)` exhibits `B` as a positive definite plus a positive semidefinite matrix. -/
theorem PosDef.of_le {A B : Matrix n n 𝕜} (hA : A.PosDef) (h : A ≤ B) : B.PosDef := by
  have key : A + (B - A) = B := by abel
  have h₂ := hA.add_posSemidef (Matrix.le_iff.1 h)
  rwa [key] at h₂

section Inverse

open scoped Matrix.Norms.L2Operator

variable [DecidableEq n]

/-- **The inverse is antitone**, in the form the potential argument needs: if `A` is
positive definite and `A⁻¹ ≤ c • 1` for some `c > 0`, then `c⁻¹ • 1 ≤ A`.

Mathlib's `CStarAlgebra.inv_le_iff` proves this for the units of any C⋆-algebra with a
star ordering; matrices over `ℂ` form such an algebra once the `ℓ₂`-operator norm is in
scope (`Matrix.Norms.L2Operator`).  The only work here is to package `A` and `c • 1` as
units, the inverse of `c • 1` being `c⁻¹ • 1`. -/
theorem PosDef.smul_one_le_of_inv_le {A : Matrix n n ℂ} (hA : A.PosDef) {c : ℝ} (hc : 0 < c)
    (h : A⁻¹ ≤ c • (1 : Matrix n n ℂ)) : c⁻¹ • (1 : Matrix n n ℂ) ≤ A := by
  have hmul : ∀ a b : ℝ, a * b = 1 →
      (a • (1 : Matrix n n ℂ)) * (b • (1 : Matrix n n ℂ)) = 1 := fun a b hab => by
    simp [smul_smul, mul_comm b a, hab]
  let u : (Matrix n n ℂ)ˣ :=
    ⟨c • 1, c⁻¹ • 1, hmul c c⁻¹ (mul_inv_cancel₀ hc.ne'),
      hmul c⁻¹ c (inv_mul_cancel₀ hc.ne')⟩
  obtain ⟨v, hv⟩ := hA.isUnit
  have hv0 : (0 : Matrix n n ℂ) ≤ (v : Matrix n n ℂ) := hv ▸ hA.posSemidef.nonneg
  have hu0 : (0 : Matrix n n ℂ) ≤ (u : Matrix n n ℂ) :=
    (Matrix.PosSemidef.one.smul hc.le).nonneg
  have hvi : ((v⁻¹ : (Matrix n n ℂ)ˣ) : Matrix n n ℂ) = A⁻¹ := by
    rw [Matrix.coe_units_inv, hv]
  have key := (CStarAlgebra.inv_le_iff hv0 hu0).1 (by rw [hvi]; exact h)
  have hui : ((u⁻¹ : (Matrix n n ℂ)ˣ) : Matrix n n ℂ) = c⁻¹ • 1 := rfl
  rwa [hui, hv] at key

/-- **A positive definite matrix dominates the reciprocal of its lower potential.**

With the lower potential `Φ(A) = Re Tr A⁻¹` of the Batson–Spielman–Srivastava argument,
`Φ(A)⁻¹ • 1 ≤ A`.  Indeed `A⁻¹` is positive definite, hence bounded by its own trace times
the identity (`Matrix.PosSemidef.le_trace_smul_one`), and inverting reverses that
inequality.

In particular `Φ(A)⁻¹` is a lower bound for the smallest eigenvalue of `A`. -/
theorem PosDef.inv_re_trace_smul_one_le [Nonempty n] {A : Matrix n n ℂ} (hA : A.PosDef) :
    (RCLike.re (A⁻¹).trace)⁻¹ • (1 : Matrix n n ℂ) ≤ A := by
  have hAinv : (A⁻¹).PosDef := hA.inv
  have hpos : 0 < RCLike.re (A⁻¹).trace := (RCLike.pos_iff.mp hAinv.trace_pos).1
  refine hA.smul_one_le_of_inv_le hpos ?_
  have h := hAinv.posSemidef.le_trace_smul_one
  rwa [← hAinv.isHermitian.ofReal_re_trace, ← RCLike.real_smul_eq_coe_smul (K := ℂ)] at h

/-- **Shrinking a positive definite matrix by a small multiple of the identity keeps it
positive definite.**  The admissible range for the increment `δ` is exactly what the
potential allows: `δ < Φ(A)⁻¹ = (Re Tr A⁻¹)⁻¹`. -/
theorem PosDef.sub_smul_one [Nonempty n] {A : Matrix n n ℂ} (hA : A.PosDef) {δ : ℝ}
    (hδ : δ < (RCLike.re (A⁻¹).trace)⁻¹) : (A - δ • (1 : Matrix n n ℂ)).PosDef := by
  refine PosDef.of_le (A := ((RCLike.re (A⁻¹).trace)⁻¹ - δ) • (1 : Matrix n n ℂ))
    (Matrix.PosDef.one.smul (by linarith)) ?_
  rw [sub_smul]
  exact sub_le_sub_right hA.inv_re_trace_smul_one_le _

/-- **The inverse is antitone on positive definite matrices**: if `A ≤ B` then `B⁻¹ ≤ A⁻¹`.

This is `CStarAlgebra.inv_le_inv` for the C⋆-algebra of matrices over `ℂ`, with the two
matrices packaged as units. -/
theorem PosDef.inv_le_inv_of_le {A B : Matrix n n ℂ} (hA : A.PosDef) (hB : B.PosDef)
    (h : A ≤ B) : B⁻¹ ≤ A⁻¹ := by
  obtain ⟨u, hu⟩ := hA.isUnit
  obtain ⟨v, hv⟩ := hB.isUnit
  have h1 : (0 : Matrix n n ℂ) ≤ (u : Matrix n n ℂ) := hu ▸ hA.posSemidef.nonneg
  have h2 : (u : Matrix n n ℂ) ≤ (v : Matrix n n ℂ) := by rw [hu, hv]; exact h
  have key := CStarAlgebra.inv_le_inv h1 h2
  rwa [Matrix.coe_units_inv, Matrix.coe_units_inv, hu, hv] at key

end Inverse

end Matrix
