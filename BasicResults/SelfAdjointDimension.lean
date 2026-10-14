/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import Mathlib.Algebra.Star.Module
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose

/-!
# The real dimension of the self-adjoint elements

In a complex vector space `A` with a compatible star operation, every element splits uniquely
as `h + i k` with `h` and `k` self-adjoint, namely `h = (x + x*)/2` and `k = (x - x*)/(2i)`.
So the self-adjoint elements form a real vector space of half the real dimension of `A`,
which is the complex dimension of `A`:

`dim_ℝ {x : x* = x} = dim_ℂ A`   (`finrank_selfAdjoint_submodule`).

For matrices this says that the Hermitian `m × m` matrices form a real vector space of
dimension `m²` (`Matrix.finrank_selfAdjoint_submodule`).

Mathlib splits every element into a self-adjoint and a skew-adjoint part
(`StarModule.decomposeProdAdjoint`); the step added here is that multiplication by `i` maps
the self-adjoint elements onto the skew-adjoint ones (`selfAdjointEquivSkewAdjoint`), so the
two parts have the same dimension.

This is what bounds the number of points of a Kiefer–Wolfowitz design by `m² + 1`: the Gram
matrices of designs are Hermitian, and Carathéodory's theorem in a real vector space of
dimension `m²` needs at most `m² + 1` points.
-/

@[expose] public section

open Module

variable {A : Type*} [AddCommGroup A] [StarAddMonoid A] [Module ℝ A] [Module ℂ A]
  [IsScalarTower ℝ ℂ A] [StarModule ℝ A] [StarModule ℂ A]

/-- **Multiplication by `i` turns self-adjoint elements into skew-adjoint ones**, as a real
linear equivalence: for `h* = h` one has `(i h)* = -i h* = -(i h)`, and multiplication by
`-i` is the inverse. -/
def selfAdjointEquivSkewAdjoint : selfAdjoint A ≃ₗ[ℝ] skewAdjoint A where
  toFun h := ⟨Complex.I • (h : A), by
    rw [skewAdjoint.mem_iff, star_smul, selfAdjoint.mem_iff.1 h.2, Complex.star_def,
      Complex.conj_I, neg_smul]⟩
  invFun k := ⟨(-Complex.I) • (k : A), by
    rw [selfAdjoint.mem_iff, star_smul, skewAdjoint.mem_iff.1 k.2, star_neg, Complex.star_def,
      Complex.conj_I, neg_neg, smul_neg, neg_smul]⟩
  map_add' h h' := Subtype.ext (smul_add _ _ _)
  map_smul' r h := Subtype.ext (smul_comm _ _ _)
  left_inv h := Subtype.ext <| by
    simp only [smul_smul, neg_mul, Complex.I_mul_I, neg_neg, one_smul]
  right_inv k := Subtype.ext <| by
    simp only [smul_smul, mul_neg, Complex.I_mul_I, neg_neg, one_smul]

/-- **The self-adjoint elements of a complex star module have real dimension `dim_ℂ A`.**

The real vector space `A` is the product of its self-adjoint and its skew-adjoint part, the
two parts are isomorphic through multiplication by `i`, and `dim_ℝ A = 2 dim_ℂ A`. -/
theorem finrank_selfAdjoint_submodule [FiniteDimensional ℂ A] :
    finrank ℝ (selfAdjoint.submodule ℝ A) = finrank ℂ A := by
  let : Invertible (2 : ℝ) := invertibleOfNonzero two_ne_zero
  have : FiniteDimensional ℝ A := FiniteDimensional.trans ℝ ℂ A
  -- the submodule and the subgroup of self-adjoint elements are the same real vector space
  let e : selfAdjoint.submodule ℝ A ≃ₗ[ℝ] selfAdjoint A :=
    { toFun := fun x => ⟨x.1, x.2⟩
      invFun := fun x => ⟨x.1, x.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have : Module.Finite ℝ (selfAdjoint A) := Module.Finite.equiv e
  have : Module.Finite ℝ (skewAdjoint A) := Module.Finite.equiv selfAdjointEquivSkewAdjoint
  -- `A` splits into the two parts, which have the same dimension
  have hsplit := (StarModule.decomposeProdAdjoint ℝ A).finrank_eq
  rw [Module.finrank_prod, ← selfAdjointEquivSkewAdjoint.finrank_eq, ← e.finrank_eq]
    at hsplit
  -- and the real dimension of `A` is twice its complex dimension
  have hreal : finrank ℝ A = 2 * finrank ℂ A := by
    rw [← Module.finrank_mul_finrank ℝ ℂ A, Complex.finrank_real_complex]
  omega

/-- **The Hermitian `m × m` matrices form a real vector space of dimension `m²`.** -/
theorem Matrix.finrank_selfAdjoint_submodule (ι : Type*) [Fintype ι] :
    finrank ℝ (selfAdjoint.submodule ℝ (Matrix ι ι ℂ)) = Fintype.card ι ^ 2 := by
  rw [_root_.finrank_selfAdjoint_submodule, Module.finrank_matrix, Module.finrank_self]
  ring
