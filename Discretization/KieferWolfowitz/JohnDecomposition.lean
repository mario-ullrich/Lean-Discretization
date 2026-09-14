/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
import BasicResults.TraceInequalities
import Discretization.KieferWolfowitz.Compact

/-!
# John's decomposition of the identity, read off a design

A design carries more than the inequality of the Kiefer–Wolfowitz theorem: its Gram matrix
decomposes the identity.  Write `G = ∑ₖ wₖ a(xₖ) a(xₖ)*` for the Gram matrix and

`t(y) = a(y)* G⁻¹ a(y)`

for the variance function.  The two facts below are:

* `sum_weight_quadForm_inv_eq_card`: `∑ₖ wₖ t(xₖ) = n`, because `Tr (G⁻¹ G) = Tr 1 = n`.  The
  variance function has weighted average `n` for *every* design, whatever its points and
  weights;
* `sum_weight_smul_quadForm_inv_eq_self`: `∑ₖ wₖ ⟪a(xₖ), z⟫ a(xₖ) = z` for every `z`, in the
  inner product `⟪u, z⟫ = u* G⁻¹ z` that the ellipsoid of the design defines.  This is
  `G G⁻¹ = 1`, read as a sum over the design points.

Together, with `cₖ = wₖ t(xₖ)` and the normalised `uₖ = a(xₖ) / √(t(xₖ))`, they say

`cₖ ≥ 0`,   `∑ₖ cₖ = n`,   `∑ₖ cₖ ⟪uₖ, z⟫ uₖ = z` for every `z`,

which is **John's decomposition of the identity**: for a convex body whose maximal-volume
inscribed ellipsoid is the Euclidean ball, the identity is a positive combination of the
rank-one projections onto the contact points, with weights summing to the dimension.  Here
the body is the unit ball of the uniform norm on the span of `a₁, …, a_n`, the ellipsoid is
the one `G` defines, and the design points take the part of the contact points.

The two Kiefer–Wolfowitz theorems measure how good that contact is.  On a compact domain
`Discretization.KieferWolfowitz.exists_design_kieferWolfowitz_of_compact` gives `t(y) ≤ n`
everywhere, and then the average `∑ₖ wₖ t(xₖ) = n` forces `t(xₖ) = n` at every point of the
design: the `uₖ` lie on the sphere and this is John position exactly.  In general
`Discretization.KieferWolfowitz.exists_design_quadForm_inv_le` gives `t(y) ≤ n + ε` with the
same average, which is John position up to `ε`.  The decomposition itself is an identity, so
the `ε` stays where it is and no limit `ε → 0` enters.

For an arbitrary convex body, rather than the unit ball of a uniform norm, the theorem is
proved directly in the companion project Lean-SNumbers as `John.john_decomposition`
(`BasicResults/John.lean`, `github.com/mario-ullrich/Lean-SNumbers`), by a separation
argument in the space of self-adjoint operators.
-/

open Matrix
open scoped ComplexOrder MatrixOrder

namespace Discretization.KieferWolfowitz

variable {Ω ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **The variance function has weighted average `n`.**

For every design with invertible Gram matrix `G`,

`∑ₖ wₖ · a(xₖ)* G⁻¹ a(xₖ) = n`.

The left-hand side is `Tr (G⁻¹ G)`, because `G` is the weighted sum of the rank-one matrices
`a(xₖ) a(xₖ)*` and `Tr (G⁻¹ a a*) = a* G⁻¹ a`.  Nothing is assumed about the weights beyond
what makes `G` invertible: the identity holds for optimal and arbitrary designs alike, which
is why it turns the bound `t(y) ≤ n` of the compact Kiefer–Wolfowitz theorem into an
equality at every design point. -/
theorem sum_weight_quadForm_inv_eq_card (a : Ω → ι → ℂ) {N : ℕ} (x : Fin N → Ω)
    (w : Fin N → ℝ) (hG : (designGram a x w).PosDef) :
    ∑ k, w k * RCLike.re (star (a (x k)) ⬝ᵥ ((designGram a x w)⁻¹ *ᵥ a (x k)))
      = Fintype.card ι := by
  have hunit : IsUnit (designGram a x w).det := (Matrix.isUnit_iff_isUnit_det _).1 hG.isUnit
  -- the same identity over `ℂ`, obtained by taking the trace of `G⁻¹ G = 1`
  have htr : ∑ k, w k • (star (a (x k)) ⬝ᵥ ((designGram a x w)⁻¹ *ᵥ a (x k)))
      = (Fintype.card ι : ℂ) := by
    have hone := congrArg Matrix.trace (Matrix.nonsing_inv_mul _ hunit)
    rw [Matrix.trace_one] at hone
    rw [← hone, designGram, Matrix.mul_sum, Matrix.trace_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Matrix.mul_smul, Matrix.trace_smul, Matrix.trace_mul_vecMulVec_self_star]
  have := congrArg RCLike.re htr
  rw [map_sum] at this
  simpa [RCLike.smul_re] using this

omit [DecidableEq ι] in
/-- **A Gram matrix acts as the weighted sum of its rank-one terms.**

`G c = ∑ₖ wₖ · ⟪a(xₖ), c⟫ · a(xₖ)` with the Euclidean inner product `⟪u, c⟫ = u* c`.  This is
the definition of `designGram` applied to a vector, and it is what turns `G G⁻¹ = 1` into a
decomposition of the identity. -/
theorem designGram_mulVec (a : Ω → ι → ℂ) {N : ℕ} (x : Fin N → Ω) (w : Fin N → ℝ)
    (c : ι → ℂ) :
    designGram a x w *ᵥ c = ∑ k, ((w k : ℂ) * (star (a (x k)) ⬝ᵥ c)) • a (x k) := by
  rw [designGram, Matrix.sum_mulVec]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Matrix.smul_mulVec, Matrix.vecMulVec_mulVec]
  ext i
  simp [Complex.real_smul, mul_comm, mul_left_comm]

/-- **The identity decomposes over the points of a design.**

For every design with invertible Gram matrix `G` and every vector `z`,

`∑ₖ wₖ · ⟪a(xₖ), z⟫ · a(xₖ) = z`,   where `⟪u, z⟫ = u* G⁻¹ z`.

This is `G (G⁻¹ z) = z` with `G = ∑ₖ wₖ a(xₖ) a(xₖ)*` expanded, and the inner product is the
one the ellipsoid of the design defines.  It is the shape of John's decomposition of the
identity; `sum_weight_quadForm_inv_eq_card` supplies the weights, which sum to `n` after the
`a(xₖ)` are normalised. -/
theorem sum_weight_smul_quadForm_inv_eq_self (a : Ω → ι → ℂ) {N : ℕ} (x : Fin N → Ω)
    (w : Fin N → ℝ) (hG : (designGram a x w).PosDef) (z : ι → ℂ) :
    ∑ k, ((w k : ℂ) * (star (a (x k)) ⬝ᵥ ((designGram a x w)⁻¹ *ᵥ z))) • a (x k) = z := by
  have hunit : IsUnit (designGram a x w).det := (Matrix.isUnit_iff_isUnit_det _).1 hG.isUnit
  rw [← designGram_mulVec, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hunit,
    Matrix.one_mulVec]

end Discretization.KieferWolfowitz
