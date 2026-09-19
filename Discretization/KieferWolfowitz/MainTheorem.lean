/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
import Discretization.KieferWolfowitz.DetMax

/-!
# The Kiefer–Wolfowitz theorem

For an `n`-dimensional space of bounded functions on an arbitrary set and every `ε > 0`
there are finitely many points `x₁, …, x_N` with nonnegative weights summing to one such
that

`|f(y)|² ≤ (n + ε) · ∑ₖ wₖ |f(xₖ)|²`   for every `f` in the space and every point `y`,

that is, the uniform norm on the space is dominated by the `L₂` norm of the finitely
supported measure `∑ₖ wₖ δ(xₖ)`, with the constant `√(n+ε)`.  This is Proposition 9 of
*Sampling projections in the uniform norm* by Krieg, Pozharska, Ullrich and Ullrich.

The bound on the quadratic form of the inverse Gram matrix,
`Discretization.KieferWolfowitz.exists_design_quadForm_inv_le`, does all the work.  What is
left is to turn

`a(y)* G⁻¹ a(y) ≤ n + ε`   into   `a(y) a(y)* ≤ (n+ε) · G`,

and the project already has that step: subtracting a rank-one matrix with a weight small
enough to keep the Sherman–Morrison denominator positive preserves positive definiteness
(`Matrix.PosDef.sub_smul_vecMulVec`).  To make the denominator *strictly* positive the
design is taken with `ε/2` in place of `ε`, which costs nothing since `ε` is arbitrary.
Evaluating the resulting Loewner inequality at a coefficient vector
(`Discretization.re_quadForm_le_of_le`) gives the theorem.
-/

open Matrix
open scoped ComplexOrder MatrixOrder

namespace Discretization.KieferWolfowitz

variable {Ω ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **The rank-one matrix is dominated by the Gram matrix.**

If the quadratic form of `G⁻¹` at `u` is at most `t`, and `s > t`, then `u u* ≤ s · G`.
The strict inequality `t < s` is what makes the Sherman–Morrison denominator positive. -/
theorem vecMulVec_le_smul_of_quadForm_inv_le {G : Matrix ι ι ℂ} (hG : G.PosDef) (u : ι → ℂ)
    {t s : ℝ} (hts : t < s) (hs : 0 < s) (ht : RCLike.re (star u ⬝ᵥ (G⁻¹ *ᵥ u)) ≤ t) :
    s⁻¹ • vecMulVec u (star u) ≤ G := by
  have hden : 0 < 1 - s⁻¹ * RCLike.re (star u ⬝ᵥ (G⁻¹ *ᵥ u)) := by
    have h1 : s⁻¹ * RCLike.re (star u ⬝ᵥ (G⁻¹ *ᵥ u)) ≤ s⁻¹ * t :=
      mul_le_mul_of_nonneg_left ht (by positivity)
    have h2 : s⁻¹ * t < 1 := by rw [inv_mul_eq_div, div_lt_one hs]; exact hts
    linarith
  exact Matrix.le_iff.2 (hG.sub_smul_vecMulVec u (by positivity) hden).posSemidef

/-- **The Kiefer–Wolfowitz theorem.**

For linearly independent bounded functions `a₁, …, a_n` on an arbitrary set and every
`ε > 0` there is a finitely supported probability measure `∑ₖ wₖ δ(xₖ)` with

`|f(y)|² ≤ (n + ε) · ∑ₖ wₖ |f(xₖ)|²`

for every point `y` and every function `f(y) = ⟪c, a(y)⟫` in the span.  Linear independence
is used in the form `∀ c, (∀ y, ⟪c, a(y)⟫ = 0) → c = 0`, which
`Discretization.KieferWolfowitz.linearIndependent_iff_forall_star` identifies with
`LinearIndependent ℂ`, and boundedness in the form of one constant `C` bounding all the
values. -/
theorem exists_design_kieferWolfowitz [Nonempty ι] (a : Ω → ι → ℂ) {C : ℝ}
    (hC : ∀ y i, ‖a y i‖ ≤ C) (hli : ∀ c : ι → ℂ, (∀ y, star c ⬝ᵥ a y = 0) → c = 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (N : ℕ) (x : Fin N → Ω) (w : Fin N → ℝ), (∀ k, 0 ≤ w k) ∧ ∑ k, w k = 1 ∧
      (designGram a x w).PosDef ∧
      ∀ (c : ι → ℂ) (y : Ω),
        ‖star c ⬝ᵥ a y‖ ^ 2 ≤ (Fintype.card ι + ε) * ∑ k, w k * ‖star c ⬝ᵥ a (x k)‖ ^ 2 := by
  have : Nonempty Ω := nonempty_of_separating hli
  have h0 : 0 ≤ C := le_trans (norm_nonneg _) (hC (Classical.arbitrary Ω) (Classical.arbitrary ι))
  obtain ⟨N, x, w, hw, hw1, hpd, hq⟩ :=
    exists_design_quadForm_inv_le a h0 hC hli (half_pos hε)
  refine ⟨N, x, w, hw, hw1, hpd, fun c y => ?_⟩
  have hs : (0 : ℝ) < Fintype.card ι + ε := by positivity
  -- the Loewner bound `a(y) a(y)* ≤ (n+ε) G`, evaluated at the coefficient vector `c`
  have hle := vecMulVec_le_smul_of_quadForm_inv_le hpd (a y) (by linarith) hs (hq y)
  have hquad := re_quadForm_le_of_le hle c
  rw [re_quadForm_designGram, Matrix.smul_mulVec, dotProduct_smul, RCLike.smul_re,
    re_dotProduct_vecMulVec_mulVec] at hquad
  rwa [inv_mul_le_iff₀ hs] at hquad

end Discretization.KieferWolfowitz
