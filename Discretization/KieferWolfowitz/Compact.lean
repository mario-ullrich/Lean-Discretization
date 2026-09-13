/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
import Discretization.KieferWolfowitz.ConvexHull
import Discretization.KieferWolfowitz.MainTheorem

/-!
# The sharp constant on a compact domain

For continuous functions on a compact domain the constant is exactly `√n`, with no `ε`.
The reason is that here the maximisation of the determinant has an actual maximiser, where
in general it has to settle for a near-maximiser: the rank-one matrices `a(y) a(y)*` form a
compact set, its convex hull is compact as well (`IsCompact.convexHull`), the determinant is
continuous, and every point of that hull is the Gram matrix of a design.

With the maximum attained, no mixture can increase the determinant at all, and
`Discretization.KieferWolfowitz.le_of_forall_mix_le_one` — the same real estimate as in the
general case, with the factor `1` — gives `a(y)* G⁻¹ a(y) ≤ n` on the nose.

The passage from that to the norm inequality is the one place that needs a *strict*
inequality, since `Matrix.PosDef.sub_smul_vecMulVec` asks for one.  So the bound is proved
with every constant `s > n` and the limit `s → n` is taken at the level of real numbers,
where it is harmless.
-/

open Matrix
open scoped ComplexOrder MatrixOrder

namespace Discretization.KieferWolfowitz

variable {Ω ι : Type*} [Fintype ι] [DecidableEq ι] [TopologicalSpace Ω]

omit [Fintype ι] [DecidableEq ι] in
/-- The map `y ↦ a(y) a(y)*` is continuous if the coordinate functions are. -/
theorem continuous_rankOne {a : Ω → ι → ℂ} (hcont : ∀ i, Continuous fun y => a y i) :
    Continuous fun y => vecMulVec (a y) (star (a y)) :=
  continuous_matrix fun i j => (hcont i).mul (continuous_star.comp (hcont j))

/-- **On a compact domain the determinant attains its maximum at a design.** -/
theorem exists_maximal_design [Nonempty ι] [CompactSpace Ω] (a : Ω → ι → ℂ)
    (hcont : ∀ i, Continuous fun y => a y i)
    (hli : ∀ c : ι → ℂ, (∀ y, star c ⬝ᵥ a y = 0) → c = 0) :
    ∃ (N : ℕ) (x : Fin N → Ω) (w : Fin N → ℝ), (∀ k, 0 ≤ w k) ∧ ∑ k, w k = 1 ∧
      (designGram a x w).PosDef ∧
      ∀ {M : ℕ} (x' : Fin M → Ω) (w' : Fin M → ℝ), (∀ k, 0 ≤ w' k) → ∑ k, w' k = 1 →
        RCLike.re (designGram a x' w').det ≤ RCLike.re (designGram a x w).det := by
  have hK : IsCompact (convexHull ℝ (rankOneSet a)) :=
    (isCompact_range (continuous_rankOne hcont)).convexHull
  obtain ⟨N₀, x₀, w₀, hw₀, hw₀1, hpd₀⟩ := exists_design_posDef a hli
  have hne : (convexHull ℝ (rankOneSet a)).Nonempty :=
    ⟨_, designGram_mem_convexHull a x₀ hw₀ hw₀1⟩
  have hcontdet : Continuous fun A : Matrix ι ι ℂ => RCLike.re A.det :=
    RCLike.continuous_re.comp (Continuous.matrix_det continuous_id)
  obtain ⟨A, hAmem, hAmax⟩ := hK.exists_isMaxOn hne hcontdet.continuousOn
  obtain ⟨N, x, w, hw, hw1, rfl⟩ := exists_design_of_mem_convexHull hAmem
  have hmax : ∀ {M : ℕ} (x' : Fin M → Ω) (w' : Fin M → ℝ), (∀ k, 0 ≤ w' k) → ∑ k, w' k = 1 →
      RCLike.re (designGram a x' w').det ≤ RCLike.re (designGram a x w).det :=
    fun x' w' h1 h2 => hAmax (designGram_mem_convexHull a x' h1 h2)
  have hpos : 0 < RCLike.re (designGram a x w).det :=
    lt_of_lt_of_le (by simpa using RCLike.pos_iff.mp hpd₀.det_pos |>.1) (hmax x₀ w₀ hw₀ hw₀1)
  refine ⟨N, x, w, hw, hw1, ?_, fun x' w' => hmax x' w'⟩
  refine (designGram_posSemidef a x hw).posDef_iff_det_ne_zero.mpr fun hzero => ?_
  rw [hzero] at hpos
  simp at hpos

/-- **The Kiefer–Wolfowitz theorem on a compact domain**, with the sharp constant.

For linearly independent continuous functions `a₁, …, a_n` on a compact space there is a
design with

`|f(y)|² ≤ n · ∑ₖ wₖ |f(xₖ)|²`

for every point `y` and every `f` in the span: the uniform norm is dominated by the `L₂`
norm of the design with the constant `√n`, and no `ε` is lost. -/
theorem exists_design_kieferWolfowitz_of_compact [Nonempty ι] [CompactSpace Ω]
    (a : Ω → ι → ℂ) (hcont : ∀ i, Continuous fun y => a y i)
    (hli : ∀ c : ι → ℂ, (∀ y, star c ⬝ᵥ a y = 0) → c = 0) :
    ∃ (N : ℕ) (x : Fin N → Ω) (w : Fin N → ℝ), (∀ k, 0 ≤ w k) ∧ ∑ k, w k = 1 ∧
      (designGram a x w).PosDef ∧
      ∀ (c : ι → ℂ) (y : Ω),
        ‖star c ⬝ᵥ a y‖ ^ 2 ≤ Fintype.card ι * ∑ k, w k * ‖star c ⬝ᵥ a (x k)‖ ^ 2 := by
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (Fintype.card_ne_zero (α := ι))
  obtain ⟨N, x, w, hw, hw1, hpd, hmax⟩ := exists_maximal_design a hcont hli
  have hdpos : 0 < RCLike.re (designGram a x w).det := by
    simpa using RCLike.pos_iff.mp hpd.det_pos |>.1
  refine ⟨N, x, w, hw, hw1, hpd, fun c y => ?_⟩
  -- the quadratic form of the inverse is bounded by `n`, with no slack
  have hq : RCLike.re (star (a y) ⬝ᵥ ((designGram a x w)⁻¹ *ᵥ a y)) ≤ Fintype.card ι := by
    rw [hm]
    push_cast
    refine le_of_forall_mix_le_one m fun α hα0 hα1 => ?_
    have hdet : RCLike.re (designGram a (Fin.snoc x y) (snocWeights w α)).det
        = (1 - α) ^ m * (1 + α * (RCLike.re (star (a y) ⬝ᵥ ((designGram a x w)⁻¹ *ᵥ a y)) - 1))
            * RCLike.re (designGram a x w).det := by
      rw [designGram_snoc, PosDef.re_det_smul_add_smul_vecMulVec hpd (by linarith) α _ hm]
      ring
    have hle := hmax (Fin.snoc x y) (snocWeights w α) (snocWeights_nonneg hw hα0 hα1.le)
      (sum_snocWeights hw1 α)
    rw [hdet] at hle
    exact le_of_mul_le_mul_right (by linarith) hdpos
  -- the norm inequality for every constant above `n`, then the limit
  set Q : ℝ := ∑ k, w k * ‖star c ⬝ᵥ a (x k)‖ ^ 2 with hQdef
  have hQ0 : 0 ≤ Q := Finset.sum_nonneg fun k _ => mul_nonneg (hw k) (sq_nonneg _)
  have key : ∀ s : ℝ, (Fintype.card ι : ℝ) < s → ‖star c ⬝ᵥ a y‖ ^ 2 ≤ s * Q := by
    intro s hs
    have hs0 : (0 : ℝ) < s := lt_of_le_of_lt (Nat.cast_nonneg _) hs
    have hle := vecMulVec_le_smul_of_quadForm_inv_le hpd (a y) hs hs0 hq
    have hquad := re_quadForm_le_of_le hle c
    rw [re_quadForm_designGram, Matrix.smul_mulVec, dotProduct_smul, RCLike.smul_re,
      re_dotProduct_vecMulVec_mulVec] at hquad
    rwa [inv_mul_le_iff₀ hs0] at hquad
  rcases eq_or_lt_of_le hQ0 with hQ | hQ
  · have h1 := key ((Fintype.card ι : ℝ) + 1) (by linarith)
    rw [← hQ] at h1 ⊢
    simpa using h1
  · refine le_of_forall_pos_le_add fun δ hδ => ?_
    have h1 := key ((Fintype.card ι : ℝ) + δ / Q) (by linarith [div_pos hδ hQ])
    calc ‖star c ⬝ᵥ a y‖ ^ 2 ≤ ((Fintype.card ι : ℝ) + δ / Q) * Q := h1
      _ = (Fintype.card ι : ℝ) * Q + δ := by
          rw [add_mul, div_mul_cancel₀ δ hQ.ne']

end Discretization.KieferWolfowitz
