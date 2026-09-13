/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
import Discretization.KieferWolfowitz.MixEstimate
import Discretization.KieferWolfowitz.NonDegenerate

/-!
# Maximising the determinant of the Gram matrix

The design that the Kiefer–Wolfowitz theorem produces is one whose Gram matrix has an almost
maximal determinant, a `D`-optimal design.  This file carries out that maximisation and
extracts its consequence.

The determinants form a set of real numbers,
`Discretization.KieferWolfowitz.detSet`, which is

* nonempty, and contains a positive number, because the functions are linearly independent
  (`Discretization.KieferWolfowitz.exists_design_posDef`), and
* bounded above, because the entries of every Gram matrix are bounded by `C²` and a
  determinant is bounded by its entries (`Matrix.norm_det_le_of_norm_apply_le`).

So the supremum `S` exists and is positive.  It need not be attained, which is why an `ε`
appears; a design whose determinant is close enough to `S` does just as well.  For such a
design `ϱ` with Gram matrix `G`, mixing in any point `y` with weight `α` multiplies the
determinant by `(1-α)^m (1 + α(t-1))`, where

`t = a(y)* G⁻¹ a(y)`,

by the matrix determinant lemma.  The mixture is a design again, so that factor cannot
exceed `S / det G`, and the real estimate of `Discretization.KieferWolfowitz.MixEstimate`
turns this into `t ≤ n + ε`, uniformly in `y`.  That uniform bound,
`Discretization.KieferWolfowitz.exists_design_quadForm_inv_le`, is the whole content of the
maximisation; everything after it is linear algebra.
-/

open Matrix
open scoped ComplexOrder MatrixOrder

namespace Discretization.KieferWolfowitz

variable {Ω ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The set of determinants of the Gram matrices of all designs.  The Kiefer–Wolfowitz
design is one whose determinant is nearly the supremum of this set. -/
noncomputable def detSet (a : Ω → ι → ℂ) : Set ℝ :=
  {d | ∃ (N : ℕ) (x : Fin N → Ω) (w : Fin N → ℝ), (∀ k, 0 ≤ w k) ∧ ∑ k, w k = 1 ∧
    RCLike.re (designGram a x w).det = d}

/-- **The determinants of Gram matrices are bounded above.**  The entries of every Gram
matrix are bounded by `C²`, and the Leibniz formula bounds a determinant by its entries. -/
theorem bddAbove_detSet (a : Ω → ι → ℂ) {C : ℝ} (h0 : 0 ≤ C) (hC : ∀ y i, ‖a y i‖ ≤ C) :
    BddAbove (detSet a) := by
  refine ⟨(Fintype.card ι).factorial * (C ^ 2) ^ Fintype.card ι, ?_⟩
  rintro d ⟨N, x, w, hw, hw1, rfl⟩
  calc RCLike.re (designGram a x w).det ≤ ‖(designGram a x w).det‖ := RCLike.re_le_norm _
    _ ≤ _ := Matrix.norm_det_le_of_norm_apply_le
        fun i j => norm_designGram_apply_le h0 hC hw hw1 i j

/-- **The supremum of the determinants is positive**, because a design with an invertible
Gram matrix exists. -/
theorem exists_pos_mem_detSet [Nonempty ι] (a : Ω → ι → ℂ)
    (hli : ∀ c : ι → ℂ, (∀ y, star c ⬝ᵥ a y = 0) → c = 0) :
    ∃ d ∈ detSet a, 0 < d := by
  obtain ⟨N, x, w, hw, hw1, hpd⟩ := exists_design_posDef a hli
  exact ⟨_, ⟨N, x, w, hw, hw1, rfl⟩, by
    simpa using RCLike.pos_iff.mp hpd.det_pos |>.1⟩

/-- **The Kiefer–Wolfowitz bound on the quadratic form.**

For linearly independent bounded functions and every `ε > 0` there is a design whose Gram
matrix `G` is invertible and satisfies

`a(y)* G⁻¹ a(y) ≤ n + ε`   for every point `y`,

where `n` is the number of functions.  The design is one whose determinant is close enough
to the supremum of all determinants; the bound is the first-order condition at that
approximate maximum, in the form supplied by
`Discretization.KieferWolfowitz.le_add_of_forall_mix_le`. -/
theorem exists_design_quadForm_inv_le [Nonempty ι] (a : Ω → ι → ℂ) {C : ℝ} (h0 : 0 ≤ C)
    (hC : ∀ y i, ‖a y i‖ ≤ C) (hli : ∀ c : ι → ℂ, (∀ y, star c ⬝ᵥ a y = 0) → c = 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (N : ℕ) (x : Fin N → Ω) (w : Fin N → ℝ), (∀ k, 0 ≤ w k) ∧ ∑ k, w k = 1 ∧
      (designGram a x w).PosDef ∧
      ∀ y, RCLike.re (star (a y) ⬝ᵥ ((designGram a x w)⁻¹ *ᵥ a y)) ≤ Fintype.card ι + ε := by
  classical
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (Fintype.card_ne_zero (α := ι))
  obtain ⟨d₀, hd₀mem, hd₀⟩ := exists_pos_mem_detSet a hli
  have hbdd := bddAbove_detSet a h0 hC
  have hne : (detSet a).Nonempty := ⟨d₀, hd₀mem⟩
  set S : ℝ := sSup (detSet a) with hS
  have hSpos : 0 < S := lt_of_lt_of_le hd₀ (le_csSup hbdd hd₀mem)
  -- how close to the supremum the design has to be
  set κ : ℝ := ε ^ 2 / (4 * ((m : ℝ) + 1) * ((m : ℝ) + ε)) with hκ
  have hκpos : 0 < κ := by
    have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    rw [hκ]; positivity
  have hlt : S / (1 + κ) < S := by
    rw [div_lt_iff₀ (by linarith)]
    nlinarith
  obtain ⟨d, ⟨N, x, w, hw, hw1, rfl⟩, hd⟩ := exists_lt_of_lt_csSup hne hlt
  -- the near-maximiser has an invertible Gram matrix
  have hdpos : 0 < RCLike.re (designGram a x w).det := by
    have : 0 < S / (1 + κ) := div_pos hSpos (by linarith)
    linarith
  have hpsd := designGram_posSemidef a x hw
  have hpd : (designGram a x w).PosDef := by
    refine hpsd.posDef_iff_det_ne_zero.mpr fun hzero => ?_
    rw [hzero] at hdpos
    simp at hdpos
  refine ⟨N, x, w, hw, hw1, hpd, fun y => ?_⟩
  -- mixing in `y` cannot raise the determinant above the supremum
  set t : ℝ := RCLike.re (star (a y) ⬝ᵥ ((designGram a x w)⁻¹ *ᵥ a y)) with ht
  have hmix : ∀ α : ℝ, 0 ≤ α → α < 1 →
      (1 - α) ^ m * (1 + α * (t - 1)) ≤ S / RCLike.re (designGram a x w).det := by
    intro α hα0 hα1
    have hdet : RCLike.re (designGram a (Fin.snoc x y) (snocWeights w α)).det
        = (1 - α) ^ m * (1 + α * (t - 1)) * RCLike.re (designGram a x w).det := by
      rw [designGram_snoc, PosDef.re_det_smul_add_smul_vecMulVec hpd (by linarith) α _ hm, ← ht]
      ring
    have hmem : RCLike.re (designGram a (Fin.snoc x y) (snocWeights w α)).det ∈ detSet a :=
      ⟨N + 1, Fin.snoc x y, snocWeights w α, snocWeights_nonneg hw hα0 hα1.le,
        sum_snocWeights hw1 α, rfl⟩
    rw [le_div_iff₀ hdpos, ← hdet]
    exact le_csSup hbdd hmem
  -- and the real estimate turns that into the bound on the quadratic form
  have hSlt : S < (1 + κ) * RCLike.re (designGram a x w).det := by
    rw [div_lt_iff₀ (by linarith : (0 : ℝ) < 1 + κ)] at hd
    linarith
  have hM : S / RCLike.re (designGram a x w).det - 1 < κ := by
    rw [sub_lt_iff_lt_add, div_lt_iff₀ hdpos]
    linarith
  have := le_add_of_forall_mix_le m hε (by rw [← hκ]; exact hM) hmix
  rw [hm]
  push_cast
  linarith

end Discretization.KieferWolfowitz
