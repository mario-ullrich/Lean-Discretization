/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
import Discretization.KieferWolfowitz.Compact

/-!
# Bounding the number of points

The design produced by the maximisation of the determinant is an arbitrary near-maximiser,
so nothing is known about how many points it uses.  Carathéodory's theorem removes that
defect after the fact: `Discretization.KieferWolfowitz.exists_design_card_le` replaces any
design by one with at most `2n² + 1` points and *the same Gram matrix*, and both forms of
the Kiefer–Wolfowitz theorem depend on the design only through its Gram matrix, since

`∑ₖ wₖ |f(xₖ)|² = c* G c`

for the coefficient vector `c` of `f`.  So the two theorems of this file are the earlier two
with the number of points bounded.

Nothing later needs the bound: the sparsification theorem, which is what the measure is
handed to next, accepts any finite and indeed any countable family of points.
-/

open Matrix
open scoped ComplexOrder MatrixOrder

namespace Discretization.KieferWolfowitz

variable {Ω ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **The Kiefer–Wolfowitz theorem with a bound on the number of points.**  At most
`2n² + 1` points are needed. -/
theorem exists_design_kieferWolfowitz_card_le [Nonempty ι] (a : Ω → ι → ℂ) {C : ℝ}
    (hC : ∀ y i, ‖a y i‖ ≤ C) (hli : ∀ c : ι → ℂ, (∀ y, star c ⬝ᵥ a y = 0) → c = 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (N : ℕ) (x : Fin N → Ω) (w : Fin N → ℝ), N ≤ 2 * Fintype.card ι ^ 2 + 1 ∧
      (∀ k, 0 ≤ w k) ∧ ∑ k, w k = 1 ∧ (designGram a x w).PosDef ∧
      ∀ (c : ι → ℂ) (y : Ω),
        ‖star c ⬝ᵥ a y‖ ^ 2 ≤ (Fintype.card ι + ε) * ∑ k, w k * ‖star c ⬝ᵥ a (x k)‖ ^ 2 := by
  obtain ⟨N, x, w, hw, hw1, hpd, hbound⟩ := exists_design_kieferWolfowitz a hC hli hε
  obtain ⟨M, x', w', hM, hw', hw'1, hgram⟩ := exists_design_card_le a x hw hw1
  refine ⟨M, x', w', hM, hw', hw'1, hgram ▸ hpd, fun c y => ?_⟩
  rw [← re_quadForm_designGram, hgram, re_quadForm_designGram]
  exact hbound c y

/-- **The Kiefer–Wolfowitz theorem on a compact domain, with a bound on the number of
points.**  At most `2n² + 1` points are needed, and the constant is the sharp `√n`. -/
theorem exists_design_kieferWolfowitz_of_compact_card_le [Nonempty ι] [TopologicalSpace Ω]
    [CompactSpace Ω] (a : Ω → ι → ℂ) (hcont : ∀ i, Continuous fun y => a y i)
    (hli : ∀ c : ι → ℂ, (∀ y, star c ⬝ᵥ a y = 0) → c = 0) :
    ∃ (N : ℕ) (x : Fin N → Ω) (w : Fin N → ℝ), N ≤ 2 * Fintype.card ι ^ 2 + 1 ∧
      (∀ k, 0 ≤ w k) ∧ ∑ k, w k = 1 ∧ (designGram a x w).PosDef ∧
      ∀ (c : ι → ℂ) (y : Ω),
        ‖star c ⬝ᵥ a y‖ ^ 2 ≤ Fintype.card ι * ∑ k, w k * ‖star c ⬝ᵥ a (x k)‖ ^ 2 := by
  obtain ⟨N, x, w, hw, hw1, hpd, hbound⟩ := exists_design_kieferWolfowitz_of_compact a hcont hli
  obtain ⟨M, x', w', hM, hw', hw'1, hgram⟩ := exists_design_card_le a x hw hw1
  refine ⟨M, x', w', hM, hw', hw'1, hgram ▸ hpd, fun c y => ?_⟩
  rw [← re_quadForm_designGram, hgram, re_quadForm_designGram]
  exact hbound c y

end Discretization.KieferWolfowitz
