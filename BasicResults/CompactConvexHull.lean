/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
import Mathlib.Analysis.Convex.Caratheodory
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.Convex.Topology
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

/-!
# The convex hull of a compact set is compact

In finite dimension the convex hull of a compact set is again compact.  Mathlib has the
case of a *finite* set (`Set.Finite.isCompact_convexHull`) and `TotallyBounded.convexHull`,
which gives total boundedness of the hull and so compactness only of its *closure*; the
point here is that in finite dimension the hull is already closed.

The proof is Carathéodory's theorem: every point of the hull is a convex combination of at
most `finrank ℝ E + 1` affinely independent points of `s`, so the hull is the image of the
compact set `stdSimplex × s^(finrank+1)` under the continuous map `(w, z) ↦ ∑ᵢ wᵢ • zᵢ`.
Only continuity of the vector space operations is used, so no norm is required and the
statement applies to spaces such as `Matrix ι ι ℂ`, whose several norms are all scoped.

This is the one ingredient the `ε = 0` case of the Kiefer–Wolfowitz theorem needs beyond
what the general case uses: on a compact domain the maximum of the determinant is attained,
and attaining it removes the `ε`.
-/

open Set

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [ContinuousAdd E]
  [ContinuousSMul ℝ E] [FiniteDimensional ℝ E]

/-- **The convex hull of a compact set is compact**, in a finite-dimensional real
topological vector space. -/
theorem IsCompact.convexHull {s : Set E} (hs : IsCompact s) : IsCompact (convexHull ℝ s) := by
  classical
  rcases Set.eq_empty_or_nonempty s with rfl | ⟨x₀, hx₀⟩
  · simp only [convexHull_empty]; exact isCompact_empty
  have hK : IsCompact ((stdSimplex ℝ (Fin (Module.finrank ℝ E + 1))) ×ˢ
      Set.univ.pi fun _ : Fin (Module.finrank ℝ E + 1) => s) :=
    IsCompact.prod (isCompact_stdSimplex ℝ (Fin (Module.finrank ℝ E + 1)))
      (isCompact_univ_pi fun _ => hs)
  have himg : _root_.convexHull ℝ s =
      (fun p : (Fin (Module.finrank ℝ E + 1) → ℝ) × (Fin (Module.finrank ℝ E + 1) → E) =>
          ∑ i, p.1 i • p.2 i) ''
        ((stdSimplex ℝ (Fin (Module.finrank ℝ E + 1))) ×ˢ
          Set.univ.pi fun _ : Fin (Module.finrank ℝ E + 1) => s) := by
    apply Set.Subset.antisymm
    · intro x hx
      obtain ⟨ι, hfin, z, w, hzs, hai, hw0, hw1, hxeq⟩ :=
        eq_pos_convex_span_of_mem_convexHull hx
      let : Fintype ι := hfin
      -- Carathéodory: affinely independent families have at most `finrank + 1` members.
      have hcard : Fintype.card ι ≤ Module.finrank ℝ E + 1 :=
        le_trans hai.card_le_finrank_succ (Nat.add_le_add_right (Submodule.finrank_le _) 1)
      -- embed the index type into `Fin (finrank + 1)`
      set f : ι → Fin (Module.finrank ℝ E + 1) :=
        fun j => Fin.castLE hcard ((Fintype.equivFin ι) j) with hf
      have hfinj : Function.Injective f := by
        intro a b hab
        have h2 := congrArg Fin.val hab
        simp only [hf, Fin.val_castLE] at h2
        exact (Fintype.equivFin ι).injective (Fin.ext h2)
      -- pad the family by weight-0 copies of a fixed point of `s`
      set w' : Fin (Module.finrank ℝ E + 1) → ℝ :=
        fun i => if h : ∃ j, f j = i then w h.choose else 0 with hw'
      set z' : Fin (Module.finrank ℝ E + 1) → E :=
        fun i => if h : ∃ j, f j = i then z h.choose else x₀ with hz'
      have hchoose : ∀ (j : ι) (h : ∃ j', f j' = f j), h.choose = j :=
        fun j h => hfinj h.choose_spec
      have hw'f : ∀ j, w' (f j) = w j := fun j => by
        simp only [hw']
        rw [dif_pos ⟨j, rfl⟩, hchoose j ⟨j, rfl⟩]
      have hz'f : ∀ j, z' (f j) = z j := fun j => by
        simp only [hz']
        rw [dif_pos ⟨j, rfl⟩, hchoose j ⟨j, rfl⟩]
      have hw'zero : ∀ i, i ∉ Finset.univ.image f → w' i = 0 := fun i hi => by
        simp only [hw']
        exact dif_neg fun h =>
          hi (Finset.mem_image.mpr ⟨h.choose, Finset.mem_univ _, h.choose_spec⟩)
      have hw'sum : ∑ i, w' i = 1 := by
        rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.image f))
          fun i _ hi => hw'zero i hi]
        rw [Finset.sum_image fun a _ b _ hab => hfinj hab]
        rw [Finset.sum_congr rfl fun j _ => hw'f j]
        exact hw1
      have hsum : ∑ i, w' i • z' i = x := by
        rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.image f))
          fun i _ hi => by rw [hw'zero i hi, zero_smul]]
        rw [Finset.sum_image fun a _ b _ hab => hfinj hab]
        rw [Finset.sum_congr rfl fun j _ => by rw [hw'f j, hz'f j]]
        exact hxeq
      refine ⟨(w', z'), ⟨⟨fun i => ?_, hw'sum⟩, Set.mem_univ_pi.mpr fun i => ?_⟩, hsum⟩
      · simp only [hw']
        by_cases h : ∃ j, f j = i
        · rw [dif_pos h]; exact (hw0 _).le
        · rw [dif_neg h]
      · simp only [hz']
        by_cases h : ∃ j, f j = i
        · rw [dif_pos h]; exact hzs (Set.mem_range_self _)
        · rw [dif_neg h]; exact hx₀
    · rintro x ⟨⟨w, z⟩, ⟨hw, hz⟩, rfl⟩
      exact mem_convexHull_of_exists_fintype w z hw.1 hw.2
        (fun i => hz i (Set.mem_univ i)) rfl
  rw [himg]
  refine hK.image (continuous_finsetSum _ fun i _ => ?_)
  exact ((continuous_apply i).comp continuous_fst).smul ((continuous_apply i).comp continuous_snd)
