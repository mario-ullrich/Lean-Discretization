/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import BasicResults.CompactConvexHull
public import BasicResults.SelfAdjointDimension
public import Discretization.KieferWolfowitz.Design

/-!
# Designs and the convex hull of the rank-one matrices

The Gram matrices of designs are exactly the convex combinations of the rank-one matrices
`a(y) a(y)*`, so they form the convex hull

`Discretization.KieferWolfowitz.rankOneSet a = {a(y) a(y)* : y}`.

This dictionary is what brings convexity to bear on designs, and it is used twice:

* `Discretization.KieferWolfowitz.exists_design_card_le`: **every design can be replaced by
  one with at most `m² + 1` points and the same Gram matrix.**  This is Carathéodory's
  theorem, in the form `eq_pos_convex_span_of_mem_convexHull`.  The rank-one matrices are
  Hermitian (`Discretization.KieferWolfowitz.vectorSpan_rankOneSet_le_selfAdjoint`), and the
  Hermitian matrices form a real vector space of dimension `m²`
  (`Matrix.finrank_selfAdjoint_submodule`).  Since every conclusion of the Kiefer–Wolfowitz
  theorem depends on the design only through its Gram matrix, the bound on the number of
  points transfers to all of them.
* the compact case, where the convex hull is compact and the determinant therefore attains
  its maximum on it.

The paper of Krieg, Pozharska, Ullrich and Ullrich has the count `r + 1`, with `r ≤ m²` the
dimension of the span of the products `aᵢ conj aⱼ`, which is smaller for particular
families.  The discretization theorem, which receives the design next, accepts any finite,
indeed any countable, family of points.
-/

@[expose] public section

open Matrix
open scoped ComplexOrder MatrixOrder

namespace Discretization.KieferWolfowitz

variable {Ω ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The rank-one matrices `a(y) a(y)*` attached to the points of the domain.  Their convex
hull is the set of Gram matrices of designs. -/
def rankOneSet (a : Ω → ι → ℂ) : Set (Matrix ι ι ℂ) :=
  Set.range fun y => vecMulVec (a y) (star (a y))

omit [Fintype ι] [DecidableEq ι] in
/-- The Gram matrix of a design lies in the convex hull of the rank-one matrices. -/
theorem designGram_mem_convexHull (a : Ω → ι → ℂ) {n : ℕ} (x : Fin n → Ω) {w : Fin n → ℝ}
    (hw : ∀ k, 0 ≤ w k) (hw1 : ∑ k, w k = 1) :
    designGram a x w ∈ convexHull ℝ (rankOneSet a) :=
  mem_convexHull_of_exists_fintype w _ hw hw1 (fun _ => Set.mem_range_self _) rfl

omit [Fintype ι] [DecidableEq ι] in
/-- Conversely, every point of the convex hull of the rank-one matrices is the Gram matrix
of a design. -/
theorem exists_design_of_mem_convexHull {a : Ω → ι → ℂ} {A : Matrix ι ι ℂ}
    (hA : A ∈ convexHull ℝ (rankOneSet a)) :
    ∃ (n : ℕ) (x : Fin n → Ω) (w : Fin n → ℝ), (∀ k, 0 ≤ w k) ∧ ∑ k, w k = 1 ∧
      designGram a x w = A := by
  classical
  obtain ⟨κ, _, v, z, hv0, hv1, hz, hsum⟩ := mem_convexHull_iff_exists_fintype.1 hA
  choose y hy using fun i => hz i
  set e := Fintype.equivFin κ
  refine ⟨Fintype.card κ, fun k => y (e.symm k), fun k => v (e.symm k), fun k => hv0 _, ?_, ?_⟩
  · rw [Equiv.sum_comp e.symm v]; exact hv1
  · rw [designGram, Equiv.sum_comp e.symm fun i => v i • vecMulVec (a (y i)) (star (a (y i)))]
    rw [← hsum]
    exact Finset.sum_congr rfl fun i _ =>
      by rw [show vecMulVec (a (y i)) (star (a (y i))) = z i from hy i]

omit [Fintype ι] [DecidableEq ι] in
/-- The rank-one matrices `a(y) a(y)*` are Hermitian: `(v v*)* = v v*`. -/
theorem rankOneSet_subset_selfAdjoint (a : Ω → ι → ℂ) :
    rankOneSet a ⊆ selfAdjoint.submodule ℝ (Matrix ι ι ℂ) := by
  rintro _ ⟨y, rfl⟩
  show star (vecMulVec (a y) (star (a y))) = vecMulVec (a y) (star (a y))
  rw [star_eq_conjTranspose, conjTranspose_vecMulVec, star_star]

omit [Fintype ι] [DecidableEq ι] in
/-- Every difference of two rank-one matrices is Hermitian, so the vectors spanned by the
rank-one matrices lie in the real vector space of Hermitian matrices. -/
theorem vectorSpan_rankOneSet_le_selfAdjoint (a : Ω → ι → ℂ) :
    vectorSpan ℝ (rankOneSet a) ≤ selfAdjoint.submodule ℝ (Matrix ι ι ℂ) := by
  rw [vectorSpan_def, Submodule.span_le]
  rintro _ ⟨p, hp, q, hq, rfl⟩
  exact (selfAdjoint.submodule ℝ _).sub_mem (rankOneSet_subset_selfAdjoint a hp)
    (rankOneSet_subset_selfAdjoint a hq)

omit [DecidableEq ι] in
/-- **Every design can be replaced by one with at most `m² + 1` points and the same Gram
matrix.**

By Carathéodory's theorem the Gram matrix, a point of the convex hull of the rank-one
matrices, is already a convex combination of affinely independent ones.  These are
Hermitian, and an affinely independent family in the real vector space of Hermitian
`m × m` matrices, of dimension `m²` (`Matrix.finrank_selfAdjoint_submodule`), has at most
`m² + 1` members. -/
theorem exists_design_card_le (a : Ω → ι → ℂ) {n : ℕ} (x : Fin n → Ω) {w : Fin n → ℝ}
    (hw : ∀ k, 0 ≤ w k) (hw1 : ∑ k, w k = 1) :
    ∃ (M : ℕ) (x' : Fin M → Ω) (w' : Fin M → ℝ), M ≤ Fintype.card ι ^ 2 + 1 ∧
      (∀ k, 0 ≤ w' k) ∧ ∑ k, w' k = 1 ∧ designGram a x' w' = designGram a x w := by
  classical
  obtain ⟨κ, _, z, v, hzs, hai, hv0, hv1, hsum⟩ :=
    eq_pos_convex_span_of_mem_convexHull (designGram_mem_convexHull a x hw hw1)
  -- the affinely independent matrices are Hermitian, a real space of dimension `m²`
  have hspan : vectorSpan ℝ (Set.range z) ≤ selfAdjoint.submodule ℝ (Matrix ι ι ℂ) :=
    (vectorSpan_mono ℝ hzs).trans (vectorSpan_rankOneSet_le_selfAdjoint a)
  have hcard : Fintype.card κ ≤ Fintype.card ι ^ 2 + 1 := by
    refine le_trans hai.card_le_finrank_succ (Nat.add_le_add_right ?_ 1)
    rw [← Matrix.finrank_selfAdjoint_submodule ι]
    exact Submodule.finrank_mono hspan
  choose y hy using fun i => Set.range_subset_iff.1 hzs i
  set e := Fintype.equivFin κ
  refine ⟨Fintype.card κ, fun k => y (e.symm k), fun k => v (e.symm k), hcard,
    fun k => (hv0 _).le, ?_, ?_⟩
  · rw [Equiv.sum_comp e.symm v]; exact hv1
  · rw [designGram, Equiv.sum_comp e.symm fun i => v i • vecMulVec (a (y i)) (star (a (y i))),
      ← hsum]
    exact Finset.sum_congr rfl fun i _ =>
      by rw [show vecMulVec (a (y i)) (star (a (y i))) = z i from hy i]

end Discretization.KieferWolfowitz
