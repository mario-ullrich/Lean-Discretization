/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
import BasicResults.CompactConvexHull
import Discretization.KieferWolfowitz.Design

/-!
# Designs and the convex hull of the rank-one matrices

The Gram matrices of designs are exactly the convex combinations of the rank-one matrices
`a(y) a(y)*`, so they form the convex hull

`Discretization.KieferWolfowitz.rankOneSet a = {a(y) a(y)* : y}`.

This dictionary is what brings convexity to bear on designs, and it is used twice:

* `Discretization.KieferWolfowitz.exists_design_card_le`: **every design can be replaced by
  one with at most `2n² + 1` points and the same Gram matrix.**  This is Carathéodory's
  theorem, in the form `eq_pos_convex_span_of_mem_convexHull`, applied in the real vector
  space of complex `n × n` matrices, whose real dimension is `2n²`.  Since every conclusion
  of the Kiefer–Wolfowitz theorem depends on the design only through its Gram matrix, the
  bound on the number of points transfers to all of them.
* the compact case, where the convex hull is compact and the determinant therefore attains
  its maximum on it.

The sharper count `r + 1` of the paper, with `r` the dimension of the span of the products
`aᵢ conj aⱼ`, would need the real dimension of the Hermitian matrices spanned by the
rank-one matrices.  Nothing downstream depends on it: the sparsification theorem accepts any
finite, indeed any countable, family of points.
-/

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
theorem designGram_mem_convexHull (a : Ω → ι → ℂ) {N : ℕ} (x : Fin N → Ω) {w : Fin N → ℝ}
    (hw : ∀ k, 0 ≤ w k) (hw1 : ∑ k, w k = 1) :
    designGram a x w ∈ convexHull ℝ (rankOneSet a) :=
  mem_convexHull_of_exists_fintype w _ hw hw1 (fun _ => Set.mem_range_self _) rfl

omit [Fintype ι] [DecidableEq ι] in
/-- Conversely, every point of the convex hull of the rank-one matrices is the Gram matrix
of a design. -/
theorem exists_design_of_mem_convexHull {a : Ω → ι → ℂ} {A : Matrix ι ι ℂ}
    (hA : A ∈ convexHull ℝ (rankOneSet a)) :
    ∃ (N : ℕ) (x : Fin N → Ω) (w : Fin N → ℝ), (∀ k, 0 ≤ w k) ∧ ∑ k, w k = 1 ∧
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

omit [DecidableEq ι] in
/-- **Every design can be replaced by one with at most `2n² + 1` points and the same Gram
matrix.**

By Carathéodory's theorem the Gram matrix, a point of the convex hull of the rank-one
matrices, is already a convex combination of affinely independent ones, and an affinely
independent family in the real vector space of complex `n × n` matrices has at most
`2n² + 1` members. -/
theorem exists_design_card_le (a : Ω → ι → ℂ) {N : ℕ} (x : Fin N → Ω) {w : Fin N → ℝ}
    (hw : ∀ k, 0 ≤ w k) (hw1 : ∑ k, w k = 1) :
    ∃ (M : ℕ) (x' : Fin M → Ω) (w' : Fin M → ℝ), M ≤ 2 * Fintype.card ι ^ 2 + 1 ∧
      (∀ k, 0 ≤ w' k) ∧ ∑ k, w' k = 1 ∧ designGram a x' w' = designGram a x w := by
  classical
  obtain ⟨κ, _, z, v, hzs, hai, hv0, hv1, hsum⟩ :=
    eq_pos_convex_span_of_mem_convexHull (designGram_mem_convexHull a x hw hw1)
  have hdim : Module.finrank ℝ (Matrix ι ι ℂ) = 2 * Fintype.card ι ^ 2 := by
    rw [Module.finrank_matrix, Complex.finrank_real_complex]; ring
  have hcard : Fintype.card κ ≤ 2 * Fintype.card ι ^ 2 + 1 := by
    refine le_trans (le_trans hai.card_le_finrank_succ
      (Nat.add_le_add_right (Submodule.finrank_le _) 1)) ?_
    rw [hdim]
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
