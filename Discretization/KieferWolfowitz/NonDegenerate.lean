/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
import Discretization.KieferWolfowitz.Design

/-!
# A design with an invertible Gram matrix

The determinant can only be maximised over a set on which it is somewhere positive.  This
file provides that: if the functions `a₁, …, a_n` are linearly independent, then finitely
many points already separate the coefficient vectors, and the uniform distribution on those
points has a positive definite Gram matrix.  It is Lemma 10 of the paper.

Linear independence is used in the form

`∀ c, (∀ y, ⟪c, a(y)⟫ = 0) → c = 0`,

that is, a function of the span that vanishes everywhere has coefficient vector zero.  This
is what is actually needed, and
`Discretization.KieferWolfowitz.linearIndependent_iff_forall_star` identifies it with
`LinearIndependent ℂ` applied to the coordinate functions.  Its unconjugated companion
`Discretization.KieferWolfowitz.linearIndependent_iff_forall` is the same condition for the
linear parametrisation `c ⬝ᵥ a y`, which the induction below runs on.

The separating points are found by a descending induction on dimension, in
`Discretization.KieferWolfowitz.exists_points_separating`: as long as some nonzero
coefficient vector is annihilated by all the points chosen so far, the hypothesis produces a
point at which that vector does not vanish, and adding it cuts the dimension down by at
least one.  The induction is on the dimension of the subspace that survives, so it stops
after at most `n` steps.
-/

open Matrix
open scoped ComplexOrder MatrixOrder

namespace Discretization.KieferWolfowitz

variable {Ω ι : Type*} [Fintype ι]

/-- Linear independence of the coordinate functions `y ↦ aᵢ(y)`, stated as the property
that is used: a vanishing linear combination has coefficient vector zero. -/
theorem linearIndependent_iff_forall (a : Ω → ι → ℂ) :
    LinearIndependent ℂ (fun i => fun y => a y i) ↔
      ∀ c : ι → ℂ, (∀ y, c ⬝ᵥ a y = 0) → c = 0 := by
  rw [Fintype.linearIndependent_iff]
  constructor
  · intro h c hc
    funext i
    exact h c (funext fun y => by simpa [dotProduct, mul_comm] using hc y) i
  · intro h c hc
    have : c = 0 := h c fun y => by
      simpa [dotProduct, mul_comm] using congrFun hc y
    simp [this]

/-- **Linear independence in the form the theorems use.**  The functions of the span are
written `f(y) = ⟪c, a(y)⟫ = star c ⬝ᵥ a y`, conjugate-linearly in the coefficient vector, so
the separating condition carries a `star`.  Conjugation is a bijection of the coefficient
vectors with `star c = 0` exactly when `c = 0`, so this is the same condition as
`Discretization.KieferWolfowitz.linearIndependent_iff_forall`. -/
theorem linearIndependent_iff_forall_star (a : Ω → ι → ℂ) :
    LinearIndependent ℂ (fun i => fun y => a y i) ↔
      ∀ c : ι → ℂ, (∀ y, star c ⬝ᵥ a y = 0) → c = 0 := by
  rw [linearIndependent_iff_forall]
  constructor
  · exact fun h c hc => star_eq_zero.mp (h (star c) hc)
  · exact fun h c hc =>
      star_eq_zero.mp (h (star c) fun y => by rw [star_star]; exact hc y)

/-- The functional `c ↦ ⟪c, a(y)⟫` on coefficient vectors, as a linear map. -/
@[simps] def evalAt (a : Ω → ι → ℂ) (y : Ω) : (ι → ℂ) →ₗ[ℂ] ℂ where
  toFun c := c ⬝ᵥ a y
  map_add' u v := by simp [add_dotProduct]
  map_smul' r v := by simp [smul_dotProduct]

/-- Auxiliary form of `Discretization.KieferWolfowitz.exists_points_separating`, with the
induction hypothesis exposed: for every subspace `W` of dimension at most `n` there are
finitely many points separating the elements of `W`. -/
theorem exists_points_separating_aux (a : Ω → ι → ℂ)
    (hli : ∀ c : ι → ℂ, (∀ y, c ⬝ᵥ a y = 0) → c = 0) (n : ℕ) (W : Submodule ℂ (ι → ℂ))
    (hW : Module.finrank ℂ W ≤ n) :
    ∃ (N : ℕ) (x : Fin N → Ω), ∀ c ∈ W, (∀ k, c ⬝ᵥ a (x k) = 0) → c = 0 := by
  induction n generalizing W with
  | zero =>
    have hbot : W = ⊥ := Submodule.finrank_eq_zero.mp (Nat.le_zero.mp hW)
    exact ⟨0, fun k => k.elim0, fun c hc _ => by rw [hbot] at hc; simpa using hc⟩
  | succ n ih =>
    by_cases hbot : W = ⊥
    · exact ⟨0, fun k => k.elim0, fun c hc _ => by rw [hbot] at hc; simpa using hc⟩
    -- a nonzero vector of `W` is detected at some point `y₀`
    obtain ⟨c₀, hc₀W, hc₀⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
    obtain ⟨y₀, hy₀⟩ : ∃ y, c₀ ⬝ᵥ a y ≠ 0 := by
      by_contra h
      exact hc₀ (hli c₀ (fun y => not_not.mp (not_exists.mp h y)))
    -- adding `y₀` cuts the subspace strictly down
    have hlt : W ⊓ LinearMap.ker (evalAt a y₀) < W := by
      refine lt_of_le_of_ne inf_le_left fun heq => hy₀ ?_
      have hmem : c₀ ∈ W ⊓ LinearMap.ker (evalAt a y₀) := by rw [heq]; exact hc₀W
      simpa [evalAt] using hmem.2
    obtain ⟨N, x, hx⟩ := ih (W ⊓ LinearMap.ker (evalAt a y₀)) (by
      have := Submodule.finrank_lt_finrank_of_lt hlt
      omega)
    refine ⟨N + 1, Fin.snoc x y₀, fun c hcW hzero => ?_⟩
    have h0 : c ⬝ᵥ a y₀ = 0 := by simpa using hzero (Fin.last N)
    exact hx c ⟨hcW, by simpa [evalAt] using h0⟩ fun k => by simpa using hzero k.castSucc

/-- **Finitely many points separate the coefficient vectors.**  If the coordinate functions
are linearly independent, there are points `x₁, …, x_N` such that a coefficient vector
annihilated by all of them is zero. -/
theorem exists_points_separating (a : Ω → ι → ℂ)
    (hli : ∀ c : ι → ℂ, (∀ y, c ⬝ᵥ a y = 0) → c = 0) :
    ∃ (N : ℕ) (x : Fin N → Ω), ∀ c : ι → ℂ, (∀ k, c ⬝ᵥ a (x k) = 0) → c = 0 := by
  obtain ⟨N, x, hx⟩ :=
    exists_points_separating_aux a hli (Module.finrank ℂ (ι → ℂ)) ⊤ (by simp)
  exact ⟨N, x, fun c => hx c Submodule.mem_top⟩

/-- Linearly independent functions live on a nonempty domain: a nonzero coefficient vector
has to be detected somewhere. -/
theorem nonempty_of_separating [Nonempty ι] {a : Ω → ι → ℂ}
    (hli : ∀ c : ι → ℂ, (∀ y, star c ⬝ᵥ a y = 0) → c = 0) : Nonempty Ω := by
  by_contra hΩ
  have hzero : ∀ y : Ω, star (fun _ => (1 : ℂ)) ⬝ᵥ a y = 0 := fun y => (hΩ ⟨y⟩).elim
  have h1 := hli _ hzero
  have h2 := congrFun h1 (Classical.arbitrary ι)
  simp at h2

/-- **A design with a positive definite Gram matrix exists.**  This is Lemma 10 of the
paper: for linearly independent functions the uniform distribution on suitable finitely many
points already has an invertible Gram matrix, so the determinant to be maximised is
somewhere positive. -/
theorem exists_design_posDef [Nonempty ι] (a : Ω → ι → ℂ)
    (hli : ∀ c : ι → ℂ, (∀ y, star c ⬝ᵥ a y = 0) → c = 0) :
    ∃ (N : ℕ) (x : Fin N → Ω) (w : Fin N → ℝ), (∀ k, 0 ≤ w k) ∧ ∑ k, w k = 1 ∧
      (designGram a x w).PosDef := by
  obtain ⟨N, x, hx⟩ := exists_points_separating a fun c hc => by
    have := hli (star c) (by simpa using hc)
    simpa using congrArg star this
  -- the points are nonempty, since a nonzero coefficient vector exists
  have hN : N ≠ 0 := by
    rintro rfl
    have h1 := hx (fun _ => (1 : ℂ)) fun k => k.elim0
    have h2 := congrFun h1 (Classical.arbitrary ι)
    simp at h2
  have hNpos : (0 : ℝ) < (N : ℝ) := by positivity
  refine ⟨N, x, fun _ => (N : ℝ)⁻¹, fun _ => by positivity, by
    simp [Finset.sum_const, Finset.card_univ, mul_inv_cancel₀ hNpos.ne'], ?_⟩
  have hpsd := designGram_posSemidef a x (w := fun _ => (N : ℝ)⁻¹) fun _ => by positivity
  refine Matrix.posDef_iff_dotProduct_mulVec.mpr ⟨hpsd.1, fun c hc => ?_⟩
  -- the quadratic form is a positive multiple of a sum of squares, one of which is nonzero
  obtain ⟨k, hk⟩ : ∃ k, star c ⬝ᵥ a (x k) ≠ 0 := by
    by_contra h
    exact hc (by
      have := hx (star c) fun k => by simpa using not_not.mp (not_exists.mp h k)
      simpa using congrArg star this)
  have hre : 0 < RCLike.re (star c ⬝ᵥ (designGram a x (fun _ => (N : ℝ)⁻¹) *ᵥ c)) := by
    rw [re_quadForm_designGram]
    refine Finset.sum_pos' (fun i _ => by positivity) ⟨k, Finset.mem_univ k, ?_⟩
    exact mul_pos (inv_pos.mpr hNpos) (pow_pos (norm_pos_iff.mpr hk) 2)
  refine lt_of_le_of_ne (hpsd.dotProduct_mulVec_nonneg c) fun h => ?_
  rw [← h] at hre
  simp at hre

end Discretization.KieferWolfowitz
