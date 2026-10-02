/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import Discretization.BSS
public import Discretization.NormDiscretization
public import Discretization.KieferWolfowitz.Measure
public import Discretization.KieferWolfowitz.Compact

/-!
# Discretizing the uniform norm with `n ≥ m` points

For an `m`-dimensional space of bounded functions on an arbitrary set and every `n ≥ m`
there are `n` points `x₁, …, xₙ` with positive weights such that

`|f(y)|² ≤ (m + ε) / (1 - √((m-1)/n))² · ∑ᵢ wᵢ |f(xᵢ)|²`

for every `f` in the space and every point `y`; for continuous functions on a compact space
the same holds with `m` in place of `m + ε`.  This is the discretization of the uniform
norm of Krieg, Pozharska, Ullrich and Ullrich (*Sampling projections in the uniform norm*),
with the constant `√((m-1)/n)` of the sparsification theorem in the form of Chkifa,
Dolbeault, Krieg and Ullrich.

The proof thins the Kiefer–Wolfowitz design.  That design, a list of `N` points with
weights, satisfies the bound with `∑ₖ wₖ |f(xₖ)|²` on the right and has a positive definite
Gram matrix `G`.  Read as a probability measure on its index set `{1, …, N}`, it can be
handed to the lower half of the sparsification theorem, `Discretization.bss_lower`, which
picks `n` of the design points and positive weights with `(1 - r)² • G ≤ ∑ᵢ wᵢ a(xᵢ) a(xᵢ)*`
for `r = √((m-1)/n)`.  Evaluated at the coefficient vector of `f`, this bounds the sum over
the design by `(1 - r)⁻²` times the sum over the `n` points, and `r < 1` because `n ≥ m`.
-/

@[expose] public section

open Matrix MeasureTheory
open scoped ComplexOrder MatrixOrder

namespace Discretization

variable {Ω ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **A design can be thinned to `n ≥ m` of its points.**

Let `x₁, …, x_N` be points with nonnegative weights `wₖ` summing to one whose Gram matrix
`∑ₖ wₖ a(xₖ) a(xₖ)*` is positive definite.  Then for every `n ≥ m` there are `n` of these
points, `x_{j(1)}, …, x_{j(n)}`, and positive weights `vᵢ` with

`(1 - √((m-1)/n))² · ∑ₖ wₖ |f(xₖ)|² ≤ ∑ᵢ vᵢ |f(x_{j(i)})|²`

for every function `f(y) = ⟪c, a(y)⟫` in the span.  The design is read as the probability
measure `∑ₖ wₖ δₖ` on its index set, whose Gram matrix is that of the design
(`Discretization.KieferWolfowitz.gram_designMeasure`), and the lower half of the
sparsification theorem, `Discretization.bss_lower`, is applied to it. -/
theorem exists_sparse_design [Nonempty ι] (a : Ω → ι → ℂ) {N : ℕ} (x : Fin N → Ω)
    {w : Fin N → ℝ} (hw : ∀ k, 0 ≤ w k) (hw1 : ∑ k, w k = 1)
    (hpd : (KieferWolfowitz.designGram a x w).PosDef) {n : ℕ} (hmn : Fintype.card ι ≤ n) :
    ∃ (j : Fin n → Fin N) (v : Fin n → ℝ), (∀ i, 0 < v i) ∧ ∀ c : ι → ℂ,
      (1 - Real.sqrt ((Fintype.card ι - 1) / n)) ^ 2 * ∑ k, w k * ‖star c ⬝ᵥ a (x k)‖ ^ 2
        ≤ ∑ i, v i * ‖star c ⬝ᵥ a (x (j i))‖ ^ 2 := by
  -- the design as a probability measure on its index set
  have := KieferWolfowitz.isProbabilityMeasure_designMeasure (id : Fin N → Fin N) hw hw1
  have ha : ∀ i, MemLp (fun k => a (x k) i) 2
      (KieferWolfowitz.designMeasure (id : Fin N → Fin N) w) := fun _ => MemLp.of_discrete
  have hgram : gram (fun k => a (x k)) (KieferWolfowitz.designMeasure (id : Fin N → Fin N) w)
      = KieferWolfowitz.designGram a x w :=
    KieferWolfowitz.gram_designMeasure (a := fun k => a (x k))
      (fun _ => Measurable.of_discrete) id hw
  -- the lower half of the sparsification theorem on that measure
  obtain ⟨j, v, hv, hlow⟩ := bss_lower ha (by rw [hgram]; exact hpd) hmn
  refine ⟨j, v, hv, fun c => ?_⟩
  have h := mul_integral_norm_sq_le_sum ha hlow c
  rw [KieferWolfowitz.integral_designMeasure id hw StronglyMeasurable.of_discrete] at h
  simp only [smul_eq_mul, id] at h
  exact h

/-- **From a design to `n ≥ m` points.**

Let `x₁, …, x_N` be points with nonnegative weights summing to one and positive definite
Gram matrix, for which `|f(y)|² ≤ K · ∑ₖ wₖ |f(xₖ)|²` holds for every point `y` and every
`f` in the span.  Then for every `n ≥ m` there are `n` points with positive weights and

`|f(y)|² ≤ K / (1 - √((m-1)/n))² · ∑ᵢ wᵢ |f(xᵢ)|²`.

The points are those of `Discretization.exists_sparse_design`; the factor is finite because
`√((m-1)/n) < 1` for `n ≥ m` (`Discretization.sqrt_div_lt_one`). -/
theorem exists_uniform_discretization_of_design [Nonempty ι] (a : Ω → ι → ℂ) {K : ℝ}
    (hK : 0 ≤ K) {N : ℕ} (x : Fin N → Ω) {w : Fin N → ℝ} (hw : ∀ k, 0 ≤ w k)
    (hw1 : ∑ k, w k = 1) (hpd : (KieferWolfowitz.designGram a x w).PosDef)
    (hbound : ∀ (c : ι → ℂ) (y : Ω),
      ‖star c ⬝ᵥ a y‖ ^ 2 ≤ K * ∑ k, w k * ‖star c ⬝ᵥ a (x k)‖ ^ 2)
    {n : ℕ} (hmn : Fintype.card ι ≤ n) :
    ∃ (x' : Fin n → Ω) (w' : Fin n → ℝ), (∀ i, 0 < w' i) ∧ ∀ (c : ι → ℂ) (y : Ω),
      ‖star c ⬝ᵥ a y‖ ^ 2 ≤ K / (1 - Real.sqrt ((Fintype.card ι - 1) / n)) ^ 2
        * ∑ i, w' i * ‖star c ⬝ᵥ a (x' i)‖ ^ 2 := by
  obtain ⟨j, v, hv, hlow⟩ := exists_sparse_design a x hw hw1 hpd hmn
  -- `n ≥ m ≥ 1`, so `r = √((m-1)/n) < 1`
  have hn : (0 : ℝ) < n := by
    have hm : 0 < Fintype.card ι := Fintype.card_pos
    exact_mod_cast lt_of_lt_of_le hm hmn
  have hr : 0 < (1 - Real.sqrt ((Fintype.card ι - 1) / n)) ^ 2 :=
    pow_pos (sub_pos.2 (sqrt_div_lt_one hn (by exact_mod_cast hmn))) 2
  refine ⟨fun i => x (j i), v, hv, fun c y => ?_⟩
  calc ‖star c ⬝ᵥ a y‖ ^ 2 ≤ K * ∑ k, w k * ‖star c ⬝ᵥ a (x k)‖ ^ 2 := hbound c y
    _ ≤ K * ((∑ i, v i * ‖star c ⬝ᵥ a (x (j i))‖ ^ 2)
          / (1 - Real.sqrt ((Fintype.card ι - 1) / n)) ^ 2) := by
        refine mul_le_mul_of_nonneg_left ?_ hK
        rw [le_div_iff₀ hr]
        linarith [hlow c]
    _ = K / (1 - Real.sqrt ((Fintype.card ι - 1) / n)) ^ 2
          * ∑ i, v i * ‖star c ⬝ᵥ a (x (j i))‖ ^ 2 := by ring

/-- **Discretization of the uniform norm with `n ≥ m` points**
(Krieg–Pozharska–Ullrich–Ullrich).

For linearly independent bounded functions `a₁, …, a_m` on an arbitrary set, every `ε > 0`
and every `n ≥ m` there are `n` points with positive weights such that

`|f(y)|² ≤ (m + ε) / (1 - √((m-1)/n))² · ∑ᵢ wᵢ |f(xᵢ)|²`

for every point `y` and every function `f(y) = ⟪c, a(y)⟫` in the span.  It is the
Kiefer–Wolfowitz design, `Discretization.KieferWolfowitz.exists_design_kieferWolfowitz`,
thinned to `n` of its points by the sparsification theorem. -/
theorem exists_uniform_discretization [Nonempty ι] (a : Ω → ι → ℂ) {C : ℝ}
    (hC : ∀ y i, ‖a y i‖ ≤ C) (hli : ∀ c : ι → ℂ, (∀ y, star c ⬝ᵥ a y = 0) → c = 0)
    {ε : ℝ} (hε : 0 < ε) {n : ℕ} (hmn : Fintype.card ι ≤ n) :
    ∃ (x : Fin n → Ω) (w : Fin n → ℝ), (∀ i, 0 < w i) ∧ ∀ (c : ι → ℂ) (y : Ω),
      ‖star c ⬝ᵥ a y‖ ^ 2 ≤ (Fintype.card ι + ε) / (1 - Real.sqrt ((Fintype.card ι - 1) / n)) ^ 2
        * ∑ i, w i * ‖star c ⬝ᵥ a (x i)‖ ^ 2 := by
  obtain ⟨N, x, w, hw, hw1, hpd, hbound⟩ :=
    KieferWolfowitz.exists_design_kieferWolfowitz a hC hli hε
  exact exists_uniform_discretization_of_design a (by positivity) x hw hw1 hpd hbound hmn

/-- **Discretization of the uniform norm with `n ≥ m` points on a compact domain.**

For linearly independent continuous functions `a₁, …, a_m` on a compact space and every
`n ≥ m` there are `n` points with positive weights such that

`|f(y)|² ≤ m / (1 - √((m-1)/n))² · ∑ᵢ wᵢ |f(xᵢ)|²`

for every point `y` and every `f` in the span.  It is the design with the sharp constant,
`Discretization.KieferWolfowitz.exists_design_kieferWolfowitz_of_compact`, thinned to `n` of
its points by the sparsification theorem. -/
theorem exists_uniform_discretization_of_compact [Nonempty ι] [TopologicalSpace Ω]
    [CompactSpace Ω] (a : Ω → ι → ℂ) (hcont : ∀ i, Continuous fun y => a y i)
    (hli : ∀ c : ι → ℂ, (∀ y, star c ⬝ᵥ a y = 0) → c = 0) {n : ℕ}
    (hmn : Fintype.card ι ≤ n) :
    ∃ (x : Fin n → Ω) (w : Fin n → ℝ), (∀ i, 0 < w i) ∧ ∀ (c : ι → ℂ) (y : Ω),
      ‖star c ⬝ᵥ a y‖ ^ 2 ≤ Fintype.card ι / (1 - Real.sqrt ((Fintype.card ι - 1) / n)) ^ 2
        * ∑ i, w i * ‖star c ⬝ᵥ a (x i)‖ ^ 2 := by
  obtain ⟨N, x, w, hw, hw1, hpd, hbound⟩ :=
    KieferWolfowitz.exists_design_kieferWolfowitz_of_compact a hcont hli
  exact exists_uniform_discretization_of_design a (Nat.cast_nonneg _) x hw hw1 hpd hbound hmn

end Discretization
