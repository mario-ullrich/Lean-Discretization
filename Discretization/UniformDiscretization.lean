/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import Discretization.OneSidedDiscretization
public import Discretization.KieferWolfowitz.Measure

/-!
# Discretization of the uniform norm with `n ≥ m` points

For an `m`-dimensional space of bounded functions on an arbitrary set and every `n ≥ m`
there are `n` points `x₁, …, xₙ`, not necessarily distinct, such that

`|f(y)|² ≤ (m + ε) / (1 - √((m-1)/n))² · (1/n) ∑ᵢ |f(xᵢ)|²`

for every `f` in the space and every point `y`; for continuous functions on a compact space
the same holds with `ε = 0`.  The uniform norm on the span is dominated by the discrete
`ℓ₂` norm of the `n` sample values.  This is the case `p = ∞` of Proposition 8 of Chkifa,
Dolbeault, Krieg and Ullrich.  For `n = 2m` points Krieg, Pozharska, Ullrich and Ullrich
(Theorem 2) prove `‖f‖_∞ ≤ 42 (∑ᵢ |f(xᵢ)|²)^{1/2}`, and Proposition 8 improves the constant
`42` to `1 + √2`; in the form here the squared factor in front of `∑ᵢ |f(xᵢ)|²` is below
`6 (1 + ε/m)`.

An average is at most the largest of its terms, so the same points also give

`|f(y)|² ≤ (m + ε) / (1 - √((m-1)/n))² · maxᵢ |f(xᵢ)|²`,

the uniform norm on the span dominated by the largest sample value
(`Discretization.exists_uniform_discretization_by_max`).  For `n = 2m` this is
`‖f‖_∞ ≤ (2 + √2) √(m + ε) maxᵢ |f(xᵢ)|`, the bound that Chkifa, Dolbeault, Krieg and
Ullrich state with `√m`.  For `n = m` points Novak (*Deterministic and stochastic error
bounds in numerical analysis*, Lemma 1.2.2, a form of Auerbach's lemma) gives
`‖f‖_∞ ≤ (m + ε) maxᵢ |f(xᵢ)|`.

The proof thins the Kiefer–Wolfowitz design.  That design, a list of `N` points with
weights, satisfies the bound with `∑ₖ wₖ |f(xₖ)|²` on the right and has a positive definite
Gram matrix.  Read as a probability measure on its index set `{1, …, N}`, it is handed to the
one-sided discretization, `Discretization.exists_one_sided_discretization`, which picks `n`
of the design points with `(1 - r)² ∑ₖ wₖ |f(xₖ)|² ≤ (1/n) ∑ᵢ |f(xᵢ)|²` for
`r = √((m-1)/n)`, and `r < 1` because `n ≥ m`.
-/

@[expose] public section

open Matrix MeasureTheory
open scoped ComplexOrder MatrixOrder

namespace Discretization

variable {Ω ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **A design bound and a thinning combine.**  If `t ≤ K T` and the thinning keeps
`(1 - √((m-1)/n))² T ≤ S`, then `t ≤ K / (1 - √((m-1)/n))² · S`.

Pure arithmetic: for `0 < m ≤ n` the number `√((m-1)/n)` is below one
(`Discretization.sqrt_div_lt_one`), so the factor `(1 - √((m-1)/n))²` may be divided by. -/
theorem le_div_sq_mul_of_le_mul {m n : ℕ} (hm : 0 < m) (hmn : m ≤ n) {K T S t : ℝ}
    (hK : 0 ≤ K) (hbound : t ≤ K * T)
    (hlow : (1 - Real.sqrt (((m : ℝ) - 1) / n)) ^ 2 * T ≤ S) :
    t ≤ K / (1 - Real.sqrt (((m : ℝ) - 1) / n)) ^ 2 * S := by
  have hn : (0 : ℝ) < n := by exact_mod_cast lt_of_lt_of_le hm hmn
  have hr : 0 < (1 - Real.sqrt (((m : ℝ) - 1) / n)) ^ 2 :=
    pow_pos (sub_pos.2 (sqrt_div_lt_one hn (by exact_mod_cast hmn))) 2
  calc t ≤ K * T := hbound
    _ ≤ K * (S / (1 - Real.sqrt (((m : ℝ) - 1) / n)) ^ 2) := by
        refine mul_le_mul_of_nonneg_left ?_ hK
        rw [le_div_iff₀ hr]
        linarith
    _ = K / (1 - Real.sqrt (((m : ℝ) - 1) / n)) ^ 2 * S := by ring

/-- **An average is at most the largest term.**  For finitely many real numbers
`s₁, …, sₙ`, with `n ≥ 1`,

`(1/n) ∑ᵢ sᵢ ≤ maxᵢ sᵢ`.

The maximum is written as the supremum `⨆ i, s i` over `Fin n`, which a finite family
attains. -/
theorem inv_mul_sum_le_iSup {n : ℕ} (hn : 0 < n) (s : Fin n → ℝ) :
    1 / (n : ℝ) * ∑ i, s i ≤ ⨆ i, s i := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  -- every term is at most the supremum, so the sum is at most `n` times it
  have hsum : ∑ i, s i ≤ n * ⨆ i, s i := by
    have h := Finset.sum_le_card_nsmul Finset.univ s (⨆ i, s i)
      fun i _ => le_ciSup (Set.finite_range s).bddAbove i
    simpa [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using h
  rw [one_div_mul_eq_div, div_le_iff₀ hn0, mul_comm]
  exact hsum

/-- **A design can be thinned to `n ≥ m` of its points with equal weights.**

Let `x₁, …, x_N` be points with nonnegative weights `wₖ` summing to one whose Gram matrix is
positive definite.  Then for every `n ≥ m` there are `n` of these points,
`x_{j(1)}, …, x_{j(n)}`, not necessarily distinct, with

`(1 - √((m-1)/n))² · ∑ₖ wₖ |f(xₖ)|² ≤ (1/n) ∑ᵢ |f(x_{j(i)})|²`

for every `f` in the span.  The design is read as the probability measure `∑ₖ wₖ δₖ` on its
index set, and `Discretization.exists_one_sided_discretization` is applied to it. -/
theorem exists_sparse_design_equal_weights [Nonempty ι] (a : Ω → ι → ℂ) {N : ℕ}
    (x : Fin N → Ω) {w : Fin N → ℝ} (hw : ∀ k, 0 ≤ w k) (hw1 : ∑ k, w k = 1)
    (hpd : (KieferWolfowitz.designGram a x w).PosDef) {n : ℕ} (hmn : Fintype.card ι ≤ n) :
    ∃ j : Fin n → Fin N, ∀ c : ι → ℂ,
      (1 - Real.sqrt ((Fintype.card ι - 1) / n)) ^ 2 * ∑ k, w k * ‖star c ⬝ᵥ a (x k)‖ ^ 2
        ≤ 1 / (n : ℝ) * ∑ i, ‖star c ⬝ᵥ a (x (j i))‖ ^ 2 := by
  -- the design as a probability measure on its index set
  have := KieferWolfowitz.isProbabilityMeasure_designMeasure (id : Fin N → Fin N) hw hw1
  have ha : ∀ i, MemLp (fun k => a (x k) i) 2
      (KieferWolfowitz.designMeasure (id : Fin N → Fin N) w) := fun _ => MemLp.of_discrete
  have hgram : gram (fun k => a (x k)) (KieferWolfowitz.designMeasure (id : Fin N → Fin N) w)
      = KieferWolfowitz.designGram a x w :=
    KieferWolfowitz.gram_designMeasure (a := fun k => a (x k))
      (fun _ => Measurable.of_discrete) id hw
  -- the lower frame bound with equal weights on that measure
  obtain ⟨j, hlow⟩ := exists_one_sided_discretization ha (by rw [hgram]; exact hpd) hmn
  refine ⟨j, fun c => ?_⟩
  have h := hlow c
  rw [KieferWolfowitz.integral_designMeasure id hw StronglyMeasurable.of_discrete] at h
  simp only [smul_eq_mul, id] at h
  exact h

/-- **From a design to `n ≥ m` points: the uniform norm by the discrete `ℓ₂` norm.**

Let `x₁, …, x_N` be points with nonnegative weights summing to one and positive definite
Gram matrix, for which `|f(y)|² ≤ K · ∑ₖ wₖ |f(xₖ)|²` holds for every point `y` and every
`f` in the span.  Then for every `n ≥ m` there are `n` points, not necessarily distinct, with

`|f(y)|² ≤ K / (1 - √((m-1)/n))² · (1/n) ∑ᵢ |f(xᵢ)|²`. -/
theorem exists_uniform_discretization_of_design_by_l2 [Nonempty ι] (a : Ω → ι → ℂ)
    {K : ℝ} (hK : 0 ≤ K) {N : ℕ} (x : Fin N → Ω) {w : Fin N → ℝ} (hw : ∀ k, 0 ≤ w k)
    (hw1 : ∑ k, w k = 1) (hpd : (KieferWolfowitz.designGram a x w).PosDef)
    (hbound : ∀ (c : ι → ℂ) (y : Ω),
      ‖star c ⬝ᵥ a y‖ ^ 2 ≤ K * ∑ k, w k * ‖star c ⬝ᵥ a (x k)‖ ^ 2)
    {n : ℕ} (hmn : Fintype.card ι ≤ n) :
    ∃ x' : Fin n → Ω, ∀ (c : ι → ℂ) (y : Ω),
      ‖star c ⬝ᵥ a y‖ ^ 2 ≤ K / (1 - Real.sqrt ((Fintype.card ι - 1) / n)) ^ 2
        * (1 / (n : ℝ) * ∑ i, ‖star c ⬝ᵥ a (x' i)‖ ^ 2) := by
  obtain ⟨j, hlow⟩ := exists_sparse_design_equal_weights a x hw hw1 hpd hmn
  exact ⟨fun i => x (j i), fun c y =>
    le_div_sq_mul_of_le_mul Fintype.card_pos hmn hK (hbound c y) (hlow c)⟩

/-- **Discretization of the uniform norm with `n ≥ m` points, by the discrete `ℓ₂` norm.**

For linearly independent bounded functions `a₁, …, a_m` on an arbitrary set, every `ε > 0`
and every `n ≥ m` there are `n` points, not necessarily distinct, such that

`|f(y)|² ≤ (m + ε) / (1 - √((m-1)/n))² · (1/n) ∑ᵢ |f(xᵢ)|²`

for every point `y` and every function `f(y) = ⟪c, a(y)⟫` in the span: the uniform norm is
dominated by the discrete `ℓ₂` norm of the `n` sample values.  This is Proposition 8 of
Chkifa, Dolbeault, Krieg and Ullrich for `p = ∞`.  For `n = 2m` the factor in front of
`∑ᵢ |f(xᵢ)|²` is below `6 (1 + ε/m)`, where Theorem 2 of Krieg, Pozharska, Ullrich and
Ullrich has `42²`. -/
theorem exists_uniform_discretization_by_l2 [Nonempty ι] (a : Ω → ι → ℂ) {C : ℝ}
    (hC : ∀ y i, ‖a y i‖ ≤ C) (hli : ∀ c : ι → ℂ, (∀ y, star c ⬝ᵥ a y = 0) → c = 0)
    {ε : ℝ} (hε : 0 < ε) {n : ℕ} (hmn : Fintype.card ι ≤ n) :
    ∃ x : Fin n → Ω, ∀ (c : ι → ℂ) (y : Ω),
      ‖star c ⬝ᵥ a y‖ ^ 2 ≤ (Fintype.card ι + ε) / (1 - Real.sqrt ((Fintype.card ι - 1) / n)) ^ 2
        * (1 / (n : ℝ) * ∑ i, ‖star c ⬝ᵥ a (x i)‖ ^ 2) := by
  obtain ⟨N, x, w, hw, hw1, hpd, hbound⟩ :=
    KieferWolfowitz.exists_design_kieferWolfowitz a hC hli hε
  exact exists_uniform_discretization_of_design_by_l2 a (by positivity) x hw hw1 hpd
    hbound hmn

/-- **Discretization of the uniform norm with `n ≥ m` points on a compact domain, by the
discrete `ℓ₂` norm.**

For linearly independent continuous functions `a₁, …, a_m` on a compact space and every
`n ≥ m` there are `n` points, not necessarily distinct, such that

`|f(y)|² ≤ m / (1 - √((m-1)/n))² · (1/n) ∑ᵢ |f(xᵢ)|²`

for every point `y` and every `f` in the span: the bound above with `ε = 0`. -/
theorem exists_uniform_discretization_of_compact_by_l2 [Nonempty ι]
    [TopologicalSpace Ω] [CompactSpace Ω] (a : Ω → ι → ℂ)
    (hcont : ∀ i, Continuous fun y => a y i)
    (hli : ∀ c : ι → ℂ, (∀ y, star c ⬝ᵥ a y = 0) → c = 0) {n : ℕ}
    (hmn : Fintype.card ι ≤ n) :
    ∃ x : Fin n → Ω, ∀ (c : ι → ℂ) (y : Ω),
      ‖star c ⬝ᵥ a y‖ ^ 2 ≤ Fintype.card ι / (1 - Real.sqrt ((Fintype.card ι - 1) / n)) ^ 2
        * (1 / (n : ℝ) * ∑ i, ‖star c ⬝ᵥ a (x i)‖ ^ 2) := by
  obtain ⟨N, x, w, hw, hw1, hpd, hbound⟩ :=
    KieferWolfowitz.exists_design_kieferWolfowitz_of_compact a hcont hli
  exact exists_uniform_discretization_of_design_by_l2 a (Nat.cast_nonneg _) x hw hw1
    hpd hbound hmn

/-! ### The largest sample value -/

/-- **The uniform norm by the largest sample value.**

For linearly independent bounded functions `a₁, …, a_m` on an arbitrary set, every `ε > 0`
and every `n ≥ m` there are `n` points, not necessarily distinct, such that

`|f(y)|² ≤ (m + ε) / (1 - √((m-1)/n))² · maxᵢ |f(xᵢ)|²`

for every point `y` and every function `f(y) = ⟪c, a(y)⟫` in the span.  The points are those
of `Discretization.exists_uniform_discretization_by_l2`, whose average is at most its largest
term (`Discretization.inv_mul_sum_le_iSup`).  For `n = 2m` this is
`‖f‖_∞ ≤ (2 + √2) √(m + ε) maxᵢ |f(xᵢ)|`, the bound that Chkifa, Dolbeault, Krieg and Ullrich
state with `√m`; Krieg, Pozharska, Ullrich and Ullrich read their Theorem 2 as
`‖f‖_∞ ≤ c √m maxᵢ |f(xᵢ)|` with `c = 42 √2`.  For `n = m` points Novak, with a form of
Auerbach's lemma, gives `‖f‖_∞ ≤ (m + ε) maxᵢ |f(xᵢ)|`. -/
theorem exists_uniform_discretization_by_max [Nonempty ι] (a : Ω → ι → ℂ) {C : ℝ}
    (hC : ∀ y i, ‖a y i‖ ≤ C) (hli : ∀ c : ι → ℂ, (∀ y, star c ⬝ᵥ a y = 0) → c = 0)
    {ε : ℝ} (hε : 0 < ε) {n : ℕ} (hmn : Fintype.card ι ≤ n) :
    ∃ x : Fin n → Ω, ∀ (c : ι → ℂ) (y : Ω),
      ‖star c ⬝ᵥ a y‖ ^ 2 ≤ (Fintype.card ι + ε) / (1 - Real.sqrt ((Fintype.card ι - 1) / n)) ^ 2
        * ⨆ i, ‖star c ⬝ᵥ a (x i)‖ ^ 2 := by
  have hn : 0 < n := Fintype.card_pos.trans_le hmn
  obtain ⟨x, hx⟩ := exists_uniform_discretization_by_l2 a hC hli hε hmn
  refine ⟨x, fun c y => (hx c y).trans ?_⟩
  exact mul_le_mul_of_nonneg_left (inv_mul_sum_le_iSup hn _) (by positivity)

/-- **The uniform norm by the largest sample value on a compact domain.**

For linearly independent continuous functions `a₁, …, a_m` on a compact space and every
`n ≥ m` there are `n` points, not necessarily distinct, such that

`|f(y)|² ≤ m / (1 - √((m-1)/n))² · maxᵢ |f(xᵢ)|²`

for every point `y` and every `f` in the span: the bound above with `ε = 0`. -/
theorem exists_uniform_discretization_of_compact_by_max [Nonempty ι]
    [TopologicalSpace Ω] [CompactSpace Ω] (a : Ω → ι → ℂ)
    (hcont : ∀ i, Continuous fun y => a y i)
    (hli : ∀ c : ι → ℂ, (∀ y, star c ⬝ᵥ a y = 0) → c = 0) {n : ℕ}
    (hmn : Fintype.card ι ≤ n) :
    ∃ x : Fin n → Ω, ∀ (c : ι → ℂ) (y : Ω),
      ‖star c ⬝ᵥ a y‖ ^ 2 ≤ Fintype.card ι / (1 - Real.sqrt ((Fintype.card ι - 1) / n)) ^ 2
        * ⨆ i, ‖star c ⬝ᵥ a (x i)‖ ^ 2 := by
  have hn : 0 < n := Fintype.card_pos.trans_le hmn
  obtain ⟨x, hx⟩ := exists_uniform_discretization_of_compact_by_l2 a hcont hli hmn
  refine ⟨x, fun c y => (hx c y).trans ?_⟩
  exact mul_le_mul_of_nonneg_left (inv_mul_sum_le_iSup hn _) (by positivity)

end Discretization
