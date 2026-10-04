/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import Discretization.BSS
public import Discretization.GeneralGram
public import Discretization.NormDiscretization

/-!
# One-sided discretization

On a probability space the lower half of the discretization theorem holds with weights that
are positive and at most `1/n`.  For a probability measure `μ`, a family `a` of `m` square-integrable functions with
positive definite Gram matrix `I` and every `n ≥ m`, there are points `x₁, …, xₙ`, not
necessarily distinct, and weights `0 < wᵢ ≤ 1/n` with

`(1 - √((m-1)/n))² • I ≤ ∑ᵢ wᵢ a(xᵢ) a(xᵢ)*`.

Replacing every weight by `1/n` only enlarges the right-hand side, so the same points
discretize the `L₂`-norm from below with equal weights, a one-sided discretization:

`(1 - √((m-1)/n))² ∫ |f|² dμ ≤ (1/n) ∑ᵢ |f(xᵢ)|²`   for every `f` in the span.

Limonova and Temlyakov (*On sampling discretization in `L₂`*, Theorem 1.1) prove a
one-sided discretization with equal weights and of the order of `m` points for spaces
satisfying a Nikol'skii-type inequality, and Bartel, Schäfer and Ullrich (*Constructive
subsampling of finite frames*) for arbitrary spaces, up to constants.  The form here is the
case `p = 2` of Proposition 8 of Chkifa, Dolbeault, Krieg and Ullrich, whose construction is
the one followed.

The bound comes from the discretization theorem with the constant function `b ≡ 1` as second
family, that is `H = ℂ`.  Its Gram operator is `J = 1`, so `Λ = 1` and the effective
dimension is `M = 1 ≤ 1 + 1/n`.  This is the case of a small effective dimension, in which the
upper verifier is the constant `U(x) = n ‖b(x)‖² / Tr J = n`, and the one-sided construction
`Discretization.exists_points_weights_of_small_dim` produces weights with `wᵢ U(xᵢ) ≤ 1`, that
is `wᵢ ≤ 1/n`.  The upper frame bound of the theorem records only the sum `∑ wᵢ ≤ 1`, so the
bound on each weight is read off the construction.  For a one-element family a single point
serves, as in `Discretization.bss_generalized_of_unique_of_small_dim`.

The results are `Discretization.bss_lower_le_one_div` for the weights,
`Discretization.bss_lower_equal_weights` in the Loewner order and
`Discretization.exists_one_sided_discretization` for the norm.
-/

@[expose] public section

open Matrix MeasureTheory
open scoped ComplexOrder MatrixOrder

namespace Discretization

variable {ι Ω : Type*} [DecidableEq ι] [MeasurableSpace Ω] {μ : Measure Ω}

/-- The average of a constant over a probability space is the constant itself; here for the
constant `n`, the average of the constant upper verifier. -/
theorem integral_const_natCast [IsProbabilityMeasure μ] (n : ℕ) :
    ∫ _ : Ω, (n : ℝ) ∂μ = n := by
  simp

/-! ### A normalized family -/

/-- **The lower frame bound with weights at most `1/n`**, for a normalized family of `m ≥ 2`
functions on a probability space.

For every `n ≥ m` there are `n` points and weights `0 < wᵢ ≤ 1/n` with
`(1 - √((m-1)/n))² • 1 ≤ ∑ wᵢ a(xᵢ) a(xᵢ)*`.  The construction tracks only the lower matrix
and compares the lower verifier with the constant `n`, whose average is `n` because `μ` is a
probability measure; the weight `wᵢ` it chooses satisfies `wᵢ · n ≤ 1`. -/
theorem bss_lower_le_one_div_of_gram_eq_one_of_two_le [Fintype ι] [Nonempty ι]
    [IsProbabilityMeasure μ] {a : Ω → ι → ℂ} (ha : ∀ k, MemLp (fun x => a x k) 2 μ)
    (hgrama : gram a μ = 1) {n : ℕ} (hm : 2 ≤ Fintype.card ι) (hmn : Fintype.card ι ≤ n) :
    ∃ (x : Fin n → Ω) (w : Fin n → ℝ), (∀ i, 0 < w i) ∧ (∀ i, w i ≤ 1 / n) ∧
      (1 - Real.sqrt ((Fintype.card ι - 1) / n)) ^ 2 • (1 : Matrix ι ι ℂ)
        ≤ ∑ i, w i • vecMulVec (a (x i)) (star (a (x i))) := by
  have hn0 : (0 : ℝ) < n := by
    have h : 0 < n := lt_of_lt_of_le (by norm_num) (le_trans hm hmn)
    exact_mod_cast h
  have hn : 0 < n := by exact_mod_cast hn0
  obtain ⟨δ, c₀, hδ0, hA₀, hgap, hframe⟩ := exists_lower_initial_data (Ω := Ω) hm hmn
  -- the one-sided construction with the constant upper verifier `n`
  obtain ⟨x, w, hwpos, hAn, hΦn, hwk⟩ :=
    exists_points_weights_of_small_dim hA₀ hδ0 ha hgrama (U := fun _ => (n : ℝ))
      (fun _ => hn0.le) (integrable_const _) hn (integral_const_natCast n) hgap n
  refine ⟨x, w, hwpos, fun i => ?_, hframe hAn hΦn⟩
  have h : w i * (n : ℝ) ≤ 1 := hwk i
  rw [le_div_iff₀ hn0]
  exact h

/-- **The lower frame bound with weights at most `1/n`** for a single normalized function on
a probability space.

The lower verifier `n |a(x)|²` and the constant `n` have the same average, so some point `y`
has `n ≤ n |a(y)|²`.  Used `n` times with the weight `1/(n |a(y)|²) ≤ 1/n`, it makes the
lower frame bound the identity `∑ wᵢ |a(xᵢ)|² = 1`. -/
theorem bss_lower_le_one_div_of_gram_eq_one_of_unique [Unique ι] [IsProbabilityMeasure μ]
    {a : Ω → ι → ℂ} (ha : ∀ k, MemLp (fun x => a x k) 2 μ) (hgrama : gram a μ = 1)
    {n : ℕ} (hn : 0 < n) :
    ∃ (x : Fin n → Ω) (w : Fin n → ℝ), (∀ i, 0 < w i) ∧ (∀ i, w i ≤ 1 / n) ∧
      (1 : Matrix ι ι ℂ) ≤ ∑ i, w i • vecMulVec (a (x i)) (star (a (x i))) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  -- one point, admissible for the two constant verifiers
  obtain ⟨y, hUL, hLpos⟩ := exists_admissible_point_of_unique_of_small_dim ha hgrama
    (U := fun _ => (n : ℝ)) (fun _ => hn0.le) (integrable_const _) hn0
    (integral_const_natCast n)
  have hUL' : (n : ℝ) ≤ n * ‖a y default‖ ^ 2 := hUL
  refine ⟨fun _ => y, fun _ => 1 / ((n : ℝ) * ‖a y default‖ ^ 2),
    fun _ => one_div_pos.2 hLpos, fun _ => one_div_le_one_div_of_le hn0 hUL', ?_⟩
  -- each point contributes exactly `1/n`
  exact le_of_eq (sum_smul_vecMulVec_eq_one hn0 _ _
    fun _ => one_div_mul_cancel hLpos.ne').symm

/-- **The lower frame bound with weights at most `1/n`** for a normalized family on a
probability space, with no side condition beyond `n ≥ m`.

For `m ≥ 2` this is `Discretization.bss_lower_le_one_div_of_gram_eq_one_of_two_le`; for
`m = 1` the frame constant `(1 - √((m-1)/n))²` is `1`, and it is
`Discretization.bss_lower_le_one_div_of_gram_eq_one_of_unique`. -/
theorem bss_lower_le_one_div_of_gram_eq_one [Fintype ι] [Nonempty ι] [IsProbabilityMeasure μ]
    {a : Ω → ι → ℂ} (ha : ∀ k, MemLp (fun x => a x k) 2 μ) (hgrama : gram a μ = 1)
    {n : ℕ} (hmn : Fintype.card ι ≤ n) :
    ∃ (x : Fin n → Ω) (w : Fin n → ℝ), (∀ i, 0 < w i) ∧ (∀ i, w i ≤ 1 / n) ∧
      (1 - Real.sqrt ((Fintype.card ι - 1) / n)) ^ 2 • (1 : Matrix ι ι ℂ)
        ≤ ∑ i, w i • vecMulVec (a (x i)) (star (a (x i))) := by
  have hcard : 0 < Fintype.card ι := Fintype.card_pos
  by_cases hm : 2 ≤ Fintype.card ι
  · exact bss_lower_le_one_div_of_gram_eq_one_of_two_le ha hgrama hm hmn
  · -- a single function
    have hcard1 : Fintype.card ι = 1 := by omega
    have hn : 0 < n := lt_of_lt_of_le hcard hmn
    rw [sq_one_sub_sqrt_div_card_eq_one hcard1, one_smul]
    have : Unique ι := (Fintype.card_eq_one_iff_nonempty_unique.1 hcard1).some
    exact bss_lower_le_one_div_of_gram_eq_one_of_unique ha hgrama hn

/-! ### A positive definite Gram matrix -/

/-- **The lower half of the sparsification theorem with weights at most `1/n`.**

Let `μ` be a probability measure and `a` a family of square-integrable functions indexed by a
finite nonempty set `ι` of `m` elements whose Gram matrix `I = ∫ a a* dμ` is positive
definite.  Then for every `n ≥ m` there are `n` points, not necessarily distinct, and weights
`0 < wᵢ ≤ 1/n` with

`(1 - √((m-1)/n))² • I ≤ ∑ wᵢ a(xᵢ) a(xᵢ)*`.

This is `Discretization.bss_lower_le_one_div_of_gram_eq_one` for the normalized family
`I^{-1/2} a`, conjugated back by `Discretization.bss_of_gram_eq_one`, which carries the bound
on the weights along. -/
theorem bss_lower_le_one_div [Fintype ι] [Nonempty ι] [IsProbabilityMeasure μ]
    {a : Ω → ι → ℂ} (ha : ∀ k, MemLp (fun x => a x k) 2 μ) (hI : (gram a μ).PosDef)
    {n : ℕ} (hmn : Fintype.card ι ≤ n) :
    ∃ (x : Fin n → Ω) (w : Fin n → ℝ), (∀ i, 0 < w i) ∧ (∀ i, w i ≤ 1 / n) ∧
      (1 - Real.sqrt ((Fintype.card ι - 1) / n)) ^ 2 • gram a μ
        ≤ ∑ i, w i • vecMulVec (a (x i)) (star (a (x i))) := by
  obtain ⟨x, w, hw, hlow, hle⟩ := bss_of_gram_eq_one ha hI
    (C := (1 - Real.sqrt ((Fintype.card ι - 1) / n)) ^ 2)
    (P := fun _ w => ∀ i, w i ≤ 1 / (n : ℝ))
    fun _ ha' hgram' => by
      obtain ⟨x, w, hw, hle, hlow⟩ := bss_lower_le_one_div_of_gram_eq_one ha' hgram' hmn
      exact ⟨x, w, hw, hlow, hle⟩
  exact ⟨x, w, hw, hle, hlow⟩

/-- **The lower half of the sparsification theorem with equal weights.**

Under the hypotheses of `Discretization.bss_lower_le_one_div` there are `n` points, not
necessarily distinct, with

`(1 - √((m-1)/n))² • I ≤ (1/n) • ∑ᵢ a(xᵢ) a(xᵢ)*`.

Each weight `wᵢ ≤ 1/n` may be raised to `1/n`, since the matrices `a(xᵢ) a(xᵢ)*` are positive
semidefinite. -/
theorem bss_lower_equal_weights [Fintype ι] [Nonempty ι] [IsProbabilityMeasure μ]
    {a : Ω → ι → ℂ} (ha : ∀ k, MemLp (fun x => a x k) 2 μ) (hI : (gram a μ).PosDef)
    {n : ℕ} (hmn : Fintype.card ι ≤ n) :
    ∃ x : Fin n → Ω, (1 - Real.sqrt ((Fintype.card ι - 1) / n)) ^ 2 • gram a μ
      ≤ (1 / (n : ℝ)) • ∑ i, vecMulVec (a (x i)) (star (a (x i))) := by
  obtain ⟨x, w, -, hle, hlow⟩ := bss_lower_le_one_div ha hI hmn
  refine ⟨x, hlow.trans ?_⟩
  rw [Finset.smul_sum]
  exact Finset.sum_le_sum fun i _ =>
    smul_le_smul_of_nonneg_right (hle i) (posSemidef_vecMulVec_self_star _).nonneg

/-- **One-sided discretization of the `L₂`-norm**
(Chkifa–Dolbeault–Krieg–Ullrich, Proposition 8).

Let `μ` be a probability measure and `a` a family of square-integrable functions indexed by a
finite nonempty set `ι` of `m` elements with positive definite Gram matrix.  Then for every
`n ≥ m` there are `n` points, not necessarily distinct, with

`(1 - √((m-1)/n))² ∫ |f|² dμ ≤ (1/n) ∑ᵢ |f(xᵢ)|²`

for every function `f(y) = ⟪c, a(y)⟫` in the span.  This is
`Discretization.bss_lower_le_one_div` read through quadratic forms
(`Discretization.mul_integral_norm_sq_le_sum`), with each weight raised to `1/n`. -/
theorem exists_one_sided_discretization [Fintype ι] [Nonempty ι] [IsProbabilityMeasure μ]
    {a : Ω → ι → ℂ} (ha : ∀ k, MemLp (fun x => a x k) 2 μ) (hI : (gram a μ).PosDef)
    {n : ℕ} (hmn : Fintype.card ι ≤ n) :
    ∃ x : Fin n → Ω, ∀ c : ι → ℂ,
      (1 - Real.sqrt ((Fintype.card ι - 1) / n)) ^ 2 * ∫ y, ‖star c ⬝ᵥ a y‖ ^ 2 ∂μ
        ≤ 1 / (n : ℝ) * ∑ i, ‖star c ⬝ᵥ a (x i)‖ ^ 2 := by
  obtain ⟨x, w, -, hle, hlow⟩ := bss_lower_le_one_div ha hI hmn
  refine ⟨x, fun c => ?_⟩
  calc (1 - Real.sqrt ((Fintype.card ι - 1) / n)) ^ 2 * ∫ y, ‖star c ⬝ᵥ a y‖ ^ 2 ∂μ
      ≤ ∑ i, w i * ‖star c ⬝ᵥ a (x i)‖ ^ 2 := mul_integral_norm_sq_le_sum ha hlow c
    _ ≤ ∑ i, 1 / (n : ℝ) * ‖star c ⬝ᵥ a (x i)‖ ^ 2 :=
        Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hle i) (by positivity)
    _ = 1 / (n : ℝ) * ∑ i, ‖star c ⬝ᵥ a (x i)‖ ^ 2 := (Finset.mul_sum _ _ _).symm

end Discretization
