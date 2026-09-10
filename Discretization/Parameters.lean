/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
import Mathlib.Analysis.Real.Sqrt

/-!
# The parameters of the construction

The construction runs on four real numbers derived from the number `m` of functions in the
first family, the effective dimension `M` of the second one, and the number `n` of sampling
points to be produced:

`r = √((m-1)/n)`,  `s = √((M-1)/n)`,  `δ = (1-r)/n`,  `ζ = (1+s)/n`.

They are chosen so that the initial gap closes exactly, `1/δ - Φ(A₀) = n = 1/ζ + Ψ_J(B₀)`,
and so that the two frame bounds come out as `(1-r)²` and `(1+s)² Λ`.  This file collects
the arithmetic of these four numbers, with no matrices in sight:

* `Discretization.sqrt_div_pos` and `Discretization.sqrt_div_lt_one` — `0 < r < 1` for
  `1 < m ≤ n`, which is what makes `δ` positive and `A₀` positive definite;
* `Discretization.one_div_le_sqrt_div` — `1/n ≤ s`, the quantitative form of the hypothesis
  `M ≥ 1 + 1/n`, and the reason the final coefficient of `J` is nonnegative;
* `Discretization.eq_mul_sq_sqrt_div_add_one` — `M = n s² + 1`, which turns the effective
  dimension into the parameter `s`;
* `Discretization.one_div_add_div_eq` and `Discretization.one_div_sub_div_eq` — the two
  identities `1/ζ + s/ζ = n` and `1/δ - r/δ = n` that close the initial gap;
* `Discretization.lt_inv_of_le_one_div_sub` — an open gap keeps the shift `δ` admissible,
  which is the hypothesis `δ < Φ(A)⁻¹` of the barrier lemma.

The square roots are never unfolded: only `Real.sq_sqrt`, `Real.sqrt_nonneg`,
`Real.le_sqrt` and `Real.sqrt_lt'` are used.
-/

namespace Discretization

/-- For `1 < m` and `0 < n` the parameter `r = √((m-1)/n)` is positive. -/
theorem sqrt_div_pos {m n : ℝ} (hn : 0 < n) (hm : 1 < m) : 0 < Real.sqrt ((m - 1) / n) :=
  Real.sqrt_pos.2 (div_pos (by linarith) hn)

/-- For `1 ≤ m ≤ n` the parameter `r = √((m-1)/n)` is smaller than one.  This is what leaves
room for the shift `δ = (1-r)/n`. -/
theorem sqrt_div_lt_one {m n : ℝ} (hn : 0 < n) (hmn : m ≤ n) : Real.sqrt ((m - 1) / n) < 1 := by
  rw [Real.sqrt_lt' zero_lt_one, one_pow, div_lt_one hn]
  linarith

/-- The square of `r = √((m-1)/n)` is `(m-1)/n`, provided `1 ≤ m`. -/
theorem sq_sqrt_div {m n : ℝ} (hn : 0 < n) (hm : 1 ≤ m) :
    Real.sqrt ((m - 1) / n) ^ 2 = (m - 1) / n :=
  Real.sq_sqrt (div_nonneg (by linarith) hn.le)

/-- **The effective dimension in terms of its parameter:** `M = n s² + 1` for
`s = √((M-1)/n)`.  Read from right to left this says that `s` measures how far the effective
dimension exceeds one, on the scale `1/n`. -/
theorem eq_mul_sq_sqrt_div_add_one {M n : ℝ} (hn : 0 < n) (hM : 1 ≤ M) :
    M = n * Real.sqrt ((M - 1) / n) ^ 2 + 1 := by
  rw [sq_sqrt_div hn hM]
  field_simp
  ring

/-- **The hypothesis `M ≥ 1 + 1/n` in terms of the parameter `s`:** it says exactly that
`s = √((M-1)/n)` is at least `1/n`.

This is the smallest effective dimension the potential argument can handle; below it the
upper verifier is replaced by a constant, see `Discretization.bss_generalized_of_small_dim`. -/
theorem one_div_le_sqrt_div {M n : ℝ} (hn : 0 < n) (hM : 1 + 1 / n ≤ M) :
    1 / n ≤ Real.sqrt ((M - 1) / n) := by
  have h1 : 1 ≤ (M - 1) * n := by
    have := (div_le_iff₀ hn).1 (show 1 / n ≤ M - 1 by linarith)
    linarith
  have h0 : 0 ≤ (M - 1) / n := div_nonneg (by nlinarith) hn.le
  rw [Real.le_sqrt (by positivity) h0, div_pow, one_pow, div_le_div_iff₀ (by positivity) hn]
  nlinarith [mul_le_mul_of_nonneg_left h1 hn.le]

/-- Reciprocals: `1/n ≤ s` with `s > 0` gives `1/s ≤ n`. -/
theorem one_div_le_of_one_div_le {n s : ℝ} (hn : 0 < n) (hs : 0 < s) (h : 1 / n ≤ s) :
    1 / s ≤ n := by
  rw [div_le_iff₀ hs]
  have h3 := mul_le_mul_of_nonneg_left h hn.le
  rwa [mul_one_div, div_self hn.ne'] at h3

/-- **The initial gap of the upper potential closes exactly:** `1/ζ + s/ζ = n` for
`ζ = (1+s)/n`. -/
theorem one_div_add_div_eq {n s : ℝ} (hn : 0 < n) (hs : 1 + s ≠ 0) :
    1 / ((1 + s) / n) + s / ((1 + s) / n) = n := by
  field_simp

/-- **The initial gap of the lower potential closes exactly:** `1/δ - r/δ = n` for
`δ = (1-r)/n`. -/
theorem one_div_sub_div_eq {n r : ℝ} (hn : 0 < n) (hr : 1 - r ≠ 0) :
    1 / ((1 - r) / n) - r / ((1 - r) / n) = n := by
  field_simp

/-- **An open gap keeps the shift admissible.**  If some positive number `c` fits below
`1/δ - Φ`, then `δ < Φ⁻¹`, which is the hypothesis under which shrinking a positive definite
matrix by `δ • 1` keeps it positive definite.

In the construction `c` is `1/ζ + Ψ_J(B)`, and in the edge case of a small effective
dimension it is `n`. -/
theorem lt_inv_of_le_one_div_sub {δ Φ c : ℝ} (hδ : 0 < δ) (hΦ : 0 < Φ) (hc : 0 < c)
    (h : c ≤ 1 / δ - Φ) : δ < Φ⁻¹ := by
  rw [lt_inv_comm₀ hδ hΦ, inv_eq_one_div]
  linarith

end Discretization
