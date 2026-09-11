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

* `Discretization.sqrt_div_pos` and `Discretization.sqrt_div_lt_one`: `0 < r < 1` for
  `1 < m ≤ n`, which is what makes `δ` positive and `A₀` positive definite;
* `Discretization.one_div_le_sqrt_div`: `1/n ≤ s`, the quantitative form of the hypothesis
  `M ≥ 1 + 1/n`, and the reason the final coefficient of `J` is nonnegative;
* `Discretization.eq_mul_sq_sqrt_div_add_one`: `M = n s² + 1`, which turns the effective
  dimension into the parameter `s`;
* `Discretization.one_div_add_div_eq` and `Discretization.one_div_sub_div_eq`: the two
  identities `1/ζ + s/ζ = n` and `1/δ - r/δ = n` that close the initial gap;
* `Discretization.lt_inv_of_le_one_div_sub`: an open gap keeps the shift `δ` admissible,
  which is the hypothesis `δ < Φ(A)⁻¹` of the barrier lemma;
* `Discretization.nonneg_mul_sub_inv_div` and `Discretization.frame_constant_eq`: the
  coefficient of `J` in the upper read-off is nonnegative, and the constant it produces is
  `(1+s)² Λ`;
* `Discretization.le_sq_one_add_sqrt_div` and `Discretization.le_sq_one_add_sqrt_div_mul`: an
  effective dimension below `1 + 1/n` is itself below `(1+s)²`, which is what the edge cases
  of a small effective dimension need.

Everything here is used twice, once for a finite second family and once for a countable one.

The square roots are never unfolded: only `Real.sq_sqrt`, `Real.sqrt_pos`, `Real.le_sqrt`
and `Real.sqrt_lt'` are used.
-/

namespace Discretization

/-- For `1 < m` and `0 < n` the parameter `r = √((m-1)/n)` is positive. -/
theorem sqrt_div_pos {m n : ℝ} (hn : 0 < n) (hm : 1 < m) : 0 < Real.sqrt ((m - 1) / n) :=
  Real.sqrt_pos.2 (div_pos (by linarith) hn)

/-- For `m ≤ n` the parameter `r = √((m-1)/n)` is smaller than one.  This is what leaves
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

This is the smallest effective dimension the potential argument can handle; below it a
constant upper verifier is used instead, see `Discretization.bss_generalized_of_small_dim`. -/
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

/-- **The coefficient of `J` in the upper read-off is nonnegative:**
`0 ≤ n ζ - (s/ζ)⁻¹` for `ζ = (1+s)/n` and `1/n ≤ s`.

Without this the bound `J ≼ Λ • 1` could not be applied to that coefficient, and it is
exactly the hypothesis `M ≥ 1 + 1/n` that makes it true. -/
theorem nonneg_mul_sub_inv_div {n s ζ : ℝ} (hn0 : 0 < n) (hs0 : 1 / n ≤ s)
    (hζ : ζ = (1 + s) / n) : 0 ≤ n * ζ - (s / ζ)⁻¹ := by
  have hspos : 0 < s := lt_of_lt_of_le (by positivity) hs0
  have hζ0 : 0 < ζ := by rw [hζ]; exact div_pos (by linarith) hn0
  rw [inv_div, show ζ / s = ζ * (1 / s) by ring]
  nlinarith [hζ0, one_div_le_of_one_div_le hn0 hspos hs0]

/-- **The constant of the upper frame bound:** `d₀ + (n ζ - (s/ζ)⁻¹) Λ = (1+s)² Λ`, for
`ζ = (1+s)/n`, `d₀ = ζ T / s` and `T = Λ (n s² + 1)`.

Here `T` is the trace of the Gram operator of the second family; the identity is what turns
the read-off of the potential into the frame bound of the theorem. -/
theorem frame_constant_eq {n s ζ d₀ T Λ : ℝ} (hn0 : 0 < n) (hs0 : 1 / n ≤ s) (hΛ : 0 < Λ)
    (hζ : ζ = (1 + s) / n) (hd₀ : d₀ = ζ * T / s) (hT : T = Λ * (n * s ^ 2 + 1)) :
    d₀ + (n * ζ - (s / ζ)⁻¹) * Λ = (1 + s) ^ 2 * Λ := by
  have hspos : 0 < s := lt_of_lt_of_le (by positivity) hs0
  rw [hd₀, hT, hζ, inv_div]
  field_simp
  ring

/-- **A small effective dimension is below the upper frame constant:** `M ≤ (1 + s)²` for
`s = √((M-1)/n)` and `M ≤ 1 + 1/n`.

This is what lets the edge case of a small effective dimension read the frame bound of the
theorem off the crude estimate alone.  For `M ≤ 1` it holds because `s` is nonnegative.
Otherwise `M ≤ 1 + 1/n` forces `s ≤ 1/n`, hence `n s ≤ 1` and `M = 1 + n s² ≤ 1 + s`. -/
theorem le_sq_one_add_sqrt_div {M n : ℝ} (hn0 : 0 < n) (hM : M ≤ 1 + 1 / n) :
    M ≤ (1 + Real.sqrt ((M - 1) / n)) ^ 2 := by
  have hs0 : 0 ≤ Real.sqrt ((M - 1) / n) := Real.sqrt_nonneg _
  by_cases hM1 : M ≤ 1
  · nlinarith [hs0]
  · replace hM1 := not_le.mp hM1
    set s : ℝ := Real.sqrt ((M - 1) / n) with hsdef
    have hs2 : s ^ 2 = (M - 1) / n := sq_sqrt_div hn0 (by linarith)
    have h1 : n * s ^ 2 = M - 1 := by rw [hs2]; field_simp
    have h2 : s ^ 2 ≤ (1 / n) ^ 2 := by
      rw [hs2]
      have h3 : M - 1 ≤ 1 / n := by linarith
      calc (M - 1) / n ≤ (1 / n) / n := by gcongr
        _ = (1 / n) ^ 2 := by field_simp
    have h4 : s ≤ 1 / n := by nlinarith [hs0, h2, hn0]
    have h5 : n * s ≤ 1 := by
      have h6 := mul_le_mul_of_nonneg_left h4 hn0.le
      rwa [mul_one_div, div_self hn0.ne'] at h6
    nlinarith [h1, h5, hs0]

/-- **The upper frame constant dominates the trace** when the effective dimension is small:
`T ≤ (1 + s)² Λ` for `s = √((T/Λ - 1)/n)` and `T/Λ ≤ 1 + 1/n`.

This is `Discretization.le_sq_one_add_sqrt_div` with the `Λ` multiplied out, the form in
which the edge cases read off their upper frame bound. -/
theorem le_sq_one_add_sqrt_div_mul {T Λ n : ℝ} (hn0 : 0 < n) (hΛ : 0 < Λ)
    (h : T / Λ ≤ 1 + 1 / n) : T ≤ (1 + Real.sqrt ((T / Λ - 1) / n)) ^ 2 * Λ := by
  have hMs := le_sq_one_add_sqrt_div hn0 h
  rw [div_le_iff₀ hΛ] at hMs
  linarith

/-- **An open gap keeps the shift admissible.**  If `c ≤ 1/δ - Φ` for some positive `c`, then
`δ < Φ⁻¹`.  That is the hypothesis under which `A - δ • 1` stays positive definite.

In the construction `c` is `1/ζ + Ψ_J(B)`, and in the edge case of a small effective
dimension it is `n`. -/
theorem lt_inv_of_le_one_div_sub {δ Φ c : ℝ} (hδ : 0 < δ) (hΦ : 0 < Φ) (hc : 0 < c)
    (h : c ≤ 1 / δ - Φ) : δ < Φ⁻¹ := by
  rw [lt_inv_comm₀ hδ hΦ, inv_eq_one_div]
  linarith

end Discretization
