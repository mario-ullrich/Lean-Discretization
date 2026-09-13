/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Analysis.Real.Sqrt

/-!
# The gain from mixing in one more point

The Kiefer–Wolfowitz argument compares a design with the designs obtained from it by giving
a single new point the weight `α`.  By the matrix determinant lemma the determinant of the
Gram matrix is multiplied in that step by

`g α = (1-α)^m · (1 + α (t-1))`,   where `n = m + 1` is the number of functions

and `t` is the value at the new point of the quadratic form attached to the inverse Gram
matrix.  Everything that is needed from the maximality of the determinant is contained in
the behaviour of this one real function, so this file has no matrices in it:

* `Discretization.KieferWolfowitz.exists_mix_ge`: if `t > n` then some admissible weight `α`
  makes `g α` exceed `1` by a definite amount.  The weight is written down explicitly,
  `α = (t-n) / (2n(t-1))`, and the estimate comes from Bernoulli's inequality
  `(1-α)^m ≥ 1 - mα` (Mathlib's `one_add_mul_le_pow`).  This replaces the first-order
  condition `p'(0) ≤ 0` of the classical proof, and it is why no derivative of a
  determinant is needed anywhere.
* `Discretization.KieferWolfowitz.le_of_forall_mix_le_one`: if no mixture increases the
  determinant, then `t ≤ n`.  This is the case of an exactly attained maximum.
* `Discretization.KieferWolfowitz.le_add_of_forall_mix_le`: if no mixture increases the
  determinant by more than the factor `M`, and `M` is close enough to `1` in terms of `n`
  and `ε`, then `t ≤ n + ε`.  This is the case of a merely approximate maximum, which is
  what a supremum that need not be attained provides.

The two conclusions are the source of the two constants `√n` and `√(n+ε)` in the
Kiefer–Wolfowitz theorem.
-/

namespace Discretization.KieferWolfowitz

/-- **Mixing in a point where the quadratic form is large increases the determinant.**

If `t > n = m+1`, the weight `α = (t-n) / (2n(t-1))` lies in `[0,1)` and satisfies

`1 + (t-n)² / (4n(t-1)) ≤ (1-α)^m (1 + α(t-1))`.

The proof is Bernoulli's inequality `1 - mα ≤ (1-α)^m`, after which the difference of the
two sides is the explicit nonnegative quantity `(t-n)² / (4n²(t-1))`.  The chosen `α` is the
one for which the linear gain `α(t-n)` is twice the quadratic loss `(n-1)(t-1)α²`, so half
of the gain survives. -/
theorem exists_mix_ge (m : ℕ) {t : ℝ} (ht : (m : ℝ) + 1 < t) :
    ∃ α : ℝ, 0 ≤ α ∧ α < 1 ∧
      1 + (t - ((m : ℝ) + 1)) ^ 2 / (4 * ((m : ℝ) + 1) * (t - 1))
        ≤ (1 - α) ^ m * (1 + α * (t - 1)) := by
  have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  set n : ℝ := (m : ℝ) + 1 with hn
  have hmn : (m : ℝ) = n - 1 := by rw [hn]; ring
  have hn0 : (0 : ℝ) < n := by rw [hn]; linarith
  have ht1 : (0 : ℝ) < t - 1 := by rw [hn] at ht; linarith
  have htn : (0 : ℝ) < t - n := by linarith
  have hden : (0 : ℝ) < 2 * n * (t - 1) := by positivity
  set α : ℝ := (t - n) / (2 * n * (t - 1)) with hα
  have hα0 : 0 ≤ α := (div_pos htn hden).le
  have hαhalf : α ≤ 1 / 2 := by
    rw [hα, div_le_div_iff₀ hden (by norm_num)]
    nlinarith
  refine ⟨α, hα0, by linarith, ?_⟩
  -- Bernoulli's inequality
  have hlin : (0 : ℝ) ≤ 1 + α * (t - 1) := by positivity
  have hbern : 1 - (m : ℝ) * α ≤ (1 - α) ^ m := by
    have h := one_add_mul_le_pow (a := -α) (by linarith) m
    simpa [sub_eq_add_neg, mul_comm] using h
  refine le_trans ?_ (mul_le_mul_of_nonneg_right hbern hlin)
  -- and the exact expansion of the remaining difference
  rw [hmn]
  have hn' : n ≠ 0 := hn0.ne'
  have ht1' : t - 1 ≠ 0 := ht1.ne'
  have key : (1 - (n - 1) * α) * (1 + α * (t - 1)) - (1 + (t - n) ^ 2 / (4 * n * (t - 1)))
      = (t - n) ^ 2 / (4 * n ^ 2 * (t - 1)) := by
    rw [hα]; field_simp; ring
  have hrest : 0 ≤ (t - n) ^ 2 / (4 * n ^ 2 * (t - 1)) :=
    div_nonneg (sq_nonneg _) (by positivity)
  linarith

/-- **An exactly maximal determinant bounds the quadratic form by `n`.**

If no mixture increases the determinant, that is, if `g α ≤ 1` for every admissible weight,
then `t ≤ n`.  This is the sharp, `ε`-free form of the Kiefer–Wolfowitz bound, available
whenever the maximum of the determinant is attained. -/
theorem le_of_forall_mix_le_one (m : ℕ) {t : ℝ}
    (h : ∀ α : ℝ, 0 ≤ α → α < 1 → (1 - α) ^ m * (1 + α * (t - 1)) ≤ 1) :
    t ≤ (m : ℝ) + 1 := by
  by_contra hc
  have hc' : (m : ℝ) + 1 < t := not_le.mp hc
  have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  obtain ⟨α, hα0, hα1, hge⟩ := exists_mix_ge m hc'
  have hpos : 0 < (t - ((m : ℝ) + 1)) ^ 2 / (4 * ((m : ℝ) + 1) * (t - 1)) :=
    div_pos (pow_pos (by linarith) 2) (by nlinarith)
  linarith [h α hα0 hα1]

/-- **An almost maximal determinant bounds the quadratic form by `n + ε`.**

If no mixture increases the determinant by more than the factor `M`, and `M` is close
enough to `1`, namely `M - 1 < ε² / (4n(n+ε-1))`, then `t ≤ n + ε`.  Written with `n = m+1`
the denominator is `4(m+1)(m+ε)`.

Beyond `n` the quantity `(t-n)²/(t-1)` grows, which is used in the factored form
`s²(m+ε) - ε²(s+m) = (s-ε)(m(s+ε) + εs)` with `s = t-n`. -/
theorem le_add_of_forall_mix_le (m : ℕ) {t M ε : ℝ} (hε : 0 < ε)
    (hM : M - 1 < ε ^ 2 / (4 * ((m : ℝ) + 1) * ((m : ℝ) + ε)))
    (h : ∀ α : ℝ, 0 ≤ α → α < 1 → (1 - α) ^ m * (1 + α * (t - 1)) ≤ M) :
    t ≤ (m : ℝ) + 1 + ε := by
  by_contra hc
  have hc' : (m : ℝ) + 1 + ε < t := not_le.mp hc
  have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  have ht1 : (0 : ℝ) < t - 1 := by linarith
  have hme : (0 : ℝ) < (m : ℝ) + ε := by linarith
  obtain ⟨α, hα0, hα1, hge⟩ := exists_mix_ge m (by linarith)
  have hlt : (t - ((m : ℝ) + 1)) ^ 2 / (4 * ((m : ℝ) + 1) * (t - 1))
      < ε ^ 2 / (4 * ((m : ℝ) + 1) * ((m : ℝ) + ε)) :=
    lt_of_le_of_lt (by linarith [h α hα0 hα1]) hM
  rw [div_lt_div_iff₀ (by positivity) (by positivity)] at hlt
  -- cancel the common factor `4(m+1)` and use `t - 1 = s + m` with `s = t - (m+1) > ε`
  have hstep : (t - ((m : ℝ) + 1)) ^ 2 * ((m : ℝ) + ε) < ε ^ 2 * (t - 1) := by
    nlinarith [hlt]
  nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ t - ((m : ℝ) + 1) - ε)
    (by nlinarith : (0 : ℝ) ≤ (m : ℝ) * (t - ((m : ℝ) + 1) + ε) + (t - ((m : ℝ) + 1)) * ε)]

end Discretization.KieferWolfowitz
