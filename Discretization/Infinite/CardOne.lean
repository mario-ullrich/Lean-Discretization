/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
import Discretization.CardOne
import Discretization.Infinite.MainTheorem

/-!
# A single function, with a countable second family

The edge case `m = card ι = 1` of `Discretization.CardOne`, for a second family indexed by a
countable set.  The reason for it is the same: the initial matrix `A₀ = (δ m / r) • 1`
involves `r = √((m-1)/n)`, which vanishes for `m = 1`, so the lower potential cannot be used.
As there, it is not needed: the lower verifier is replaced by the constant

`L(x) = n |a(x)|²`,   with   `∫ L dμ = n`

for a normalized single function, and the largest admissible weight `1/wᵢ = L(xᵢ)` makes the
lower frame bound the identity `∑ wᵢ |a(xᵢ)|² = 1 = (1 - √((m-1)/n))²`.

Only the upper half is new, and it is the one of `Discretization.Infinite.MainTheorem`: the
construction tracks the operator `B_k` alone
(`Discretization.Infinite.exists_points_weights_of_unique`), and the read-off is the same
`Discretization.Infinite.upper_frame_bound`.  Everything on the lower side is the finite
statement verbatim, `Discretization.sum_smul_vecMulVec_eq_one`.

The result is `Discretization.Infinite.bss_generalized_of_unique`.
-/

open MeasureTheory
open scoped InnerProductSpace ComplexOrder MatrixOrder
open InnerProductSpace
open ContinuousLinearMap

namespace Discretization

namespace Infinite

variable {ι κ Ω H : Type*} [DecidableEq ι] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [MeasurableSpace Ω] {μ : Measure Ω} {e : HilbertBasis κ ℂ H}
  {J : H →L[ℂ] H}

/-! ### The one-sided construction -/

/-- **The construction for a single function, with an operator on the upper side.**  Only the
upper operator is tracked; the weights are chosen as large as the constant lower verifier
allows, so that each point contributes exactly `1/n` to the lower frame bound.

This is `Discretization.exists_points_weights_of_unique` with the operator barrier lemma in
place of the matrix one. -/
theorem exists_points_weights_of_unique [Unique ι] [Nonempty κ] [Countable κ]
    (hJ : IsFiniteTracePos e J) {B₀ : H →L[ℂ] H} (hB₀ : IsStrictlyPositive B₀) {ζ : ℝ}
    (hζ : 0 < ζ) {a : Ω → ι → ℂ} {b : Ω → H} (ha : ∀ k, MemLp (fun x => a x k) 2 μ)
    (hb : MemLp b 2 μ) (hgrama : gram a μ = 1)
    (hgramb : ∀ u, RCLike.re ⟪u, J u⟫_ℂ = ∫ x, ‖⟪u, b x⟫_ℂ‖ ^ 2 ∂μ) {n : ℕ}
    (hgap : 1 / ζ + upperPotential e J B₀ ≤ n) (k : ℕ) :
    ∃ (x : Fin k → Ω) (w : Fin k → ℝ), (∀ i, 0 < w i) ∧
      IsStrictlyPositive (upperState J B₀ ζ b x w) ∧
      upperPotential e J (upperState J B₀ ζ b x w) ≤ upperPotential e J B₀ ∧
      ∀ i, w i * ((n : ℝ) * ‖a (x i) default‖ ^ 2) = 1 := by
  induction k with
  | zero => exact ⟨Fin.elim0, Fin.elim0, fun i => i.elim0, by simpa using hB₀, by simp,
      fun i => i.elim0⟩
  | succ k ih =>
    obtain ⟨x, w, hwpos, hBk, hΨ, hwk⟩ := ih
    -- the average of the constant lower verifier is `n`, and dominates that of the upper one
    have hint : ∫ y, (n : ℝ) * ‖a y default‖ ^ 2 ∂μ = n := by
      rw [integral_const_mul, integral_norm_sq_eq_one ha hgrama, mul_one]
    have hlt : ∫ y, upperVerifier e J (upperState J B₀ ζ b x w) ζ (b y) ∂μ
        < ∫ y, (n : ℝ) * ‖a y default‖ ^ 2 ∂μ := by
      rw [hint]
      have h1 := integral_upperVerifier_lt hJ hBk hζ hb hgramb
      linarith
    obtain ⟨y, hy⟩ := exists_lt_of_integral_lt (μ := μ)
      (f := fun y => (n : ℝ) * ‖a y default‖ ^ 2)
      (g := fun y => upperVerifier e J (upperState J B₀ ζ b x w) ζ (b y))
      ((integrable_norm_sq ha default).const_mul _)
      (integrable_upperVerifier hb J (upperState J B₀ ζ b x w) ζ) hlt
    -- the weight allowed by the constant verifier
    have hU0 : 0 ≤ upperVerifier e J (upperState J B₀ ζ b x w) ζ (b y) :=
      upperVerifier_nonneg hJ hBk hζ (b y)
    have hLpos : 0 < (n : ℝ) * ‖a y default‖ ^ 2 := lt_of_le_of_lt hU0 hy
    obtain ⟨hwnew, -, hcondU⟩ := weight_of_verifier_lt hU0 hy
    obtain ⟨hBnew, hΨnew⟩ := upperPotential_update_le hJ hBk hζ (b y) hwnew hcondU
    refine ⟨Fin.snoc x y, Fin.snoc w (1 / ((n : ℝ) * ‖a y default‖ ^ 2)), ?_, ?_, ?_, ?_⟩
    · exact forall_snoc_pos hwpos hwnew
    · rw [upperState_snoc]; exact hBnew
    · rw [upperState_snoc]; exact hΨnew.trans hΨ
    · refine Fin.lastCases ?_ ?_
      · simpa using one_div_mul_cancel hLpos.ne'
      · intro j; simpa using hwk j

/-! ### The theorem for a single function -/

/-- **Generalized sparsification theorem for a one-element first family and a countable
second family.**

For `card ι = 1` the lower frame bound is the identity `1 = (1 - √((m-1)/n))²`, and the upper
bound is the one of `Discretization.Infinite.bss_generalized_of_gram_eq_one`.  Together with
that theorem, which needs `m ≥ 2`, every size of the first family is covered. -/
theorem bss_generalized_of_unique [Unique ι] [Nonempty κ] [Countable κ]
    (hJ : IsFiniteTracePos e J) {Λ : ℝ} (hΛ : 0 < Λ)
    (hJΛ : J ≤ Λ • (1 : H →L[ℂ] H)) {a : Ω → ι → ℂ} {b : Ω → H}
    (ha : ∀ k, MemLp (fun x => a x k) 2 μ) (hb : MemLp b 2 μ) (hgrama : gram a μ = 1)
    (hgramb : ∀ u, RCLike.re ⟪u, J u⟫_ℂ = ∫ x, ‖⟪u, b x⟫_ℂ‖ ^ 2 ∂μ)
    {n : ℕ} (hn : 0 < n) (hM : 1 + 1 / (n : ℝ) ≤ traceAlong e J / Λ) :
    ∃ (x : Fin n → Ω) (w : Fin n → ℝ), (∀ i, 0 < w i) ∧
      (1 : Matrix ι ι ℂ) ≤ ∑ i, w i • Matrix.vecMulVec (a (x i)) (star (a (x i))) ∧
      ∑ i, w i • rankOne ℂ (b (x i)) (b (x i))
        ≤ ((1 + Real.sqrt ((traceAlong e J / Λ - 1) / n)) ^ 2 * Λ)
            • (1 : H →L[ℂ] H) := by
  -- the parameters of the upper half of the construction
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  set M : ℝ := traceAlong e J / Λ with hMdef
  set s : ℝ := Real.sqrt ((M - 1) / n) with hsdef
  have hs0 : 1 / (n : ℝ) ≤ s := one_div_le_sqrt_div hn0 hM
  have hspos : 0 < s := lt_of_lt_of_le (by positivity) hs0
  have hM1 : (1 : ℝ) ≤ M := by
    have h1 : 0 < 1 / (n : ℝ) := by positivity
    linarith
  have hM_eq : M = (n : ℝ) * s ^ 2 + 1 := eq_mul_sq_sqrt_div_add_one hn0 hM1
  have hT : traceAlong e J = Λ * ((n : ℝ) * s ^ 2 + 1) := by
    rw [← hM_eq, hMdef]
    field_simp
  set ζ : ℝ := (1 + s) / n with hζdef
  have hζ0 : 0 < ζ := div_pos (by linarith) hn0
  clear_value M s
  have hT0 : 0 < traceAlong e J := hJ.traceAlong_pos
  set d₀ : ℝ := ζ * traceAlong e J / s with hd₀def
  have hd₀0 : 0 < d₀ := div_pos (by positivity) hspos
  have hB₀ : IsStrictlyPositive (d₀ • (1 : H →L[ℂ] H)) := isStrictlyPositive_smul_one hd₀0
  clear_value ζ d₀
  have hΨ₀ : upperPotential e J (d₀ • (1 : H →L[ℂ] H)) = s / ζ := by
    rw [upperPotential_smul_one hd₀0.ne', hd₀def]
    field_simp
  have h1s : (1 : ℝ) + s ≠ 0 := by positivity
  have hgap : 1 / ζ + upperPotential e J (d₀ • (1 : H →L[ℂ] H)) ≤ n := by
    rw [hΨ₀, hζdef, one_div_add_div_eq hn0 h1s]
  -- run the one-sided construction
  obtain ⟨x, w, hwpos, hBn, hΨn, hwk⟩ :=
    exists_points_weights_of_unique hJ hB₀ hζ0 ha hb hgrama hgramb hgap n
  refine ⟨x, w, hwpos, ?_, ?_⟩
  · -- the lower frame bound is an identity: each point contributes exactly `1/n`
    rw [sum_smul_vecMulVec_eq_one hn0 x w hwk]
  · -- the upper frame bound, exactly as in the main theorem
    exact upper_frame_bound hJ hΛ hJΛ hn0 hs0 hζdef hd₀def hT hBn (hΨ₀ ▸ hΨn)

end Infinite

end Discretization
