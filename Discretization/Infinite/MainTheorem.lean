/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
import Discretization.Infinite.Bounds
import Discretization.Infinite.Iteration
import Discretization.MainTheorem

/-!
# The generalized sparsification theorem with a countable second family

The theorem `Discretization.bss_generalized_of_gram_eq_one` for a second family indexed by a
countable set:
the first family is finite, with Gram matrix the identity, and the second is a
square-integrable map `b : Ω → H` into a Hilbert space whose Gram operator `J` is positive,
injective and of finite trace, bounded by `Λ • 1`.  With

`m = card ι`,  `M = Tr J / Λ`,  `r = √((m-1)/n)`,  `s = √((M-1)/n)`,

the conclusion is that for every `n ≥ m` there are `n` points and positive weights with

`(1 - r)² • 1 ≼ ∑ᵢ wᵢ a(xᵢ) a(xᵢ)*`  and  `∑ᵢ wᵢ b(xᵢ) b(xᵢ)* ≼ (1 + s)² Λ • 1`,

the first in the matrix order, the second in the operator order.  This is
`Discretization.Infinite.bss_generalized_of_gram_eq_one`.

The lower half and the arithmetic of the four parameters are those of the finite case
(`Discretization.lower_frame_bound`, `Discretization.Parameters`).  This file proves the
operator counterpart of the upper read-off and assembles the theorem.
-/

open MeasureTheory
open scoped InnerProductSpace ComplexOrder MatrixOrder
open InnerProductSpace
open ContinuousLinearMap

namespace Discretization

namespace Infinite

variable {ι κ Ω H : Type*} [Fintype ι] [DecidableEq ι] [NormedAddCommGroup H]
  [InnerProductSpace ℂ H] [CompleteSpace H] {e : HilbertBasis κ ℂ H} {J : H →L[ℂ] H}

/-! ### Multiples of the identity -/

omit [CompleteSpace H] in
/-- The inverse of a positive multiple of the identity. -/
theorem inverse_smul_one {c : ℝ} (hc : c ≠ 0) :
    Ring.inverse (c • (1 : H →L[ℂ] H)) = c⁻¹ • (1 : H →L[ℂ] H) := by
  refine Ring.inverse_eq_of_mul_eq_one ?_ ?_ <;>
    rw [smul_mul_assoc, one_mul, smul_smul]
  · rw [mul_inv_cancel₀ hc, one_smul]
  · rw [inv_mul_cancel₀ hc, one_smul]

/-- A positive multiple of the identity is strictly positive. -/
theorem isStrictlyPositive_smul_one {c : ℝ} (hc : 0 < c) :
    IsStrictlyPositive (c • (1 : H →L[ℂ] H)) := by
  refine ⟨smul_nonneg hc.le zero_le_one, ⟨⟨c • 1, c⁻¹ • 1, ?_, ?_⟩, rfl⟩⟩ <;>
    rw [smul_mul_assoc, one_mul, smul_smul]
  · rw [mul_inv_cancel₀ hc.ne', one_smul]
  · rw [inv_mul_cancel₀ hc.ne', one_smul]

omit [CompleteSpace H] in
/-- `Ψ_J(c • 1) = Tr J / c`. -/
theorem upperPotential_smul_one {c : ℝ} (hc : c ≠ 0) :
    upperPotential e J (c • (1 : H →L[ℂ] H)) = traceAlong e J / c := by
  rw [upperPotential, inverse_smul_one hc, mul_smul_comm, mul_one, traceAlong_smul,
    div_eq_inv_mul]

/-! ### Reading off the upper frame bound -/

/-- **The upper frame bound.**  If the final upper state, started from `c₀ • 1`, is strictly
positive with upper potential at most `c`, then the accumulated sum of rank-one operators is
at most `c₀ • 1 + (k ζ - c⁻¹) • J`. -/
theorem upper_bound_of_state [Nonempty κ] (hJ : IsFiniteTracePos e J) {c₀ ζ : ℝ}
    {b : Ω → H} {k : ℕ} {x : Fin k → Ω} {w : Fin k → ℝ}
    (hstate : IsStrictlyPositive (upperState J (c₀ • (1 : H →L[ℂ] H)) ζ b x w)) {c : ℝ}
    (hpot : upperPotential e J (upperState J (c₀ • (1 : H →L[ℂ] H)) ζ b x w) ≤ c) :
    ∑ i, w i • rankOne ℂ (b (x i)) (b (x i))
      ≤ c₀ • (1 : H →L[ℂ] H) + ((k : ℝ) * ζ - c⁻¹) • J := by
  have hΨ0 : 0 < upperPotential e J (upperState J (c₀ • (1 : H →L[ℂ] H)) ζ b x w) :=
    upperPotential_pos hJ hstate
  have h1 : (upperPotential e J (upperState J (c₀ • (1 : H →L[ℂ] H)) ζ b x w))⁻¹ • J
      ≤ upperState J (c₀ • (1 : H →L[ℂ] H)) ζ b x w :=
    inv_upperPotential_smul_le hJ hstate
  have hinv : c⁻¹
      ≤ (upperPotential e J (upperState J (c₀ • (1 : H →L[ℂ] H)) ζ b x w))⁻¹ :=
    inv_anti₀ hΨ0 hpot
  have h2 : c⁻¹ • J ≤ upperState J (c₀ • (1 : H →L[ℂ] H)) ζ b x w :=
    (smul_le_smul_of_nonneg_right hinv hJ.nonneg).trans h1
  have h4 : upperState J (c₀ • (1 : H →L[ℂ] H)) ζ b x w
      = c₀ • (1 : H →L[ℂ] H) + ((k : ℝ) * ζ) • J
        - ∑ i, w i • rankOne ℂ (b (x i)) (b (x i)) := by
    simp only [upperState]
  rw [h4] at h2
  have h5 := sub_le_sub_left h2 (c₀ • (1 : H →L[ℂ] H) + ((k : ℝ) * ζ) • J)
  calc ∑ i, w i • rankOne ℂ (b (x i)) (b (x i))
      = c₀ • (1 : H →L[ℂ] H) + ((k : ℝ) * ζ) • J
        - (c₀ • (1 : H →L[ℂ] H) + ((k : ℝ) * ζ) • J
          - ∑ i, w i • rankOne ℂ (b (x i)) (b (x i))) := by module
    _ ≤ c₀ • (1 : H →L[ℂ] H) + ((k : ℝ) * ζ) • J - c⁻¹ • J := h5
    _ = c₀ • (1 : H →L[ℂ] H) + ((k : ℝ) * ζ - c⁻¹) • J := by module

/-- **The upper frame bound of the theorem.**  Started from `B₀ = d₀ • 1` with
`d₀ = ζ Tr J / s`, `ζ = (1+s)/n` and `Tr J = Λ (n s² + 1)`, a final upper potential of at
most `s/ζ` turns into the frame bound `(1+s)² Λ • 1`.

This is the operator counterpart of `Discretization.upper_frame_bound`, with the same
arithmetic. -/
theorem upper_frame_bound [Nonempty κ] (hJ : IsFiniteTracePos e J) {Λ : ℝ} (hΛ : 0 < Λ)
    (hJΛ : J ≤ Λ • (1 : H →L[ℂ] H)) {n : ℕ} (hn0 : (0 : ℝ) < n) {s ζ d₀ : ℝ}
    (hs0 : 1 / (n : ℝ) ≤ s) (hζ : ζ = (1 + s) / n) (hd₀ : d₀ = ζ * traceAlong e J / s)
    (hT : traceAlong e J = Λ * ((n : ℝ) * s ^ 2 + 1)) {b : Ω → H} {x : Fin n → Ω}
    {w : Fin n → ℝ}
    (hBn : IsStrictlyPositive (upperState J (d₀ • (1 : H →L[ℂ] H)) ζ b x w))
    (hΨn : upperPotential e J (upperState J (d₀ • (1 : H →L[ℂ] H)) ζ b x w) ≤ s / ζ) :
    ∑ i, w i • rankOne ℂ (b (x i)) (b (x i))
      ≤ ((1 + s) ^ 2 * Λ) • (1 : H →L[ℂ] H) := by
  have hcoef0 : 0 ≤ (n : ℝ) * ζ - (s / ζ)⁻¹ := nonneg_mul_sub_inv_div hn0 hs0 hζ
  calc ∑ i, w i • rankOne ℂ (b (x i)) (b (x i))
      ≤ d₀ • (1 : H →L[ℂ] H) + ((n : ℝ) * ζ - (s / ζ)⁻¹) • J :=
        upper_bound_of_state hJ hBn hΨn
    _ ≤ d₀ • (1 : H →L[ℂ] H)
          + (((n : ℝ) * ζ - (s / ζ)⁻¹) * Λ) • (1 : H →L[ℂ] H) := by
        have hstep : (((n : ℝ) * ζ - (s / ζ)⁻¹) • J : H →L[ℂ] H)
            ≤ (((n : ℝ) * ζ - (s / ζ)⁻¹) * Λ) • (1 : H →L[ℂ] H) := by
          rw [← smul_smul]
          exact smul_le_smul_of_nonneg_left hJΛ hcoef0
        exact add_le_add le_rfl hstep
    _ = ((1 + s) ^ 2 * Λ) • (1 : H →L[ℂ] H) := by
        rw [← add_smul]
        congr 1
        exact frame_constant_eq hn0 hs0 hΛ hζ hd₀ hT

/-! ### The theorem -/

variable [MeasurableSpace Ω] {μ : Measure Ω}

/-- **Generalized sparsification theorem for a countable second family**
(Chkifa–Dolbeault–Krieg–Ullrich, Theorem 3).

Let `a` be a family of square-integrable functions indexed by a finite set `ι` of `m ≥ 2`
elements whose Gram matrix is the identity, and let `b : Ω → H` be square-integrable with
Gram operator `J`, that is `Re ⟪u, J u⟫ = ∫ |⟪u, b x⟫|² dμ` for every `u`.  Assume `J`
positive, injective and of finite trace, bounded by `Λ • 1`, and let `M = Tr J / Λ` be the
effective dimension of the second family, with `M ≥ 1 + 1/n`.  Then for every `n ≥ m` there
are `n` points and positive weights such that

`(1 - √((m-1)/n))² • 1 ≼ ∑ᵢ wᵢ a(xᵢ) a(xᵢ)*`  and
`∑ᵢ wᵢ b(xᵢ) b(xᵢ)* ≼ (1 + √((M-1)/n))² Λ • 1`.

Compared with `Discretization.bss_generalized_of_gram_eq_one`, the second family may be
infinite: what bounds the number of points is its **effective dimension**, and that is
finite as soon as `J` has finite trace. -/
theorem bss_generalized_of_gram_eq_one [Nonempty ι] [Nonempty κ] [Countable κ]
    (hJ : IsFiniteTracePos e J) {Λ : ℝ} (hΛ : 0 < Λ)
    (hJΛ : J ≤ Λ • (1 : H →L[ℂ] H)) {a : Ω → ι → ℂ} {b : Ω → H}
    (ha : ∀ k, MemLp (fun x => a x k) 2 μ) (hb : MemLp b 2 μ) (hgrama : gram a μ = 1)
    (hgramb : ∀ u, RCLike.re ⟪u, J u⟫_ℂ = ∫ x, ‖⟪u, b x⟫_ℂ‖ ^ 2 ∂μ)
    {n : ℕ} (hm : 2 ≤ Fintype.card ι) (hmn : Fintype.card ι ≤ n)
    (hM : 1 + 1 / (n : ℝ) ≤ traceAlong e J / Λ) :
    ∃ (x : Fin n → Ω) (w : Fin n → ℝ), (∀ i, 0 < w i) ∧
      (1 - Real.sqrt ((Fintype.card ι - 1) / n)) ^ 2 • (1 : Matrix ι ι ℂ)
        ≤ ∑ i, w i • Matrix.vecMulVec (a (x i)) (star (a (x i))) ∧
      ∑ i, w i • rankOne ℂ (b (x i)) (b (x i))
        ≤ ((1 + Real.sqrt ((traceAlong e J / Λ - 1) / n)) ^ 2 * Λ)
            • (1 : H →L[ℂ] H) := by
  -- the parameters of the construction
  have hn0 : (0 : ℝ) < n := by
    have h : 0 < n := lt_of_lt_of_le (by norm_num) (le_trans hm hmn)
    exact_mod_cast h
  set m : ℝ := (Fintype.card ι : ℝ) with hmdef
  have hm2 : (2 : ℝ) ≤ m := by rw [hmdef]; exact_mod_cast hm
  have hmn' : m ≤ (n : ℝ) := by rw [hmdef]; exact_mod_cast hmn
  set M : ℝ := traceAlong e J / Λ with hMdef
  set r : ℝ := Real.sqrt ((m - 1) / n) with hrdef
  set s : ℝ := Real.sqrt ((M - 1) / n) with hsdef
  have hr0 : 0 < r := sqrt_div_pos hn0 (by linarith)
  have hr1 : r < 1 := sqrt_div_lt_one hn0 hmn'
  have hm_eq : m = (n : ℝ) * r ^ 2 + 1 := eq_mul_sq_sqrt_div_add_one hn0 (by linarith)
  have hs0 : 1 / (n : ℝ) ≤ s := one_div_le_sqrt_div hn0 hM
  have hspos : 0 < s := lt_of_lt_of_le (by positivity) hs0
  have hM1 : (1 : ℝ) ≤ M := by
    have h1 : 0 < 1 / (n : ℝ) := by positivity
    linarith
  have hM_eq : M = (n : ℝ) * s ^ 2 + 1 := eq_mul_sq_sqrt_div_add_one hn0 hM1
  have hT : traceAlong e J = Λ * ((n : ℝ) * s ^ 2 + 1) := by
    rw [← hM_eq, hMdef]
    field_simp
  set δ : ℝ := (1 - r) / n with hδdef
  set ζ : ℝ := (1 + s) / n with hζdef
  have hδ0 : 0 < δ := div_pos (by linarith) hn0
  have hζ0 : 0 < ζ := div_pos (by linarith) hn0
  clear_value m M r s
  -- the initial data
  have hT0 : 0 < traceAlong e J := by nlinarith [hT, hΛ, hspos, hn0]
  set c₀ : ℝ := δ * m / r with hc₀def
  set d₀ : ℝ := ζ * traceAlong e J / s with hd₀def
  have hc₀0 : 0 < c₀ := div_pos (by positivity) hr0
  have hd₀0 : 0 < d₀ := div_pos (by positivity) hspos
  have hA₀ : (c₀ • (1 : Matrix ι ι ℂ)).PosDef := Matrix.PosDef.one.smul hc₀0
  have hB₀ : IsStrictlyPositive (d₀ • (1 : H →L[ℂ] H)) := isStrictlyPositive_smul_one hd₀0
  clear_value δ ζ c₀ d₀
  -- the initial potentials, and the gap they leave open
  have hΦ₀ : lowerPotential (c₀ • (1 : Matrix ι ι ℂ)) = r / δ := by
    rw [lowerPotential_smul_one hc₀0.ne', ← hmdef, hc₀def]
    field_simp
  have hΨ₀ : upperPotential e J (d₀ • (1 : H →L[ℂ] H)) = s / ζ := by
    rw [upperPotential_smul_one hd₀0.ne', hd₀def]
    field_simp
  have h1s : (1 : ℝ) + s ≠ 0 := by positivity
  have h1r : (1 : ℝ) - r ≠ 0 := by linarith
  have hgap : 1 / ζ + upperPotential e J (d₀ • (1 : H →L[ℂ] H))
      ≤ 1 / δ - lowerPotential (c₀ • (1 : Matrix ι ι ℂ)) := by
    rw [hΦ₀, hΨ₀, hδdef, hζdef, one_div_add_div_eq hn0 h1s, one_div_sub_div_eq hn0 h1r]
  -- run the construction and read off the two frame bounds
  obtain ⟨x, w, hwpos, hAn, hBn, hΦn, hΨn⟩ :=
    exists_points_weights hA₀ hJ hB₀ hδ0 hζ0 ha hb hgrama hgramb hgap n
  refine ⟨x, w, hwpos, ?_, ?_⟩
  · exact lower_frame_bound hn0 hr0 h1r hm_eq hδdef hc₀def hAn (hΦ₀ ▸ hΦn)
  · exact upper_frame_bound hJ hΛ hJΛ hn0 hs0 hζdef hd₀def hT hBn (hΨ₀ ▸ hΨn)

end Infinite

end Discretization
