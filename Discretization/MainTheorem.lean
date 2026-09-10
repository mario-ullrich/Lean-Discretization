/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
import Discretization.Iteration

/-!
# The generalized sparsification theorem

This file turns the construction of the previous file into frame bounds.  The two
ingredients are the initial data and the final read-off:

* the initial matrices are multiples of the identity, `A₀ = (δ m / r) • 1` and
  `B₀ = (ζ Tr J / s) • 1`, chosen so that the gap condition holds with equality,
  `1/δ - Φ(A₀) = n = 1/ζ + Ψ_J(B₀)`
  (`Discretization.lowerPotential_smul_one`, `Discretization.upperPotential_smul_one`);
* at the end, a bound on a potential is a bound on the matrix, which turns into a bound on
  the sum of rank-one matrices that has been accumulated
  (`Discretization.lower_bound_of_state`, `Discretization.upper_bound_of_state`).

The parameters are those of the paper: with `m = card ι`, `M = Tr J / Λ` the effective
dimension of the second family, and

`r = √((m-1)/n)`,  `s = √((M-1)/n)`,  `δ = (1-r)/n`,  `ζ = (1+s)/n`,

the two frame bounds come out as `(1-r)²` and `(1+s)² Λ`.
-/

open Matrix MeasureTheory
open scoped ComplexOrder MatrixOrder

namespace Discretization

variable {ι κ Ω : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  [MeasurableSpace Ω] {μ : Measure Ω}

/-! ### Potentials of a multiple of the identity -/

/-- The inverse of a positive multiple of the identity. -/
theorem inv_smul_one {c : ℝ} (hc : c ≠ 0) :
    (c • (1 : Matrix ι ι ℂ))⁻¹ = c⁻¹ • (1 : Matrix ι ι ℂ) := by
  refine Matrix.inv_eq_right_inv ?_
  rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, smul_smul, mul_inv_cancel₀ hc,
    one_smul]

/-- `Φ(c • 1) = m / c`, where `m` is the size of the matrix. -/
theorem lowerPotential_smul_one {c : ℝ} (hc : c ≠ 0) :
    lowerPotential (c • (1 : Matrix ι ι ℂ)) = Fintype.card ι / c := by
  rw [lowerPotential, inv_smul_one hc, Matrix.trace_smul, RCLike.smul_re, Matrix.trace_one]
  simp [div_eq_inv_mul]

/-- `Ψ_J(c • 1) = Re Tr J / c`. -/
theorem upperPotential_smul_one (J : Matrix κ κ ℂ) {c : ℝ} (hc : c ≠ 0) :
    upperPotential J (c • (1 : Matrix κ κ ℂ)) = RCLike.re J.trace / c := by
  rw [upperPotential, inv_smul_one hc, mul_smul_comm, mul_one, Matrix.trace_smul,
    RCLike.smul_re, div_eq_inv_mul]

/-! ### Reading off the frame bounds -/

omit [MeasurableSpace Ω] in
/-- **The lower frame bound.**  If the final lower state, started from `c₀ • 1`, is positive
definite with lower potential at most `c`, then the accumulated sum of rank-one matrices is
at least `(c⁻¹ + k δ - c₀) • 1`. -/
theorem lower_bound_of_state [Nonempty ι] {c₀ δ : ℝ} {a : Ω → ι → ℂ} {k : ℕ}
    {x : Fin k → Ω} {w : Fin k → ℝ}
    (hstate : (lowerState (c₀ • (1 : Matrix ι ι ℂ)) δ a x w).PosDef) {c : ℝ}
    (hpot : lowerPotential (lowerState (c₀ • (1 : Matrix ι ι ℂ)) δ a x w) ≤ c) :
    (c⁻¹ + (k : ℝ) * δ - c₀) • (1 : Matrix ι ι ℂ)
      ≤ ∑ i, w i • vecMulVec (a (x i)) (star (a (x i))) := by
  have hΦ0 : 0 < lowerPotential (lowerState (c₀ • (1 : Matrix ι ι ℂ)) δ a x w) :=
    lowerPotential_pos hstate
  have h1 : (lowerPotential (lowerState (c₀ • (1 : Matrix ι ι ℂ)) δ a x w))⁻¹
      • (1 : Matrix ι ι ℂ) ≤ lowerState (c₀ • (1 : Matrix ι ι ℂ)) δ a x w :=
    hstate.inv_re_trace_smul_one_le
  have hinv : c⁻¹ ≤ (lowerPotential (lowerState (c₀ • (1 : Matrix ι ι ℂ)) δ a x w))⁻¹ :=
    inv_anti₀ hΦ0 hpot
  have h2 : c⁻¹ • (1 : Matrix ι ι ℂ) ≤ lowerState (c₀ • (1 : Matrix ι ι ℂ)) δ a x w :=
    (smul_le_smul_of_nonneg_right hinv Matrix.PosSemidef.one.nonneg).trans h1
  have h4 : lowerState (c₀ • (1 : Matrix ι ι ℂ)) δ a x w
      = (c₀ - (k : ℝ) * δ) • (1 : Matrix ι ι ℂ)
        + ∑ i, w i • vecMulVec (a (x i)) (star (a (x i))) := by
    simp only [lowerState]; module
  rw [h4] at h2
  have h5 := sub_le_sub_right h2 ((c₀ - (k : ℝ) * δ) • (1 : Matrix ι ι ℂ))
  calc (c⁻¹ + (k : ℝ) * δ - c₀) • (1 : Matrix ι ι ℂ)
      = c⁻¹ • (1 : Matrix ι ι ℂ) - (c₀ - (k : ℝ) * δ) • (1 : Matrix ι ι ℂ) := by module
    _ ≤ _ := by simpa using h5

omit [MeasurableSpace Ω] in
/-- **The upper frame bound.**  If the final upper state, started from `c₀ • 1`, is positive
definite with upper potential at most `c`, then the accumulated sum of rank-one matrices is
at most `c₀ • 1 + (k ζ - c⁻¹) • J`. -/
theorem upper_bound_of_state [Nonempty κ] {J : Matrix κ κ ℂ} (hJ : J.PosDef) {c₀ ζ : ℝ}
    {b : Ω → κ → ℂ} {k : ℕ} {x : Fin k → Ω} {w : Fin k → ℝ}
    (hstate : (upperState J (c₀ • (1 : Matrix κ κ ℂ)) ζ b x w).PosDef) {c : ℝ}
    (hpot : upperPotential J (upperState J (c₀ • (1 : Matrix κ κ ℂ)) ζ b x w) ≤ c) :
    ∑ i, w i • vecMulVec (b (x i)) (star (b (x i)))
      ≤ c₀ • (1 : Matrix κ κ ℂ) + ((k : ℝ) * ζ - c⁻¹) • J := by
  have hΨ0 : 0 < upperPotential J (upperState J (c₀ • (1 : Matrix κ κ ℂ)) ζ b x w) :=
    upperPotential_pos hJ hstate
  have h1 : (upperPotential J (upperState J (c₀ • (1 : Matrix κ κ ℂ)) ζ b x w))⁻¹ • J
      ≤ upperState J (c₀ • (1 : Matrix κ κ ℂ)) ζ b x w :=
    hstate.inv_re_trace_mul_smul_le hJ
  have hinv : c⁻¹ ≤ (upperPotential J (upperState J (c₀ • (1 : Matrix κ κ ℂ)) ζ b x w))⁻¹ :=
    inv_anti₀ hΨ0 hpot
  have h2 : c⁻¹ • J ≤ upperState J (c₀ • (1 : Matrix κ κ ℂ)) ζ b x w :=
    (smul_le_smul_of_nonneg_right hinv hJ.posSemidef.nonneg).trans h1
  have h4 : upperState J (c₀ • (1 : Matrix κ κ ℂ)) ζ b x w
      = c₀ • (1 : Matrix κ κ ℂ) + ((k : ℝ) * ζ) • J
        - ∑ i, w i • vecMulVec (b (x i)) (star (b (x i))) := by
    simp only [upperState]
  rw [h4] at h2
  have h5 := sub_le_sub_left h2 (c₀ • (1 : Matrix κ κ ℂ) + ((k : ℝ) * ζ) • J)
  calc ∑ i, w i • vecMulVec (b (x i)) (star (b (x i)))
      = c₀ • (1 : Matrix κ κ ℂ) + ((k : ℝ) * ζ) • J
        - (c₀ • (1 : Matrix κ κ ℂ) + ((k : ℝ) * ζ) • J
          - ∑ i, w i • vecMulVec (b (x i)) (star (b (x i)))) := by module
    _ ≤ c₀ • (1 : Matrix κ κ ℂ) + ((k : ℝ) * ζ) • J
        - c⁻¹ • J := h5
    _ = c₀ • (1 : Matrix κ κ ℂ) + ((k : ℝ) * ζ - c⁻¹) • J := by module

/-! ### The frame bounds with the parameters of the construction inserted -/

omit [MeasurableSpace Ω] in
/-- **The lower frame bound of the theorem.**  Started from `A₀ = c₀ • 1` with
`c₀ = δ m / r`, `δ = (1-r)/n` and `m = n r² + 1`, a final lower potential of at most `r/δ`
turns into the frame bound `(1-r)² • 1`.

The arithmetic behind it is `c⁻¹ + n δ - c₀ = (1-r)²` for `c = r/δ`. -/
theorem lower_frame_bound [Nonempty ι] {n : ℕ} (hn0 : (0 : ℝ) < n) {m r δ c₀ : ℝ}
    (hr0 : 0 < r) (h1r : (1 : ℝ) - r ≠ 0) (hm : m = (n : ℝ) * r ^ 2 + 1)
    (hδ : δ = (1 - r) / n) (hc₀ : c₀ = δ * m / r) {a : Ω → ι → ℂ} {x : Fin n → Ω}
    {w : Fin n → ℝ}
    (hAn : (lowerState (c₀ • (1 : Matrix ι ι ℂ)) δ a x w).PosDef)
    (hΦn : lowerPotential (lowerState (c₀ • (1 : Matrix ι ι ℂ)) δ a x w) ≤ r / δ) :
    (1 - r) ^ 2 • (1 : Matrix ι ι ℂ)
      ≤ ∑ i, w i • vecMulVec (a (x i)) (star (a (x i))) := by
  refine le_trans (le_of_eq ?_) (lower_bound_of_state hAn hΦn)
  congr 1
  rw [hc₀, hδ, hm]
  field_simp
  ring

omit [MeasurableSpace Ω] in
/-- **The upper frame bound of the theorem.**  Started from `B₀ = d₀ • 1` with
`d₀ = ζ Tr J / s`, `ζ = (1+s)/n` and `Tr J = Λ (n s² + 1)`, a final upper potential of at
most `s/ζ` turns into the frame bound `(1+s)² Λ • 1`.

The hypothesis `1/n ≤ s` is what makes the coefficient `n ζ - (s/ζ)⁻¹` of `J` nonnegative,
so that the bound `J ≤ Λ • 1` may be applied to it; the arithmetic behind the constant is
`d₀ + (n ζ - ζ/s) Λ = (1+s)² Λ`. -/
theorem upper_frame_bound [Nonempty κ] {J : Matrix κ κ ℂ} (hJ : J.PosDef) {Λ : ℝ}
    (hΛ : 0 < Λ) (hJΛ : J ≤ Λ • (1 : Matrix κ κ ℂ)) {n : ℕ} (hn0 : (0 : ℝ) < n)
    {s ζ d₀ : ℝ} (hs0 : 1 / (n : ℝ) ≤ s) (hζ : ζ = (1 + s) / n)
    (hd₀ : d₀ = ζ * RCLike.re J.trace / s)
    (hT : RCLike.re J.trace = Λ * ((n : ℝ) * s ^ 2 + 1)) {b : Ω → κ → ℂ} {x : Fin n → Ω}
    {w : Fin n → ℝ}
    (hBn : (upperState J (d₀ • (1 : Matrix κ κ ℂ)) ζ b x w).PosDef)
    (hΨn : upperPotential J (upperState J (d₀ • (1 : Matrix κ κ ℂ)) ζ b x w) ≤ s / ζ) :
    ∑ i, w i • vecMulVec (b (x i)) (star (b (x i)))
      ≤ ((1 + s) ^ 2 * Λ) • (1 : Matrix κ κ ℂ) := by
  have hspos : 0 < s := lt_of_lt_of_le (by positivity) hs0
  have hζ0 : 0 < ζ := by rw [hζ]; exact div_pos (by linarith) hn0
  have hcoef0 : 0 ≤ (n : ℝ) * ζ - (s / ζ)⁻¹ := by
    rw [inv_div, show ζ / s = ζ * (1 / s) by ring]
    nlinarith [hζ0, one_div_le_of_one_div_le hn0 hspos hs0]
  calc ∑ i, w i • vecMulVec (b (x i)) (star (b (x i)))
      ≤ d₀ • (1 : Matrix κ κ ℂ) + ((n : ℝ) * ζ - (s / ζ)⁻¹) • J :=
        upper_bound_of_state hJ hBn hΨn
    _ ≤ d₀ • (1 : Matrix κ κ ℂ)
          + (((n : ℝ) * ζ - (s / ζ)⁻¹) * Λ) • (1 : Matrix κ κ ℂ) := by
        have hstep : (((n : ℝ) * ζ - (s / ζ)⁻¹) • J : Matrix κ κ ℂ)
            ≤ (((n : ℝ) * ζ - (s / ζ)⁻¹) * Λ) • (1 : Matrix κ κ ℂ) := by
          rw [← smul_smul]
          exact smul_le_smul_of_nonneg_left hJΛ hcoef0
        exact add_le_add le_rfl hstep
    _ = ((1 + s) ^ 2 * Λ) • (1 : Matrix κ κ ℂ) := by
        rw [← add_smul]
        congr 1
        rw [hd₀, hT, hζ, inv_div]
        field_simp
        ring

/-! ### The theorem -/

/-- **Generalized sparsification theorem** (Chkifa–Dolbeault–Krieg–Ullrich, Theorem 3), for
finite families and a normalized first family.

Let `a` be a family of square-integrable functions indexed by a finite set `ι` of `m ≥ 2`
elements whose Gram matrix is the identity, and let `b` be a second family whose Gram matrix
`J` is positive definite and bounded by `Λ • 1`.  Write `M = Tr J / Λ` for the effective
dimension of the second family and assume `M ≥ 1 + 1/n`.  Then for every `n ≥ m` there are
`n` points and positive weights such that

`(1 - √((m-1)/n))² • 1 ≤ ∑ wᵢ a(xᵢ) a(xᵢ)*`  and
`∑ wᵢ b(xᵢ) b(xᵢ)* ≤ (1 + √((M-1)/n))² Λ • 1`.

Compared with the theorem of Batson, Spielman and Srivastava, the upper bound involves the
effective dimension `M` instead of the number of functions in the second family, and the two
families may be different. -/
theorem bss_generalized_of_gram_eq_one [Nonempty ι] [Nonempty κ]
    {J : Matrix κ κ ℂ} (hJ : J.PosDef) {Λ : ℝ} (hΛ : 0 < Λ)
    (hJΛ : J ≤ Λ • (1 : Matrix κ κ ℂ)) {a : Ω → ι → ℂ} {b : Ω → κ → ℂ}
    (ha : ∀ k, MemLp (fun x => a x k) 2 μ) (hb : ∀ k, MemLp (fun x => b x k) 2 μ)
    (hgrama : gram a μ = 1) (hgramb : gram b μ = J)
    {n : ℕ} (hm : 2 ≤ Fintype.card ι) (hmn : Fintype.card ι ≤ n)
    (hM : 1 + 1 / (n : ℝ) ≤ RCLike.re J.trace / Λ) :
    ∃ (x : Fin n → Ω) (w : Fin n → ℝ), (∀ i, 0 < w i) ∧
      (1 - Real.sqrt ((Fintype.card ι - 1) / n)) ^ 2 • (1 : Matrix ι ι ℂ)
        ≤ ∑ i, w i • vecMulVec (a (x i)) (star (a (x i))) ∧
      ∑ i, w i • vecMulVec (b (x i)) (star (b (x i)))
        ≤ ((1 + Real.sqrt ((RCLike.re J.trace / Λ - 1) / n)) ^ 2 * Λ)
            • (1 : Matrix κ κ ℂ) := by
  -- the parameters of the construction
  have hn0 : (0 : ℝ) < n := by
    have h : 0 < n := lt_of_lt_of_le (by norm_num) (le_trans hm hmn)
    exact_mod_cast h
  set m : ℝ := (Fintype.card ι : ℝ) with hmdef
  have hm2 : (2 : ℝ) ≤ m := by rw [hmdef]; exact_mod_cast hm
  have hmn' : m ≤ (n : ℝ) := by rw [hmdef]; exact_mod_cast hmn
  set M : ℝ := RCLike.re J.trace / Λ with hMdef
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
  have hT : RCLike.re J.trace = Λ * ((n : ℝ) * s ^ 2 + 1) := by
    rw [← eq_mul_sq_sqrt_div_add_one hn0 hM1, hMdef]
    field_simp
  set δ : ℝ := (1 - r) / n with hδdef
  set ζ : ℝ := (1 + s) / n with hζdef
  have hδ0 : 0 < δ := div_pos (by linarith) hn0
  have hζ0 : 0 < ζ := div_pos (by linarith) hn0
  clear_value m M r s
  -- the initial matrices
  have hT0 : 0 < RCLike.re J.trace := (RCLike.pos_iff.mp hJ.trace_pos).1
  set c₀ : ℝ := δ * m / r with hc₀def
  set d₀ : ℝ := ζ * RCLike.re J.trace / s with hd₀def
  have hc₀0 : 0 < c₀ := div_pos (by positivity) hr0
  have hd₀0 : 0 < d₀ := div_pos (by positivity) hspos
  have hA₀ : (c₀ • (1 : Matrix ι ι ℂ)).PosDef := Matrix.PosDef.one.smul hc₀0
  have hB₀ : (d₀ • (1 : Matrix κ κ ℂ)).PosDef := Matrix.PosDef.one.smul hd₀0
  clear_value δ ζ c₀ d₀
  -- the initial potentials, and the gap they leave open
  have hΦ₀ : lowerPotential (c₀ • (1 : Matrix ι ι ℂ)) = r / δ := by
    rw [lowerPotential_smul_one hc₀0.ne', ← hmdef, hc₀def]
    field_simp
  have hΨ₀ : upperPotential J (d₀ • (1 : Matrix κ κ ℂ)) = s / ζ := by
    rw [upperPotential_smul_one J hd₀0.ne', hd₀def]
    field_simp
  have h1s : (1 : ℝ) + s ≠ 0 := by positivity
  have h1r : (1 : ℝ) - r ≠ 0 := by linarith
  have hgap : 1 / ζ + upperPotential J (d₀ • (1 : Matrix κ κ ℂ))
      ≤ 1 / δ - lowerPotential (c₀ • (1 : Matrix ι ι ℂ)) := by
    rw [hΦ₀, hΨ₀, hδdef, hζdef, one_div_add_div_eq hn0 h1s, one_div_sub_div_eq hn0 h1r]
  -- run the construction and read off the two frame bounds
  obtain ⟨x, w, hwpos, hAn, hBn, hΦn, hΨn⟩ :=
    exists_points_weights hA₀ hJ hB₀ hδ0 hζ0 ha hb hgrama hgramb hgap n
  refine ⟨x, w, hwpos, ?_, ?_⟩
  · exact lower_frame_bound hn0 hr0 h1r hm_eq hδdef hc₀def hAn (hΦ₀ ▸ hΦn)
  · exact upper_frame_bound hJ hΛ hJΛ hn0 hs0 hζdef hd₀def hT hBn (hΨ₀ ▸ hΨn)

end Discretization
