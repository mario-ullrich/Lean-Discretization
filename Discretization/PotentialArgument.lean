/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import Discretization.Iteration

/-!
# The potential argument

This file turns the construction of the previous file into frame bounds.  The two
ingredients are the initial data and the final read-off:

* the initial states are multiples of the identity, `A₀ = (δ m / r) • 1` and
  `B₀ = (ζ Tr J / s) • 1`, chosen so that the gap condition holds with equality,
  `1/δ - Φ(A₀) = n = 1/ζ + Ψ_J(B₀)`
  (`Discretization.lowerPotential_smul_one` and the field `pot_smul_one` of an upper
  barrier);
* at the end, a bound on a potential is a bound on the state, which turns into a bound on
  the sum of rank-one pieces that has been accumulated
  (`Discretization.lower_bound_of_state`, `Discretization.UpperBarrier.upper_bound_of_state`).

The parameters are those of the paper: with `m = card ι`, `M = Tr J / Λ` the effective
dimension of the second family, and

`r = √((m-1)/n)`,  `s = √((M-1)/n)`,  `δ = (1-r)/n`,  `ζ = (1+s)/n`,

the two frame bounds come out as `(1-r)²` and `(1+s)² Λ`.

The upper half is proved once for every upper barrier
(`Discretization.UpperBarrier.bss_generalized_of_gram_eq_one`), and the theorem for finite
families, `Discretization.bss_generalized_of_gram_eq_one`, is its instance for
`Discretization.matrixUpperBarrier`.

## Matrices and operators

A finite second family is also the case `H = ℂ^κ` of the operator argument in
`Discretization.Infinite`, and Mathlib's `Matrix.toEuclideanCLM` transports statements
between the two.  Reaching the finite case that way needs bridges for the Loewner order, for
the trace and for the rank-one matrices, and it makes an elementary statement rest on the
continuous functional calculus, on the order of a C⋆-algebra and on sums along a Hilbert
basis.  So the analysis of the upper state is done twice: with `Matrix.inv`, `Matrix.trace`
and Sherman–Morrison for matrices here, which is the argument of the paper and what
`BasicResults` offers to Mathlib, and with their operator counterparts in
`Discretization.Infinite`.  Everything else is shared: the lower side, the arithmetic of
`Discretization.Parameters`, the real inequalities behind the barrier lemma, the
construction and the assembly of the theorem through `Discretization.UpperBarrier`, and the
removal of the normalisation (`Discretization.bss_of_gram_eq_one`).
-/

@[expose] public section

open Matrix MeasureTheory
open scoped ComplexOrder MatrixOrder

namespace Discretization

variable {ι κ Ω : Type*} [Fintype ι] [DecidableEq ι]

/-! ### Reading off the lower frame bound -/

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

/-! ### The lower frame bound with the parameters of the construction inserted -/

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

namespace UpperBarrier

variable [MeasurableSpace Ω] {μ : Measure Ω} {S : Type*} [AddCommGroup S] [PartialOrder S]
  [IsOrderedAddMonoid S] [Module ℝ S] [IsOrderedModule ℝ S] [One S] (U : UpperBarrier μ S)

/-! ### Reading off the upper frame bound -/

/-- **The upper frame bound.**  If the final upper state, started from `c₀ • 1`, is
admissible with upper potential at most `c`, then the accumulated sum of rank-one pieces is
at most `c₀ • 1 + (k ζ - c⁻¹) • J`. -/
theorem upper_bound_of_state {c₀ ζ : ℝ} {k : ℕ} {x : Fin k → Ω} {w : Fin k → ℝ}
    (hstate : U.Adm (U.upperState (c₀ • 1) ζ x w)) {c : ℝ}
    (hpot : U.pot (U.upperState (c₀ • 1) ζ x w) ≤ c) :
    ∑ i, w i • U.R (x i) ≤ c₀ • (1 : S) + ((k : ℝ) * ζ - c⁻¹) • U.J := by
  have hΨ0 : 0 < U.pot (U.upperState (c₀ • 1) ζ x w) := U.pot_pos hstate
  have hinv : c⁻¹ ≤ (U.pot (U.upperState (c₀ • 1) ζ x w))⁻¹ := inv_anti₀ hΨ0 hpot
  have h2 : c⁻¹ • U.J ≤ U.upperState (c₀ • 1) ζ x w :=
    (smul_le_smul_of_nonneg_right hinv U.J_nonneg).trans (U.inv_pot_smul_le hstate)
  have h5 := sub_le_sub_left h2 (c₀ • (1 : S) + ((k : ℝ) * ζ) • U.J)
  calc ∑ i, w i • U.R (x i)
      = c₀ • (1 : S) + ((k : ℝ) * ζ) • U.J - U.upperState (c₀ • 1) ζ x w := by
        simp only [upperState]; abel
    _ ≤ c₀ • (1 : S) + ((k : ℝ) * ζ) • U.J - c⁻¹ • U.J := h5
    _ = c₀ • (1 : S) + ((k : ℝ) * ζ - c⁻¹) • U.J := by module

/-- **The upper frame bound of the theorem.**  Started from `B₀ = d₀ • 1` with
`d₀ = ζ Tr J / s`, `ζ = (1+s)/n` and `Tr J = Λ (n s² + 1)`, a final upper potential of at
most `s/ζ` turns into the frame bound `(1+s)² Λ • 1`.

The hypothesis `1/n ≤ s` is what makes the coefficient `n ζ - (s/ζ)⁻¹` of `J` nonnegative,
so that the bound `J ≤ Λ • 1` may be applied to it; the arithmetic behind the constant is
`d₀ + (n ζ - ζ/s) Λ = (1+s)² Λ` (`Discretization.frame_constant_eq`). -/
theorem upper_frame_bound {Λ : ℝ} (hΛ : 0 < Λ) (hJΛ : U.J ≤ Λ • (1 : S)) {n : ℕ}
    (hn0 : (0 : ℝ) < n) {s ζ d₀ : ℝ} (hs0 : 1 / (n : ℝ) ≤ s) (hζ : ζ = (1 + s) / n)
    (hd₀ : d₀ = ζ * U.tr / s) (hT : U.tr = Λ * ((n : ℝ) * s ^ 2 + 1)) {x : Fin n → Ω}
    {w : Fin n → ℝ} (hBn : U.Adm (U.upperState (d₀ • 1) ζ x w))
    (hΨn : U.pot (U.upperState (d₀ • 1) ζ x w) ≤ s / ζ) :
    ∑ i, w i • U.R (x i) ≤ ((1 + s) ^ 2 * Λ) • (1 : S) := by
  have hcoef0 : 0 ≤ (n : ℝ) * ζ - (s / ζ)⁻¹ := nonneg_mul_sub_inv_div hn0 hs0 hζ
  calc ∑ i, w i • U.R (x i)
      ≤ d₀ • (1 : S) + ((n : ℝ) * ζ - (s / ζ)⁻¹) • U.J := U.upper_bound_of_state hBn hΨn
    _ ≤ d₀ • (1 : S) + (((n : ℝ) * ζ - (s / ζ)⁻¹) * Λ) • (1 : S) := by
        have hstep : ((n : ℝ) * ζ - (s / ζ)⁻¹) • U.J
            ≤ (((n : ℝ) * ζ - (s / ζ)⁻¹) * Λ) • (1 : S) := by
          rw [← smul_smul]
          exact smul_le_smul_of_nonneg_left hJΛ hcoef0
        exact add_le_add le_rfl hstep
    _ = ((1 + s) ^ 2 * Λ) • (1 : S) := by
        rw [← add_smul]
        congr 1
        exact frame_constant_eq hn0 hs0 hΛ hζ hd₀ hT

/-! ### The theorem for an upper barrier -/

/-- **Generalized sparsification theorem for an upper barrier**, with a normalized first
family of `m ≥ 2` functions and an effective dimension `M = Tr J / Λ ≥ 1 + 1/n`: for every
`n ≥ m` there are `n` points and positive weights with

`(1 - √((m-1)/n))² • 1 ≤ ∑ wᵢ a(xᵢ) a(xᵢ)*`  and
`∑ wᵢ R(xᵢ) ≤ (1 + √((M-1)/n))² Λ • 1`. -/
theorem bss_generalized_of_gram_eq_one [Nonempty ι] {Λ : ℝ} (hΛ : 0 < Λ)
    (hJΛ : U.J ≤ Λ • (1 : S)) {a : Ω → ι → ℂ} (ha : ∀ k, MemLp (fun x => a x k) 2 μ)
    (hgrama : gram a μ = 1) {n : ℕ} (hm : 2 ≤ Fintype.card ι) (hmn : Fintype.card ι ≤ n)
    (hM : 1 + 1 / (n : ℝ) ≤ U.tr / Λ) :
    ∃ (x : Fin n → Ω) (w : Fin n → ℝ), (∀ i, 0 < w i) ∧
      (1 - Real.sqrt ((Fintype.card ι - 1) / n)) ^ 2 • (1 : Matrix ι ι ℂ)
        ≤ ∑ i, w i • vecMulVec (a (x i)) (star (a (x i))) ∧
      ∑ i, w i • U.R (x i) ≤ ((1 + Real.sqrt ((U.tr / Λ - 1) / n)) ^ 2 * Λ) • (1 : S) := by
  -- the parameters of the construction
  have hn0 : (0 : ℝ) < n := by
    have h : 0 < n := lt_of_lt_of_le (by norm_num) (le_trans hm hmn)
    exact_mod_cast h
  set m : ℝ := (Fintype.card ι : ℝ) with hmdef
  have hm2 : (2 : ℝ) ≤ m := by rw [hmdef]; exact_mod_cast hm
  have hmn' : m ≤ (n : ℝ) := by rw [hmdef]; exact_mod_cast hmn
  set M : ℝ := U.tr / Λ with hMdef
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
  have hT : U.tr = Λ * ((n : ℝ) * s ^ 2 + 1) := by
    rw [← eq_mul_sq_sqrt_div_add_one hn0 hM1, hMdef]
    field_simp
  set δ : ℝ := (1 - r) / n with hδdef
  set ζ : ℝ := (1 + s) / n with hζdef
  have hδ0 : 0 < δ := div_pos (by linarith) hn0
  have hζ0 : 0 < ζ := div_pos (by linarith) hn0
  clear_value m M r s
  -- the initial states
  set c₀ : ℝ := δ * m / r with hc₀def
  set d₀ : ℝ := ζ * U.tr / s with hd₀def
  have hc₀0 : 0 < c₀ := div_pos (by positivity) hr0
  have hd₀0 : 0 < d₀ := div_pos (mul_pos hζ0 U.tr_pos) hspos
  have hA₀ : (c₀ • (1 : Matrix ι ι ℂ)).PosDef := Matrix.PosDef.one.smul hc₀0
  have hB₀ : U.Adm (d₀ • (1 : S)) := U.adm_smul_one hd₀0
  clear_value δ ζ c₀ d₀
  -- the initial potentials, and the gap they leave open
  have hΦ₀ : lowerPotential (c₀ • (1 : Matrix ι ι ℂ)) = r / δ := by
    rw [lowerPotential_smul_one hc₀0.ne', ← hmdef, hc₀def]
    field_simp
  have hΨ₀ : U.pot (d₀ • (1 : S)) = s / ζ := by
    have hT0 := U.tr_pos
    rw [U.pot_smul_one hd₀0.ne', hd₀def]
    field_simp
  have h1s : (1 : ℝ) + s ≠ 0 := by positivity
  have h1r : (1 : ℝ) - r ≠ 0 := by linarith
  have hgap : 1 / ζ + U.pot (d₀ • (1 : S))
      ≤ 1 / δ - lowerPotential (c₀ • (1 : Matrix ι ι ℂ)) := by
    rw [hΦ₀, hΨ₀, hδdef, hζdef, one_div_add_div_eq hn0 h1s, one_div_sub_div_eq hn0 h1r]
  -- run the construction and read off the two frame bounds
  obtain ⟨x, w, hwpos, hAn, hBn, hΦn, hΨn⟩ :=
    U.exists_points_weights hA₀ hB₀ hδ0 hζ0 ha hgrama hgap n
  refine ⟨x, w, hwpos, ?_, ?_⟩
  · exact lower_frame_bound hn0 hr0 h1r hm_eq hδdef hc₀def hAn (hΦ₀ ▸ hΦn)
  · exact U.upper_frame_bound hΛ hJΛ hn0 hs0 hζdef hd₀def hT hBn (hΨ₀ ▸ hΨn)

end UpperBarrier

/-! ### The theorem for finite families -/

variable [Fintype κ] [DecidableEq κ] [MeasurableSpace Ω] {μ : Measure Ω}

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
            • (1 : Matrix κ κ ℂ) :=
  (matrixUpperBarrier hJ hb hgramb).bss_generalized_of_gram_eq_one hΛ hJΛ ha hgrama hm hmn hM

end Discretization
