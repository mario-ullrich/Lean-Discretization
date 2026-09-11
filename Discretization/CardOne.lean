/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
import Discretization.MainTheorem

/-!
# The case of a single function

The main theorem needs `m = card ι ≥ 2`, because the initial matrix `A₀ = (δ m / r) • 1` of
the construction involves `r = √((m-1)/n)`, which vanishes for `m = 1`.  As the paper
observes, for `m = 1` the lower potential is not needed at all: the lower verifier can be
replaced by the constant

`L(x) = n |a(x)|²`,   with   `∫ L dμ = n`

whenever the single function `a` is normalized.  The construction then tracks only the upper
matrix, and choosing the largest admissible weight, `1/wᵢ = L(xᵢ)`, makes the lower frame
bound an identity:

`∑ wᵢ |a(xᵢ)|² = ∑ 1/n = 1 = (1 - √((m-1)/n))²`.

The upper half of the argument is that of the main theorem; only the induction is one-sided
(`Discretization.exists_points_weights_of_unique`).  That the weights make the lower bound an
identity is `Discretization.sum_smul_vecMulVec_eq_one`, and the result is
`Discretization.bss_generalized_of_unique`.

Here `card ι = 1` is expressed by the typeclass assumption `[Unique ι]`, and `default : ι` is
the single index.
-/

open Matrix MeasureTheory
open scoped ComplexOrder MatrixOrder

namespace Discretization

variable {ι κ Ω : Type*} [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  [MeasurableSpace Ω] {μ : Measure Ω}

/-! ### The constant lower verifier -/

/-- The single function of a normalized one-element family has `∫ |a|² dμ = 1`. -/
theorem integral_norm_sq_eq_one [Unique ι] {a : Ω → ι → ℂ}
    (ha : ∀ k, MemLp (fun x => a x k) 2 μ) (hgrama : gram a μ = 1) :
    ∫ x, ‖a x default‖ ^ 2 ∂μ = 1 := by
  rw [integral_norm_sq ha default, hgrama, Matrix.one_apply_eq]
  simp

omit [MeasurableSpace Ω] in
/-- **The lower frame bound of a one-element family is an identity.**  If every weight is
the reciprocal of the constant lower verifier, `wᵢ · n |a(xᵢ)|² = 1`, then the `n` rank-one
matrices add up to exactly the identity, each of them contributing `1/n`. -/
theorem sum_smul_vecMulVec_eq_one [Unique ι] {n : ℕ} (hn0 : (0 : ℝ) < n) {a : Ω → ι → ℂ}
    (x : Fin n → Ω) (w : Fin n → ℝ)
    (hw : ∀ i, w i * ((n : ℝ) * ‖a (x i) default‖ ^ 2) = 1) :
    ∑ i, w i • vecMulVec (a (x i)) (star (a (x i))) = (1 : Matrix ι ι ℂ) := by
  have h1 : ∀ i : Fin n, (w i • vecMulVec (a (x i)) (star (a (x i)))) default default
      = ((1 / (n : ℝ) : ℝ) : ℂ) := by
    intro i
    have h2 : w i * ‖a (x i) default‖ ^ 2 = 1 / n := by
      rw [eq_div_iff hn0.ne']
      calc w i * ‖a (x i) default‖ ^ 2 * n
          = w i * ((n : ℝ) * ‖a (x i) default‖ ^ 2) := by ring
        _ = 1 := hw i
    calc (w i • vecMulVec (a (x i)) (star (a (x i)))) default default
        = ((w i * ‖a (x i) default‖ ^ 2 : ℝ) : ℂ) := by
          rw [Matrix.smul_apply, Matrix.vecMulVec_apply, Pi.star_apply, RCLike.star_def,
            RCLike.mul_conj, Complex.real_smul]
          norm_cast
          exact (Complex.ofReal_mul _ _).symm
      _ = ((1 / (n : ℝ) : ℝ) : ℂ) := by rw [h2]
  have hnC : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (by exact_mod_cast hn0.ne')
  ext p q
  rw [Subsingleton.elim p default, Subsingleton.elim q default, Matrix.one_apply_eq,
    Matrix.sum_apply, Finset.sum_congr rfl fun i _ => h1 i]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  push_cast
  field_simp

/-! ### The one-sided construction -/

/-- **The construction for a single function.**  Only the upper matrix is tracked; the weights
are chosen as large as the constant lower verifier allows, so that each point contributes
exactly `1/n` to the lower frame bound. -/
theorem exists_points_weights_of_unique [Unique ι] [Nonempty κ] {J B₀ : Matrix κ κ ℂ}
    (hJ : J.PosDef) (hB₀ : B₀.PosDef) {ζ : ℝ} (hζ : 0 < ζ) {a : Ω → ι → ℂ} {b : Ω → κ → ℂ}
    (ha : ∀ k, MemLp (fun x => a x k) 2 μ) (hb : ∀ k, MemLp (fun x => b x k) 2 μ)
    (hgrama : gram a μ = 1) (hgramb : gram b μ = J) {n : ℕ}
    (hgap : 1 / ζ + upperPotential J B₀ ≤ n) (k : ℕ) :
    ∃ (x : Fin k → Ω) (w : Fin k → ℝ), (∀ i, 0 < w i) ∧
      (upperState J B₀ ζ b x w).PosDef ∧
      upperPotential J (upperState J B₀ ζ b x w) ≤ upperPotential J B₀ ∧
      ∀ i, w i * ((n : ℝ) * ‖a (x i) default‖ ^ 2) = 1 := by
  induction k with
  | zero => exact ⟨Fin.elim0, Fin.elim0, fun i => i.elim0, by simpa using hB₀, by simp,
      fun i => i.elim0⟩
  | succ k ih =>
    obtain ⟨x, w, hwpos, hBk, hΨ, hwk⟩ := ih
    -- the average of the constant lower verifier is `n`, and dominates that of the upper one
    have hint : ∫ y, (n : ℝ) * ‖a y default‖ ^ 2 ∂μ = n := by
      rw [integral_const_mul, integral_norm_sq_eq_one ha hgrama, mul_one]
    have hlt : ∫ y, upperVerifier J (upperState J B₀ ζ b x w) ζ (b y) ∂μ
        < ∫ y, (n : ℝ) * ‖a y default‖ ^ 2 ∂μ := by
      rw [hint]
      have h1 := integral_upperVerifier_lt hJ hBk hζ hb hgramb
      linarith
    obtain ⟨y, hy⟩ := exists_lt_of_integral_lt (μ := μ)
      (f := fun y => (n : ℝ) * ‖a y default‖ ^ 2)
      (g := fun y => upperVerifier J (upperState J B₀ ζ b x w) ζ (b y))
      ((integrable_norm_sq ha default).const_mul _) (integrable_upperVerifier hb) hlt
    -- the weight allowed by the constant verifier
    have hU0 : 0 ≤ upperVerifier J (upperState J B₀ ζ b x w) ζ (b y) :=
      upperVerifier_nonneg hJ hBk hζ (b y)
    have hLpos : 0 < (n : ℝ) * ‖a y default‖ ^ 2 := lt_of_le_of_lt hU0 hy
    have hwnew : 0 < 1 / ((n : ℝ) * ‖a y default‖ ^ 2) := one_div_pos.2 hLpos
    have hcondU : upperVerifier J (upperState J B₀ ζ b x w) ζ (b y)
        ≤ 1 / (1 / ((n : ℝ) * ‖a y default‖ ^ 2)) := by
      rw [one_div_one_div]; exact hy.le
    obtain ⟨hBnew, hΨnew⟩ := upperPotential_update_le hJ hBk hζ (b y) hwnew hcondU
    refine ⟨Fin.snoc x y, Fin.snoc w (1 / ((n : ℝ) * ‖a y default‖ ^ 2)), ?_, ?_, ?_, ?_⟩
    · refine Fin.lastCases ?_ ?_
      · simpa using hwnew
      · intro j; simpa using hwpos j
    · rw [upperState_snoc]; exact hBnew
    · rw [upperState_snoc]; exact hΨnew.trans hΨ
    · refine Fin.lastCases ?_ ?_
      · simpa using one_div_mul_cancel hLpos.ne'
      · intro j; simpa using hwk j

/-! ### The theorem for a single function -/

/-- **Generalized sparsification theorem for a one-element first family.**

For `card ι = 1` the lower frame bound is `1 = (1 - √((m-1)/n))²`, and the upper bound is as
in `Discretization.bss_generalized_of_gram_eq_one`.  Together with that theorem, which needs
`m ≥ 2`, every `m` is covered. -/
theorem bss_generalized_of_unique [Unique ι] [Nonempty κ]
    {J : Matrix κ κ ℂ} (hJ : J.PosDef) {Λ : ℝ} (hΛ : 0 < Λ)
    (hJΛ : J ≤ Λ • (1 : Matrix κ κ ℂ)) {a : Ω → ι → ℂ} {b : Ω → κ → ℂ}
    (ha : ∀ k, MemLp (fun x => a x k) 2 μ) (hb : ∀ k, MemLp (fun x => b x k) 2 μ)
    (hgrama : gram a μ = 1) (hgramb : gram b μ = J)
    {n : ℕ} (hn : 0 < n) (hM : 1 + 1 / (n : ℝ) ≤ RCLike.re J.trace / Λ) :
    ∃ (x : Fin n → Ω) (w : Fin n → ℝ), (∀ i, 0 < w i) ∧
      (1 : Matrix ι ι ℂ) ≤ ∑ i, w i • vecMulVec (a (x i)) (star (a (x i))) ∧
      ∑ i, w i • vecMulVec (b (x i)) (star (b (x i)))
        ≤ ((1 + Real.sqrt ((RCLike.re J.trace / Λ - 1) / n)) ^ 2 * Λ)
            • (1 : Matrix κ κ ℂ) := by
  -- the parameters of the upper half of the construction
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  set M : ℝ := RCLike.re J.trace / Λ with hMdef
  set s : ℝ := Real.sqrt ((M - 1) / n) with hsdef
  have hs0 : 1 / (n : ℝ) ≤ s := one_div_le_sqrt_div hn0 hM
  have hspos : 0 < s := lt_of_lt_of_le (by positivity) hs0
  have hM1 : (1 : ℝ) ≤ M := by
    have h1 : 0 < 1 / (n : ℝ) := by positivity
    linarith
  have hM_eq : M = (n : ℝ) * s ^ 2 + 1 := eq_mul_sq_sqrt_div_add_one hn0 hM1
  have hT : RCLike.re J.trace = Λ * ((n : ℝ) * s ^ 2 + 1) := by
    rw [← hM_eq, hMdef]
    field_simp
  set ζ : ℝ := (1 + s) / n with hζdef
  have hζ0 : 0 < ζ := div_pos (by linarith) hn0
  clear_value M s
  have hT0 : 0 < RCLike.re J.trace := (RCLike.pos_iff.mp hJ.trace_pos).1
  set d₀ : ℝ := ζ * RCLike.re J.trace / s with hd₀def
  have hd₀0 : 0 < d₀ := div_pos (by positivity) hspos
  have hB₀ : (d₀ • (1 : Matrix κ κ ℂ)).PosDef := Matrix.PosDef.one.smul hd₀0
  clear_value ζ d₀
  have hΨ₀ : upperPotential J (d₀ • (1 : Matrix κ κ ℂ)) = s / ζ := by
    rw [upperPotential_smul_one J hd₀0.ne', hd₀def]
    field_simp
  have h1s : (1 : ℝ) + s ≠ 0 := by positivity
  have hgap : 1 / ζ + upperPotential J (d₀ • (1 : Matrix κ κ ℂ)) ≤ n := by
    rw [hΨ₀, hζdef, one_div_add_div_eq hn0 h1s]
  -- run the one-sided construction
  obtain ⟨x, w, hwpos, hBn, hΨn, hwk⟩ :=
    exists_points_weights_of_unique hJ hB₀ hζ0 ha hb hgrama hgramb hgap n
  refine ⟨x, w, hwpos, ?_, ?_⟩
  · -- the lower frame bound is an identity: each point contributes exactly `1/n`
    rw [sum_smul_vecMulVec_eq_one hn0 x w hwk]
  · -- the upper frame bound, exactly as in the main theorem
    exact upper_frame_bound hJ hΛ hJΛ hn0 hs0 hζdef hd₀def hT hBn (hΨ₀ ▸ hΨn)

end Discretization
