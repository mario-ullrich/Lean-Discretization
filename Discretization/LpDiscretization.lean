/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import Discretization.OneSidedDiscretization
public import Discretization.KieferWolfowitz.Measure

/-!
# Discretization of the `L_p`-norms with `n ≥ m` points

Let `μ` be a probability measure and `a₁, …, a_m` bounded measurable functions whose Gram
matrix `∫ a a* dμ` is positive definite.  For every `n ≥ m` there are `n` points
`x₁, …, xₙ`, not necessarily distinct, such that

`κ ‖f‖_{L_p(μ)} ≤ m^{1/2 - 1/p} ((2/n) ∑ᵢ |f(xᵢ)|²)^{1/2}`,   `κ = max(1 - √(m/n), 1/(2m))`,

for every `f` in the span and every `2 ≤ p ≤ ∞`, with the same points for all `p`.  For
finite `p` the theorem states the `p`-th power of this inequality, for `p = ∞` the inequality
at every point.  This is Proposition 8 of Chkifa, Dolbeault, Krieg and Ullrich.  The paper
takes `2n` points, `n` for `μ` and `n` for the Kiefer–Wolfowitz measure `ϱ`, each with the
weight `1/n`; here `n` points with the weight `2/n` serve both, chosen for the mixture
`(μ + ϱ)/2`.

The proof combines three facts.

* The Kiefer–Wolfowitz measure `ϱ` (`Discretization.KieferWolfowitz.exists_optimal_measure`)
  controls the uniform norm, `|f(y)|² ≤ (m + ε) ∫ |f|² dϱ`.
* The one-sided discretization of the mixture `(μ + ϱ)/2`
  (`Discretization.exists_one_sided_discretization`) gives `n` points with
  `(1 - r)² (∫ |f|² dμ + ∫ |f|² dϱ) ≤ (2/n) ∑ᵢ |f(xᵢ)|²`, where `r = √((m-1)/n)`.
* On a probability space `∫ |f|^p dμ ≤ ‖f‖_∞^{p-2} ∫ |f|² dμ`.

The factor `κ` lies strictly below `1 - r` (`Discretization.max_one_sub_sqrt_div_lt`), and this
gap absorbs the `ε` of the Kiefer–Wolfowitz measure: with `ε = m ((1 - r)²/κ² - 1)` one has
`κ² (m + ε) = m (1 - r)²`.  The final estimate is a statement about real numbers,
`Discretization.lp_bound_of_averages`.
-/

@[expose] public section

open Matrix MeasureTheory
open scoped ComplexOrder MatrixOrder ENNReal

namespace Discretization

/-! ### Real inequalities -/

/-- **The factor of Proposition 8 lies below the sharp one.**  For `1 ≤ m ≤ n`,

`max (1 - √(m/n)) (1/(2m)) < 1 - √((m-1)/n)`.

The first term is smaller because `m - 1 < m`.  The second is smaller because
`√((m-1)/n) ≤ √((m-1)/m) < 1 - 1/(2m)`, as `(1 - 1/(2m))² m = m - 1 + 1/(4m)`. -/
theorem max_one_sub_sqrt_div_lt {m n : ℝ} (hm : 1 ≤ m) (hmn : m ≤ n) :
    max (1 - Real.sqrt (m / n)) (1 / (2 * m)) < 1 - Real.sqrt ((m - 1) / n) := by
  have hn : 0 < n := by linarith
  have hm0 : 0 < m := by linarith
  refine max_lt ?_ ?_
  · have h : Real.sqrt ((m - 1) / n) < Real.sqrt (m / n) :=
      Real.sqrt_lt_sqrt (div_nonneg (by linarith) hn.le)
        (div_lt_div_of_pos_right (by linarith) hn)
    linarith
  · have h1 : Real.sqrt ((m - 1) / n) ≤ Real.sqrt ((m - 1) / m) :=
      Real.sqrt_le_sqrt (div_le_div_of_nonneg_left (by linarith) hm0 hmn)
    have hpos : 0 < 1 - 1 / (2 * m) := by
      rw [sub_pos, div_lt_one (by positivity)]
      linarith
    have h2 : Real.sqrt ((m - 1) / m) < 1 - 1 / (2 * m) := by
      rw [Real.sqrt_lt' hpos, div_lt_iff₀ hm0]
      have hsq : (1 - 1 / (2 * m)) ^ 2 * m = m - 1 + 1 / (4 * m) := by
        field_simp
        ring
      have h4 : 0 < 1 / (4 * m) := by positivity
      linarith
    linarith

/-- The factor `max (1 - √(m/n)) (1/(2m))` of Proposition 8 is positive. -/
theorem max_one_sub_sqrt_div_pos {m n : ℝ} (hm : 0 < m) :
    0 < max (1 - Real.sqrt (m / n)) (1 / (2 * m)) :=
  lt_max_of_lt_right (by positivity)

/-- **A product of an average and a power of another.**  For `A, B ≥ 0` and `q ≥ 0`,

`B^q · A ≤ (A + B)^{q+1}`,

since each factor is at most `A + B`. -/
theorem rpow_mul_le_add_rpow {A B q : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hq : 0 ≤ q) :
    B ^ q * A ≤ (A + B) ^ (q + 1) := by
  have hq1 : q + 1 ≠ 0 := (by linarith : (0 : ℝ) < q + 1).ne'
  rw [Real.rpow_add_one' (add_nonneg hA hB) hq1]
  exact mul_le_mul (Real.rpow_le_rpow hB (by linarith) hq) (by linarith) hA
    (Real.rpow_nonneg (add_nonneg hA hB) q)

/-- **The interpolation step, at one point.**  For `t ≥ 0`, `p ≥ 2` and `t² ≤ T`,

`t^p ≤ T^{p/2 - 1} t²`:

the factor `t^{p-2} = (t²)^{p/2 - 1}` is at most `T^{p/2 - 1}`.  With `t = |f(y)|` and
`T = ‖f‖²_∞` this is `|f(y)|^p ≤ ‖f‖_∞^{p-2} |f(y)|²`. -/
theorem rpow_le_rpow_mul_sq {t T p : ℝ} (ht : 0 ≤ t) (hp : 2 ≤ p) (htT : t ^ 2 ≤ T) :
    t ^ p ≤ T ^ (p / 2 - 1) * t ^ 2 := by
  have hq : 0 ≤ p / 2 - 1 := by linarith
  have hsq : 0 ≤ t ^ 2 := sq_nonneg t
  have hq1 : p / 2 - 1 + 1 ≠ 0 := (by linarith : (0 : ℝ) < p / 2 - 1 + 1).ne'
  calc t ^ p = (t ^ 2) ^ (p / 2 - 1 + 1) := by
        rw [sub_add_cancel, ← Real.rpow_natCast, ← Real.rpow_mul ht]
        congr 1
        push_cast
        ring
    _ = (t ^ 2) ^ (p / 2 - 1) * t ^ 2 := Real.rpow_add_one' hsq hq1
    _ ≤ T ^ (p / 2 - 1) * t ^ 2 :=
        mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hsq htT hq) hsq

/-- **The `L_p` bound from the two averages**, for real numbers.  Let `A, B ≥ 0`, let
`s² (A + B) ≤ X`, and let `0 ≤ κ ≤ s` with `κ² K ≤ m s²`, where `K, m ≥ 0`.  Then for every
`q ≥ 0`

`(κ²)^{q+1} (K B)^q A ≤ m^q X^{q+1}`.

In the application `A` and `B` are the averages of `|f|²` for `μ` and for the
Kiefer–Wolfowitz measure, `K B` bounds `‖f‖²_∞`, `X` is the discrete average, `s = 1 - r`,
and `q = p/2 - 1`. -/
theorem lp_bound_of_averages {A B K X m s κ q : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hK : 0 ≤ K)
    (hm : 0 ≤ m) (hκ0 : 0 ≤ κ) (hκs : κ ≤ s) (hκK : κ ^ 2 * K ≤ m * s ^ 2)
    (hX : s ^ 2 * (A + B) ≤ X) (hq : 0 ≤ q) :
    (κ ^ 2) ^ (q + 1) * ((K * B) ^ q * A) ≤ m ^ q * X ^ (q + 1) := by
  have hκ2 : 0 ≤ κ ^ 2 := sq_nonneg κ
  have hs2 : κ ^ 2 ≤ s ^ 2 := pow_le_pow_left₀ hκ0 hκs 2
  have hAB : 0 ≤ A + B := add_nonneg hA hB
  have hq1 : q + 1 ≠ 0 := (by linarith : (0 : ℝ) < q + 1).ne'
  calc (κ ^ 2) ^ (q + 1) * ((K * B) ^ q * A)
      = (κ ^ 2 * K) ^ q * κ ^ 2 * (B ^ q * A) := by
        rw [Real.mul_rpow hK hB, Real.rpow_add_one' hκ2 hq1, Real.mul_rpow hκ2 hK]
        ring
    _ ≤ (m * s ^ 2) ^ q * s ^ 2 * (A + B) ^ (q + 1) :=
        mul_le_mul
          (mul_le_mul (Real.rpow_le_rpow (mul_nonneg hκ2 hK) hκK hq) hs2 hκ2
            (Real.rpow_nonneg (mul_nonneg hm (sq_nonneg s)) q))
          (rpow_mul_le_add_rpow hA hB hq) (mul_nonneg (Real.rpow_nonneg hB q) hA)
          (mul_nonneg (Real.rpow_nonneg (mul_nonneg hm (sq_nonneg s)) q) (sq_nonneg s))
    _ = m ^ q * (s ^ 2 * (A + B)) ^ (q + 1) := by
        rw [Real.mul_rpow hm (sq_nonneg s), Real.mul_rpow (sq_nonneg s) hAB,
          Real.rpow_add_one' (sq_nonneg s) hq1]
        ring
    _ ≤ m ^ q * X ^ (q + 1) :=
        mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (mul_nonneg (sq_nonneg s) hAB) hX (by linarith))
          (Real.rpow_nonneg hm q)

/-- The case `p = ∞` of `Discretization.lp_bound_of_averages`: under the same hypotheses on
`A, B, K, m, s, κ, X`, every `t ≤ K B` satisfies `κ² t ≤ m X`. -/
theorem sq_mul_le_of_averages {A B K X m s κ t : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hK : 0 ≤ K)
    (hκK : κ ^ 2 * K ≤ m * s ^ 2) (hm : 0 ≤ m) (hX : s ^ 2 * (A + B) ≤ X)
    (ht : t ≤ K * B) : κ ^ 2 * t ≤ m * X := by
  have hκ2 : 0 ≤ κ ^ 2 := sq_nonneg κ
  calc κ ^ 2 * t ≤ κ ^ 2 * (K * (A + B)) :=
        mul_le_mul_of_nonneg_left (ht.trans (mul_le_mul_of_nonneg_left (by linarith) hK)) hκ2
    _ = κ ^ 2 * K * (A + B) := by ring
    _ ≤ m * s ^ 2 * (A + B) := mul_le_mul_of_nonneg_right hκK (add_nonneg hA hB)
    _ = m * (s ^ 2 * (A + B)) := by ring
    _ ≤ m * X := mul_le_mul_of_nonneg_left hX hm

/-! ### The equal mixture of two measures -/

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The equal mixture `(μ + ϱ)/2` of two probability measures is a probability measure. -/
theorem isProbabilityMeasure_half_add (μ ϱ : Measure Ω) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ϱ] : IsProbabilityMeasure ((2 : ℝ≥0∞)⁻¹ • (μ + ϱ)) := by
  constructor
  rw [Measure.smul_apply, Measure.add_apply, measure_univ, measure_univ, smul_eq_mul,
    one_add_one_eq_two, ENNReal.inv_mul_cancel (by simp) (by simp)]

/-- **Integration against the equal mixture** `(μ + ϱ)/2` is the mean of the two integrals. -/
theorem integral_half_add {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {μ ϱ : Measure Ω} {g : Ω → E} (hμ : Integrable g μ)
    (hϱ : Integrable g ϱ) :
    ∫ y, g y ∂((2 : ℝ≥0∞)⁻¹ • (μ + ϱ)) = (2⁻¹ : ℝ) • (∫ y, g y ∂μ + ∫ y, g y ∂ϱ) := by
  rw [integral_smul_measure, integral_add_measure hμ hϱ, ENNReal.toReal_inv,
    ENNReal.toReal_ofNat]

variable {ι : Type*}

/-- **The Gram matrix of the equal mixture** `(μ + ϱ)/2` is the mean of the two Gram
matrices. -/
theorem gram_half_add {μ ϱ : Measure Ω} {a : Ω → ι → ℂ}
    (haμ : ∀ k, MemLp (fun x => a x k) 2 μ) (haϱ : ∀ k, MemLp (fun x => a x k) 2 ϱ) :
    gram a ((2 : ℝ≥0∞)⁻¹ • (μ + ϱ)) = (2⁻¹ : ℝ) • (gram a μ + gram a ϱ) := by
  ext k l
  rw [gram_apply, integral_half_add (integrable_mul_star haμ k l) (integrable_mul_star haϱ k l),
    Matrix.smul_apply, Matrix.add_apply, gram_apply, gram_apply]

/-! ### Bounded measurable families -/

/-- The coordinates of a bounded measurable family are square-integrable for every finite
measure. -/
theorem memLp_two_of_bound {μ : Measure Ω} [IsFiniteMeasure μ] {a : Ω → ι → ℂ} {C : ℝ}
    (hC : ∀ y i, ‖a y i‖ ≤ C) (hmeas : ∀ i, Measurable fun y => a y i) (k : ι) :
    MemLp (fun y => a y k) 2 μ :=
  MemLp.of_bound (hmeas k).aestronglyMeasurable C (ae_of_all _ fun y => hC y k)

variable [Fintype ι]

omit [MeasurableSpace Ω] in
/-- A function `f(y) = ⟪c, a(y)⟫` of the span of a family bounded by `C` is bounded by
`∑ₖ |cₖ| C`. -/
theorem norm_dotProduct_le {a : Ω → ι → ℂ} {C : ℝ} (hC : ∀ y i, ‖a y i‖ ≤ C) (c : ι → ℂ)
    (y : Ω) : ‖star c ⬝ᵥ a y‖ ≤ ∑ i, ‖c i‖ * C := by
  simp only [dotProduct, Pi.star_apply]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [norm_mul, norm_star]
  exact mul_le_mul_of_nonneg_left (hC y i) (norm_nonneg _)

/-- The squared modulus of a function `f(y) = ⟪c, a(y)⟫` of the span of a measurable family is
measurable. -/
theorem measurable_norm_dotProduct_sq {a : Ω → ι → ℂ}
    (hmeas : ∀ i, Measurable fun y => a y i) (c : ι → ℂ) :
    Measurable fun y => ‖star c ⬝ᵥ a y‖ ^ 2 :=
  Measurable.pow_const (Measurable.norm
    (Finset.measurable_sum _ fun i _ => Measurable.mul measurable_const (hmeas i))) 2

/-- The squared modulus of a function of the span of a bounded measurable family is integrable
for every finite measure. -/
theorem integrable_norm_dotProduct_sq {μ : Measure Ω} [IsFiniteMeasure μ] {a : Ω → ι → ℂ}
    {C : ℝ} (hC : ∀ y i, ‖a y i‖ ≤ C) (hmeas : ∀ i, Measurable fun y => a y i)
    (c : ι → ℂ) : Integrable (fun y => ‖star c ⬝ᵥ a y‖ ^ 2) μ := by
  refine (integrable_const ((∑ i, ‖c i‖ * C) ^ 2)).mono'
    (measurable_norm_dotProduct_sq hmeas c).aestronglyMeasurable (ae_of_all _ fun y => ?_)
  rw [Real.norm_of_nonneg (by positivity)]
  exact pow_le_pow_left₀ (norm_nonneg _) (norm_dotProduct_le hC c y) 2

/-! ### The theorem -/

variable [DecidableEq ι]

/-- **Discretization of the `L_p`-norms from a measure that controls the uniform norm.**

Let `μ` be a probability measure and `a` a bounded measurable family indexed by a finite
nonempty set `ι` of `m` elements, with positive definite Gram matrix.  Let `ϱ` be a
probability measure with positive definite Gram matrix and `|f(y)|² ≤ K ∫ |f|² dϱ` at every
point `y`, and let `0 ≤ κ ≤ 1 - √((m-1)/n)` with `κ² K ≤ m (1 - √((m-1)/n))²`.  Then for
every `n ≥ m` there are `n` points, not necessarily distinct, with

`κ^p ∫ |f|^p dμ ≤ m^{p/2-1} ((2/n) ∑ᵢ |f(xᵢ)|²)^{p/2}`   for every `p ≥ 2`, and
`κ² |f(y)|² ≤ m (2/n) ∑ᵢ |f(xᵢ)|²`   for every point `y`,

for every function `f(y) = ⟪c, a(y)⟫` in the span.  The points are those of the one-sided
discretization of the mixture `(μ + ϱ)/2`, which gives
`(1 - r)² (∫ |f|² dμ + ∫ |f|² dϱ) ≤ (2/n) ∑ᵢ |f(xᵢ)|²` with `r = √((m-1)/n)`; the rest is
`Discretization.lp_bound_of_averages`. -/
theorem exists_lp_discretization_of_measure [Nonempty ι] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {a : Ω → ι → ℂ} {C : ℝ} (hC : ∀ y i, ‖a y i‖ ≤ C)
    (hmeas : ∀ i, Measurable fun y => a y i) (hI : (gram a μ).PosDef) {ϱ : Measure Ω}
    [IsProbabilityMeasure ϱ] (hG : (gram a ϱ).PosDef) {K : ℝ} (hK0 : 0 ≤ K)
    (hK : ∀ (c : ι → ℂ) (y : Ω), ‖star c ⬝ᵥ a y‖ ^ 2 ≤ K * ∫ z, ‖star c ⬝ᵥ a z‖ ^ 2 ∂ϱ)
    {n : ℕ} (hmn : Fintype.card ι ≤ n) {κ : ℝ} (hκ0 : 0 ≤ κ)
    (hκ : κ ≤ 1 - Real.sqrt ((Fintype.card ι - 1) / n))
    (hκK : κ ^ 2 * K ≤ Fintype.card ι * (1 - Real.sqrt ((Fintype.card ι - 1) / n)) ^ 2) :
    ∃ x : Fin n → Ω, ∀ c : ι → ℂ,
      (∀ p : ℝ, 2 ≤ p →
        κ ^ p * ∫ y, ‖star c ⬝ᵥ a y‖ ^ p ∂μ
          ≤ (Fintype.card ι : ℝ) ^ (p / 2 - 1)
              * (2 / (n : ℝ) * ∑ i, ‖star c ⬝ᵥ a (x i)‖ ^ 2) ^ (p / 2)) ∧
      ∀ y : Ω, κ ^ 2 * ‖star c ⬝ᵥ a y‖ ^ 2
          ≤ Fintype.card ι * (2 / (n : ℝ) * ∑ i, ‖star c ⬝ᵥ a (x i)‖ ^ 2) := by
  -- the mixture `(μ + ϱ)/2`, a probability measure with positive definite Gram matrix
  have haμ : ∀ k, MemLp (fun y => a y k) 2 μ := memLp_two_of_bound hC hmeas
  have haϱ : ∀ k, MemLp (fun y => a y k) 2 ϱ := memLp_two_of_bound hC hmeas
  have := isProbabilityMeasure_half_add μ ϱ
  have haν : ∀ k, MemLp (fun y => a y k) 2 ((2 : ℝ≥0∞)⁻¹ • (μ + ϱ)) :=
    memLp_two_of_bound hC hmeas
  have hIν : (gram a ((2 : ℝ≥0∞)⁻¹ • (μ + ϱ))).PosDef := by
    rw [gram_half_add haμ haϱ]
    exact (hI.add hG).smul (by norm_num)
  -- its one-sided discretization
  obtain ⟨x, hx⟩ := exists_one_sided_discretization haν hIν hmn
  refine ⟨x, fun c => ?_⟩
  have hintμ := integrable_norm_dotProduct_sq (μ := μ) hC hmeas c
  have hintϱ := integrable_norm_dotProduct_sq (μ := ϱ) hC hmeas c
  have hA : 0 ≤ ∫ y, ‖star c ⬝ᵥ a y‖ ^ 2 ∂μ := integral_nonneg fun _ => by positivity
  have hB : 0 ≤ ∫ y, ‖star c ⬝ᵥ a y‖ ^ 2 ∂ϱ := integral_nonneg fun _ => by positivity
  have hm : (0 : ℝ) ≤ Fintype.card ι := Nat.cast_nonneg _
  -- the discrete average controls the sum of the two averages
  have hX : (1 - Real.sqrt ((Fintype.card ι - 1) / n)) ^ 2
      * (∫ y, ‖star c ⬝ᵥ a y‖ ^ 2 ∂μ + ∫ y, ‖star c ⬝ᵥ a y‖ ^ 2 ∂ϱ)
      ≤ 2 / (n : ℝ) * ∑ i, ‖star c ⬝ᵥ a (x i)‖ ^ 2 := by
    have h := hx c
    rw [integral_half_add hintμ hintϱ, smul_eq_mul] at h
    calc _ = 2 * ((1 - Real.sqrt ((Fintype.card ι - 1) / n)) ^ 2
          * (2⁻¹ * (∫ y, ‖star c ⬝ᵥ a y‖ ^ 2 ∂μ + ∫ y, ‖star c ⬝ᵥ a y‖ ^ 2 ∂ϱ))) := by ring
      _ ≤ 2 * (1 / (n : ℝ) * ∑ i, ‖star c ⬝ᵥ a (x i)‖ ^ 2) :=
        mul_le_mul_of_nonneg_left h (by norm_num)
      _ = _ := by ring
  refine ⟨fun p hp => ?_, fun y => sq_mul_le_of_averages hA hB hK0 hκK hm hX (hK c y)⟩
  -- interpolation: `∫ |f|^p dμ ≤ (K B)^{p/2-1} ∫ |f|² dμ`
  have hq : 0 ≤ p / 2 - 1 := by linarith
  have hint : ∫ y, ‖star c ⬝ᵥ a y‖ ^ p ∂μ
      ≤ (K * ∫ z, ‖star c ⬝ᵥ a z‖ ^ 2 ∂ϱ) ^ (p / 2 - 1) * ∫ y, ‖star c ⬝ᵥ a y‖ ^ 2 ∂μ := by
    have h := integral_mono_of_nonneg (μ := μ) (f := fun y => ‖star c ⬝ᵥ a y‖ ^ p)
      (ae_of_all _ fun y => Real.rpow_nonneg (norm_nonneg _) p)
      (hintμ.const_mul ((K * ∫ z, ‖star c ⬝ᵥ a z‖ ^ 2 ∂ϱ) ^ (p / 2 - 1)))
      (ae_of_all _ fun y => rpow_le_rpow_mul_sq (norm_nonneg _) hp (hK c y))
    rwa [integral_const_mul] at h
  -- assembly
  have hκp : κ ^ p = (κ ^ 2) ^ (p / 2 - 1 + 1) := by
    rw [sub_add_cancel, ← Real.rpow_natCast, ← Real.rpow_mul hκ0]
    congr 1
    push_cast
    ring
  calc κ ^ p * ∫ y, ‖star c ⬝ᵥ a y‖ ^ p ∂μ
      ≤ κ ^ p * ((K * ∫ z, ‖star c ⬝ᵥ a z‖ ^ 2 ∂ϱ) ^ (p / 2 - 1)
          * ∫ y, ‖star c ⬝ᵥ a y‖ ^ 2 ∂μ) :=
        mul_le_mul_of_nonneg_left hint (Real.rpow_nonneg hκ0 p)
    _ = (κ ^ 2) ^ (p / 2 - 1 + 1) * ((K * ∫ z, ‖star c ⬝ᵥ a z‖ ^ 2 ∂ϱ) ^ (p / 2 - 1)
          * ∫ y, ‖star c ⬝ᵥ a y‖ ^ 2 ∂μ) := by rw [hκp]
    _ ≤ (Fintype.card ι : ℝ) ^ (p / 2 - 1)
          * (2 / (n : ℝ) * ∑ i, ‖star c ⬝ᵥ a (x i)‖ ^ 2) ^ (p / 2 - 1 + 1) :=
        lp_bound_of_averages hA hB hK0 hm hκ0 hκ hκK hX hq
    _ = (Fintype.card ι : ℝ) ^ (p / 2 - 1)
          * (2 / (n : ℝ) * ∑ i, ‖star c ⬝ᵥ a (x i)‖ ^ 2) ^ (p / 2) := by rw [sub_add_cancel]

/-- **Discretization of the `L_p`-norms with `n ≥ m` points**
(Chkifa–Dolbeault–Krieg–Ullrich, Proposition 8).

Let `μ` be a probability measure and `a₁, …, a_m` bounded measurable functions with positive
definite Gram matrix `∫ a a* dμ`.  Then for every `n ≥ m` there are `n` points, not
necessarily distinct, such that, with `κ = max(1 - √(m/n), 1/(2m))`,

`κ^p ∫ |f|^p dμ ≤ m^{p/2-1} ((2/n) ∑ᵢ |f(xᵢ)|²)^{p/2}`   for every `p ≥ 2`, and
`κ² |f(y)|² ≤ m (2/n) ∑ᵢ |f(xᵢ)|²`   for every point `y`,

for every function `f(y) = ⟪c, a(y)⟫` in the span.  In norm form,
`κ ‖f‖_p ≤ m^{1/2-1/p} ((2/n) ∑ᵢ |f(xᵢ)|²)^{1/2}` for every `2 ≤ p ≤ ∞`, with the same points
for all `p`.  The paper takes `2n` points, `n` for `μ` and `n` for the Kiefer–Wolfowitz
measure, each with the weight `1/n`.

The proof takes the Kiefer–Wolfowitz measure with `ε = m ((1 - r)²/κ² - 1)`, `r = √((m-1)/n)`,
so that `κ² (m + ε) = m (1 - r)²`, and applies
`Discretization.exists_lp_discretization_of_measure`; `ε > 0` because `κ < 1 - r`
(`Discretization.max_one_sub_sqrt_div_lt`). -/
theorem exists_lp_discretization [Nonempty ι] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (a : Ω → ι → ℂ) {C : ℝ} (hC : ∀ y i, ‖a y i‖ ≤ C)
    (hmeas : ∀ i, Measurable fun y => a y i) (hI : (gram a μ).PosDef) {n : ℕ}
    (hmn : Fintype.card ι ≤ n) :
    ∃ x : Fin n → Ω, ∀ c : ι → ℂ,
      (∀ p : ℝ, 2 ≤ p →
        (max (1 - Real.sqrt (Fintype.card ι / n)) (1 / (2 * (Fintype.card ι : ℝ)))) ^ p
            * ∫ y, ‖star c ⬝ᵥ a y‖ ^ p ∂μ
          ≤ (Fintype.card ι : ℝ) ^ (p / 2 - 1)
              * (2 / (n : ℝ) * ∑ i, ‖star c ⬝ᵥ a (x i)‖ ^ 2) ^ (p / 2)) ∧
      ∀ y : Ω, (max (1 - Real.sqrt (Fintype.card ι / n)) (1 / (2 * (Fintype.card ι : ℝ)))) ^ 2
            * ‖star c ⬝ᵥ a y‖ ^ 2
          ≤ Fintype.card ι * (2 / (n : ℝ) * ∑ i, ‖star c ⬝ᵥ a (x i)‖ ^ 2) := by
  have hm1 : (1 : ℝ) ≤ Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hmn' : (Fintype.card ι : ℝ) ≤ n := by exact_mod_cast hmn
  have hκ0 := max_one_sub_sqrt_div_pos (n := (n : ℝ)) (by linarith : (0 : ℝ) < Fintype.card ι)
  have hκs := max_one_sub_sqrt_div_lt hm1 hmn'
  set κ := max (1 - Real.sqrt (Fintype.card ι / n)) (1 / (2 * (Fintype.card ι : ℝ))) with hκ
  set s := 1 - Real.sqrt ((Fintype.card ι - 1) / n) with hs
  -- the `ε` that the gap between `κ` and `s` absorbs
  have hκs2 : κ ^ 2 < s ^ 2 := by nlinarith
  have hε : 0 < (Fintype.card ι : ℝ) * (s ^ 2 / κ ^ 2 - 1) :=
    mul_pos (by linarith) (sub_pos.2 ((one_lt_div (by positivity)).2 hκs2))
  have hκK : κ ^ 2 * (Fintype.card ι + (Fintype.card ι : ℝ) * (s ^ 2 / κ ^ 2 - 1))
      = Fintype.card ι * s ^ 2 := by
    have hκne : κ ≠ 0 := hκ0.ne'
    field_simp
    ring
  have hli := forall_eq_zero_of_posDef_gram (memLp_two_of_bound hC hmeas) hI
  obtain ⟨ϱ, hϱ, hG, hbound⟩ := KieferWolfowitz.exists_optimal_measure a hC hmeas hli hε
  exact exists_lp_discretization_of_measure hC hmeas hI hG (by linarith) hbound hmn hκ0.le
    hκs.le hκK.le

end Discretization
