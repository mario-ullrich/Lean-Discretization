/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
import BasicResults.LoewnerOrder
import BasicResults.TraceInequalities
import BasicResults.PotentialBounds
import BasicResults.ShermanMorrison
import BasicResults.IntegralQuadraticForm
import BasicResults.OperatorTrace
import BasicResults.OperatorShermanMorrison

/-!
# General ingredients

The matrix analysis and integration facts that the discretization theory consumes.
Nothing in this library mentions discretization, sampling or measures on the domain of the
functions; every result here is a statement about matrices over an `RCLike` field or about
Bochner integrals, and most of them are candidates for Mathlib.

Throughout, matrices are compared in the **Loewner order** `A ≤ B ↔ (B - A).PosSemidef`,
which Mathlib provides after `open scoped MatrixOrder`; positivity of scalars needs
`open scoped ComplexOrder` alongside it.

## Layout

* `BasicResults.OperatorTrace` — the trace of an operator along a Hilbert basis, for the
  passage to a countably infinite second family: `Re ⟪x, T x⟫ = ‖√T x‖²` for a positive
  operator, so that the trace is a squared Hilbert–Schmidt norm, and the crude bound
  `T ≤ Tr(T) • 1`.
* `BasicResults.LoewnerOrder` — comparisons with multiples of the identity: a Hermitian
  matrix is below `c • 1` once `c` bounds its eigenvalues, a positive semidefinite matrix is
  below `(Tr A) • 1`, the inverse is antitone, and `A - δ • 1` stays positive definite for
  `δ` below the reciprocal of `Tr A⁻¹`.
* `BasicResults.TraceInequalities` — the trace of a product of positive semidefinite
  matrices is nonnegative (positive for positive definite ones), the trace of a product of
  Hermitian matrices is real, and Cauchy–Schwarz for the semi-inner product
  `⟪P, Q⟫ = Tr (Q * Y * Pᴴ)`.
* `BasicResults.PotentialBounds` — a positive definite `B` dominates `Ψ(B)⁻¹ • J`, where
  `Ψ(B) = Re Tr (J B⁻¹)`; this is the step that makes the upper frame bound depend on the
  effective dimension only.
* `BasicResults.ShermanMorrison` — the inverse, the trace of the inverse, and positive
  definiteness under a rank-one update `A ↦ A ± w a a*`.
* `BasicResults.IntegralQuadraticForm` — the bridge to measure theory: the average of a
  quadratic form along a square-integrable family is the trace against its Gram matrix.
-/
