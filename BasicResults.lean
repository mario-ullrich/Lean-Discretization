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
import BasicResults.OperatorQuadraticForm

/-!
# General ingredients

The matrix analysis and integration facts that the discretization theory consumes.
Nothing in this library mentions discretization, sampling or measures on the domain of the
functions; every result here is a statement about matrices over an `RCLike` field or about
Bochner integrals, and most of them are candidates for Mathlib.

Throughout, matrices are compared in the **Loewner order** `A ≤ B ↔ (B - A).PosSemidef`.
In Lean this order is switched on by the command `open scoped MatrixOrder`, and the order on
`ℂ` by `open scoped ComplexOrder`.

## Layout

* `BasicResults.LoewnerOrder`: comparisons with multiples of the identity.  A Hermitian
  matrix is below `c • 1` once `c` bounds its eigenvalues, a positive semidefinite matrix is
  below `(Re Tr A) • 1`, the inverse is antitone, and `A - δ • 1` stays positive definite for
  `δ` below the reciprocal of `Re Tr A⁻¹`.  It also holds the resolvent identity for the two
  shifts `A ↦ A - δ • 1` and `B ↦ B + ζ • J` of the construction.
* `BasicResults.TraceInequalities`: the trace of a product of positive semidefinite
  matrices is nonnegative (positive for positive definite ones), the trace of a product of
  Hermitian matrices is real, and Cauchy–Schwarz for the semi-inner product
  `⟪P, Q⟫ = Tr (Q * Y * Pᴴ)`.
* `BasicResults.PotentialBounds`: a positive definite `B` dominates `Ψ(B)⁻¹ • J`, where
  `Ψ(B) = Re Tr (J B⁻¹)`.  This is the step that makes the upper frame bound depend on the
  effective dimension only.
* `BasicResults.ShermanMorrison`: the inverse, the trace of the inverse, and positive
  definiteness under a rank-one update `A ↦ A ± w a a*`.
* `BasicResults.IntegralQuadraticForm`: the bridge to measure theory.  The average of a
  quadratic form along a square-integrable family is the trace against its Gram matrix.
* `BasicResults.OperatorTrace`: the trace of an operator along a Hilbert basis, for the
  passage to a countably infinite second family.  For a positive operator
  `Re ⟪x, T x⟫ = ‖√T x‖²`, so the trace is a squared Hilbert–Schmidt norm, and the crude
  bound `T ≤ Tr(T) • 1` holds.
* `BasicResults.OperatorShermanMorrison`: rank-one updates of an operator, with the
  Sherman–Morrison formula for `Ring.inverse` and the preservation of strict positivity.  The
  last section is the operator counterpart of the order facts above, for the shift
  `B ↦ B + ζ • J`.
* `BasicResults.OperatorQuadraticForm`: the average of a quadratic form along a
  square-integrable family is a trace against the Gram operator.
-/
