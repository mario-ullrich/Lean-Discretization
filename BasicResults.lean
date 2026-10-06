/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import BasicResults.SqrtConjugation
public import BasicResults.IntegralQuadraticForm
public import BasicResults.CompactConvexHull
public import BasicResults.Matrix.LoewnerOrder
public import BasicResults.Matrix.TraceInequalities
public import BasicResults.Matrix.PotentialBounds
public import BasicResults.Matrix.ShermanMorrison
public import BasicResults.Matrix.QuadraticForm
public import BasicResults.Matrix.RankOneDeterminant
public import BasicResults.Operator.Trace
public import BasicResults.Operator.ShermanMorrison
public import BasicResults.Operator.QuadraticForm
public import BasicResults.Operator.GramOperator

/-!
# General ingredients

The matrix analysis, operator theory and integration facts that the discretization theory
consumes: statements about matrices, operators on a complex Hilbert space and Bochner
integrals, most of them candidates for Mathlib.  Two files,
`IntegralQuadraticForm` and `Matrix/QuadraticForm`, use the namespace `Discretization`, since
their lemmas are phrased for the families of functions of the development.

Throughout, matrices are compared in the **Loewner order** `A ≤ B ↔ (B - A).PosSemidef`.
In Lean this order is switched on by the command `open scoped MatrixOrder`, and the order on
`ℂ` by `open scoped ComplexOrder`.

## Layout

The files at the top level are general; `BasicResults/Matrix/` holds the matrix facts
and `BasicResults/Operator/` their counterparts for operators on a Hilbert space, which
a second family in a Hilbert space needs.

* `BasicResults.SqrtConjugation`: a bound on the conjugate of `X` by the inverse square root
  of `B` is a bound on `X` itself, in any C⋆-algebra.  This is the step that turns a bound on
  a potential into a bound on the matrix, or the operator, that it measures.
* `BasicResults.IntegralQuadraticForm`: the bridge to measure theory.  The average of a
  quadratic form along a square-integrable family is the trace against its Gram matrix.
* `BasicResults.CompactConvexHull`: in finite dimension the convex hull of a compact set is
  compact, by Carathéodory's theorem.
* `BasicResults.Matrix.LoewnerOrder`: comparisons with multiples of the identity.  A Hermitian
  matrix is below `c • 1` once `c` bounds its eigenvalues, a positive semidefinite matrix is
  below `(Re Tr A) • 1`, the inverse is antitone, and `A - δ • 1` stays positive definite for
  `δ` below the reciprocal of `Re Tr A⁻¹`.  It also holds the resolvent identity for the two
  shifts `A ↦ A - δ • 1` and `B ↦ B + ζ • J` of the construction.
* `BasicResults.Matrix.TraceInequalities`: the trace of a product of positive semidefinite
  matrices is nonnegative (positive for positive definite ones), the trace of a product of
  Hermitian matrices is real, and Cauchy–Schwarz for the semi-inner product
  `⟪P, Q⟫ = Tr (Q * Y * Pᴴ)`.
* `BasicResults.Matrix.PotentialBounds`: a positive definite `B` dominates `Ψ(B)⁻¹ • J`, where
  `Ψ(B) = Re Tr (J B⁻¹)`.  This is the step that makes the upper frame bound depend on the
  effective dimension only.
* `BasicResults.Matrix.ShermanMorrison`: the inverse, the trace of the inverse, and positive
  definiteness under a rank-one update `A ↦ A ± w a a*`.
* `BasicResults.Matrix.QuadraticForm`: the dictionary between matrices and functions.  The
  quadratic form of `∑ wᵢ a(xᵢ) a(xᵢ)*` at a coefficient vector is `∑ wᵢ |f(xᵢ)|²`, and the
  quadratic form is monotone for the Loewner order.
* `BasicResults.Matrix.RankOneDeterminant`: the **matrix determinant lemma**, the exact value of
  `det (β A + α u u*)`, which is affine in `α` because `u u*` has rank one, and the crude
  bound `|det A| ≤ n! Cⁿ` by the size of the entries.
* `BasicResults.Operator.Trace`: the trace of an operator along a Hilbert basis, for the
  passage to a second family in a Hilbert space.  For a positive operator
  `Re ⟪x, T x⟫ = ‖√T x‖²`, so the trace is a squared Hilbert–Schmidt norm, it does not depend
  on the basis, and the crude bound `T ≤ Tr(T) • 1` holds.  The basis-free trace
  `ContinuousLinearMap.trace` is computed along a basis chosen once; a space with a countable
  Hilbert basis is separable, `HilbertBasis.separableSpace`.
* `BasicResults.Operator.ShermanMorrison`: rank-one updates of an operator, with the
  Sherman–Morrison formula for `Ring.inverse` and the preservation of strict positivity.  The
  last section is the operator counterpart of the order facts above, for the shift
  `B ↦ B + ζ • J`.
* `BasicResults.Operator.QuadraticForm`: the average of a quadratic form along a
  square-integrable family is a trace against the Gram operator.
* `BasicResults.Operator.GramOperator`: the Gram operator `∫ b(x) b(x)* dμ(x)` of a
  square-integrable map as a Bochner integral, its quadratic form, and the readings of
  `J ≤ Λ • 1` as a Bessel-type bound and of injectivity as nondegeneracy of `b`.
-/
