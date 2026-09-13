# Candidates for Mathlib

`BasicResults` is general matrix analysis and operator theory that Mathlib lacks,
kept here only because the discretization argument needs it. Everything is stated
over a general `RCLike` field wherever the C⋆-algebra structure is not needed.
Grouped by topic, with the main declarations:

* **Traces of products of positive matrices** (`BasicResults/TraceInequalities.lean`):
  the trace of a product of positive semidefinite matrices is nonnegative
  (`Matrix.PosSemidef.trace_mul_nonneg`) and positive when one factor is positive
  definite and the other nonzero (`Matrix.PosDef.re_trace_mul_pos`); Cauchy–Schwarz
  for the trace semi-inner product (`Matrix.PosSemidef.norm_trace_mul_sq_le`,
  `.re_trace_mul_sq_le`), whose underlying inner product Mathlib constructs but keeps
  `private`; and the real-valuedness of the trace of a Hermitian matrix and of a
  nonnegative scalar (`Matrix.IsHermitian.ofReal_re_trace`, `.ofReal_re_trace_mul`,
  `RCLike.ofReal_re_of_nonneg`).
* **The Loewner order against multiples of the identity**
  (`BasicResults/LoewnerOrder.lean`): `A ≼ (Tr A) • 1` for `A ≽ 0`
  (`Matrix.PosSemidef.le_trace_smul_one`), the same from a bound on the eigenvalues
  (`Matrix.IsHermitian.le_smul_one`), antitonicity of the inverse packaged for
  matrices (`Matrix.PosDef.inv_le_inv_of_le`), and conjugation by a Hermitian matrix
  (`Matrix.PosSemidef.mul_mul_same_of_isHermitian`,
  `Matrix.PosDef.mul_mul_same_of_isHermitian`) — the form of
  `Matrix.PosSemidef.conjTranspose_mul_mul_same` that arises in practice.
* **Conjugation by a square root** (`BasicResults/SqrtConjugation.lean`): in a
  C⋆-algebra, a bound on the conjugate of `X` by the inverse square root of `B` is a
  bound on `X` itself (`CStarAlgebra.inv_smul_le_of_conj_inv_sqrt_le`).
* **Sherman–Morrison** (`BasicResults/ShermanMorrison.lean`,
  `BasicResults/OperatorShermanMorrison.lean`): the inverse and the trace of a
  rank-one update written with `Matrix.vecMulVec` (`Matrix.inv_add_smul_vecMulVec`,
  `Matrix.trace_inv_add_smul_vecMulVec`, and the real-weight forms
  `Matrix.PosDef.inv_add_smul_vecMulVec`, `.inv_sub_smul_vecMulVec`), where Mathlib
  has only the block form `Matrix.add_mul_mul_inv_eq_sub`; the same for operators
  (`ContinuousLinearMap.inverse_add_smul_rankOne`), which Mathlib has in no form; and
  `Ring.inverse_eq_of_mul_eq_one`, the converse of the two cancellation laws.
* **The trace of an operator** (`BasicResults/OperatorTrace.lean`): Mathlib has no
  trace outside finite dimension. `ContinuousLinearMap.traceAlong` defines it along a
  fixed Hilbert basis, and the invariance of the Hilbert–Schmidt sum under adjoints
  (`.tsum_norm_sq_adjoint`), the cyclicity `∑ₖ ⟪S eₖ, T eₖ⟫ = ∑ₖ ⟪T* eₖ, S* eₖ⟫`
  (`.tsum_inner_apply_comm`) and the bound `T ≼ Tr(T) • 1`
  (`.le_traceAlong_smul_one`) are general facts.
* **Averages of quadratic forms** (`BasicResults/IntegralQuadraticForm.lean`,
  `BasicResults/OperatorQuadraticForm.lean`): the average of a quadratic form along a
  square-integrable family is a trace against its Gram matrix
  (`Discretization.integral_quadForm`), and against its Gram operator in infinite
  dimension (`ContinuousLinearMap.integral_re_inner_apply`).
* **Rank-one updates of a determinant** (`BasicResults/RankOneDeterminant.lean`): the
  matrix determinant lemma in terms of `Matrix.vecMulVec`
  (`Matrix.det_add_vecMulVec`), where Mathlib has it only for a product of a column
  and a row (`Matrix.det_add_replicateCol_mul_replicateRow`); the exact value of
  `det (β A + α u u*)`, affine in `α` because `u u*` has rank one
  (`Matrix.det_smul_add_smul_vecMulVec`, with the real form
  `Matrix.PosDef.re_det_smul_add_smul_vecMulVec`); and the Leibniz bound
  `|det A| ≤ n! Cⁿ` by the size of the entries
  (`Matrix.norm_det_le_of_norm_apply_le`).
* **The convex hull of a compact set is compact**
  (`BasicResults/CompactConvexHull.lean`): in finite dimension the hull of a compact
  set is compact (`IsCompact.convexHull`). Mathlib has the finite-set case
  (`Set.Finite.isCompact_convexHull`) and `TotallyBounded.convexHull`, which gives
  compactness only of the closure. The proof needs no norm, only continuity of the
  vector space operations, which is what lets it apply to spaces such as
  `Matrix ι ι ℂ`, whose norms are all scoped.
* **Quadratic forms and sums of squares** (`BasicResults/QuadraticForm.lean`): the
  quadratic form of a weighted sum of rank-one matrices is the corresponding weighted
  sum of squared moduli (`Discretization.re_dotProduct_sum_mulVec`), and the quadratic
  form is monotone for the Loewner order (`Discretization.re_quadForm_le_of_le`).
