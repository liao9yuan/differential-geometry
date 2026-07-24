# IndexFormNegativeSmooth

## 2026-07-23

Architecture ruling: use an explicit quantitative `H¹`-type smoothing in the
fixed Hilbert space of the abstract Jacobi ODE.  Do not add derivative
matching, global smoothness of the input half-fields, or abstract index-form
continuity assumptions.

The construction is complete.  Its first hard gate, `exists_deriv_bound`,
expands the derivative of the `CutoffProfile.value` splice.  Value matching at
the junction makes the `1 / δ` transition derivative multiply an `O(δ)` field
difference, so the resulting derivative bound is independent of `δ`.

The private `exists_splice_error` then splits the index form into left,
central, and right intervals.  The tails agree almost everywhere with the
input half-fields, and the three central terms have lengths `2 * δ`, `δ`, and
`δ`.  This gives an explicit `C * δ` error bound without an abstract
index-form continuity assumption.

The public theorem `exists_smooth_indexForm_neg_of_split` is proved.  It first
uses a compact plateau to extend each locally smooth half-field globally
without changing its value or derivative on `[0, 1]`, and then chooses `δ`
small enough that the smoothed field still has negative index.  Its statement
has no derivative-matching, `CompleteSpace`, self-adjointness, Jacobi, or
global input-smoothness hypothesis.

Focused verification and the targeted module build passed; the file is
warning-free and contains no `sorry`.

The umbrella import was added to `DifferentialGeometry.lean`.  Its focused
root check could not reach the new import because the unrelated
`Evolution/BBSLimitProducer.olean` artifact is currently absent.  A broad
refresh was not started while other shared lanes are active.

One reusable lesson is that the older `intInt_indexIntegrand` declaration
carries an unnecessary `CompleteSpace F` parameter from its source section.
This module avoids propagating that assumption by proving scalar integrability
directly from continuity of the index integrand.

This finishes the abstract fixed-Hilbert smoothing bridge, not the geometric
N-d endpoint.  The remaining frontier is to lift the smooth coefficient field
through the parallel orthonormal frame, prove perpendicularity and equality
with the geometric index form, and feed it to the minimizing-geodesic
nonnegativity theorem.
