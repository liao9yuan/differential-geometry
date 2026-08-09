# BasisHaar.lean

## Purpose

This module records the determinant normalization relating the additive Haar
measures attached to two finite bases.  It also exposes the corresponding
nonnegative-integral identity, allowing a basis-change determinant in a
Jacobian density to cancel against the reference measure.

## Status

Focused verification passed without warnings.  Both public theorems are proved
without `sorry`.

The only elaboration seam was that `Basis.addHaar_eq_iff` requires a
`SigmaFinite` instance for the scaled measure.  Although the theorem is stated
with the natural `ENNReal.ofReal` scalar, the proof changes it definitionally to
the corresponding `NNReal` scalar; Mathlib then supplies the existing
sigma-finite scalar-measure instance.
