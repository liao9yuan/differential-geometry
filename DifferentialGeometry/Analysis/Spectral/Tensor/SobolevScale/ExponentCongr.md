# ExponentCongr

## Role

Transport of the spectral Sobolev scale `tensorHs g r s σ` along an equality
of exponents, with its compatibility with the scale inclusions.

## Why it exists

`tensorHs` is indexed by a **real** exponent. Arithmetically equal exponents
therefore give equal but not definitionally equal spaces: `(2 : ℝ) + 2` and
`(4 : ℝ)` are the same real number, but `Real` addition does not reduce, so
`tensorHs g r s ((2 : ℝ) + 2)` and `tensorHs g r s (4 : ℝ)` are not
interchangeable by `rfl`, and unification cannot solve `?a + 2 =?= 4`.

This bites as soon as a family produced at a literal order has to feed a
consumer whose orders are written arithmetically in a scale parameter. The
concrete instance that motivated the file: the low-regularity Ricci--DeTurck
coefficient families are at literal orders (`lowA2Hi : H4 →L H2`,
`lowA1Hi : H3 →L H2`, `lowA2Lo : H3 →L H1`, `lowA1Lo : H2 →L H1`,
`lowRegA2Time : H4 →L H2`), while `nonautL2_lift` demands `H^{a+2} →L H^a` and
`H^{a+1} →L H^a` with `H^{a-1}` on the low side.

`orderOneH2Iso` (`ShortTime/LowRegPrincipalTime.lean`) was the one-off version
of this for `(1 : ℝ) + 1 = 2`; `tensorHsCongr` is the general form and should
be preferred for any new instance.

## Contents

`tensorHsCongr` (isometric equivalence), `tensorHsCongrL` (its continuous
linear map form), reduction at `rfl`, norm preservation, and the naturality
`tensorHsCongr_incl` / `tensorHsCongrL_incl` against `tensorHsInclusion` in
pointwise and composed form, plus `opNorm_comp_congr_le` for moving a uniform
operator bound across a transport.

## Placement

The canonical home for this concept is beside `tensorHsInclusion`, i.e.
`SobolevScale/Inclusion.lean`. It was put in a **new sibling file** instead
purely to keep the blast radius at zero: `Inclusion.lean` sits under
essentially the whole `Analysis/Spectral` tree, and editing it would invalidate
thousands of downstream modules while other lanes are building. Folding this
file back into `Inclusion.lean` is a safe cleanup whenever a broad rebuild is
happening anyway; the namespace is already the right one
(`DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation`), so the merge is
a pure move.

## Lessons

Every statement here is definitional after `cases` on the exponent equality,
because the transport is `LinearIsometryEquiv.refl` at `rfl`. Use `cases`, not
`subst`: the equality proof occurs inside the goal (as the argument of
`tensorHsCongr`), and `cases` abstracts both the variable and the proof, so the
goal closes by `rfl`.

## Verification

Focused verification passed, and a targeted module build passed. All
declarations are axiom-clean.

## Addendum 2026-07-30: `norm_congr_comp`

Added the codomain-side companion of `opNorm_comp_congr_le`:
`‖(tensorHsCongrL g r s h).comp L‖ = ‖L‖`, proved by `cases h` then
`tensorHsCongrL_refl` / `ContinuousLinearMap.id_comp`.

Motivation: `PrincipalLowRegPair` states the low principal arm at
`rank2H1 g = tensorHs g 0 2 ((1 : ℕ) : ℝ)`, while `lowA2Lo` and
`lowreg_lift_two` live at `(1 : ℝ)`, and `((1 : ℕ) : ℝ) = (1 : ℝ)` is **not**
`rfl` (checked).  So the low family must be post-composed with a transport, and
its uniform bound has to survive that.  The domain-side lemma did not apply.
