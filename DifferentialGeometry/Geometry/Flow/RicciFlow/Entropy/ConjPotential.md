# Conjugate-heat potential

## Goal

Realize the lower-order term in the forward time-reversed conjugate heat
equation as the genuine family

`A1(s) = multiplication by -R(T-s) : H¹(gT) →L H⁰(gT)`.

There is no drift term and no moving-measure conjugation in this fixed-reference
formulation.  The connection-difference times gradient contribution already
belongs to the completed moving-Laplacian operator `A2`.

## Route

`conjCoeff` bundles the fixed-time smooth scalar coefficient `-R(t)`.
`conjA1` applies the fixed-metric multiplier `scalarPotH0`.  Operator-norm
continuity follows from `scalar_unif` and the pointwise pairwise multiplier
bound.  Compactness bounds the terminal scalar curvature, while the same
uniform time modulus gives a short-interval bound for every reflected slice.

`conjCoeff_joint` now reduces joint smoothness of the coefficient directly to
the geometric producer `scalar_joint`.  That producer uses actual local
coordinate-frame domains and the Ricci-flow identity
`Ric = -1/2 * ∂ₜ g`; it does not add a global chart selector or a
consumer-side smoothness assumption.

`conjCoeff_rev` is the orientation adapter used by the forward reversed-time
problem.  It composes `conjCoeff_joint` with the smooth map
`(x, s) ↦ (T - s, x)` and restricts exactly to reflected regular times.  It
adds no assumptions or independent regularity package.

## Verification status

The previously existing operator results passed focused verification and their
targeted module build.  Final focused verification of the newly added
`conjCoeff_joint` is pending because concurrent dependency builds are currently
making imported `.olean` files disappear and reappear.  No local theorem error
has been exposed.

## Progress accounting

- A2 short-time measurable input: complete (100%).
- A1 operator and `conjA1_short`: complete (100%).
- `conjCoeff_joint`: theorem body present; count as 0% verified until its focused
  check is green.  Its dedicated geometric producer machinery is about 95%.
- `conjCoeff_rev`: theorem body present; count as 0% verified until the same
  focused check is green.
- The next independent A1 regularity frontier is the uniform scalar-multiplier
  jet estimate; joint coefficient smoothness alone does not prove it.
- The separate genuine A2/A1 input producers and their dedicated machinery:
  complete (100%); `ConjStrong.conj_strong_exists` now completes their
  specialized spectral strong-solution assembly (100%).
- Classical moving-metric conjugate-heat existence theorem: not proved (0%);
  its dedicated analytic machinery is about 70%.  The next exact producer is
  the strong-to-classical bridge `heatpot_of_maxreg` (theorem 0%).
- Perelman no-local-collapsing theorem: not proved (0%).
