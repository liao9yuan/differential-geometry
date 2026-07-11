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

## Verification status

Focused verification and the targeted module build both pass.  The focused
check has no local warning or `sorry`; the targeted build reports only replayed
upstream warnings.

## Progress accounting

- A2 short-time measurable input: complete (100%).
- A1 operator and `conjA1_short`: complete (100%).
- The separate genuine A2/A1 input producers and their dedicated machinery:
  complete (100%); `ConjStrong.conj_strong_exists` now completes their
  specialized spectral strong-solution assembly (100%).
- Classical moving-metric conjugate-heat existence theorem: not proved (0%);
  its dedicated analytic machinery is about 70%.  The next exact producer is
  the strong-to-classical bridge `heatpot_of_maxreg` (theorem 0%).
- Perelman no-local-collapsing theorem: not proved (0%).
