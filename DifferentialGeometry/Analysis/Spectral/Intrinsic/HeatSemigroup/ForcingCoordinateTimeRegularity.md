# ForcingCoordinateTimeRegularity.lean — notes

Created 2026-08-03 during bricks F2–F5 of `ShortTime/FORCEJETMASS_PLAN.md`.
This note records only what that pass touched and learned; it is not a full audit
of the 1300-line file.

## Status

`sorry`-free.  The two POSITs advertised in the file header as "Honest `sorry`"
(**(A)** `deTurckForcing_solCoeff_jetSpectralMass`, **(B)**
`deTurckSobolevNHa2_jetSpectralMass_preserving`) were discharged long ago (commits
`358687842`, `b369c07f0`, `272498f86`).  The header prose was stale and is fixed as
part of this pass (docstring-only; risk 7.6 of `FORCEJETMASS_PLAN.md`).

## Structure worth knowing

The file carries **two parallel towers** over `ForcingFiniteOrderTimeRegularity.lean`:

* the *raw* tower on `deTurckSobolevNHa2` (imported, not defined here);
* the *symmetrized* tower `*Symm`, defined inside
  `section SymmSCoefficientBlockTransfer`, which pre-composes with `symmS`.

The Symm tower is the one downstream Ricci–DeTurck consumers want, because the
geometric nonlinearity is the *symmetrized* smooth remainder.  Its extra content is
one idea: the slot symmetrizer mixes eigen-coordinates only **within an eigenvalue
block** (`eigenBlockFinset`), so its action on a coordinate family is a finite
per-block linear combination (`symmCoeffPath`) with `∑ⱼ (swapEigenCoeff i j)² ≤ 1`.
Time regularity is therefore preserved verbatim, and spectral mass is preserved at
the price of one Weyl-shifted input order (Cauchy–Schwarz over the block).

## Promotions made (2026-08-03)

`private` removed from five declarations, names and namespaces unchanged, docstrings
added.  All five are consumed by the `a = 2` lane in
`ShortTime/LowRegAllOrderJet.lean`:

| name | what it gives |
|---|---|
| `exists_smoothCcPath_realizing_coeff` | all-order spatial mass on `Icc 0 d₂` ⟹ a `SmoothCcTensor` realizing the coordinates at each time of the slab (the (S2) step) |
| `symmCoeffPath` | the eigen-coordinate family of the symmetrized path |
| `symmCoeffPath_contDiff` | it inherits `C^n` from the input family |
| `symmCoeffPath_realizes` | it really is the coordinate family of `symmS g₀ X` |
| `symmCoeffPath_spectralMass` | `τ`-mass + `(τ + weylSobolevExp + 1)`-mass of the input ⟹ `τ`-mass of the output |

The supporting `private` lemmas (`eigenBlockFinset`, `swapEigenCoeff`,
`mem_eigenBlockFinset`, `sum_sq_swapEigenCoeff_le_one`,
`tensorSobolevWeight_eq_of_block`, `iteratedDeriv_symmCoeffPath`,
`tensorL2Coeff_toL2_symmS_eq_blockSum`, …) stay `private`: nothing outside the file
needs to unfold `symmCoeffPath`, and keeping them private keeps the public surface
to the five statements above.

A public `def` may refer to `private` constants in its body; Lean 4 raises no
complaint, and downstream files simply cannot `unfold` it.  That is the desired
behaviour here.

Not promoted: `exists_smoothCcTensor_of_allOrder_spectralMass_local`
(`ForcingFiniteOrderTimeRegularity.lean`) — the *pointwise* twin of
`exists_smoothCcPath_realizing_coeff`.  `FORCEJETMASS_PLAN.md` §7.5 asked for that
one, but the path form is what consumers need and it lives here, next to the
`symmS` transport that had to be promoted regardless; promoting it alone touches one
file instead of two.  The third copy at `DeTurckRemainderPathTimeJet.lean:38` was
left untouched.

## Templates this file provides for other Sobolev orders

Three bodies were transplanted verbatim (modulo the completed-operator step) into
the `a = 2` lane:

* `deTurckSobolevNHa2Symm_finiteOrder_jetSpectralMass_preserving` — one rung;
* `deTurckForcing_finiteOrderSmoothDriverSymm` — the induction on `k`;
* `maxRegForcing_smoothTimeJetDriver_of_galerkinSpatialMassSymm` — the a.e.-agreement
  diagonal (`Measure.eqOn_of_ae_eq` ⟹ `ContDiffOn ℝ ∞` ⟹
  `contDiffOn_Icc_scalar_globalExtend`, with `iteratedDerivWithin_congr` to move the
  jets between rungs).

The only step that does **not** transplant below `2·finrank ℝ E + 10 ≤ a` is the
identification of the completed Nemytskii with its smooth core on the realizability
ball (`deTurckSobolevNHa2_eq_smoothN`, via `deTurckSobolevNHa2_exists_of_super`).
Everything else is order-generic.  Consequently the two horizon shrinks
(`d` in `deTurckForcing_solCoeff_continuous_smallTimeBase`, `d₂` inside the rung)
exist *only* to enter that ball and can be dropped whenever the ball is available as
a hypothesis on the whole slab.

## Verification

Focused check after the promotions and the header prose fix: GREEN.  Targeted module
build: GREEN.  No statement content changed, so no downstream statement moved.
