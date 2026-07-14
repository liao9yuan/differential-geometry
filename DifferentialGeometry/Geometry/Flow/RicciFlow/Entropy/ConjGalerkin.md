# Finite scalar Galerkin solutions

## 2026-07-14 source implementation

`ConjGalerkin.lean` defines the finite scalar spectral vector, the coordinate
embedding/restriction maps, the frozen diagonal heat operator, and the genuine
time-dependent perturbation

`lapDiffA20 + conjA1 ∘ (H² → H¹)`.

`scalarGalVec_supp` and `scalarGalVec_finite` expose the exact finite-support
facts needed by the later critical-energy consumer; no support witness is
added as a theorem hypothesis.  `scalarGalVec_inc` records that cross-scale
inclusion leaves those finite coordinates unchanged, while
`scalarGalRepr_eq` records that their genuine smooth representative is
independent of the Sobolev exponent used to package them.

The source proof of `scalar_gal_exists` applies the generic global
finite-dimensional ODE theorem on one short interval independent of the finite
spectral set.  The returned coefficient family is continuous on that interval,
solves the projected reversed conjugate-heat system, agrees with the initial
spectral coordinates on the chosen set, and is definitionally zero outside it.

Verification is pending because shared Lean writers were active while this
source pass was made.  No new consumer assumption, chart-selection hypothesis,
or frontier wrapper was introduced.

The next required coefficient bridge is now source-written as
`scalarGalPert_fin`.  It stays in the fully applied scalar normal form and uses
`lapDiffA20_core` plus `lapDiffCore_eq_cc` for A2, and
`scalarPotH0_apply` plus `scalarPotOp_core` for A1.  Its output is exactly the
`tensorL2Coeff` of the smooth sum consumed by `scalar_crit_tame`; it does not
assert equality of whole time-dependent operators.

After this bridge verifies, the next theorem is `scalar_gal_bound`: combine
`scalar_gal_exists`, `scalar_crit_tame`, and the generic
`galerkin_energy_uniform_bound_perScale` for an arbitrary sequence of finite
mode sets.  Scalar exhaustion/projection remains a later limit-layer API;
existing `eigenIdxFinset` and `TimeL2EigenProjection` are specialized to rank
`(0,2)` and cannot honestly be reused for `(0,0)`.

Honest accounting: `scalar_gal_exists` and `scalarGalPert_fin` are
source-written but theorem-level 0% until focused verification; their dedicated
source machinery is about 94%.
The scalar critical-tame theorem remains theorem-level 0% pending verification,
and the Galerkin-to-limit/second-order bootstrap remains 0%.  Perelman
no-local-collapsing and `ham3_noncollapse` remain endpoint-level 0%, with about
42% dedicated analytic machinery.  Whole HCG machinery remains about 54%, with
its endpoint theorems at 0%.
