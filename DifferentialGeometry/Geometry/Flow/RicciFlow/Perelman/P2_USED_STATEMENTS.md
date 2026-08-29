# P2 used-statement crosswalk

This table freezes the reduced-geometry statements actually used by the current
Poincare program.  Morgan--Tian remains the authority for the project consumers;
the reduced-geometry chapter of the read-only `book12.tex` supplies corrected
quantifiers and smooth-to-surgery interface shape.  Book semantic identifiers
are not Lean declaration names.

Status words have their literal meanings:

- **checked**: the native declaration is proved and its current status note
  records focused verification;
- **conditional**: checked machinery exists, but the exact consumer theorem is
  not yet stated and proved;
- **missing**: a genuine producer is absent;
- **blocked**: the statement cannot be expressed honestly before another phase
  supplies its data model.

## Compact ordinary-flow consumers (P2a, closed)

| Source use | Native declaration | Exact role | Status |
|---|---|---|---|
| `newcomp2` theorem `n/2`, used in `noncoll` | `exists_redLen_le` | Complete terminal metric, regular slab, uniform curvature, and `tau < sigma` give the reduced-length fence used by smooth noncollapsing. | checked |
| `newcomp2` `lipcomplete`, used for the full-measure exponential image | `lExp_inj_ae`; `lCost_chart_lip` | Almost-everywhere injectivity is the exact change-of-variables consumer; fixed-time chart Lipschitz regularity supplies its local regularity layer. | checked |
| `newcomp2` `4pi` monotonicity and small-time normalization | `redVolume_anti`; `redVolume_le_one`; `redVolume_zero_lim` | Native normalization is Euclidean mass `1`, rather than Morgan--Tian's unnormalized `(4*pi)^(n/2)`. | checked |
| Smooth compact noncollapsing capstone | `redVolume_ball_unif`; `smooth_nlc` | Uniform reduced-volume ball bound and compact ordinary-flow no-local-collapsing endpoint. | checked |

The direct P2 audit currently records only `propext`, `Classical.choice`, and
`Quot.sound` for these public endpoints.  P2a is not reopened by the book's
alternative upper-support/distributional monotonicity proof.

## Complete bounded-curvature producers (P2b, active)

| Source/book node | Native coverage | Exact gap | Status / phase boundary |
|---|---|---|---|
| Complete Shi tower used by future compactness | `estimate_barrier_at` plus the solution-level `towerNorm_grad_le` and `shiBarrierCutoff_of_sol`; actual consumers already assemble this route in `Compactness/Shi/Local.lean` | `BernsteinTower.estimate_complete` is over-general: it supplies neither `TowerNormGradUpTo` nor a generic cutoff producer. Its sole caller is an unused private wrapper. | statement/API blocker; theorem endpoint 0%, dedicated machinery about 90--95% |
| Arbitrary regular pole and same-clock segment action (`def:red-clocked-action`) | `lDensity S T gamma`; `lLength S T gamma a b` | The raw action already supports arbitrary `T` and arbitrary oriented intervals. The pole-only real-valued `lCost` is not the book's restricted extended-real segment value. | raw action checked; segment value missing |
| Fixed-curve pointed action convergence (`prop:red-action-convergence`, item 1) | Same-flow engines `lAction_chart_lim`, `lAction_h1_lim`, and `lAction_liminf`; `lVelocity_src_map` and `lKinetic_src_pull` now give the pointed source-map velocity/kinetic identity. | `SmoothCGHConverges` still exposes only pointwise scalar convergence and does not package compact-uniform control of the reference speed, so the cross-flow action theorem is not yet honest. | local identities axiom-clean; action theorem missing |
| Transported competitors and confined minimizers (`prop:red-action-convergence`, items 2--3) | Chart splicing, compact-category lower semicontinuity, and minimizer machinery exist for one flow | Cross-flow limsup and full convergence require the fixed-curve producer plus explicit common confinement. | conditional on fixed-curve convergence and domain confinement |
| Reduced-density convergence and total masses (`prop:red-action-convergence`, item 4) | Pointed smooth convergence exists generically | Local density-measure convergence must remain separate from total mass convergence; full mass needs chart tightness and compact ball capture. | missing producer |
| Changing distance (`lem:red-changing-distance`) | `dist_short_support` constructs the fixed-endpoint short-distance differentiable upper support from `minJoin`, endpoint-ball Ricci control, and `pathLength_timeDeriv_of_ricciFlow`. | The long-distance sharp bound still needs the endpoint-ramp index estimate; moving endpoints separately need a variable-endpoint metric-speed/triangle-chain producer. | short endpoint axiom-clean; full theorem remains missing |
| Two-point coercivity (`lem:red-two-point`) | Prefix minimization is available | Missing ancient-flow/Harnack estimate `ell(q1)+ell(q2) >= c*d(q1,q2)^2/tau-1`; it depends on the changing-distance producer and ancient reduced-distance inputs. | missing mathematical producer |
| Moving-center Gaussian tightness (`lem:red-blowdown-Gaussian-tail`) | `lSrcGauss_tail` and `lRedJac_tail_lim` concern terminal tangent-source/Jacobian tails only | They do not imply spacetime density tails about moving reduced-length centers. | missing producer |
| No mass loss (`thm:red-no-mass-loss`) | Generic pointed compactness exists | Needs local density convergence, compact ball capture, and the moving-center Gaussian tail before full reduced-volume convergence can be proved. | missing producer; required by P3 |

## RFWS-independent smooth interfaces (P2c, active)

| Book node | Native coverage | Exact next interface | Status |
|---|---|---|---|
| Same-clock additivity / dynamic programming (`prop:red-dynamic-programming`) | `lLength_add_adj`, `lRegAction_add`, `lRegAction_sum`, and `lReg_prefix_min` | Piecewise concatenation is a thin adapter. The infimum identity is genuinely missing until an arbitrary segment-value API exists. | one-curve additivity checked; DPP missing |
| Domain calculus (`prop:red-domain-calculus`) | No restricted competitor-domain value; `lRegDomain` is an ODE domain and must not be reused for this meaning | Restriction monotonicity, strict leaving-curve gap, and compact-graph exhaustion for the eventual segment-value API. | missing producer |
| Fixed diffeomorphism covariance (`prop:red-covariance`) | Regularized ODE/L-exponential naturality plus `lDensity_pull` and `lLength_pull` in `Naturality.lean` | These checked fixed-diffeomorphism identities do not claim open-embedding locality or time-dependent covariance. | axiom-clean |
| Crossing cost (`lem:red-crossing-cost`) | `lLength_cross` proves the sharp curve-level lower bound from scalar and reference-metric coercivity plus a lower bound on reference arc length. | Endpoint-set distance discharges the final arc-length hypothesis in consumers; no surgery specialization is stated here. | axiom-clean |

## Phase boundaries

- Reduced-volume equality rigidity and the asymptotic-shrinker theorem are P3
  endpoints.  The shrinker theorem remains unstated and 0%; P2 supplies only
  coercivity, tightness, no-mass-loss, and pointed-stability producers.
- Surviving points/worldlines, pre/post surgery maps, across-event admissible
  curves, jump errors, seam additivity, and eventwise noncollapsing are blocked
  by the absent reviewed P6b event/seam/RFWS presentation.  P2 must not package
  them as assumptions or invent a parallel generalized-flow object.

## Current execution order

1. Preserve the exact `estimate_complete` blocker without moving it into a new
   assumption wrapper; decide its public-signature cleanup only with explicit
   design authority.
2. Prove the fixed-curve cross-flow action-convergence producer under explicit
   smooth pointed/confinement hypotheses.
3. Close the smallest checked P2c adapters (`lDensity_pull`, `lLength_pull`) and
   the smooth crossing-cost theorem.
4. Use those producers to expose only the next exact missing consumer, keeping
   P3 and P6b endpoints out of the P2 completion count.
