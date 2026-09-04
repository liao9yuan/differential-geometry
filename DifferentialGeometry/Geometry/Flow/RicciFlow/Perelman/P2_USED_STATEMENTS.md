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
| Complete Shi tower used by future compactness | `movingShi_complete` is the actual solution endpoint; it assembles `estimate_barrier_at`, `towerNorm_grad_le`, and `shiBarrierCutoff_of_sol` through `complete_of_barrier` in `Compactness/Shi/Local.lean`. | The former arbitrary-`MetricConnectionFamily` interface supplied neither `TowerNormGradUpTo` nor a cutoff producer and had no live caller; it and its dead private wrapper were removed. | actual solution endpoint 100%; focused regression and direct axiom audit green |
| Arbitrary regular pole and same-clock segment action (`def:red-clocked-action`) | `lDensity S T gamma`; `lLength S T gamma a b`; `lSegValue S T Ω a b x y` | The raw action supports arbitrary `T` and oriented intervals. The restricted extended-real value now gives `⊤` to an empty competitor class and is the native same-clock value used by domain calculus and DPP. | raw action and restricted value checked |
| Fixed-curve pointed action convergence (`prop:red-action-convergence`, item 1) | `ConvOut.kinetic_convOn`, `lKinetic_map`, `ConvOut.mapKin_convOn`, and `lDensity_aemeas` supply the kinetic, transport, confinement, and measurability layer; `ConvOut.scalar_convOn` supplies scalar convergence; `lLength_conv_curve` assembles the checked fixed `C¹` curve L-length limit. | The theorem deliberately fixes one `C¹` curve.  Full finite-energy AC/H¹ competitors and varying minimizers/reduced distances require additional compactness and lower-semicontinuity producers. | fixed `C¹` curve endpoint checked; stronger items 2--3 conditional |
| Transported competitors and confined minimizers (`prop:red-action-convergence`, items 2--3) | `lSegChartH1_fin` realizes raw finite-action segments in finitely many chart-H1 pieces, and `lSegValue_eq_reg` identifies their infimum with the global `C1` regularized cost. `lSegValue_limsup` gives the transported fixed-competitor limsup; `lEnergy_cpt_subseq`/`lEnergy_cpt_fix` give confined curve compactness; `lRegAction_pt_lsc` gives the varying-action liminf; and `lSegValue_pt_lim` assembles exact restricted-value convergence from explicit source/limit attainers and common chart-H1 confinement. | Geometric equicoercive confinement and existence of compatible exact attainers remain external inputs; the checked theorem does not assume its own action comparison. | raw/C1 infimum equality and explicit-confinement restricted-value convergence checked; geometric ancient-flow production conditional |
| Reduced-density convergence and total masses (`prop:red-action-convergence`, item 4) | `redDensity_pt_lim` gives pointwise convergence; `redDensity_cpt_lim` integrates it with the converging chart-volume factor on a compact common coordinate set; `paramDens_src_eq` and `redDensity_src_lim` change variables to the actual term-manifold source images. `redDensity_wgt_lim` proves weighted compact-chart convergence, `redDensity_src_wgt` carries the weight through the actual term/limit parametrizations, and `redDensity_cc_lim` uses `lint_map_fin_loc` plus the canonical finite POU to prove signed `C_c` convergence for the raw transported measures on one fixed limit space. `tailBall_capture` and `canon_ball_capture` recover the finite-stage reverse-ball provenance; `map_inv_tail_le`, `redDensityTermMeas`, and `redSrc_tail_le` turn it into fixed-space compact-complement control. `mass_tendsto_of_cc` is the checked generic assembly from compactly supported test convergence plus a common compact tail bound. | A `FiniteMeasure` wrapper belongs only after tail finiteness. Reverse canonical ball capture and fixed-space tail transport are closed; the uniform moving-center quadratic coercivity and common tail constants remain P3. | fixed-space `C_c` convergence and reverse-tail transport checked; geometric no-mass-loss theorem missing |
| Changing distance (`lem:red-changing-distance`) | `dist_short_support` and `dist_long_support` give the fixed-endpoint supports; `edist_inc_tendsto` is the sharp fixed-metric differentiable endpoint rate; `edist_smooth_rate` controls a locally `C¹` endpoint for the varying backward metric; `dist_short_slope` and `dist_long_slope` assemble the book12 pointwise smooth moving-endpoint bounds.  `edist_curve_lip` and `edistEquiv_Icc` combine in `dist_lip_Icc`, while `dist_ac_Icc` supplies compact-interval moving-distance absolute continuity under a global absolute Ricci bound.  `dist_ac_rm` is the checked complete bounded-curvature specialization, using the native `Rm`-to-Ricci quadratic estimate.  `sub_le_integral_dini` and `sub_le_int_loc_dini` give the whole-interval and positive-time local-AC Dini integration steps. | The geometric AC producer and its complete bounded-curvature adapter are closed.  The later scale-invariant speed inequality consumes ancient Harnack/gradient inputs and belongs to P3. | pointwise smooth, compact-interval Lipschitz/AC, bounded-curvature adapter, and Dini-integration endpoints 100% |
| Two-point coercivity (`lem:red-two-point`) | `lExp_time_c1` and `lExp_c1On` supply the endpoint regularity consumed by moving-distance support; `lMinSpeed_eq` is the exact minimizing-ray speed/reduced-length/scalar/`K` identity; `lMinPrefix_le` gives the book's prefix reduced-length estimate from scalar nonnegativity on only the intervening segment.  The complete pointwise smooth short/long changing-distance chain, compact-interval moving-distance AC, and generic Dini integration are checked. | The scale-invariant speed inequality genuinely requires the ancient Hamilton--Harnack lower bound for `K`, while the endpoint-ball Ricci input requires the ancient gradient estimate and nonnegative curvature operator.  Those are P3 producers and must not be replaced by P2 assumptions. | native kinematic/action/prefix/Dini/AC substitution 100%; ancient Harnack producers missing; final coercivity theorem 0% |
| Moving-center Gaussian tightness (`lem:red-blowdown-Gaussian-tail`) | `redDensity_gauss` is the checked pointwise adapter from a quadratic `redLength` lower bound. `gauss_tail_of_ball` and `gaussTail_zero` provide the explicit shell tail and its vanishing. `riem_gauss_tail` supplies the complete nonnegative-Ricci slice estimate, and `redDensity_tail_le` now assembles the actual reduced-density exterior-mass bound with the exact Perelman normalization. | The geometric consumer still needs P3 two-point coercivity to produce common quadratic constants for the moving centers and to pass that bound to the limit. | conditional reduced-density tail endpoint checked/refresh green; uniform moving-center theorem 0% |
| No mass loss (`thm:red-no-mass-loss`) | Generic pointed compactness, `redDensity_cc_lim`, `redDensity_tail_le`, `ball_subset_image`, `tailBall_capture`, `canon_ball_capture`, `map_inv_tail_le`, `redSrc_tail_le`, and `mass_tendsto_of_cc` provide the fixed-space compact-test, conditional-tail, reverse-capture, transported-tail, and abstract assembly layers. | The remaining geometric input is the P3 uniform moving-center coercivity/common-tail estimate. No P2 assumption wrapper is introduced. | P2-side compact-test/capture/transport producers checked; geometric endpoint missing and required by P3 |

## RFWS-independent smooth interfaces (P2c, active)

| Book node | Native coverage | Exact next interface | Status |
|---|---|---|---|
| Same-clock additivity / dynamic programming (`prop:red-dynamic-programming`) | `IsLSegCurve`, `lSegCurve_restrict`, `lSegCurve_join`, `lSegValue`, and `lSegValue_dpp` give the fixed-pole metric admissible category, extended-real restricted value, and exact infimum-over-midpoints law. | This is an infimum identity and deliberately does not assert minimizer existence. | restricted same-clock DPP checked |
| Domain calculus (`prop:red-domain-calculus`) | `lSegValue_mono` proves restriction monotonicity, `lSegValue_exhaust` proves compact-graph exhaustion including empty competitor classes, and `lSegValue_gap` converts an honest positive outside-action gap into value equality and strict epsilon-minimizer confinement. `lRegDomain` remains the unrelated ODE domain. | The three order-theoretic rules are closed. Producing a uniform positive gap from geometric separation is a separate analytic input and is not asserted here. | all three stated domain rules checked; geometric gap producer missing |
| Fixed diffeomorphism covariance (`prop:red-covariance`) | Regularized ODE/L-exponential naturality plus `lDensity_pull` and `lLength_pull` in `Naturality.lean`. `lLength_restrict` gives exact open-subflow locality for every raw subtype-valued curve. | No time-dependent covariance is claimed. | fixed-diffeomorphism endpoint axiom-clean; open locality warning-free focused green |
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

1. Preserve `movingShi_complete` as the canonical complete bounded-curvature
   solution endpoint and do not resurrect the removed under-specified generic
   interface or replace it with an assumption wrapper.
2. Preserve the checked `lLength_conv_curve` fixed `C¹` endpoint; do not
   advertise it as finite-energy competitor or varying-minimizer convergence.
3. Preserve the checked `redDensity_gauss` and `gauss_tail_of_ball` adapters.
   The geometric moving-center tail next requires two-point coercivity and the
   thin intrinsic Bishop ball-growth specialization.  Local measure
   convergence, reverse ball capture, and fixed-space tail transport are now
   checked independently.
4. Preserve the checked `lLength_restrict`, `lSegValue_dpp`,
   `lSegValue_mono`, `lSegValue_exhaust`, and `lSegValue_gap` interfaces.  The
   next high-leverage P2b chain is the two-point coercivity producer needed by
   moving-center tightness.  Its pointwise smooth short/long changing-distance
   input, fixed-ray compact-interval regularity, exact minimizing-speed
   identity, prefix estimate, generic Dini integration, and the complete
   bounded-curvature moving-distance AC adapter `dist_ac_rm` are checked.  The
   scale-invariant speed inequality beyond that consumes the ancient
   Hamilton--Harnack lower bound in P3; P2 must not restate it as an assumption
    wrapper.  The independent explicit-confinement target
    `lRegAction_pt_lsc` and its restricted-value consumer `lSegValue_pt_lim`
    are focused/refresh green and three-standard-axiom clean.  The fixed-space
    compact-test/capture chain now closes at `redSrc_tail_le`, through
    `tailBall_capture`, `canon_ball_capture`, and `map_inv_tail_le`.  Its next
    missing geometric input is P3 uniform moving-center coercivity, so no
    further P2 wrapper is scheduled.  Keep geometric confinement production and the
    genuinely geometric positive-gap producer, P3 endpoints, and P6b/RFWS data
    outside the order-theoretic layer.
