# P2AxiomCheck

## Role

This diagnostic module imports the completed compact smooth-flow
noncollapsing chain together with the checked P2b/P2c producer interfaces and
asks Lean for the axioms of their public endpoints. It is not part of the
L-geometry umbrella and introduces no declarations.

## Verification

The compact P2a audit is warning-free green. Every previously printed endpoint,
including `redVolume_ball_unif` and `smooth_nlc`, depends only on Lean's standard
logical axioms (`propext`, `Classical.choice`, and `Quot.sound`).

The audit now also covers raw same-clock concatenation, the fixed-
diffeomorphism action identities, the smooth crossing bound, the pointed
source-domain velocity/kinetic identities, abstract fixed-curve action
convergence, short changing-distance support, generic tightness-to-total-mass
convergence, compact two-jet scalar control, and compact-by-time scalar
convergence.  It now also covers fixed-curve compact-uniform kinetic
convergence, source-map kinetic identification, local density measurability,
transported kinetic convergence, and the assembled fixed `C¹` curve L-length
limit. The pointwise moving-center Gaussian density adapter and the same-clock
segment-action scalar lower bound are also included. The source audit now adds
the actual complete bounded-curvature solution endpoint `movingShi_complete`,
for 32 printed declarations. The expanded focused audit is warning-free green:
all 32 endpoints, including `movingShi_complete`, depend only on `propext`,
`Classical.choice`, and `Quot.sound`. The obsolete under-specified
`estimate_complete` interface has been removed rather than hidden behind a new
assumption. The diagnostic module itself exports no declarations and is not
named-refreshed.

The unified audit extends this list from 32 to 49 declarations: the exact
same-clock `lSegValue_dpp`, all three domain-calculus endpoints
(`lSegValue_mono`, `lSegValue_exhaust`, and `lSegValue_gap`), the generic
Gaussian-tail limit and ball-growth adapter, and the Riemannian ball-volume
specialization `riem_gauss_tail`.  It also includes the canonical fixed-path
Ricci-flow length derivative, the static endpoint-Ricci integral bound, the
checked long-distance upper support, and the complete eleven-item changing-
distance subchain through the final smooth short/long slopes.

The final 49-declaration focused audit is warning-free green.  Every printed
endpoint depends only on `propext`, `Classical.choice`, and `Quot.sound`.
The diagnostic module exports no declarations and is intentionally not named-
refreshed.

The audit was extended from 49 to 56 declarations.  In addition to the
positive-time fixed-ray regularity bridge `lExp_time_c1`, the exact minimizing-
ray Hamilton identity `lMinSpeed_eq`, and the scalar-nonnegative prefix
estimate `lMinPrefix_le`, it includes the compact-interval adapter `lExp_c1On`,
the two generic upper-Dini integration theorems, and the pointed confined
segment-value limsup `lSegValue_limsup`.  Every producer file is independently
warning-free focused green.  Direct audits of `lMinSpeed_eq`, `lExp_c1On`, the
two Dini theorems, and `lSegValue_limsup` report only the same three logical
axioms.

The previous unified audit contained 60 declarations.  The four added moving-
distance producers are `edist_curve_lip`, `edistEquiv_Icc`, `dist_lip_Icc`,
and `dist_ac_Icc`.  After exact-refreshing only their real producer modules and
the previously focused 56-item additions, the 60-item focused audit passed
warning-free.  Every printed declaration depends only on `propext`,
`Classical.choice`, and `Quot.sound`.  This is now the verified unified
baseline; the diagnostic module itself still exports no declarations and is
not named-refreshed.

The current unified audit contains 61 declarations.  The added
`dist_ac_rm` theorem specializes compact-interval moving-distance absolute
continuity to the complete bounded-curvature input by reusing the native
curvature-to-Ricci quadratic estimate.  Its producer file is warning-free
focused green and exact-refresh green.  The 61-item focused audit is warning-
free green, and every declaration still depends only on `propext`,
`Classical.choice`, and `Quot.sound`.

The unified audit now contains 70 declarations.  The nine additions cover the
compact-chart Gram difference estimate, the local chart-kinetic identities,
pointed Gram convergence and kinetic liminf, arbitrary-clock scalar
composition, the two compact-confined energy subsequence adapters, and the
actual pointed regularized-action lower-semicontinuity endpoint
`lRegAction_pt_lsc`.  The 70-item focused audit is warning-free green; every
printed declaration depends only on `propext`, `Classical.choice`, and
`Quot.sound`.

Reaching that final audit required repairing and exact-refreshing the genuine
`RiemannianTail` dependency cone: `JacobiField`, `RadialSurjectivity`,
`JacobiVariation`, `SegmentDomain`, `MinimalGeodesicNoConjugate`,
`SegmentDensity`, `SegmentPolar`, and the required Euclidean volume consumer.
`RiemannianTail` itself is warning-free focused green and exact-refresh green.
Two final stale-artifact conflicts were resolved narrowly by exact-refreshing
`Distance.RicciFlow` and `SegmentValue`; neither required a source theorem or
axiom change.

The separate focused `P2DistanceCheck` independently audits the complete
eleven-declaration distance subchain, including `edistOf_comm`,
`edist_inc_tendsto`, `edist_smooth_rate`, `dist_short_slope`, and
`dist_long_slope`; it reports the same standard three axioms.

The unified audit now contains 73 declarations.  The three additions are the
positive-start raw/regular action bridge `lLength_sqrt_Icc`, the canonical
restricted attainer predicate `IsLSegAttainer`, and the pointed restricted-
value convergence endpoint `lSegValue_pt_lim`.  The focused audit is warning-
free green; all 73 declarations depend only on `propext`,
`Classical.choice`, and `Quot.sound`.

This audit does not promote explicit-confinement pointed convergence to the
full geometric ancient-flow consumer: producing confinement, compact-test
reduced-density convergence, and reduced-volume no-mass-loss remains separate.

The next audit extension adds the three finite-segment density bridges,
pointwise reduced-density convergence, compact chart-volume convergence, the
source parametric-density identity, and compact common-coordinate integration.
The resulting 80-declaration focused audit is warning-free green; every printed
declaration still depends only on `propext`, `Classical.choice`, and
`Quot.sound`.

The source-manifold compact integral endpoint `redDensity_src_lim` and the
conditional quantitative exterior-mass theorem `redDensity_tail_le` extend the
unified list to 82 declarations.  Their direct audits are standard-three-axiom
clean, both producer artifacts are exact-refresh GREEN, and the integrated
82-item focused audit is warning-free GREEN with the same three axioms.

The next source extension adds `redDensity_wgt_lim`, `redDensity_src_wgt`, and
the generic reverse-ball core `ball_subset_image`, bringing the list to 85
declarations.  All three direct audits report only `propext`,
`Classical.choice`, and `Quot.sound`.  Both newly imported producer artifacts
are exact-refresh GREEN, and the integrated 85-item focused audit is warning-
free GREEN with exactly those same three axioms.

The current audit contains 89 declarations.  The four additions are the
generic finite partial-diffeomorphism localization theorem `lint_map_fin_loc`,
the raw transported and limit reduced-density measures `redDensitySrcMeas` and
`redDensityLimMeas`, and the fixed-limit-space compact-test endpoint
`redDensity_cc_lim`.  The endpoint and its exact producer artifact are
warning-free focused/refresh GREEN; the expanded audit is warning-free focused
GREEN, and all 89 declarations still depend only on `propext`,
`Classical.choice`, and `Quot.sound`.

The unified audit now contains 94 declarations.  The five additions are the
two tail-map provenance equations `tailSystem_apply` and
`tailInvIncl_apply`, the generic reverse compact-ball producer
`tailBall_capture`, its canonical member-map bridge `tailMember_chain`, and the
public canonical endpoint `canon_ball_capture`.  Their producer artifacts are
warning-free focused and exact-refresh GREEN.  The expanded 94-declaration
focused audit is GREEN, and every printed declaration still depends only on
`propext`, `Classical.choice`, and `Quot.sound`.

The final audit for the fixed-space tail-transport chain contains 97
declarations.  Its three additions are the generic inverse-map estimate
`map_inv_tail_le`, the named terminal reduced-density measure
`redDensityTermMeas`, and the fixed-limit-space tail bound `redSrc_tail_le`.
Both producer modules are warning-free focused and exact-refresh GREEN.  The
97-declaration focused audit is GREEN, and every printed declaration depends
only on `propext`, `Classical.choice`, and `Quot.sound`.
