# Perelman L-geometry umbrella

`LGeometry.lean` is the import-only public entry point for the fixed-manifold
Perelman L-geometry modules.  Its terminal imports expose the foundational
definitions, square-root reparameterization, moving-metric and first-variation
identities, regularized ODE/L-exponential construction, and the pullback and
parabolic-scaling naturality chains.  The terminal second-variation import now
also exposes the regularized and ordinary L-Jacobi predicates, the square-root
Jacobi bridge, the differential-of-`lExp` Jacobi theorem, the symmetric
L-index form and Green identity, and the natural-input fixed-endpoint capstone
`lLength_second_var`.

The public entry point also exposes `lRegJacobi_unique`, the fixed-chart
initial-value uniqueness theorem for regularized L-Jacobi fields, and the
domain-aware L-conjugacy API `IsLConj`, including its kernel and Jacobi-field
characterizations and the nonconjugate differential bijectivity lemmas.

`RegIndex.lean` adds the nonsingular square-root-time index density and form,
their symmetric and Green identities with an allowed endpoint at `s = 0`, the
Jacobi boundary formula, and the almost-everywhere square change of variables
back to the ordinary `lIndex`.

`RegAction.lean` adds the direct square-root-time Lagrangian and action,
their compatibility with ordinary L-length, first variation with internally
produced compact domination, joint regularity of the Euler residual, and the
fixed-endpoint formula `lRegAction_second`.  The latter remains valid when an
endpoint is `s = 0` and produces all Jacobi and index-density integrability
inside the proof.  Its compact-slab coercivity and family-uniform
action-to-energy bounds feed the compactness layer without assuming scalar
curvature is nonnegative.

`Minimizer.lean` starts the honest minimizing layer with
`lRegIndex_nonneg_var`: for an actual smooth fixed-endpoint variation whose
regularized action has a local minimum at the central parameter, its diagonal
regularized index is nonnegative.  This is a direct second-derivative
necessary condition, not a semidefiniteness assumption.  The arbitrary-field
theorem `lRegIndex_nonneg` realizes a smooth zero-endpoint field by a genuine
fixed-endpoint variation and transfers the same conclusion.

`ActionCompact.lean` adds `lAction_subseq`: every family of regularized curves
with one action bound on a fixed compact parameter interval and compact target
has a uniformly convergent subsequence.  It derives uniform equicontinuity from
one family-wide reference-energy budget and the reference Riemannian distance;
equicontinuity is not supplied as an assumption.  The corollary
`lAction_subseq_fix` also proves that two common endpoints are preserved by the
limit.

The finite-chart direct-method layer is now public as well.  Generic
`timeH1` slicing, finite-family weak extraction, moving-coefficient quadratic
lower semicontinuity, and compact chart subdivision feed
`ActionFinite.lean`.  `curve_mdiff_local` recovers almost-everywhere manifold
differentiability from each local `timeH1` representative.  Consequently
`lRegAction_chart` identifies the finite generalized chart action exactly with
the raw manifold `lRegAction`, rather than comparing bundle or Hom objects.

`ActionCapstone.lean` exposes both assembly levels.  `lAction_chart_lsc` keeps
the finite chart witnesses and their generalized lower-semicontinuity
inequality.  The terminal theorem `lAction_liminf` hides those witnesses and
returns a fixed-endpoint uniformly convergent subsequence whose continuous
limit satisfies the actual raw-action bound

```text
lRegAction S T gamma a b
  <= liminf (fun n => lRegAction S T (alpha (chi n)) a b) atTop.
```

`ActionDensity.lean` closes the complementary recovery side of the direct
method.  `lAction_c1_dense` takes the finite local chart-`timeH1`
realization of a relaxed curve and produces global fixed-endpoint C1 curves
which converge strongly in every local H1 chart, uniformly as manifold
curves, and with the complete regularized L-action converging to the relaxed
action.  Endpoint-flat vector-valued density, finite chart gluing, repeated
subdivision nodes, and zero-length pieces are handled internally; the public
theorem does not expose compact buffer choices.

`ActionEuler.lean` names the genuine curve-dependent chart Lagrangian and
action and proves `lRegAction_stat`: an actual smooth fixed-endpoint local
minimum is stationary for the full nonlinear regularized L-action.  The
coefficient is evaluated along the curve and is not frozen.  The generic
`mom_rep_cont_l1` theorem handles the natural integrable force, while
`ActionVelocity.lean` derives the chart-Gram bounds internally and converts
the resulting continuous momentum representative into a continuous velocity
representative using the metric's native inverse.

`ActionAttain.lean` closes the relaxed direct-method endpoint:
`exists_lRegMinC1` attains the infimum of the global fixed-endpoint C1 actions
by a continuous curve with finite chart-H1 representatives.  This is not yet
the terminal regular L-minimizer.  `ActionSplice.lean` and
`ActionLocalMin.lean` transfer its global competitor inequality to an actual
fixed-endpoint local minimum of each positive chart segment; in particular,
`lChartAct_local` does not assume the desired Euler equation.

The checked regularity-side producers are also public.  `ActionForce.lean`
constructs the actual integrable chart force.  `ActionForceC1.lean` gives its
canonical continuous representative once a continuous velocity
representative is available.  `ActionVelocityC1.lean` combines a C1 momentum
representative with the jointly smooth native Gram inverse, and
`ActionBootstrap.lean` proves the genuine C1-to-C2 step `lChartVel_c1` from an
actual weak Euler identity.  No inverse, force representative, or regularity
conclusion is supplied as a consumer assumption.

`ActionNodeSplice.lean` exposes `lNode_c1_dense`, the two-chart shared-node
recovery producer.  It constructs the continuous joined curve internally and
returns global fixed-endpoint C1 competitors converging strongly in both local
chart-H1 pieces, uniformly on the manifold, and in the complete regularized
L-action.  Repeated subdivision nodes are allowed.  The generic
`TimeC1Glue`, `TimeH1Tent`, and `TimeH1TentC1` modules separately provide the
closed-interval C1 join and exact-node smooth tent approximation needed for a
later corner equation.

`ActionWeakEuler.lean` and `ActionRegular.lean` are now public as well.
`lChartAct_line` differentiates the genuine nonlinear chart action, and
`lChart_weak_euler` derives its weak Euler identity from an actual local
minimum. `lChart_min_c1` then produces a continuous weak-velocity
representative and closed-interval C1 chart regularity. The scalar-value
continuity proof reuses the carrier-subtype `ScalarSTContOn` API rather than
re-elaborating joint smoothness, and no stationarity or regularity conclusion
is supplied as an assumption.

The positive two-piece corner chain is public through `ActionNodeC1.lean`.
`lNode_mom_same` proves the same-chart momentum equation from exact action
comparison; `lNode_mom_match` obtains the cross-chart scalar equation from the
global fixed-endpoint C1 competitor inequality by rewriting a positive head
of the right segment in the left chart.  `lNode_vel_match` cancels the native
positive-definite Gram operator, and `lNode_c1` combines the resulting
coordinate-velocity match with the piecewise chart regularity to prove C1 on
the whole two-piece interval.  None of these endpoints assumes the desired
corner equation or node regularity.

The generic support is kept below the Ricci-flow layer.
`CurveC1Glue.lean` proves `curve_c1_join` in a chart centered only at the
shared node, while `CurveC1Finite.lean` iterates it over a positive strict
finite subdivision.  `chartDeriv_shift` and `chartDeriv_change` supply the
translation and coordinate-change derivative bridges.  Repeated or
zero-length subdivision pieces are now handled generically by
`FiniteSubdivision.exists_strict_subdiv`: it returns a strict subdivision
together with the original positive-segment indices and exact segment
endpoints.  `ActionStrict.exists_lStrict` performs the corresponding
L-specific dependent transport: it retains the original positive-segment
map and returns the strict nodes, charts, `timeH1` pieces, chart containment,
and exact coordinate-representation witnesses.

`ActionNodeWindow.lean` supplies the finite-realization localization needed
for internal nodes.  `lNodeWin_cmp` selects any adjacent positive pair, embeds
arbitrary target-contained replacements into the complete dependent family,
recovers global fixed-endpoint C1 competitors, applies the global minimum, and
cancels every unchanged prefix and suffix term.  It is deliberately stated
for an arbitrary finite realization, so the same theorem can be reused after
inserting a short right-hand head.  `ActionNodeRefine.lNodeRef_cmp` carries out
that dependent refinement: it splits the selected right segment, keeps the
short head in the left chart, slices the old right representative for the
tail, preserves every other finite witness, and returns the exact common-chart
left/head comparison.

`ActionStrictC1.lStrict_piece_c1` supplies the regularity of every piece in a
strict finite realization.  It transfers the genuine global competitor
inequality to each positive segment with `lChartAct_local` and invokes
`lChart_min_c1`; no Euler identity or regularity conclusion is assumed.

`ActionFiniteNode.lFinNode_vel` closes the corresponding internal-node
equation for an arbitrary positive finite realization.  For a selected node
it proves C1 regularity only where needed, constructs a left-chart head,
applies `lNodeRef_cmp` and `lNode_mom_same`, transports the head derivative
back to the original right chart, and cancels the positive-definite Gram
operator.  Its public assumptions require only positivity of each piece, not
an unnecessarily bundled strict-subdivision hypothesis.

`ActionFiniteC1.lFinCurve_c1` combines the piece and node producers for any
positive number of strict pieces.  The one-piece case is handled directly;
for multiple pieces it translates the endpoint velocity equations into the
node-centered charts and applies the generic `curve_c1_fin`.  Thus a positive
finite minimizing realization is C1 on its whole closed interval.

`ActionMinC1.lMinCurve_c1` removes the strictness restriction from that
conclusion.  It compresses an arbitrary monotone realization with
`exists_lStrict`, uses the strict separation of the global endpoints to rule
out an empty compressed family, and applies `lFinCurve_c1`.  Repeated and
zero-length chart pieces therefore no longer survive in the C1 consumer.

`ActionAttainC1.exists_lRegMinC1On` packages the direct-method consequence.
It hides every finite chart, `timeH1`, and approximating-sequence witness and
returns a closed-interval C1 curve with the prescribed endpoints, exact
`lRegCostC1` equality, and the genuine global fixed-endpoint C1 competitor
inequality.  It deliberately does not claim `IsLRegCurveOn`; the current node
regularity chain retains the ambient positive-finrank instance even though
the underlying relaxed-attainment theorem itself does not need it.

`ActionStrictC2.lStrict_piece_c2` continues the analytic bootstrap on every
strict piece.  Starting again from the genuine global minimum, it obtains the
local weak Euler identity and continuous velocity, applies `lChartVel_c1`,
and identifies the returned C1 velocity with the within-derivative to conclude
closed-interval C2 coordinate regularity.  Euler and C2 are conclusions, not
consumer assumptions.

`ActionClassical.lChartEuler_iff` closes the pointwise classical bridge in a
fixed chart.  At local parameter `r` it differentiates the metric momentum at
the correct global square-root time `a + r` and proves that the momentum
equation is equivalent to the second component of `lPhaseField`.  The proof
fully applies the moving metric to model-space vectors: `chartGram_spatial`
identifies its spatial derivative with the Christoffel contraction,
`lRegInner_deriv` supplies the moving-time term, and `lRegAccel_inner` supplies
the intrinsic acceleration pairing.  It introduces no Euler or acceleration
hypothesis.  The next consumer is `lChart_min_accel`, which applies this iff to
the momentum representative of an actual fixed-chart minimum and then uses a
phase shifted by `s - a`.

`ActionMinAccel.lChart_min_accel` completes that consumer.  From an actual
positive fixed-chart local minimum it obtains the C1 momentum and velocity
representatives, differentiates the momentum identity, invokes
`lChartEuler_iff`, and applies `lPhase_accel` to the shifted phase.  A final
neighborhood congruence replaces the auxiliary phase velocity with the actual
`lVelocity`, so the public conclusion is the intrinsic
`covDerivAlong = lRegAccel` equation at every interior square-root time.  It
does not require compactness, a pseudometric, or a supplied Euler equation.

`ActionPieceAccel.lStrict_piece_accel` transports that equation to the actual
manifold curve in a strict finite minimizing realization.  On every open
positive piece, `lChartAct_local` supplies the genuine chart minimum, the
coordinate representation and chart inverse identify the shifted auxiliary
curve with the attained curve as germs, and native derivative/covariant-
derivative congruence transfers the result.  The theorem compares only fully
applied tangent vectors and assumes no acceleration equation.

`ActionStrictC2.lStrict_piece_c2_at` is the canonical manifold-valued form of
the strict piecewise C2 theorem.  It reconstructs the attained curve through
the inverse chart on a genuine open piece; both the node and whole-interior
consumers reuse this producer rather than carrying duplicate reconstruction
proofs.

`ActionNodeAccel.lFinNode_reg` fills every internal subdivision node.  Global
C1 gluing makes the actual chart phase continuous, the two adjacent strict
C2/acceleration pieces solve the phase equation off the node, and the generic
`hasDerivAt_of_punct` theorem extends that equation through the deleted point.
The result supplies manifold differentiability, differentiability of the
actual-velocity chart representative, and the intrinsic acceleration equation.

`ActionStrictReg.lStrict_curve_reg` combines open pieces and internal nodes to
give the full regularized triple at every time in the open global interval of
a strict realization.  `ActionMinReg.lMinCurve_reg` then consumes
`exists_lStrict`, removes zero-length and repeated pieces, and gives the same
interior theorem for the original monotone finite minimizing realization.

`PhaseAt.exists_lPhaseSol_at` supplies the missing arbitrary-base-time local
ODE producer.  At a regular state `(s0,z0)` it applies the autonomized integral-
curve construction directly at time `s0`, then proves that the autonomized
clock component is the actual time on a neighborhood.  This is not a time
translation of the phase field, so the coefficient remains `T - s^2`.

`RegCurveAt.exists_lRegCurve_at` reconstructs that phase solution as an
intrinsic curve through arbitrary regular data `(s0,x,A0)`.  Its initial
velocity is the actual `lVelocity alpha s0 = A0`, and throughout a two-sided
neighborhood it supplies manifold differentiability, differentiability of the
actual-velocity chart representative, and the intrinsic regularized
acceleration equation.  This is the endpoint-local producer needed for the
later closed-interval extension.

`ActionExtend.exists_lRegExtOn` performs that closed-interval extension without
misreading one-sided derivatives as total derivatives.  It keeps the original
curve on `Icc a b`, attaches local regularized ODE curves outside the two
endpoints using the one-sided chart velocities, and applies the punctured
phase argument at each endpoint.  After shrinking inside the open time-regular
set, the returned total curve has the full regularized triple on an actual
open neighborhood of `Icc a b`; `exists_lRegExt` preserves the older closed-
interval projection.

`ActionRegMin.exists_lRegMinOn` applies the extension to the actual direct-
method witness before hiding its finite chart data.  On a normalized positive
interval it returns an endpoint-honest `IsLRegCurveOn`, the prescribed terminal
point, exact equality with `lRegCostC1`, and the genuine comparison inequality
against every global fixed-endpoint C1 competitor.  Its initial parameter is
`Z = (1/2) • lVelocity alpha 0`, with the API's `2 • Z` normalization proved
explicitly rather than assumed.  The open extension and `lRegCurve_eqIcc`
also identify this minimizer with the totalized maximal `lRegCurve` on the
whole closed interval.

`Minimizer.lCost` is the raw L-length infimum over square-root
reparameterizations of global regularized C1 competitors.
`ActionRawMin.lCost_eq_reg` identifies it with `lRegCostC1`, and
`ActionRawMin.exists_lMinimizer` proves compact positive-time attainment.  The
returned curve is an endpoint-honest `IsLRegCurveOn`; its `sqrtReparam` has raw
`lLength = lCost` and is no longer than every competitor in the stated class.
Its normalized initial tangent now satisfies the actual endpoint equation
`lExp S T x Z tau = y`.
The theorem does not silently enlarge this class to arbitrary AC or
piecewise-C1 paths.

`ActionAttain.lRegCostC1_le` exposes the direct-method infimum bound for any
global fixed-endpoint C1 competitor without making downstream modules unfold
`sInf`.  `CutDomain.IsLMinVec` and `lMinDomain` then record exactly the positive
L-exp rays that realize raw `lCost`; `CutDomain.exists_lMinVec` proves that the
compact direct-method endpoint is reached by such a ray.
`ActionNodeSplice.exists_chartH1_join` realizes two arbitrary closed-interval
C1 pieces meeting at one node, including a zero-length middle segment.
`ActionPrefix.lReg_prefix_min` and `lRegCostC1_eq_on` turn that realization and
the global C1 density theorem into honest prefix minimality and closed-prefix
cost identification.  `CutDomain.lMinDomain_down` consumes those results to
prove backward-time star-shapedness, and `lMinFiber_ord` packages the fixed-
tangent minimizing times as an order-connected set.
`CutStrict.lMinVec_unique_lt` then proves the broken-path conclusion: if the
`Z` ray remains minimizing to a later time, every minimizing ray to the same
strictly earlier endpoint has initial tangent `Z`.  Its proof obtains C1 node
matching from the finite chart-H1 minimizer machinery and propagates the
matched phase state back to zero by the regularized ODE uniqueness theorem.

This inclusive minimizing domain can contain its cut boundary, so openness is
not claimed.  The next genuine L5 frontiers are nonconjugacy strictly before a
later minimizing time and the limiting cut alternative.  They are needed to
define the separate open injectivity domain and identify its boundary before
proving the cut image measure zero.

Focused verification of the updated umbrella passes without warnings after
the new node modules were individually focused-checked and refreshed. The
umbrella contains no declarations and introduces no additional assumptions.
The weak Euler, fixed-chart C1,
positive two-piece momentum/velocity matching, positive two-piece C1, and
arbitrary positive-window action-comparison stages are complete. Generic
repeated-node compression and its L-specific strict realization are complete;
caller-side finite refinement and strict piecewise C1 regularity are complete.
Finite internal-node velocity matching and strict finite C1 gluing are
complete; repeated-node compression has been consumed by the global C1
minimizer theorem, and C1 relaxed attainment is now exposed without its finite
witnesses.  Strict piecewise C2 regularity and the pointwise intrinsic
classical Euler-equation bridge are complete.  The shifted
minimizer-to-acceleration consumer is also complete; transport across the open
pieces, internal nodes, and the entire open interval of both strict and
monotone finite minimizing realizations is complete.  Arbitrary-base phase
existence has been lifted to a genuine intrinsic regularized curve, and both
closed-interval endpoint patches plus their open continuation certificate are
complete.  The relaxed minimizer `exists_lRegMinC1` is complete, and the terminal regular
`exists_lMinimizer` is now complete for the compact global-regularized-C1
category, including its `lExp` endpoint representation.  The nonconjugate
local-diffeomorphism producer, minimizing-prefix transfer, and star-shaped
inclusive minimizing domain are also complete; strict pre-cut uniqueness is
complete as well. `redVolume_anti` remains unproved (0%); the next L5 frontier
is nonconjugacy before cut plus the limiting cut alternative, followed by the
open injectivity domain and measure-zero cut image.
