# SegmentValue

## Role

This module supplies the non-class finite-action curve category, its exact
same-clock restriction and concatenation closure, and the scalar lower bound
and extended-real restricted value required by book12, together with its
same-clock dynamic-programming statement.

## Native route

`lLength_lower` discards the nonnegative kinetic term, integrates the scalar
lower bound against `sqrt s`, and evaluates that integral by the native real
power formula.  It assumes only nonnegative ordered endpoints, the pointwise
scalar bound along the curve, and integrability of the actual L-density.

The earlier lower-bound-only state did not define an admissible curve category
or an honest empty-domain value.  `IsLSegCurve` and its closure theorems fill
the first gap.  The new `lSegValue` fills the second using `WithTop Real`;
`lRegCostC1` cannot substitute because arbitrary concatenation is not globally
`C¹`, and its real-valued `sInf` does not represent an empty competitor set by
`+∞`.

## Finite-action segment curves

`IsLSegCurve` is the non-class admissible category required by the book's
same-clock value and domain consumers.  It uses one canonical auxiliary metric,
the solution metric at the fixed pole time `T`, on every subinterval.  Its
fields are exactly absolute continuity, almost-everywhere manifold
differentiability, interval integrability of the actual L-density, and
membership of the spacetime graph `(gamma s, T - s)` in the supplied set.
Endpoints are deliberately left to the future value competitor rather than
being built into the curve predicate.

`lSegCurve_restrict` restricts an admissible curve to an ordered closed
subinterval.  Absolute continuity and density integrability use their native
interval-monotonicity theorems, almost-everywhere differentiability is pulled
back along monotonicity of restricted volume, and graph confinement is direct
set inclusion.  It introduces no second curve notion or endpoint convention.

`lSegCurve_join` pastes two such curves at a common endpoint.  The absolute-
continuity field uses the generic `AbsolutelyContinuousOnInterval.piecewise_Iic`
theorem.  Almost-everywhere differentiability and density integrability use the
two piecewise germs away from the null joining time; spacetime confinement is
pointwise.  This is the exact closure property used by the segment value's
future dynamic-programming theorem.

## Extended-real segment value

`lSegCosts` is the private set of actual real L-actions witnessed by admissible
curves with the requested endpoint values.  `lSegValue` takes the infimum of
its coerced image in `WithTop Real`, so an empty competitor class is
definitionally assigned `⊤` rather than an arbitrary real default.

`IsLSegAttainer` is the canonical proof predicate bundling admissibility, the
two endpoint equalities, and exact realization of `lSegValue`.  It introduces
no second value or minimizer construction; pointed stability uses it to keep
source and limit attainment hypotheses precise.

Under the single confinement-set scalar bound
`hR : ∀ q ∈ Ω, -K ≤ S.scalar q.2 q.1`, `lSegCosts_bdd` pulls the
graph-membership field back to `lLength_lower`.  For a nonempty competitor
class, `lSegValue_coe` then identifies the extended infimum with the coerced
real infimum via `WithTop.coe_sInf'`.  The public accessors say that every
competitor bounds the value above, the scalar estimate bounds it below, and a
single competitor makes it different from `⊤`.  The lower accessor handles
the empty class separately, where the conclusion follows from
`WithTop.sInf_empty`.

`lSegValue_mono` is the confinement-set monotonicity law.  An inclusion
`Ω ⊆ Ω'` sends every cost witness for `Ω` to one for `Ω'` by composing
only the graph-membership field.  When the smaller cost class is nonempty,
`csInf_le_csInf` gives the reversed value inequality from the cost-image
inclusion and the scalar lower bound on `Ω'`; when it is empty, its value is
`⊤`.

`lSegValue_exhaust` is the compact-graph exhaustion rule at the value level.
Every stage lies in `Ω`, and the stated graph hypothesis places each actual
fixed-endpoint `Ω`-competitor wholly in one stage.  Monotonicity makes the
full value a lower bound for all stage values.  For the reverse inequality, a
nonempty real cost witness is assigned to its stage and bounded using
`csInf_le` followed by `lSegValue_le` with the scalar bound restricted from
`Ω`; an empty full cost class has value `⊤`.  No convergence or `Tendsto`
corollary is asserted here.

`lSegCosts_split` is the private exact set-level dynamic-programming identity.
Restriction sends a long competitor to its two subintervals, while
`lSegCurve_join` and `lLength_join` paste any compatible pair back together;
the middle endpoint indexes the union.  `lSegValue_add` is the matching private
infimum algebra.  It treats the four empty/nonempty combinations explicitly so
that `⊤` obeys the intended empty-domain convention, and in the nonempty case
uses `csInf_image2_eq_csInf_csInf` together with the real lower bounds and
`WithTop.coe_sInf'`.  These are implementation bricks for the later public DPP,
whose quantified middle-point infimum statement is `lSegValue_dpp`.

## Dynamic programming

`lSegValue_dpp` identifies the long segment value with the infimum, over the
middle point, of the sum of the two subsegment values.  Its proof does not
assume nonempty competitor classes.  Locally, `F y` is the coerced summed-cost
fiber, `U` is their union, and `V y` is the sum of the two subsegment values.
The cost-splitting identity identifies the long cost image with `U`.
`isGLB_csInf` handles every nonempty fiber, while `isGLB_empty` assigns `⊤`
to empty fibers.  The union GLB is proved directly from the range GLB and the
fiber GLBs, with a separate empty-union branch closed by `IsGLB.unique`.
Finally, `lSegValue_add` identifies `V` pointwise with the fiber infima.

The source crosswalk for book12 confirms that later domain calculus needs
restriction monotonicity, a strict leaving-curve gap, and compact-graph
exhaustion for this same confined competitor class.  `IsLRegCurveOn` remains an
ODE-solution predicate and is not reused as an admissible segment domain.

## Verification

The earlier focused verification of `lLength_lower` is warning-free green, so
that theorem remains 100% for its stated scalar-lower-bound role.  Its check
required only the native curvature namespace, the finite-dimensional instance
genuinely used by scalar curvature, and explicit interval endpoints for the
continuity integrability lemma.

The first coordinated focused check of `IsLSegCurve` and `lSegCurve_join`
failed locally.  The fixed-metric constructor was missing the explicit
pointwise tangent `InnerProductSpace` instance used by the native
Cheeger--Gromov metric construction.  The proof also needed explicit `Iic`
membership coercions, one right-germ equality orientation repair, and an
`omit` for the lower theorem's unused connectedness assumption.  Those repairs
are source-written by mirroring the native instance order, and the private
class-valued metric constructor is reducible as required by the linter.  A
second focused check then exposed the remaining native instance-order detail:
the Riemannian tangent bundle needs the local `IsManifold I 1 M` consequence
of the smooth manifold instance before its fiber structures are inferred.  It
also found the analogous left-germ equality orientation.  The source now
mirrors `PointedRiemannianManifold.emetricSpace` by installing that local
manifold instance before the Riemannian bundle, and the redundant explicit
fiber-inner instance has been removed.  The left germ is repaired; a third
focused check showed that this context still requires the explicit pointwise
tangent `InnerProductSpace` after the local `C¹` and Riemannian-bundle
instances.  It also reported that connectedness is not a theorem-level
dependency of `lSegCurve_join`.  The explicit fiber-inner instance is therefore
restored in the confirmed native order.  The fourth focused check showed that
the pointwise inner-product instance still could not be synthesized because
the tangent `VectorBundle` instance was not installed explicitly in this local
metric construction.  It also exposed the parser-sensitive placement of the
join theorem's local `omit`.  The source now installs the canonical
`TangentSpace.vectorBundle` after the local `C¹` manifold instance and before
the Riemannian bundle, while retaining the pointwise inner-product instance;
the `omit` now scopes both the join theorem's docstring and declaration.  A
fifth focused check narrowed the remaining failure to that explicit pointwise
inner-product declaration: its `inferInstance` does not close reliably while
the surrounding tangent-family instances use mixed syntactic presentations.
The source now uses the single family expression
`(TangentSpace I : M → Type _)` throughout and follows the shorter checked
repository-native construction from `VolumeComparisonBridge`: install
`g.toContinuousRiemannianMetric`, derive its Riemannian bundle, then call
`EMetricSpace.ofRiemannianMetric`.  This avoids redundant pointwise and manual
continuity instances; the canonical tangent fiber/vector bundles remain
available through their native instances.  The next focused check has not yet
run.  The sixth focused check then showed that the remaining construction was
too strong rather than missing a Riemannian instance:
`EMetricSpace.ofRiemannianMetric` demands `T3Space M`, and the subsequent
distance-equality error was only cascading from that missing instance.  Since
absolute continuity and the generic join theorem require only a
`PseudoMetricSpace`, the auxiliary fixed-time structure is now built with
`PseudoEMetricSpace.ofRiemannianMetric` under the weaker `RegularSpace M`
assumption and converted using the connected-manifold
`riemannianEDist_ne_top` theorem.  No `T3Space` assumption is added; the next
focused check found only that `lSegCurve_join` could no longer omit
`ConnectedSpace M`: `IsLSegCurve` now genuinely references both regularity and
connectedness through its fixed pseudo-metric.  That stale local `omit` is
removed.  The independent scalar theorem `lLength_lower` still omits both
unused assumptions; the next focused check has not yet run.

The eighth focused check is warning-free green for `IsLSegCurve`,
`lSegCurve_join`, and `lLength_lower`.  The subsequent
`lSegCurve_restrict` implementation is also warning-free focused green by the
native monotonicity route above.

The segment-value definition and its three public order/finiteness accessors
are warning-free focused green using `WithTop.coe_sInf'`, `csInf_le`, and
`le_csInf`.

The private cost-splitting and extended-real addition identities are
proved by the restriction/join and four-case infimum routes above.  Their first
coordinated focused check found one local elaboration error in the
degenerate `c = b` endpoint branch: `piecewise_eq_of_mem` requires the explicit
membership proof `b ∈ Iic b`, not the bare order proof.  The source now uses
`Set.mem_Iic.mpr le_rfl`; the repaired split/add layer is warning-free focused
green.

The public `lSegValue_dpp` statement and GLB proof are source-written by the
route above.  Its first focused check found only that the convenient theorem
`isGLB_iUnion_iff_of_isLUB` lies outside the current import cone.  No import is
added: the source now proves the same union GLB directly by unpacking union and
range membership and composing the already available fiber/range GLBs.  This
repair is warning-free focused green.

The public confinement monotonicity theorem is proved by direct cost-image
inclusion and the empty/nonempty split above.  It is warning-free focused
green.

The public compact-graph exhaustion equality is proved by the range lower-bound
and per-competitor stage assignment above.  Its focused check is warning-free
green, including the empty-competitor branch where every restricted value is
forced to top.

The same-clock dynamic-programming theorem is therefore 100% for its stated
restricted extended-real endpoint.  Its dedicated admissible-curve
restriction/join, segment-value order, cost splitting, and infimum-addition
machinery are also verified.  This does not prove minimizer existence or the
broader complete-flow reduced-geometry package.  Confinement monotonicity and
compact-graph exhaustion are each 100% for their stated domain-calculus
endpoints.

The public `lSegValue_gap` theorem is the exact order-theoretic leaving-gap
rule: a finite restricted value and an honest positive action gap for every
ambient competitor that leaves the smaller confinement set imply equality of
the two values and trap every strict epsilon-minimizer with epsilon below the
gap.  Finiteness is converted to a nonempty restricted cost class directly;
the proof does not misuse the one-way `lSegValue_ne_top` theorem.  Its first
focused check found only the wrong left/right addition-monotonicity lemma and
an explicit call that supplied implicit domain arguments.  A second check
found the analogous strict-addition orientation at the final real-valued
contradiction.  After those local repairs, the focused check is warning-free
green.

Thus all three stated order-theoretic domain-calculus endpoints are 100%.
Producing the positive gap uniformly from geometric separation, curvature,
and confinement remains a distinct analytic producer and is not hidden behind
this theorem.

## 2026-08-31 time-slab competitor bound

`lSegValue_le_time` weakens the earlier confinement-wide scalar hypothesis to
the exact backward-time slab used by a competitor.  It proves boundedness of
the real cost set directly from `lLength_lower`, then applies the native
`lSegValue_coe`/`csInf_le` route to compare the extended-real value with that
competitor's L-length.  The theorem is non-definitional and adds no compactness,
regularity, or global scalar-curvature assumption.

The focused check is warning-free green.  This endpoint is 100%; it closes the
order-theoretic lower-bound input for the future `lSegValue`/regular-cost
identification.  That identification theorem remains unstated (0%), and its
next dedicated frontier is admissibility of the square-root reparameterized
regular curve.

## 2026-08-31 square-root admissibility

`lSegCurve_sqrt` closes that admissibility frontier.  A global `C1`
square-root-time curve whose regularized Lagrangian is interval integrable
becomes an `IsLSegCurve` on the squared backward-time interval, under only the
explicit spacetime-confinement hypothesis.  The proof has four independent
pieces: compact-interval Lipschitz control in the fixed pole-time Riemannian
metric, composition with the absolutely continuous square root, almost-
everywhere differentiability away from the zero-time endpoint, and the
monotone square substitution combined with `lDensity_sq_pos` and
`lRegDensity_eq`.

The private fixed-metric Lipschitz helper uses the native
`chart_symm_edist_le` estimate and compactness of `Icc`; it introduces no new
metric class or public wrapper.  `le_lSegValue` is the complementary pure-order
accessor: any common lower bound for all admissible fixed-endpoint actions lies
below the extended-real infimum, including the empty-class case.

`lSegValue_le_c1` packages the easy comparison direction: every global `C1`
square-root-time competitor with integrable regularized Lagrangian bounds the
same-clock segment value above.  It uses `lSegCurve_sqrt`, the time-slab scalar
lower bound, and `lLength_sqrt_Icc`; it does not assume compactness or existence
of a minimizer.

The focused check is warning-free green.  All three stated public endpoints are
100%.
The full equality between `lSegValue` and the existing regular `C1` cost is
still unstated (0%): the easy inequality now follows from `lSegCurve_sqrt`,
whereas the reverse inequality requires a genuine finite-action raw-curve to
global-`C1` action-density theorem.  The missing internal producer is a finite
chart `timeH1` realization for raw absolutely continuous curves with square-
integrable velocity; it must not be replaced by extra public chart/H1
assumptions.

## 2026-08-31 raw absolute-continuity projection

The fixed pole-time pseudo-metric already used definitionally by
`IsLSegCurve` is now exposed as `lSegmentMetric`, together with the projection
`IsLSegCurve.ac`.  This is representation access needed by the forthcoming
raw-curve chart realization; it adds no new metric or hypothesis.  Two direct
topological continuity wrappers were tried and removed because unfolding the
class-valued metric at their public boundary exhausted deterministic
elaboration heartbeats.  Keeping the absolute-continuity projection is both
smaller and more useful: downstream proofs can install the metric only inside
their local calculation.

Focused verification is warning-free green.
