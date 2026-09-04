# Raw ball polar equality

## Result

`rawSeg`, `rawSegInt`, and `rawSegEnd_ray_sub` are warning-free focused GREEN.
They are the compactness-free raw polar brick: on any fixed positive raw ray,
the raw minimizing locus minus the radially extendible locus has at most one
parameter.

The proof follows the existing `segEnd_ray_sub` pattern but does not use
intrinsic exponential maps, connectedness, ambient completeness, curvature,
compactness, or a metric-norm witness.  It works directly with the raw
`expMap` distance-equality locus, so it is the appropriate lower layer for a
compact-buffer polar argument.

`rawSegInt_ball_meas` is warning-free focused GREEN as the compact-buffer Borel
producer.  For `0 < R < R₀` and a
compact `closedEBall p R₀`, it sets `S = (R + R₀) / 2` and exhausts
`rawSegInt ∩ gBall R` by the countable family of fixed rational dilations
`q` with `1 < q < S / R`.  The corresponding preimage is taken from the
compact set `rawSeg ∩ closedGBall S`, supplied by `isCompact_rawSeg`; the
reverse inclusion is exactly the strict radial-extension witness, while the
forward inclusion uses `rawSegInt_sub` to contract the original longer raw
endpoint.  Thus the result is genuine `MeasurableSet`, not a consequence of
the endpoint locus's `NullMeasurableSet`, and it adds neither completeness nor
a wrapper hypothesis.

`rawSegInt_image_eq` is warning-free focused GREEN as the exact raw
change-of-variables bridge.  On the same
compact buffer it takes the measurable interior ball as `K`, obtains
`K ⊆ expDomain` from `rawSegInt_sub` and `rawSeg_mem_dom`, and applies the
generic `riemVol_image_eq` using `rawExp_inj_seg`.  The terminal integrand is
then rewritten pointwise by `raw_exp_density` to the raw radial Gram density.
This is equality for the raw-exponential *image* only: it deliberately does
not yet identify that image with the ambient metric ball or use the endpoint
null bridge.

Its first focused pass reached only a local namespace repair: the raw radial
Gram density is named `Variation.curveDensity`, so this module now opens the
existing `Variation` namespace explicitly.  No domain, injectivity, measure,
or change-of-variables obligation was reached or changed by that repair.  The
following focused pass is warning-free GREEN.

`rawBall_integral_eq` is warning-free focused GREEN (25.9 seconds).  It states
the required equality for the genuine strict
`riemannianEDist` ball, not a set equality with a raw exponential image.  Let
`L = rawSeg ∩ closedGBall R` and `K = rawSegInt ∩ gBall R`.  The lower
inclusion is the raw distance equality, while `ball_sub_rawSeg` covers the
ambient ball by the larger compact image `rawExp '' L`.  The measure difference
`L \ K` lies in the union of `rawSegEnd` and the fixed `g`-sphere.  The first is
zero by `rawSegEnd_null`; the latter is transported by `normalFrame` to a
Euclidean sphere and is `modelHaar`-null.  Thus the two raw density integrals
agree almost everywhere.  `riemVol_rawExp_le` gives the ambient-ball upper
bound from `L`, `rawSegInt_image_eq` gives exact COV on `K`, and the raw
distance equality yields the reverse inclusion of the interior image in the
ball.  This uses neither `CompleteSpace M` nor a wrapper predicate; the
private `gSphere_null` is only the fixed-radius Haar-null fact needed for that
single measure comparison.

The first focused check found two purely local source repairs before reaching
the measure comparison: this raw module must import the existing `BasisHaar`
API for the normal-frame Haar determinant transport, and the strict `gBall`
inequality is the second component of the `rawSegInt ∩ gBall` hypothesis.
Both are now made explicit; no theorem hypothesis or proof route changed.
The subsequent focused pass proved the body and found only that the private
normal-frame sphere lemma inherits four unused global geometry instances.
They are now omitted locally; this does not alter the public theorem's
compact-buffer assumptions.  The final focused check is warning-free GREEN.

The next source-written bridge is `rawSegEnd_null`: with a compact buffer from
`isCompact_rawSeg`, it proves that
`(rawSeg \ rawSegInt) ∩ closedGBall` is `modelHaar`-null.  Its proof does not
assume that the global raw locus is measurable.  Instead it encloses the
target in a measurable local terminal set obtained from the countable union
of compact images
`{t • w | 0 ≤ t ≤ n / (n + 1), w ∈ K}`.  This local terminal set is
subsingleton on every positive ray, so `lintegral_polar` and the existing
radial null argument prove its `modelHaar`-nullity.  The target inherits that
nullity.  `rawSegEnd_nullMeas` records the consequent `NullMeasurableSet`,
which is the honest measurable interface without adding a Haar-completeness
assumption.

The first two focused checks reached only local elaboration repairs: the
countable-union theorem name, pair-evaluation rewrites for the compact-image
witnesses, the available division-cancellation lemma, and the explicit
zero-vector exponential evaluation.  No mathematical or measurability
obstruction appeared.  After those repairs, the third focused check passed
without warnings.

`rawSeg_mem_dom` is the next source-written domain bridge.  A raw equality
vector cannot use the raw exponential's outside-domain junk value: away from
zero that value would make its positive radial norm equal to zero distance,
and zero already belongs to `expDomain`.  This is the smallest reusable fact
needed before constructing a common raw radial geodesic for a raw interior
vector.  Its first focused check reached only a local definitional-shape
repair: the raw-locus membership had to be explicitly unfolded before
rewriting the exponential's outside-domain value.  The corrected theorem then
passed its second focused check; the declaration's unused file-level instances
were subsequently omitted explicitly, following the established local style.
The final focused recheck is warning-free GREEN.

`rawSeg_same_len` is the source-written collision pre-bridge.  It only unfolds
the two raw distance equalities and uses injectivity of `ENNReal.ofReal` on
nonnegative square roots.  Thus two raw minimizing vectors whose raw
exponential endpoints coincide have a common radial metric length, with no
geodesic continuation or completeness hypothesis.  It is the normalization
input for the pending raw-interior `Set.InjOn` proof and awaits its first
focused verification alongside the fresh raw interior bridge.

`rawExp_inj_seg` is now source-written as that direct raw-interior
`Set.InjOn` producer.  It first applies `rawSegInt_sub` and
`rawSeg_same_len`, normalizes a nonzero collision to two unit raw rays, and
uses `smul_mem_expDomain` at the longer raw endpoints to obtain their full
unit-speed raw domains.  The two global smooth raw-ray extensions are then
the inputs to `broken_minimizer_velocity_match`.  The matching local radial
curves continue through the collision by `geoLift_isIntegralOn` and
`gvf_eqOn` on the shifted intersection of their open time intervals.  The
two small private derivative helpers only transfer time shifts and extract the
prescribed initial velocity from `IsGeodesicOnWithInitial`; neither adds a
mathematical assumption.  In particular, the source avoids the convenient
but inapplicable `isGeodesic_eq_of_initial`, which requires ambient
completeness.  This long source chain has not yet been elaborated, so it is
not a verified producer.

Its first focused check after the `MaximalRescaling` export was available
failed only on mechanical elaboration shape: the file needed the `Topology`
scope for neighborhood notation, explicit `WithTop ℕ∞` smoothness orders,
explicit tangent-fiber casts before radial scalar rewrites, the locally induced
Riemannian-bundle instance for `IsMetricNorm`, and qualified `Variation`
velocity names.  The collision argument itself was not reached as a distinct
mathematical error.  These local repairs are source-written and await the
next focused check.

The local-bundle attempt was then rejected: rebinding `RiemannianBundle` changes
the implicit metric instance in `rawSeg` and makes existing raw-membership
proofs ill-typed.  The correct minimal interface is the existing consumer
input `hEnorm : IsMetricNorm g`, now made explicit only in `rawSegInt_sub` and
`rawExp_inj_seg`.  It is mathematically required both to compare the raw
radial `g`-speed with `riemannianEDist` and by
`broken_minimizer_velocity_match`; it is already an explicit hypothesis of
the planned `rawBall_vol_rel` consumer and of the raw density APIs.  No global
completeness or local compatibility wrapper is introduced.

The first full focused pass with that corrected interface reached the collision
assembly and exposed only local elaboration shapes: `radialGeo_of_dom` supplies
an `EqOn` with the time inferred from membership, raw radial endpoint equalities
need explicit tangent-fiber casts, and the affine geodesic restriction needs an
explicit shifted-interval inclusion.  The same pass also identified mechanical
normal-form repairs for the zero vector and the normalized metric inner
products.  Those corrections are source-written; no new mathematical
assumption, common-domain claim, or cut-locus assertion was introduced.

The full collision chain is now warning-free focused GREEN.  The `hEnorm`
binder is explicit only on `rawSegInt_sub` and `rawExp_inj_seg`, precisely
where conversion between `g`-speed and ambient distance is used.  The final
argument is the completeness-free route above: raw extension gives the two
unit-speed germs, the broken-minimizer theorem identifies their meeting
velocities, and `gvf_eqOn` transports that equality through the common shifted
open interval to time zero.  Thus `rawExp_inj_seg` is a genuine global
`Set.InjOn` producer, not a local-diffeomorphism substitute.

`rawSegInt_geo` is the next source-written radial producer.  It expands the
strict radial extension in `rawSegInt`, uses `rawSeg_mem_dom` at that endpoint,
and returns the common geodesic interval from `radialGeo_of_end`.  Its output
now identifies both time one with `expMap v` and the longer endpoint with
`expMap (c • v)`: the canonical `smul_mem_expDomain` contracts the supported
longer vector to `v`, and maximal-geodesic uniqueness supplies the time-one
identity.  The same two facts plus openness of `expDomain` give a germ equality
between this local geodesic and the raw radial exponential curve at every time
of the compact segment; this is the exact input for a global smooth radial
extension in the injectivity proof.  It introduces neither completeness nor a
new predicate.  The native
radial-geodesic API does require the file's existing
standard `[I.Boundaryless]` geometry instance; this is retained rather than
omitted, while the other unused file-level instances remain omitted.  It is
source-updated and awaits a focused recheck after the fresh
`MaximalRescaling` artifact is available.

`rawSegInt_ext` is the next raw-polar producer for the injectivity route.  It
uses that segment germ equality with `exists_raw_ray_ext`, so the global smooth
raw radial extension is geodesic on the compact segment by eventual-equality
transfer.  This is the required replacement for the private
`RadialSurjectivity.globalize_geo_seg` helper and remains free of ambient
completeness.

`rawSegInt_sub` is the next source-written lower bridge.  Starting from the
strictly longer raw endpoint, canonical radial contraction supplies domain
support on the whole compact segment.  The existing `rawSpeed_sq` and the
completeness-free `HopfRinow.curve_edist_le_speed_mul_time` bound the initial
and terminal subarcs.  Together with the raw equality at the longer endpoint
and the distance triangle inequality, the two bounds force the time-one raw
equality.  Thus it produces `rawSegInt ⊆ rawSeg` without a path-length
wrapper, intrinsic exponential map, or ambient completeness.  This source
uses the already verified public speed producer; it awaits its first focused
check together with the preceding source updates.

The first recheck after this adjustment failed before testing that intended
change: the mechanical edit had removed `Boundaryless` from `rawSeg_mem_dom`
instead of `rawSegInt_geo`, leaving the latter's omission in place.  The source
now restores the former omission and removes only the latter.  The next focused
check confirms that `Boundaryless` is now available, but exposes the native
`radialGeo_of_end` requirement `[T2Space (TangentBundle I M)]`.  Both native
regularity instances are now retained for `rawSegInt_geo`; the other unused
file-level instances remain omitted.  The following focused check passed
warning-free.

## Boundary

`rawExp_inj_seg`, `rawSegInt_ball_meas`, `rawSegInt_image_eq`, and
`rawBall_integral_eq` are warning-free focused GREEN.  The common-domain/
cut-locus assembly is therefore closed.  The remaining E2 work is the actual
two-radius raw-density/Bishop comparison; no ball-cover endpoint or
image-equality wrapper remains to be invented.

## Accounting

- `rawBall_vol_rel`: unstated and unproved, **0%**.
- Ray-endpoint sublemma: **100%**, focused checked.
- Compact-buffer null bridge: **100%**, warning-free focused checked.
- Raw-domain bridge: **100%**, warning-free focused checked.
- Raw interior geodesic bridge: **100%**, warning-free focused checked.
- Raw interior-to-minimizing bridge: **100%**, warning-free focused checked.
- Raw collision-length bridge: **100%**, warning-free focused checked.
- Raw interior injectivity producer: **100%**, warning-free focused checked.
- Compact-buffer raw-interior Borel producer: **100%**, warning-free focused checked.
- Raw-interior image change-of-variables: **100%**, warning-free focused checked.
- Raw ball/interior polar equality: **100%**, warning-free focused checked.
- Dedicated P1b machinery: about **98%**; aggregate P1 endpoints: eleven of
  fourteen (**78.6%**); whole Poincare endpoint: unstated (**0%**).
