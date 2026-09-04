# MaximalRescaling

## 2026-08-30: global-support chosen curves

### Result

- `maximalGeodesicChosenCurve_rescale_eventually` keeps its existing public
  statement and continues to reuse the fixed-chart theorem
  `projectCurve_rescale_eventually`.
- The chosen witnesses now integrate the global geodesic vector field.  Near
  time zero, continuity of their bundle projections keeps both feet in the
  initial chart source.  Restricting to that neighborhood and applying
  `chart_vf_on_iff` recovers the fixed-chart integral-curve hypotheses needed
  by the existing rescaling machinery.
- No theorem below the chosen-curve boundary was changed, and no new public
  wrapper or assumption was introduced.

### Failed attempts and repairs

- The first focused pass found a look-alike Unicode neighborhood symbol; it was
  replaced by the project's `𝓝` notation.
- The first version of the bridge exposed that `chart_vf_on_iff` still carried
  a nonzero-finrank instance while this theorem intentionally does not.  The
  producer was subsequently strengthened to cover finrank zero, so no local
  dimension split or extra hypothesis remains here.

### Verification

- Focused verification passed without warnings after the source-free global
  vector-field producer was refreshed.
- This consumer migration is complete.  It is infrastructure only: the P1a
  compact-buffer Bishop endpoint theorem is not stated or proved in this file
  and therefore remains 0% complete here.

## 2026-08-30: global raw radial rescaling

### Mathematical change

- `expMap_smul_max_ne` starts from nonzero `a` and raw domain support of
  `a • v`. It inverse-rescales the supplied global-geodesic-vector-field
  witness, using monotone or antitone interval transport according to the sign
  of `a`, thereby proving `a` belongs to the maximal interval for `v` and
  identifying the two endpoints through `maximalGeo_eqOn`.
- `expMap_smul_eq_max` preserves the positive-scaling public interface as the
  direct positive specialization.
- The private affine-lift bridge restricts each time to a chart neighborhood,
  applies `scaledTangentLift_transport`, converts with `chart_vf_on_iff`, and
  enlarges the derivative back to the original within-filter. Thus no fixed
  initial chart is imposed on the global witness.
- `radialGeo_of_end` is the weakest segment constructor: one positive supported
  endpoint yields a prescribed-velocity geodesic on an open preconnected
  interval containing the preceding closed time segment, with the requested
  raw exponential endpoint value.
- `radialGeo_of_dom` packages pointwise raw domain support on a positive radial
  segment by reusing `radialGeo_of_end` and adding pointwise raw-exponential
  agreement on that closed interval.

### Verification and progress

The nonzero-scaling addition passed warning-free focused verification.  No
named refresh or broader build was run for it during the parallel-task window.
Its pointwise raw-radial consequence belongs in a bridge above the exponential-
domain smoothness layer and this maximal-rescaling layer, so neither lower
module acquires a reverse dependency.

Focused verification of the new declarations passed without warnings. The
first focused pass exposed only local elaboration issues: a let-bound set was
incorrectly used as a rewrite theorem, radial-domain membership needed explicit
unfolding, and the inverse-rescaled dependent pair needed the repository's
`TotalSpace.ext` pattern. The rescaled curve and its support were then
normalized by separate function and set equalities, and the original
prescribed-initial-data package was reconstructed from its destructured fields.
No theorem statement, assumption, or mathematical route changed.

The three radial-rescaling declarations in this file are verified (100% at
this local infrastructure layer). The downstream `minExp_of_cptBall` source
proof uses both radial constructors in its supremum continuation assembly, but
that endpoint is still unverified and therefore remains 0% complete as a Lean
theorem. Its dedicated machinery and source assembly are about 95%; the wider
P1a compact-closure Bishop endpoint remains 0% until the final producer and its
consumers are verified.

## 2026-09-01: raw radial-domain contraction

`smul_mem_expDomain` is the canonical forward star-domain producer: from
`v ∈ expDomain` and `t ∈ Icc 0 1`, it constructs the rescaled global geodesic
witness on the preimage interval `{s | t * s ∈ J}`.  The zero case uses the
existing zero-domain fact; the positive case transports the tangent lift via
the private global rescaling bridge and uses preconnectedness of `J` to retain
time one.  It assumes no ambient completeness and is not a consumer wrapper.

The source is written during the parallel source-only window and awaits its
focused verification.  Its first focused pass found only that the explicit
`TotalSpace.ext` tail after the initial-value rewrite was redundant; that tail
was removed before the next focused pass.  The next pass proved the theorem but
reported that the tangent-bundle `T2Space` instance is unused here; it is now
omitted locally.  The final focused recheck passed without warnings.
