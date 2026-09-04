# Raw framed-exponential multiplicity area

## Intended endpoint

`raw_mul_le_area` should be the completeness-free analogue of
`framed_mul_le_area`: for a measurable model-space set on which
`framedExpMap` is a local homeomorphism, a pointwise lower bound on the
cardinality of its fibers should bound the Riemannian volume of a measurable
target set by the integral of the raw radial Jacobi density.

The public statement must use `framedExpMap`, raw `expDomain` membership, and
the existing `curveDensity`/radial-variation fields.  It must not assume
`CompleteSpace M` or mention `expMapIntrinsic`.

## Native reuse audit

- `raw_exp_density` gives exactly the pointwise identification of
  `mapJacDensity` for the unframed raw exponential with the raw radial
  `curveDensity`.
- `normalFrame` is a continuous linear isometry.  The existing
  `Module.Basis.map_addHaar` argument in `expJac_normal_int` supplies the
  required change of variables between `modelHaar` on the tangent model and
  Euclidean `volume` in framed coordinates.
- `riemVol_mul_le_area` contains the needed multiplicity partition and
  summation pattern, but its public interface and its private image-equality
  lemma are specialized to `expMapIntrinsic` and require
  `[CompleteSpace M]`.

## Resolved lower-layer blocker

The previously missing measurable-set injective image formula is now supplied
by `riemVol_image_eq` in `Analysis/Integration/Measure/ManifoldImageEq.lean`.
It is warning-free focused verified and has exactly the open-neighborhood,
measurable-set, `C¹`, and `Set.InjOn` hypotheses required by the countable
injective pieces in the multiplicity proof.

Three routes were checked:

1. Directly specialize `riemVol_mul_le_area`: impossible without reintroducing
   `CompleteSpace M`, because both its map and density are intrinsic.
2. Use `riemVol_image_le` on the injective partition: its `IsCompact` source
   premise does not hold for the measurable disjoint pieces, and an arbitrary
   measurable subset of finite-dimensional Euclidean space is not supplied by
   the project as a countable union of compact subsets.
3. Identify raw and intrinsic exponentials on the raw domain: the intrinsic
   exponential itself is only available under the completeness package, so
   this does not remove the forbidden assumption.

Those failed routes motivated the smallest native bridge, now implemented in
the canonical companion `Analysis/Integration/Measure/ManifoldImageEq.lean`:

```text
riemVol_image_eq
  (hK : MeasurableSet K)
  (hKU : K ⊆ U) (hU : IsOpen U)
  (hf : ContMDiffOn ... 1 f U) (hinj : Set.InjOn f K) :
  riemannianVolumeMeasure g (f '' K)
    = ∫⁻ x in K, ENNReal.ofReal (mapJacDensity g f x) ∂modelHaar
```

Its proof is the chart/partition-of-unity lift of Mathlib's exact Euclidean
formula `lintegral_image_eq_lintegral_abs_det_fderiv_mul`.

`raw_mul_le_area` is now source-written along the resulting short route.  The
proof transports the framed local diffeomorphism through `normalFrame`,
partitions its raw image domain into countably many measurable disjoint
injective pieces, and applies `riemVol_image_eq` on each piece.  A private
basis-change lemma identifies the chart-basis raw Jacobian with the
`normalBasis` radial-Jacobi density, while `Module.Basis.map_addHaar` returns
the final integral to Euclidean `volume` on the framed set.

The public theorem uses only `framedExpMap`, raw `expDomain` coverage, a raw
`IsLocalDiffeomorphOn`, and the fiber-cardinality lower bound.  It contains no
`CompleteSpace M`, connectedness, intrinsic exponential, or intrinsic-distance
assumptions.

## Verification and accounting

The generic measure-layer producer is stated, proved, warning-free focused
verified, and exactly refreshed for this true downstream consumer.  The first
raw-specialization elaboration exposed only two local source issues: the
existing `curveDensity_recomb` declaration needed its direct `SegmentGauss`
import, and the final preimage rewrite needed the local `normalFrame` alias
made explicit.  Both repairs preserve the public statement and mathematical
route.  The next pass then exposed only that the private density-basis helper
must explicitly receive the `RiemannianBundle` instance already present on the
public theorem; this does not strengthen the endpoint.  Focused
re-verification then elaborated the complete proof and exposed only unused
section instances on that private helper; the helper now explicitly omits
them.  The following pass found the identical three unused instances on the
private Haar-transport helper; it now omits them as well, with a final
recheck.  That pass elaborated the endpoint and showed that the public theorem
itself does not need positive model dimension, so `NeZero(finrank)` is now
omitted from the endpoint as well.  The final focused check is warning-free
GREEN.

`raw_mul_le_area` is stated, proved, and warning-free focused verified; this
dedicated raw multiplicity-area producer is **100% complete**.  The generic
image-equality machinery is also **100% complete**.  These are machinery for
the later raw CGT assembly and do not by themselves add endpoint credit to P1b
or the whole Poincare program.

## Pull-volume composition

`raw_mul_le_pull` specializes `raw_mul_le_area` to the centered model ball and
then uses the existing private `rawJac_normal_int` conversion to identify its
normal-frame radial-density integral with `rawPullVol`.  The conversion remains
private: the public composition theorem is the canonical interface, so no
temporary basis-change API is exposed and the measure proof is not duplicated.

Its hypotheses are exactly measurability of the target set, raw exponential
domain coverage on the model ball, the raw framed local-diffeomorphism premise,
and the same general fiber-cardinality lower bound used by
`raw_mul_le_area`.  It adds no completeness, connectedness, or intrinsic
exponential assumption.

The first focused preflight stopped before this module elaborated because the
newly imported `RawPullVolume` artifact did not yet exist.  The import is
acyclic, and the exact dependency refresh was performed only after the
parallel lanes reached a coordinated boundary.  The next pass found only a
local model-with-corners notation typo; after correcting it, the proof
elaborated and exposed that positive model dimension was unused.  The public
theorem now explicitly omits that instance.  Final focused verification is
warning-free GREEN.

`raw_mul_le_pull` is stated, proved, and focused verified, so this local
composition theorem and its dedicated machinery are **100% complete**.  It
remains P1b producer machinery rather than a P1b endpoint, so endpoint and
whole-Poincare percentages are unchanged.
