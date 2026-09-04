# Local two-radius Bishop attempt

## Status

`rawBall_vol_rel` is not stated: **0% theorem completion**.  No wrapper,
additional hypothesis, `sorry`, or incomplete source declaration was retained.
The dedicated P1b machinery remains about **96%**; aggregate P1 endpoints
remain eleven of fourteen (**78.6%**); the whole Poincare endpoint remains
unstated (**0%**).

## Intended native statement

The intended lowest-layer result belongs in this volume-comparison module and
has the compact-buffer/local-Ricci shape

```lean
theorem rawBall_vol_rel
    [PseudoEMetricSpace M] [IsRiemannianManifold I M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p : M) {q s R R0 : Real}
    (hq : 0 <= q) (hs : 0 < s) (hsR : s <= R) (hRR0 : R < R0)
    (hcpt : IsCompact (Metric.closedEBall p (ENNReal.ofReal R0)))
    (hRic : forall y in Metric.closedEBall p (ENNReal.ofReal R),
      forall w : TangentSpace I y,
        -(((Module.finrank Real E - 1 : Nat) : Real) * q^2) *
            g.inner y w w <= ricciTensor (I := I) g y w w) :
    vol(B p R) * ENNReal.ofReal (hypRadVol q (finrank - 1) s) <=
      ENNReal.ofReal (hypRadVol q (finrank - 1) R) * vol(B p s)
```

Here `vol(B p r)` abbreviates the existing `riemannianVolumeMeasure` of the
strict `riemannianEDist` ball; the final source must use that expression rather
than introduce a new wrapper.

## Attempts and exact boundary

1. **Complete polar reuse.**  A direct `segBall_vol_rel` application was
   prepared and focused-checked.  The first pass exposed only a local notation
   issue in the temporary probe; after that repair the shared elaboration lock
   rejected the retry, so no source declaration was kept.  The checked source
   signature of `segBall_vol_rel` requires both `CompleteSpace M` and a global
   `RicciBoundedBelow`; it is therefore not an adapter for the stated local
   compact-buffer theorem.

2. **Raw two-radius integration.**  `rawBall_vol_le_int` provides only
   `vol(B p r) <= integral(K_r, rawDensity)`, where `K_r` is the compact raw
   minimizing equality locus.  `raw_ratio_anti` and `rawDens_le_zero` are
   one-ray, zero-curvature comparison inputs and cannot reverse this inequality
   or identify the two different raw loci `K_s` and `K_R`.  For the requested
   arbitrary `q`, the only raw ratio core is private and specialized to `q = 0`;
   there is no public raw negative-Ricci density-ratio theorem.

3. **Complete pullback extension.**  `CGT.rawExt_complete` completes a
   model-space raw pullback only after a caller supplies
   `IsLocalDiffeomorphOn framedExpMap`.  It supplies neither an ambient metric
   extension nor transfer of ambient distance balls, local Ricci bounds, or
   Riemannian volume, so it cannot justify applying the global Bishop theorem.

The shared exact obstruction is a missing **raw common-domain/cut-locus
equality**.  The smallest decisive producer is a compact-buffer raw analogue
of `segBall_area_eq`/`segBall_reg_zero`: define the interior raw minimizing
locus, prove raw exponential injectivity there, prove its complement in the
raw equality locus is `modelHaar`-null (ray-endpoint plus sphere-null), and use
`riemVol_image_eq` to obtain equality between ball volume and the raw polar
integral.  The general-`q` version additionally needs the raw radial
comparison export before this equality can be integrated to `hypRadVol`.

This is a substantial missing API/mathematical producer, not a local
elaboration repair; it is not expected to close without implementing that
cut-locus equality layer first.
