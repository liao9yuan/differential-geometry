# ConvFieldCanon

## Role

`ConvFieldCanon.lean` is the readable final producer assembly where the two P4
lanes meet.  It takes the concrete `StepDCanonData` sidecar, completeness, and
the sequence curvature package and keeps the following objects explicit in the
proof:

```text
canon → mc → Phi → bf
              ↓
       per-window equivalence + Shi
              ↓
           srcData
              ↓
 hbound / hcovTail / hlipTail / hlipSrc / hcp
              ↓
       open_upgrade_of_raw
```

The public theorem is `open_upgrade_canon`; the name is eighteen characters
and stays within the repository's twenty-character limit.

## Exact assembly

For each canonical window, one call to
`CurvBoundInput.metricEquiv_open` chooses the Ricci coefficient and finite
equivalence majorant before the sequence index.  The same window data are used
for all later consumers, avoiding independent incompatible choices.

The target-side data are reindexed by `mc.subseq` and restricted from
`Set.univ` to `Phi.target k`.  `CurvBoundInput.movingShi_open` is transported
to each source domain by `srcShi`.  The canonical `canon_rel` and `canon_init`
projections then feed `srcCovLip_of_soln`, producing one `SrcCovLipData` per
window.

The raw packages are transparent projections/adapters:

- `hbound` uses `hbound_of_equiv` with
  `cLow n = (Crel * Bmax n)⁻¹`;
- `hcovTail` uses grow-local `covTail_of_bounds` and `srcData.cov`;
- `hlipTail` uses grow-local `lipTail_of_src` and `srcData.lip`;
- `hlipSrc` restricts the stronger whole-source `srcData.lip` estimate to the
  requested compact set;
- `hcp` is exactly `StepDCanonData.canon_cp`.

No endpoint assumption, bump-derivative assumption, new radius hierarchy, or
claim about arbitrary `MetricCompactnessConclusion` was added.

## Current verification state

The source draft contains no new `sorry`, `admit`, or `axiom`.  Focused checking
is intentionally paused while the H6 framed-normal-coordinate migration owns
the downstream refresh window.  The current `StepDAssembly.olean` predates its
new `domain_eq` field, so checking now would produce a known stale-interface
failure rather than useful proof diagnostics.

The first local obligation to verify after refresh is the definitional equality

```text
tgtRefSrc gRefT hsrc htgt k = srcMetric hsrc htgt k 0
```

used to convert `canon_rel` into the reference relation consumed by
`srcEquivOn`.  Both sides are the same target-time-zero restriction and
source-target pullback, so this is expected to be `rfl`.  The next likely work
is only `simpa` normalization across the metric-to-flow field copy.

`open_upgrade_canon` is theorem-level 0% until focused verification is green;
its dedicated assembly is approximately 85%.  Its four genuine upstream
frontiers remain visible and independent: the arbitrary-dimensional curvature
tower, the complete-noncompact Bernstein/Shi theorem, the constants-first
varying-source induction, and the concrete Step-D canonical-bounds proof.
The unconditional `compactnessSol` endpoint remains 0%; dedicated P4 support
machinery remains roughly 97%, and whole-HCG support machinery roughly 60%.
