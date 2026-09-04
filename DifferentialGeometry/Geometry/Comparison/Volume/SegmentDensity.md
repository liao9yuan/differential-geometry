# Segment density

## Raw exponential producer

`raw_exp_density` identifies `mapJacDensity` of the raw time-one exponential
map with the canonical `curveDensity` of the radial curve

```text
t ↦ expMap g p (t • v)
```

and the time-dependent radial variation fields obtained by differentiating

```text
s ↦ expMap g p (t • (v + s • chartModelBasis E i)).
```

The theorem applies at every `v ∈ expDomain g p`; it has no target-chart
parameter or chart-membership hypothesis.  It does not assume a metric space
on `M`, metric completeness, connectedness, an intrinsic norm realization, or
an intrinsic exponential map.

## Proof route and reuse

The proof is the coordinate-free raw counterpart of `exp_density_curve`:

1. `radial_jacobi_dom`, whose proof uses `expMap_contMDiffAt`, identifies each
   time-one radial variation field with the
   corresponding column of the raw exponential differential.
2. The time-one `curveGram` is therefore definitionally the Gram matrix in
   `mapJacDensity`.
3. Unfolding `curveDensity` and `mapJacDensity` finishes the equality directly.

No private chart helper from `ManifoldImageLe`, new density definition,
completeness wrapper, area argument, or partition-of-unity proof is exposed or
duplicated.

## Assumptions and placement

The declaration keeps exactly the ambient hypotheses used by this route:
finite model dimension, `I.Boundaryless`, and Hausdorff tangent-bundle phase
space.  It explicitly omits the file-level `RiemannianBundle`, positive-
dimension, `CompleteSpace E`, `T2Space M`, and `SigmaCompactSpace M`
hypotheses.  Its canonical home is beside the generic
determinant identity and the existing intrinsic density theorem in
`Comparison/Volume/SegmentDensity`.

The import chain is acyclic: this module imports `ManifoldImageLe` for the
public `mapJacDensity` and already imports `JacobiVariation`, which imports
`Smoothness/Domain`; none of those upstream modules imports `SegmentDensity`.

## Verification and project status

The proof is source-written without `sorry`, `admit`, axioms, or a new frontier
predicate, and its focused verification passed without warnings.  The first
named refresh exposed a dependent-instance normalization that the earlier
focused pass had missed: the Gram basepoint remained `expMap p (1 • v)` after
the columns were rewritten.  The proof now records that basepoint equality
explicitly before applying the column identities, rather than asking `simp` to
cross the tangent-space cast.  The repaired file is again warning-free focused
green, and its exact refresh is green (3843/3843).

Thus `raw_exp_density` and its dedicated source proof are verified (100%).  The
raw compact-ball polar/volume endpoint remains unstated and 0% complete; this
file provides only its density-identification brick.
