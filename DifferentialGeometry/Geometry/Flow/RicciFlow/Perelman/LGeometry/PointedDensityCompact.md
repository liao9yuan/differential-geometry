# Compact common-coordinate reduced-density convergence

## Route

- `redDensity_cpt_lim` is the actual fixed-common-coordinate compact-set
  endpoint: its sequence integrand is the chart density of `gSeqExt` multiplied
  by the reduced density of the corresponding flow term, and its limit
  integrand uses `co.gInf` and the limit flow's reduced density.
- `ConvOut.volDens_compOn` is consumed internally.  The theorem accepts the
  exact pointwise reduced-density convergence input needed by dominated
  convergence, which `redDensity_pt_lim` supplies without duplicating its large
  confinement package here.
- Reduced-density measurability and its uniform finite bound are kept explicit,
  with measurability required only eventually.  The chart-density bound is
  derived internally from compactness and `ConvOut.volDens_compOn`.  This avoids
  importing P3 coercivity or hiding it behind a desired integral-convergence
  assumption.
- Compactness makes the restricted `modelHaar` measure finite, and the proof
  applies nonnegative dominated convergence to a tail on which all hypotheses
  hold; removing a finite prefix recovers convergence of the original sequence.

## Boundary

- This module does not assert a source-manifold Riemannian-volume integral
  identity.  The separate pullback-density bridge belongs to the compactness
  volume-convergence layer and is not folded into this lower common-coordinate
  endpoint.
- No kappa-solution, surgery, event-seam, or RFWS object is introduced.

## Verification

- The private DCT engine and the actual geometric endpoint are warning-free
  focused GREEN.  Its initial generic public exposure was removed because it
  made the reduced-density name overpromise.
- The exact named module refresh is GREEN now that the exported compact theorem
  has a real audit and source-manifold consumer.

## Progress

- `redDensity_cpt_lim`: theorem endpoint 100% and dedicated common-coordinate
  DCT machinery 100%.
- The later source-manifold change-of-variables endpoint remains unstated (0%).
