# MovingShiOpen

## Verified interface

The file passes its focused check.

- `shiOpenConst` is an explicit constants-first envelope depending only on the
  model dimension, the common squared-curvature bound, the buffered time slab,
  and the requested finite order.  It contains no flow or sequence-member
  argument.
- `movingShi_complete` is fully assembled from the constants-first core.
- `CurvBoundInput.movingShi_open` is fully assembled on the canonical windows.
  It uses
  `alpha = openWindowLeft a 0 (n + 1)`,
  `beta = openWindowLeft a 0 n`, and
  `psi = openWindowRight b 0 n`.
  The curvature package first chooses one `C` on `[alpha, psi]`; the theorem
  then chooses `shiOpenConst ... C alpha beta psi N` before introducing the
  sequence member `k`.  Thus there is no invalid uniformization of memberwise
  existential constants.

The public sequence conclusion necessarily displays the stored topology,
charted-space, manifold, sigma-compactness, and `T2Space` instances for each
varying carrier.  These are the canonical fields of `PointedFlowData`, not new
geometric hypotheses.

## Exact frontier

`movingShi_of_bound` contains this file's single `sorry`.  It owns the
constants-first analytic assembly, not another input package.  Its proof must
combine:

1. `exists_rmTowerSol` / `towerHeatSol_any`, whose missing lower producer is
   the all-order genuine commuted-curvature star decomposition;
2. `BernsteinTower.estimate_complete`, whose missing lower producer is the
   complete-noncompact scalar parabolic maximum principle with cutoff or
   exhaustion;
3. the arbitrary-dimensional Ricci trace bound;
4. one-sided metric equivalence from the complete left anchor under the
   curvature bound; and
5. finite truncation through order `N` with the explicit common constant.

The single-flow and sequence/open-window theorems contain no further `sorry`.
In particular, the sequence theorem must never be reproved by calling
`movingShi_complete` separately for each member and then trying to extract a
uniform constant.

## Honest accounting

- `movingShi_of_bound`: statement 100%, proof 0%.
- `movingShi_complete`: Lean proof 100%, but trusted theorem completion 0%
  while it consumes `movingShi_of_bound`.
- `CurvBoundInput.movingShi_open`: Lean wrapper proof 100%, but trusted theorem
  completion 0% for the same reason.
- dedicated open-window wrapper and quantifier architecture: about 90%; the
  remaining work is analytic rather than wrapper plumbing.
- arbitrary-dimensional curvature-tower machinery: about 70%.
- complete-noncompact Bernstein machinery: about 10%.
- unconditional `compactnessSol`: theorem 0%.
- whole-HCG support machinery: about 60%.
