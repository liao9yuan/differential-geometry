# MovingShiOpen

## Current verification state

The previously checked public interface remains unchanged.  The analytic body
of `movingShi_of_bound` is now assembled in source with no local `sorry`, but
its focused check is pending: the shared H6 migration temporarily owns the
upstream refresh chain, and `GaussLemma.olean` is currently absent.  No Lean
source error from `MovingShiOpen.lean` has yet been observed in this pass.
Static signature review did identify and repair one definite, still-unverified
binder error: the call to
`ricci_diag_eq_sum_rm04_diag_of_orthonormal` had passed an extra `hON`
immediately after the basis, although the next argument is the Ricci section.
The remaining inspected calls to `towerHeatSol_any`,
`BernsteinTower.estimate_complete`, `MetricComplete.complete`,
`ricTower_normSq_le`, and `MovingShiBoundOn` match their current source
signatures.

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

## Analytic assembly

`movingShi_of_bound` now combines:

1. `exists_rmTowerSol` / `towerHeatSol_any`, whose missing lower producer is
   the all-order genuine commuted-curvature star decomposition;
2. `BernsteinTower.estimate_complete`, whose missing lower producer is the
   complete-noncompact scalar parabolic maximum principle with cutoff or
   exhaustion;
3. the arbitrary-dimensional Ricci trace bound;
4. one-sided metric equivalence from the complete left anchor under the
   curvature bound; and
5. finite truncation through order `N` with the explicit common constant.

The strict start needed by `towerHeatSol_any` forces the canonical midpoint
`t0 = (alpha + beta) / 2`.  Consequently the uniform denominator in
`shiOpenConst` is `((beta - alpha) / 2) ^ k`, not
`(beta - alpha) ^ k`.  The complete anchor remains the given metric at
`alpha`; a private one-sided Ricci-flow comparison transports it to the
shifted Bernstein slab.  No completeness-at-every-time, compactness,
injectivity-radius, or endpoint-radius hypothesis was added.

The proof uses a private complete finite-truncation adapter around
`BernsteinTower.estimate_complete`; it does not create a second public
Bernstein API.  The lower theorems `exists_rmTowerSol` and
`BernsteinTower.estimate_complete` still contain the repository's honest
analytic `sorry`s, so a focused-green HCG-facing assembly would not yet make
the complete Shi route trusted end to end.

The single-flow and sequence/open-window theorems contain no further `sorry`.
In particular, the sequence theorem must never be reproved by calling
`movingShi_complete` separately for each member and then trying to extract a
uniform constant.

## Honest accounting

- `movingShi_of_bound`: proof source assembled, but theorem completion remains
  0% until its focused check passes.
- `movingShi_complete` and `CurvBoundInput.movingShi_open`: wrapper proofs 100%;
  their checked consumption of the new core is pending the same focused check.
- dedicated HCG-facing complete-Shi assembly machinery: about 95%, with only
  verification and local elaboration repairs remaining.
- arbitrary-dimensional curvature-tower machinery: about 70%; its genuine
  commutator producer remains an honest lower `sorry`.
- complete-noncompact Bernstein machinery: about 25%; the HCG adapter is
  assembled, while its scalar noncompact maximum-principle producer remains
  an honest lower `sorry`.
- unconditional `compactnessSol`: theorem 0%.
- whole-HCG support machinery: about 60%.
