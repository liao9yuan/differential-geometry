# MovingShiOpen

## Current verification state

The public interface remains unchanged.  `movingShi_of_bound`,
`movingShi_complete`, and `CurvBoundInput.movingShi_open` are focused-green and
the exact target is current (`9663/9663`), with no local `sorry` or warning.
All three public theorems have been replayed with axioms consisting only of
`propext`, `Classical.choice`, and `Quot.sound`.

The route is now trusted end to end.  `movingShi_of_bound` constructs the
solution-generated point-centered barrier-cutoff family, supplies the checked
curvature-tower Kato estimate, and calls
`BernsteinTower.estimate_barrier_at`.  The former private legacy adapter around
the sorry-backed `BernsteinTower.estimate_complete` has been deleted and is not
a dependency of any public theorem in this module.

- `shiOpenConst` is an explicit constants-first envelope depending only on the
  model dimension, the common squared-curvature bound, the buffered time slab,
  and the requested finite order.  Its finite envelope includes the extra
  `N + 1` tower level needed by Kato, and contains no flow or sequence-member
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

## 2026-07-23 fixed-order cutoff adapter

The finite truncation has been factored once as the private
`exists_trunc_tower`.  The legacy `complete_of_heat` path and the new
`complete_of_cutoff` path share that constructor rather than duplicating the
tower proof.  The cutoff path retains the genuine tower through `m + 1`, bounds
the reaction constants through that same level, and transports only the Kato
prefix through `m` to `BernsteinTower.estimate_cutoff_at`.  It does not consume
metric equivalence or a Ricci lower bound.

After one local multiplication-order repair and the coordinated
`BernsteinComplete` refresh, the complete file is focused GREEN with zero
diagnostics and exact GREEN (`9634/9634`).  The conditional cutoff adapter is
therefore checked; it is not yet the public route because the solution cutoff
producer does not exist.

## Analytic assembly

`movingShi_of_bound` now combines:

1. exact-current `towerHeatSol_any`, with the explicit constructor-tree cost
   `rmTowerCost`;
2. exact-current `BernsteinTower.estimate_barrier_at` through the checked
   private `complete_of_barrier`, together with solution-produced
   `ShiBarrierCutoffData` and `towerNorm_grad_le`;
3. the arbitrary-dimensional Ricci trace bound;
4. completeness transport from the complete left anchor to the shifted
   time-zero slice; and
5. finite truncation through order `N + 1` with an explicit common constant,
   followed by the requested output through order `N`.

The strict start needed by `towerHeatSol_any` forces the canonical midpoint
`t0 = (alpha + beta) / 2`.  Consequently the uniform denominator in
`shiOpenConst` is `((beta - alpha) / 2) ^ k`, not
`(beta - alpha) ^ k`.  The complete anchor remains the given metric at
`alpha`; a private one-sided Ricci-flow comparison transports it to the
shifted Bernstein slab.  No completeness-at-every-time, compactness,
injectivity-radius, or endpoint-radius hypothesis was added.

The public proof uses `complete_of_barrier`.  The obsolete private
`complete_of_heat` adapter has been removed; the remaining
`complete_of_cutoff` is a checked conditional smooth-cutoff adapter and is not
the public route.

## 2026-07-24 point-centered barrier adapter

Added the private fixed-order `complete_of_barrier`.  It uses the same
`exists_trunc_tower` constructor as the smooth-cutoff adapter, retains the
tower through `m + 1`, transports Kato control through `m`, and consumes the
quantifier-correct point-centered family

```text
∀ O, Nonempty (ShiBarrierCutoffData G T O).
```

After rewriting the truncated time horizon, it calls the exact-current
`BernsteinTower.estimate_barrier_at`.  Focused verification of the complete
file is GREEN, and the coordinated exact refresh is GREEN (`9634/9634`).
This adapter adds no new public assumption and does not yet replace the public
legacy call: that switch remains blocked on the actual solution-generated
barrier-cutoff family.

The single-flow and sequence/open-window theorems contain no further `sorry`.
In particular, the sequence theorem must never be reproved by calling
`movingShi_complete` separately for each member and then trying to extract a
uniform constant.

## 2026-07-27 trusted Route B-prime switch

The concrete producer `shiBarrierCutoff_of_sol` is now exact-current.  The
public `movingShi_of_bound` proof has been switched from the legacy heat
adapter to `complete_of_barrier`.  It transports completeness from the original
left anchor to the shifted time-zero slice, builds the cutoff family at every
center, and supplies `towerNorm_grad_le` through the requested order.

The truncation and explicit constant now retain reaction levels through
`N + 1`.  This is the minimal extra level needed to estimate the gradient of
the order-`N` tower norm; the public conclusion still ranges only over
orders `k ≤ N`.  Obsolete metric-equivalence calculations and the private
legacy `complete_of_heat` adapter were removed.

Focused verification and the exact target are green (`9663/9663`).  Axiom
replay for `movingShi_of_bound`, `movingShi_complete`, and
`CurvBoundInput.movingShi_open` contains only `propext`,
`Classical.choice`, and `Quot.sound`.

## Honest accounting

- `movingShi_of_bound`: theorem-level **100%**, focused/exact-green and
  axiom-clean apart from the standard three axioms above.
- `movingShi_complete` and `CurvBoundInput.movingShi_open`: theorem-level
  **100%** on the trusted barrier route.
- dedicated HCG-facing complete-Shi assembly machinery: 100%.
- arbitrary-dimensional curvature-tower producer and dedicated machinery:
  100% checked.
- generic fixed-order cutoff/barrier Bernstein consumers and their HCG
  adapters, plus the concrete solution-produced `ShiBarrierCutoffData`
  theorem: 100% checked.
- unconditional `compactnessSol`: theorem 0%.
- whole-HCG support machinery: about 60%.

## 2026-07-29 time-zero bounded geometry

The complete-barrier proof already produced the intrinsic Riemann curvature
tower before taking its Ricci trace.  That estimate is now exposed as
`rmOpenBound` and `movingRm_of_bound`; `movingShi_of_bound` is its
Ricci-trace consequence.  `CurvBoundInput.atZeroGeomOpen` applies the same
constants-first estimate on one fixed buffered canonical window and packages
the resulting all-order time-zero bounds as `SeqBoundedGeometry`.

Focused verification and the exact module refresh are green (`9679/9679`).
A direct axiom audit of `atZeroGeomOpen` contains only `propext`,
`Classical.choice`, and `Quot.sound`.  The unrelated legacy `sorry` warning in
`BernsteinComplete.estimate_complete` is not on this declaration's dependency
path.

This closes the last time-zero producer used by unconditional
`compactnessSol`.  Superseding the historical accounting above:

- `movingRm_of_bound`, `movingShi_of_bound`, `movingShi_open`, and
  `atZeroGeomOpen`: 100%;
- unconditional MSM135 Theorem 3.10 `compactnessSol`: 100%;
- whole-HCG supporting machinery: approximately 84%;
- the later Hamilton blow-up endpoint `ham3_cgh_limit`: still a separate
  theorem-level 0%.
