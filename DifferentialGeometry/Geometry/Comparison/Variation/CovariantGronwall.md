# CovariantGronwall.lean — covariant Grönwall transfer (B3 keystone)

Verification passed, sorry-free (2026-06-11). Part of the Step A item-3a ladder
(`Comparison/ConvexBalls.md` B3; B0 stage-4 base).

## `covGronwall_ne_zero`

Field `J` along `γ` with a second-order covariant bound
`g(D²J, D²J) ≤ K²·g(J,J)` on `Ico 0 b`, a **parallel `g`-ON frame `F` of full
cardinality** on `Icc 0 b`, ICs `J 0 = 0`, `D_tJ 0 = w`, and the Grönwall
smallness `gronwallBound 0 (max K 1) (K·b·√g(w,w)) b < b·√g(w,w)`
⟹ `J b ≠ 0`.

Route: coefficients `yᵢ t = g(Fᵢ t, J t)` differentiate by
`metric_compat_hasDerivAt_inner` (parallel frame kills the `D_tF` terms), bundle
into `Y : ℝ → EuclideanSpace ℝ ι` via `(EuclideanSpace.equiv ι ℝ).symm` +
`hasDerivAt_pi` + `HasFDerivAt.comp_hasDerivAt`; the ℓ²-norm equals the `g`-norm
exactly (`inner_self_eq_sum_sq`, full ON frame), so `hODE` transports to
`‖Y''‖ ≤ K‖Y‖`; `gronwall_ne_zero` (SecondOrderGronwall) finishes; `Y b ≠ 0`
⟹ `J b ≠ 0` (coefficients of `0` vanish).

## Consumers / next bricks

Instantiate with the radial Jacobi field of `exp_p` (`Exponential/
JacobiVariation.lean`: `exists_radial_jacobi_radius` + ICs + endpoint
`J(1) = d(exp_p)w`) to get `d(exp)_v` injective below the curvature scale.
REMAINING for that instantiation:
- the curvature-norm input `g(R(J,γ')γ', R(J,γ')γ') ≤ K²·g(J,J)` (b);
- a full parallel ON frame along the radial geodesic (PerpFrame gives the perp
  part; add the parallel unit velocity);
- chartRep-differentiability of the radial `J`, `D_tJ`, frame (regularity
  plumbing);
- **the `t = 0` gap**: the radial Jacobi equation is only available on `(0,1)`
  (rescale identity on `Icc 0 1`), while `hODE` is needed on `Ico 0 b` — use the
  ε-shift (start the Grönwall at `ε` with ICs from continuity) or strengthen
  the rescale lemma (blueprint note in `B0NormalCoordBounds.md`).
- then (d): the manifold IFT at `v ≠ 0` to convert `mfderiv` injectivity into
  `IsLocalDiffeomorphOn` (B2's `hloc`).

## Lean gotchas

- `HasFDerivAt.comp_hasDerivAt` has the base point `x` as an EXPLICIT argument
  (section variable) — `hl.comp_hasDerivAt t hf`.
- `hasDerivAt_pi.mpr` needs the Pi-valued function pinned by an expected type
  (higher-order unification).
- `set`-bound `Y` crossings handled by `show` (zeta-defeq), avoiding the
  β-unreduced `rw [hYdef]` trap; `PiLp.ext` for EuclideanSpace equalities;
  `(EuclideanSpace.equiv ι ℝ).symm c i = c i` is `rfl`.
- Stale-olean shape: a just-added upstream lemma (`gronwall_ne_zero`) reported
  "Unknown identifier" until the upstream module was target-built.
