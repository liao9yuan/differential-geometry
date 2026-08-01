# UnifDeTurckRHSZero.lean — notes

Status: **COMPLETE, sorry-free, axiom-clean** (`[propext, Classical.choice, Quot.sound]`),
verified by a real `lake build` of the module.

## What it delivers (brick E3, `j = 0` half of `Ksup`)

For the `Λ`-class (`1 ≤ Λ < 2`, comparability + `MetricCovDerivOrderBoundOn` at orders 1, 2),
with every constant chosen from `(Λ, gBase)` **before** `g₀` is named:

* `covDerivConnDiff_tens` — `covDerivConnDiff` is tensorial (depends on its three section
  arguments only through their values at the point).  Proved by pairing both readings with the
  same one-form through the public `connDiffSection_covGrad_eq_covDerivConnDiff` — whose LHS is
  a genuine fibre tensor evaluated on the three *values* — and separating with the `g₂`-flat of
  the difference (`g0FlatCLM`, `cotangentToDual_g0FlatCLM`, `g₂.pos`).
* `rhsTermBound` (private) — the per-frame-vector estimate: for `g₀`-unit `b`, the summand of
  `deTurckVF_covDeriv_eq` pairs with `w` inside `(C₁ + 3C₀²)Λ⁴ √(g₀(v,v))√(g₀(w,w))`.
* `unifCovDerivVF` — `|g₀(∇^{g₀}_v W, w)| ≤ K √(g₀(v,v))√(g₀(w,w))`,
  `K = n(C₁ + 3C₀²)Λ⁴`, `W = deTurckVF g₀ gBase`.
* `unifRHSBilin` — `|deTurckRicciRHS gBase g₀ (v,w)| ≤ (2K_Ric + 2K)√(g₀(v,v))√(g₀(w,w))`.
* `unifRHSFib` — `riemannianFiberNormSq g₀ 0 2 x (deTurckRHSSection gBase g₀) ≤ (n·K₀)²`.
* `unifKsupZero` — the same in the exact `hsup`-at-`j = 0` currency of
  `ShortTime/UnifNZeroBound.lean` (`iteratedCovGrad g₀ 0 2 0`, index `2 + 0`).

## Route

`deTurckRicciRHS gBase g₀ = −2 Ric(g₀) + 𝓛_W g₀` (`deTurckRicciRHS_apply`).
Ricci half = `unifRicBilin` (banked, `UnifCurvatureJetsLow.lean`).
Lie half = `cartan_formula_for_lie_deriv_metric` + `deTurckVF_covDeriv_eq`
(`Geometry/Flow/DeTurckVFCovDeriv.lean`) fed by `unifCovConnDiffSup` / `unifConnDiffSup`.
Fibre packaging = `rfns0_unit_eq` + `normSq0S_le_card_of_component_bound` on a
`g₀`-orthonormal basis, component values read off by `deTurckRHSSection_toModel_apply`.

## Constant bookkeeping (why the `Λ` powers)

All class bounds are stated in `gBase`-lengths; the target is in `g₀`-lengths.  Using
`√Λ ≤ Λ` (valid since `Λ ≥ 1`) both conversions cost one factor `Λ`, and a `g₀`-unit frame
vector has `gBase`-length `≤ Λ`.  Hence `Λ³` inside each `gBase` estimate and one more `Λ`
converting the output, i.e. `Λ⁴`.  Generous but closed in `(Λ, gBase)`, which is all `Ksup`
needs.

## Lean lessons

* Do **not** try to avoid `covDerivConnDiff_tens`: the identity of `deTurckVF_covDeriv_eq`
  necessarily carries the *frame sections* in slots 2 and 3 (differentiating the frame is the
  whole point), while every `Λ`-class bound is stated on `smoothExtensionTangent`.
  Tensoriality is the only bridge, and it is cheap.
* `g0FlatCLM` lives in `DifferentialGeometry.Analysis.Sobolev.TensorHilbert`;
  `abs_metric_inner_le_sqrt_metric_quadratic` / `metric_inner_self_nonneg` in
  `DifferentialGeometry.Analysis.Laplacian`.  Import `HCGCompactness.ConnDiffDerivBound` and
  mirror its `open` list — it is the nearest leaf that already assembles this exact instance
  environment.
* `ContMDiffSection.exists_eq_at` at `Tensor0SModel 1 ℝ E` needs
  `set_option backward.isDefEq.respectTransparency false` (and a raised
  `synthInstance.maxHeartbeats`), exactly as in `ConnDiffDerivBound.lean`.
* For `|α + β − γ − δ| ≤ …`, `rcases abs_le.mp` on each piece then
  `abs_le.mpr ⟨by nlinarith, by nlinarith⟩` is far more robust than chaining `abs_add`.

## What is NOT closed

The `j = 1` slot of `Ksup` (`∇` of the static field) — it needs `∇Ric(g₀)`, which is blocked
on the missing order-`≥ 1` curvature-difference asset (the "2a-hi" brick) recorded in
`UnifCurvatureJetsLow.md` and PLAN2 №71.  Nothing in this file depends on it, and nothing
here unblocks it.

## Superseding status (2026-07-31)

The zero-order witness has been made explicit and its quantifiers reordered.
The public packet now includes `vfZeroC`, `rhsZeroC`, `ksupZeroC`, their
nonnegativity lemmas, and the supplied-background-cap endpoints
`unifCovDerivVF_of`, `unifRHSBilin_of`, `unifRHSFib_of`, and
`unifKsupZero_of`.  Thus the zero-slot constant depends only on `gBase`, `Λ`,
and a background curvature cap chosen before `g₀`.

Focused and exact verification passed.  The old compatibility endpoints remain
available.  The `j = 1` obstruction described above was subsequently closed in
`UnifDeTurckRHSOne.lean`; it is no longer a live frontier.
