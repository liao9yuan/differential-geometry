# MetricCovDerivLinear

## 2026-06-21

This file contains linearity and smooth-slot evaluation helpers for the
metric-covariant tower.

What is verified:

- `metricCovDeriv_succ_eval_smooth_slots_gen` is the boundaryless-free
  successor-slot evaluation formula for `metricCovDeriv`.
- The theorem exposes the same decomposition used by the private pullback proof:
  leading scalar directional derivative minus the finite sum of Levi-Civita
  correction terms.
- The formula is now reusable by open-subtype restriction and other locality
  arguments without importing the pullback-specific HCG bridge.

Verification passed.  No blocker remains in this helper file.

## 2026-07-24 — brick T eval gate: generic-rank `diffStep` evaluation (LANDED)

Added two theorems that CROSS the generic-rank tensor-bundle EVAL instance gate that had
blocked brick T's norm layer (`UnifCovSumCross.md` §Session 4).  Both sorry-free, axioms
`[propext, Classical.choice, Quot.sound]`, `lake build +…MetricCovDerivLinear` EXIT=0 (3633
jobs).

- **`diffStep_apply`** (section form, the eval gate proper).  For smooth vector fields `X`
  (leading slot) and `V : Fin s → …` (lower slots),
  `diffStep g₁ g₂ s S x (Fin.cons (X x) (V · x)) = −∑ₐ (S x)(update (V·x) a ((Γ₁−Γ₂)(V a x))(X x))`,
  where `Γ₁−Γ₂ = CovariantDerivative.difference (LC g₁) (LC g₂) x`.  This is the generic-`(0,s)`
  lift of `Tensor0SBundle.nabla0SFun_sub_cov` to the bundled field.
  Proof (route r1, ~15 lines): unfold `diffStep = covStep g₁ − covStep g₂` at the section level
  (`ContMDiffSection.coe_sub` + `Pi.sub_apply`), split the fibre sub-apply by `change` (defeq for
  `Tensor0SSpace = Bundle.continuousMultilinearMap`), rewrite each `covStep … x` by
  `covStep_apply` then `totalNabla0SFun_apply_section`, and close with `nabla0SFun_sub_cov`.
- **`diffStep_eval`** (pointwise form, arbitrary tangent vectors — the form the norm route
  consumes).  `diffStep g₁ g₂ s S x (Fin.cons v slots) = −∑ₐ (S x)(update slots a ((Γ₁−Γ₂)(slots a))(v))`
  for ANY `v, slots`.  Proof: every tangent vector is a global smooth-field value
  (`Geometry.Riemannian.exists_contMDiff_vectorField_eq`, `[T2Space M]`); bundle via
  `ContMDiffSection.mk`, apply `diffStep_apply`, and `simp only [coeFn_mk, hXv, hVv]` (the RHS
  Γ-difference slot sum depends only on the values).  Needed one new import
  `…Geometry.Metric.SmoothVectorFieldExtGlobal`.

### Why the gate was crossable HERE (instance lessons)
The §Session-4 blocker ("`NormedSpace ℝ (Tensor0SModel (s+1) ℝ E)` / `FiberBundle …` won't
synth at variable rank `s+1`") did NOT need any `attribute [-instance]` removal set.  Root
cause: `UnifCovSumCross.lean` lacked `set_option backward.isDefEq.respectTransparency false`;
THIS file carries it (line 7), and with it `totalNabla0SFun_apply_section` elaborates at variable
rank exactly as `metricCovDeriv_succ_eval_smooth_slots_gen` already did at rank `a+2`.  So route
(ii) of §Session-4 was correct and the removal-set worry (route (i)) was a non-issue.
Concrete instance haveIs the proof needs (copied from `covStep`'s own def):
`IsManifold I 1 M`, `IsManifold I 2 M`, `IsManifold I (∞+1) M` (`change IsManifold I ∞ M`),
plus `IsManifold I (1 + 1) M` and
`haveI : ContMDiffVectorBundle 1 E (TangentSpace I) I := TangentBundle.contMDiffVectorBundle (n := 1)`
(this last needs `IsManifold I (1 + 1) M` — NOT defeq to the `IsManifold I 2 M` haveI, so both
are required; `nabla0SFun_sub_cov` demands `[VectorBundle …]` + `[ContMDiffVectorBundle 1 …]`
which are `variable`-declared upstream, not auto-synth from `IsManifold`).

### Remaining T-A / T-B (not in this file; norm layer lives in `UnifCovSumCross.lean`)
`diffStep_eval` unblocks `diffStep_norm_le` but does not finish it.  The norm atom still needs:
(a) a `gBase`-orthonormal frame at `x` (`Module.Basis` + `hON`/`MetricInverseInBasis_gen`) to run
`normSq0S_identity_eq_sum_sq` / `abs_apply_le_sqrt_normSq0S`; (b) the raw connection-difference
component Cauchy–Schwarz bounding `|(Γ₁−Γ₂)(u)(w)|_{gBase}` by
`√normSqRS(connectionDifferenceTensorAt)·|u|·|w|` (the sharp-constant-`s` route, ~100 lines
Finset). Then T-B base-Leibniz remains the multi-session frontier.

## 2026-07-25 — brick T-B: base-connection Leibniz split (committed currency, LANDED)

Added the identity-layer core of the base-Leibniz.  All pure operator algebra (no bundle-derivative
work, no `∇₂A` materialisation), so they are cheap and green; full design + frontier in
`UnifCovSumCross.md` §Session 8.

- `covStep_smul` / `covStep_sub` — complete the `covStep` linearity API next to `covStep_add`
  (`covStep_sub` via `sub_eq_add_neg` + `covStep_add` + `neg_one_smul` + `covStep_smul`, mirroring
  `covDerivOfField_sub`; `covStep_smul` via `covStep_apply` + `totalNabla0SFun_smul`).
- **`diffStep_leibniz`** — `covStep g₂ (s+1) (diffStep g₁ g₂ s S) = diffStep g₁ g₂ (s+1) (covStep g₂
  s S) + (covStep g₂ (covStep g₁ S) − covStep g₁ (covStep g₂ S))`.  Term1 = the `A⋆(∇₂S)` half
  (committed `diffStep`); Term2 = the mixed second-derivative commutator `∇₂∇₁S − ∇₁∇₂S = (∇₂A)⋆S`
  (the `∂∂S` symbols cancel).  Proof: `simp only [diffStep]; rw [covStep_sub]; abel`.
- **`iterCov_succ_diffStep`** — `iterCov g₁ (N+1) = covStep g₂ (iterCov g₁ N) + diffStep g₁ g₂
  (iterCov g₁ N)` (`∇₁ = ∇₂ + (∇₁−∇₂)`), the base-connection recursion driver.  Proof:
  `rw [iterCov_succ]; simp only [diffStep]; abel`.

The single remaining frontier is `mixedComm_norm_le` (the `∇₂A` bound on Term2), which needs the
genuinely-unbuilt covariant derivative of `connectionDifferenceTensorAt` — see `UnifCovSumCross.md`
§Session 8 route (F1).
