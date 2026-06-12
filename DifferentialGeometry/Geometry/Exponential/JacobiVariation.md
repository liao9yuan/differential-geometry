# JacobiVariation.lean — radial expMap variation is a Jacobi field (B0 stage 2)

Goal: `exists_radial_jacobi_radius` — around every `p` a radius `r > 0` such that
for `‖x‖, ‖w‖ < r` the field `J v = ∂ₛ|₀ expMap g p (v•(x+s•w))` satisfies
`IsJacobiAt g γ J t₀` along `γ v = expMap g p (v•x)` for every `t₀ ∈ (0,1)`.
This is MSM135 Ch.4 / B0 stage 2 (see `HCGCompactness/B0NormalCoordBounds.md` for
the whole-route spec and status).

## Route (decided 2026-06-10)

- The W=∂_t covariant commutation `[∇_s∇_t − ∇_t∇_s](∂_t f) = R(∂_s f, ∂_t f)∂_t f`
  at `s = 0` ALREADY EXISTED: `commute_ds_dt_curvature`
  (`Comparison/Variation/CovariantCommutationCurvature.lean:759`) — it was `private`
  and unused.  De-privatized (visibility-only edit; file + targeted build verified).
  Do NOT re-prove it; its `houterL`/`houterR` hypotheses are the intended inputs.
- It needs a GLOBAL `IsSmoothVariation` (degree-8 `ContMDiff` on ℝ²).  The radial
  variation is globalised by clamping BOTH parameters with
  `exists_smooth_clamp` (`Analysis/Calculus/SmoothClamp.lean`, NEW, verified):
  a `C^∞` bounded clamp that is the IDENTITY on `[a,b] ∋ [0,1]` (bump-integral).
  Degree-8 expMap regularity on a small ball: `Exponential.expMap_contMDiffAtN_of_norm_lt`.
- `houterL` discharge: the inner field `s ↦ ∇_t∂_t F(s,·)|t₀` vanishes identically
  (clamped slices satisfy the geodesic equation at interior parameters —
  `clamped_slice_covDeriv_velocity_zero`, via
  `radial_hasGeodesicEquationAt_of_norm_lt_radius` + rescale +
  `HasGeodesicEquationAt.congr_of_eventuallyEq_at` +
  `covDerivAlong_velocity_eq_zero_of_hasGeodesicEquationAt_C2`).
- `houterR` discharge: pointwise symmetry `commute_ds_dt_intrinsic` (∀v) +
  `variationField_covDeriv_chartRep_differentiableAt` (public, CovariantCommutationCurvature:1187).
- Transfer clamped → clean radial objects by germ congruence:
  `covDerivAlong_congr_curve` (NEW here: curve+section eventual congruence, stated
  E-valued so no dependent-type motive issues), `Filter.EventuallyEq.mfderiv_eq`,
  and `riemannOp_congr_point` (subst-based point transport with E-valued slots).

## Status

- 2026-06-10 (later): **stage 2 FULLY DONE.** Added the second initial condition
  **`exists_radial_jacobi_deriv_radius`** (`D_t J(0) = w`), VERIFIED GREEN, plus the
  reusable **`covDerivAlong_const`** (covariant derivative along a constant curve =
  ordinary derivative). De-privatized `radialCurve_launch_velocity` in
  `GaussLemmaPullback.lean` (visibility-only; olean rebuilt). Route: at `t = 0` the
  transverse curve `s ↦ F s 0` is constant `p` (clamped launch radius `ψ 0 = 0`), so
  `commute_ds_dt_intrinsic` turns `D_t J(0)` into the constant-curve covariant
  derivative of the launch field `s ↦ x + φ(s)·w`, which is the ordinary deriv
  `φ'(0)·w = w`. The two `covDerivAlong_congr_curve` transfers (RHS→clean, LHS→const)
  reuse the same clamped `F` setup as the main theorem (duplicated inline; see
  "future cleanup" below).
- 2026-06-10: **`exists_radial_jacobi_radius` VERIFIED GREEN**, plus the endpoint
  lemmas **`radial_jacobi_zero`** (`J 0 = 0`) and **`radial_jacobi_one`**
  (`J 1 = mfderiv (expMap g p ·) x w`) — file lint-clean, zero warnings.
  SmoothClamp + JacobiField (`IsJacobiAt` pointwise predicate added) green.
  De-privatized `commute_ds_dt_curvature` green; the FULL downstream chain
  (SecondVariation, RegularParameterFirstVariation, GaussLemmaPullback, the whole
  Exponential tree) rebuilt green against it — the visibility change is
  downstream-safe (the private name had no users).
- First-check error patterns worth remembering: `expMap` lives in namespace
  `…Riemannian.Exponential` (NOT bare `…Riemannian`, unlike `expMapC2Radius`) —
  needs the file-level `open`; the `@[simp] covDerivAlong_zero` did not fire
  through `simp` against a β-annotated zero section (`(0 : TangentSpace I ((fun
  s' => F s' t₀) s))`) — `exact covDerivAlong_zero …` with explicit curve closes
  it; two `rw`-chains ended at syntactically reflexive goals that auto-rfl did
  not close — append explicit `rfl`.
- What WORKED first try (the risky parts): the E-valued curve+section congruence
  `covDerivAlong_congr_curve` (subst-helper for mixed-foot
  `continuousLinearMapAt` rewrites; `show`-from-by-rw for the `symmL` CLM
  equality), the `riemannOp_congr_point` subst helper with model-space slots,
  `Filter.EventuallyEq.mfderiv_eq` across propositionally different feet, the
  degree-8 `IsSmoothVariation` from clamps + `expMap_contMDiffAtN_of_norm_lt`
  (cast via `exact_mod_cast`), and the full `commute_ds_dt_curvature`
  application with both houter dischargers.

## Remaining (after stage 2)

- `g_{ij}(x) = ⟨J_i, J_j⟩(1, x)` metric pullback identification: now essentially a
  one-liner from `radial_jacobi_one` (rewrite `mfderiv (expMap g p ·) x eᵢ` to
  `Jᵢ(1)` in both slots of `g.inner (expMap g p x) · ·`); deferred until the
  component/normal-chart API is in play downstream (avoid a content-free wrapper).
- **Stage 4** (the real mass): pull `J` back through a parallel orthonormal frame
  `P_{t,x}` to `Y = P⁻¹J` solving `Y'' + A Y = 0`, `‖A‖ ≤ C₀|x|²`; ICs `Y(0)=0`,
  `Y'(0)=w` are exactly `radial_jacobi_zero` + `exists_radial_jacobi_deriv_radius`;
  differentiate in `x`, Grönwall (`norm_le_gronwall_secondOrder`), conclude
  `|∂^α g_{ij}| ≤ C̃_α`. Stage 3 (parallel frame) is `Comparison/Variation/
  ParallelTransport.lean` (exists, 0-sorry) modulo x-smoothness if stage 4 needs it.
- note: the Jacobi equation is proved on `Ioo 0 1` only (rescale identity lives on
  `Icc 0 1`); the Grönwall stage can start from `[ε, 1]` + continuity, or the
  rescale lemma can be strengthened later.

## Future cleanup

- `exists_radial_jacobi_radius` and `exists_radial_jacobi_deriv_radius` both inline
  the same clamped-variation setup (clamps `ψ`/`φ`, radius `δ/26`, `F`, `hFsmooth`,
  the window agreements `hcentral_eq`/`hJ_eq`). Factor a private
  `exists_radial_clamped_variation` helper returning `F` + those facts and have both
  consume it. Deferred to keep the green proofs untouched while the route settled.
- `covDerivAlong_const` is general enough to live in
  `Connection/ParallelTransport/CovariantDerivativeAlong.lean` (next to
  `covDerivAlong_zero`); kept local for now (surgical, one consumer).

## Lean lessons (this file)

- `expMap` is in namespace `…Riemannian.Exponential`; `expMapC2Radius` in bare
  `…Riemannian` — both opens needed.
- The β-reduced foot problem: `mfderiv_comp`-family conclusions β-reduce
  `(fun s => x + s•w) 0` to `x + 0•w`, which `rw` cannot match against the
  written form, and numerals in CLM-argument slots elaborate at the
  `TangentSpace` synonym type (different `OfNat` path than `(1 : ℝ)`), so `rw`
  by an applied-CLM equation can silently fail to find the pattern.  Robust
  pattern: build the chain with `have`-pinned statements + `Eq.trans` /
  `congrArg (fun L : E →L[ℝ] E => L w)` (defeq-tolerant `exact`s), and
  transport CLM feet with an `E →L[ℝ] E`-ascribed equation proved by
  `rw [hfoot]`.
- `mfderiv_comp_apply` needs `(f := …) (x := …)` named args (higher-order
  unification cannot invert `(f x)`).
- `simp` may refuse (`no progress`) on `(smulRight 1 w) 1 = w` — use the gauss
  pattern `change` + `rw [smulRight_apply, one_apply, one_smul]`.

## NEXT BRICK (2026-06-11, B3 regularity export — blueprint for continuation)

Goal: export, for the CLEAN radial objects (`γ v = expMap p (v•x)`,
`J v = ∂ₛ|₀ expMap p (v•(x+s•w))`), the chartRep-differentiability needed by
`covGronwall_ne_zero` (`Variation/CovariantGronwall.lean`):
`hJdiff`/`hDJdiff` : ∀ t ∈ Icc 0 b (b < 1), DifferentiableAt ℝ (chartRepAt γ J/DJ t) t.

Route (all machinery exists; mimic `exists_radial_jacobi_radius`'s transfer):
1. Rebuild the clamped variation `F s t = expMap p (ψ t • (x + φ s • w))` with
   the same norm budget (δ/26); `hJ_eq`-style: clean J = clamped ∂ₛF on the open
   window `Ioo (-1) 2` ⊇ Icc 0 b (germ argument at each v: `hgerm` +
   `mfderiv_congr_of_eventuallyEq`-style as in the file).
2. Clamped `∂ₛF`'s chartRep-diff at each t: `slice_transverseVelocity_chartRep_…`
   / the `chartCoord_transverseVelocity_contDiffAt` C² lemma
   (CovariantCommutationCurvature.lean) at the slice `s = 0`, any `t`.
3. Transfer by `chartRepAt_eventuallyEq_of_eventuallyEq` (ParallelTransport.lean:939)
   + `Filter.EventuallyEq.differentiableAt_iff`.
4. Same for `DJ = covDerivAlong γ J`: clamped counterpart's diff =
   `variationField_covDeriv_chartRep_differentiableAt` (CovariantCommutationCurvature
   :1193, check it is t-general); equality of fields on the window from `hDJ_ev`
   (in-file pattern) + `covDerivAlong_congr_of_eventuallyEq` (ParallelTransport:948).
5. ALSO export `hODE`-side: `D²J(0) = 0` (the t=0 Jacobi-equation endpoint) —
   needs continuity of `D²J` at `0` (NOT yet available; if hard, leave as the one
   hypothesis and document).

Consumers after this brick: instantiate `covGronwall_ne_zero` with
`exists_parallel_frame` (PerpFrame) seeds from `exists_gOrthonormalBasis`,
ICs `radial_jacobi_zero` + `exists_radial_jacobi_deriv_radius`, hODE from
`exists_radial_jacobi_radius` (Ioo 0 1) + curvature-norm input + the t=0 point,
endpoint `radial_jacobi_one` ⟹ `d(exp)_x` injective below the Grönwall scale.
Then (d) the manifold IFT at `v ≠ 0` ⟹ `IsLocalDiffeomorphOn` ⟹
`exists_expBall_diffeo`'s `hloc` (Step A item 3a complete modulo B4/B5).

### Brick progress (2026-06-11, live)
- Step A DONE: `chartCoord_transverseVelocity_contDiffAt` de-privatized
  (CovariantCommutationCurvature.lean, visibility-only, re-verified green).
- Step B IN PROGRESS: the regularity-export theorem in JacobiVariation.lean.
  ACTIVE CLAIM on JacobiVariation.lean: token bca77123-4994-4b4b-88ce-d9c5b2bc4953
  (release with `./scripts/lake-locked.ps1 release -Token bca77123-...` when done).

### OBSTRUCTION discovered (2026-06-11, before writing the export theorem)

The instantiation plan hits a smoothness-ORDER mismatch:
- `exists_parallel_transport_on_Icc` / `exists_parallel_frame` demand
  `hγ : ContMDiff 𝓘(ℝ,ℝ) I ∞ γ`;
- the radial curve's smoothness comes from `expMap_contMDiffAtN_of_norm_lt`
  (OffZero.lean:994) — per FINITE order `n` with an `n`-DEPENDENT radius `δ(n)`;
  no `∞`-order statement on a uniform ball exists, and the clamped variation is
  only `IsSmoothVariation` (degree 8).

Resolution options (design choice for the next session):
1. **Weaken the transport producers to finite order** (recommended first check):
  inspect what order `exists_parallel_transport_on_Icc`'s PROOF actually
  consumes (parallel-transport ODE plausibly needs only low order, ≤ 8);
  changing `∞` to that order in the hypothesis is a statement-strengthening
  (more general) edit, then the clamped/clean curves qualify.
2. Prove `expMap` is `ContMDiffAt ∞` on a uniform small ball (true — geodesic
  flow is `C^∞`; the per-`N` radius is a construction artifact) — bigger.
3. Build an order-8 variant of the frame producer.
Status: regularity-export theorem NOT started (obstruction precedes it);
no `sorry` introduced anywhere. Claim on JacobiVariation.lean RELEASED.

### Resolution-1 recon (2026-06-11, order audit of the transport chain)

`hγ : ContMDiff … ∞` is consumed in the chain ONLY as:
- `hγ.continuous` (chart preimages, overlap consistency) — order-free;
- ONE composition `hφ.comp hγ.contMDiffOn` (exists_piece_parallel_section,
  the chart-curve regularity feeding the parallel ODE) — works at ANY order
  the chart composition supports (the ODE needs low order).
⟹ weakening `∞ → (n : ℕ∞)` (with `1 ≤ n`, or fixed `8` matching
`IsSmoothVariation`) across `exists_piece_parallel_section`,
`parallel_transport_unique_of_eq_at_point`,
`exists_global_parallel_transport_on_Ioo`, `exists_parallel_transport_on_Icc`,
`parallel_transport_preserves_inner_product` (check its own hγ uses), and
`PerpFrame.exists_parallel_frame` is a mechanical signature+proof-order edit —
the FIRST brick of the next session. Then the clamped radial curve (degree 8)
qualifies directly, and the regularity-export brick proceeds per the blueprint
above.
