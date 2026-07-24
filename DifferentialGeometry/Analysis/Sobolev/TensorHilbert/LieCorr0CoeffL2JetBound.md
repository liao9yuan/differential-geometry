# LieCorr0CoeffL2JetBound

New leaf (RULING 1, planner acceptance №19): the `TensorHilbert/` home of the
`lieCorr0Field` realizedFam jet-L2 top-separated producer (2nd genuinely-missing
`C₀` constituent of `Ψ₀`).  Namespace `DifferentialGeometry.Integral.Connection`.

## State (2026-07-24): WRITTEN but BLOCKED-UNVERIFIED on a broken upstream dep.

Written so far (top piece + assembly helper — the decisive R-free-Ktop brick):
- `endoArm_eq_dlb`: `deTurckLieEndoArmField g₀ g₁ g_bg = deTurckLieDLbCoeffField
  g₀ g₁ g_bg` (both `ofCLM(deTurckLieDLbFib g₁ g_bg)`, by `ext` + the two
  `_toSection` simp lemmas).
- `lc0Insert_base_eq_neg_dlb`: `lc0Insert g₀ g₁ g₀ = −deTurckLieDLbCoeffField
  g₀ g₁ g₀` (from `insert_base` at `g_bg := g₀` + `sub_self` +
  `eq_neg_of_add_eq_zero_left` + `endoArm_eq_dlb`).
- `lc0InsertBase_realizedFam_perOrder_topSeparated`: the top piece's per-order
  top-separated bound, inherited verbatim from the DLb field producer
  `deTurckLieDLbCoeffField_realizedFam_jetL2_perOrder_topSeparated` at
  `g_bg := g₀`, via `lc0Insert_base_eq_neg_dlb` + `iteratedCovGrad_neg` +
  `norm_neg`.  `Ktop = Ktop_DLb` (R-free).
- `sq_le_five_add`: `t ≤ a+b+c+d+e` (all ≥0) ⟹ `t² ≤ 5(a²+…+e²)` (nlinarith,
  10 `sq_nonneg` cross terms) — the `lc0_decomp` five-summand triangle helper.

## BLOCKER (needs planner scope ruling) — upstream deps do NOT build.

`lake build` of the new leaf fails immediately: the imported
`LieCorr0Split.olean` / `LieCorr0LowJet.olean` do not exist in `C:/dgb2/e87b`,
and they cannot be produced because **both modules FAIL `lake build` under the
lakefile's `autoImplicit false`** — they are `lake env lean` FALSE-GREENs
(passed the read-only focused check with autoImplicit=true, per their `.md`s'
"focused verification passes"; never truly built).  This CORRECTS recon №19's
"the low pointwise machinery is PRE-BUILT" premise: it is committed but does not
compile.

- `LieCorr0Split.lean` — EXACT fix known, ONE line: it lacks
  `open DifferentialGeometry.Integral.L2` (present in `LieCorr0Core` and
  `LieCorr0LowJet`).  All 8 build errors are `Unknown identifier
  SmoothCcTensor` / `SmoothCcTensor.ext` (`:36 :47 :58 :69 :108 :160`, plus two
  cascade `No goals` at `:109 :161`) — every one resolved by that open.  No
  other issue.
- `LieCorr0LowJet.lean` — already has the open; UNKNOWN further depth (1832
  lines, never built; behind Split in the build order).  Must build it once
  Split is fixed to discover any residual `autoImplicit false` issues.

These two files are OUTSIDE the authorized editable set (new leaf + notes only),
so the fix requires a planner scope extension: authorize editing
`LieCorr0Split.lean` (+`LieCorr0LowJet.lean` if it needs cleanup) to add the
missing open(s) / autoImplicit-false fixes, OR have them repaired + rebuilt
upstream first.  Everything else in the entry plan (recon §"jetL2 top-separated
producer recon" in `LieCorr0Core.md`) is unchanged and ready.

## Verification
NONE possible yet — the leaf cannot be checked until Split/LowJet build.
`(N)` `ricci_flow_unif_existence` still 0%.

## UPDATE (2026-07-24, build phase after repair authorization) — Split repair EXCEEDS hygiene; STOP.

Planner authorized REPAIR of `LieCorr0Split`/`LieCorr0LowJet` (hygiene only:
opens/binders/implicit-arg plumbing; STOP if a proof genuinely fails).
Repairing `LieCorr0Split` (186 lines) surfaced, in order:
1. Missing `open …Integral.L2` (hygiene) — fixed; revealed →
2. Instance-synthesis failures at the four `SmoothCcTensor` record
   constructions — fixed by adding the rest of `LieCorr0Core`'s open set
   (`MeasureTheory Set Filter Topology ContinuousLinearMap`, scoped
   `ENNReal NNReal BigOperators Matrix`, and namespace opens
   `Integral.Connection/Measure`, `MetricRealization`, `RicciLinearization`,
   `DivergenceTheorem`, `TensorRegularity`, `DeTurckCoefficients`) — hygiene.
3. `tail_base_split` proof genuinely failed: `rw [insert_base]` found no
   pattern (after `lc0_decomp` the `lc0Insert+endoArm` pair is non-adjacent).
   Fixed by `rw [← insert_base]` (statement-sound; one-token, non-refold).
4. `insert_base` and `lc0_decomp` `.ext` proofs fail
   `failed to synthesize FiberBundle (TensorRSModel 2 2 ℝ E) (fun x ↦
   TensorRSSpace 2 2 I x)`.  THREE routes tried, all failed to resolve it:
   (a) import the providing module
   `…ChartTensor.Inner.TensorRSContRiemannianBundle` (its global
   `tensorRSSpace_fiberBundle` instance) — still not synthesized;
   (b) `letI := tensorRSSpace_fiberBundle 2 2` — unknown identifier (that
   wrapper is in `DifferentialGeometry.Tensor.TensorRSRiemannianBundleContinuous`,
   not `TensorSpectral`);
   (c) `letI : FiberBundle … := Tensor0SBundle.tensorRSBundle_fiber 2 2`
   (elaborates) — the subsequent `.ext` STILL fails to synthesize the SAME
   FiberBundle type.  The working TensorHilbert files (e.g.
   `DeTurckLieKernelL2JetBound` `.ext` at :82) resolve it automatically, and
   elsewhere set up `letI : Bundle.RiemannianBundle … := tensorRS_riemannianBundle
   g r s` (metric-dependent).  So the fix is a coherent RiemannianBundle
   bundle-instance setup, NOT a bare-FiberBundle letI — this is genuine
   instance-resolution/bundle-setup plumbing, past "missing opens/binders".

VERDICT: the drafts are genuinely uncompiled (`lake env lean` FALSE-GREEN was
hiding real breakage, not one open).  `LieCorr0Split` alone needs opens + a
proof-direction fix + non-trivial bundle-instance setup for every `.ext` proof.
`LieCorr0LowJet` (1832 lines) uses `.ext` PERVASIVELY across its refolds
(`vb_refold`/`amix_refold`/`riem_refold` + the `_diff`/`_fiber` helpers) — the
same bundle-setup × many, plus unknown further issues.  Per the planner's
guardrail (proof genuinely fails, not hygiene → STOP; unsound drafts = planner
decision, not a patch), STOPPED.  `LieCorr0Split` left with the correct hygiene
portion applied (opens + `← insert_base`); it still does NOT build (FiberBundle).
`LieCorr0LowJet` untouched.  Reverted my non-working import + FiberBundle-letI
attempts.  `(N)` still 0%.

DECISION NEEDED: (a) authorize the full bundle-instance-setup repair of both
drafts (bounded-but-extensive `RiemannianBundle` letI plumbing per `.ext` +
whatever else surfaces — this is repairing unverified 3rd-party drafts, not the
lieCorr0 mathematics); OR (b) have the drafts' author/Codex rebuild + truly
verify `LieCorr0Split`+`LieCorr0LowJet` (they never compiled), then I resume the
leaf per the ratified plan (top piece + Kc + assembly).  Re-deriving the LowJet
refold/grid layer fresh in the leaf is not viable (it is the whole low-jet
machinery — forbidden parallel API).
