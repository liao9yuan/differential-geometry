# LieCorr0CoeffL2JetBound

New leaf (RULING 1, planner acceptance №19): the `TensorHilbert/` home of the
`lieCorr0Field` realizedFam jet-L2 top-separated producer (2nd genuinely-missing
`C₀` constituent of `Ψ₀`).  Namespace `DifferentialGeometry.Integral.Connection`.

## State (2026-07-25): dedup DONE; still blocked on LowJet WIP (not the diamond).

The TensorRS TotalSpace topology-instance diamond dedup (GPT Pro ruling,
`ShortTime/UNIF_DIAMOND_PRO_RULING.md`) is DONE + verified: Edit A (harden
`tensorRSBundle_fiber`'s explicit fibre-topology family, `RSTensor/Defs.lean`),
Edit B (3× `instance`→`def` in `…/TensorRSContRiemannianBundle.lean`), Edit C
(type-based audit — no additional alias). Probes green in both eta spellings /
both import contexts; Phase 2b (2743 jobs) + Phase 4 (9388-job rich-import cone)
GREEN — dedup is regression-free.

CORRECTION to the §D-ROUND / T1 classification below: the "≥3 competing
TotalSpace topologies" count was type-miscounted. There is ONE canonical
pointwise fibre topology (`tensorRSSpace_topologicalSpace`, KEEP), ONE canonical
TotalSpace topology (`tensorRSBundle_topology`, KEEP), one redundant TotalSpace
wrapper alias (demoted), plus a SEPARATE documented pointwise norm-topology
diamond (out of scope). Trust the ruling over the D-ROUND note.

The consumer chain still doesn't build, but NOT because of the diamond:
`LieCorr0Split` is now GREEN (dedup + a mechanical `set_option
backward.isDefEq.respectTransparency false`). `LieCorr0LowJet` (which THIS file
imports) is deep pre-existing WIP — syntax errors, embedded `sorry`s, unimported
symbols (`ccTensorBilinSymm`, `gFibreOpBound`), undefined `lieCorr0IVPerm`, and
genuine proof failures — a STOP beyond mechanical-hygiene scope. See
`LieCorr0LowJet.md`. So this leaf remains BLOCKED on LowJet, no longer on the
topology diamond.

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

## P3 REACHED (2026-07-24, ruling №21 probe) — RiemannianBundle pattern did NOT fix `.ext`; GPT Pro consult.

Applied the working-file preamble to Split's two `.ext` proofs (`insert_base`,
`lc0_decomp`):
```
letI : Bundle.RiemannianBundle (fun y : M => TensorRSSpace 2 2 I y) :=
  Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 2 2
```
`lake build +LieCorr0Split` (wait-poll cleared after ~5 min): the `letI`
elaborates with NO error, but the SUBSEQUENT `apply ContMDiffSection.ext`
STILL fails identically at :119 and :173. Reason: `Bundle.RiemannianBundle`
equips an existing bundle with a fiber inner product — it does NOT *provide*
the `FiberBundle` instance `.ext` needs. So the RiemannianBundle pattern is not
the fix; the working files get `FiberBundle` from their AMBIENT import cone, not
from a letI. Per ruling №21 P3: STOP for a GPT Pro consult.

### Consult diagnostic (exact goal / error / setups tried / clue)

- **Target lemmas:** `insert_base`, `lc0_decomp` in
  `Analysis/Spectral/Intrinsic/DeTurckCoefficients/LieCorr0Split.lean` — each an
  equality of two `SmoothCcTensor g₀ 2 2`, proved by
  `apply SmoothCcTensor.ext; apply ContMDiffSection.ext; …`.
- **Current goal at the failure:** `SmoothCcTensor.ext` succeeds (yields a
  `ContMDiffSection` equality); `apply ContMDiffSection.ext` then triggers
  typeclass synthesis of the fiber-bundle instance and fails.
- **Exact error (both sites):**
  `failed to synthesize  FiberBundle (TensorRSModel 2 2 ℝ E) fun x ↦ TensorRSSpace 2 2 I x`.
- **Setups tried, all failing to resolve it:**
  1. `import …Analysis.Spectral.Tensor.ChartTensor.Inner.TensorRSContRiemannianBundle`
     — provides the GLOBAL `instance tensorRSSpace_fiberBundle (r s : ℕ) :
     FiberBundle (TensorRSModel r s ℝ E) (TensorRSSpace r s I (M := M))`
     (namespace `DifferentialGeometry.Tensor.TensorRSRiemannianBundleContinuous`).
     `.ext` still fails. (Reverted the import.)
  2. `letI : FiberBundle (TensorRSModel 2 2 ℝ E) (fun x : M => TensorRSSpace 2 2 I x)
     := Tensor0SBundle.tensorRSBundle_fiber 2 2` — the `letI` elaborates, but the
     following `.ext` STILL reports the same synthesis failure.
  3. `letI : Bundle.RiemannianBundle … := Tensor0SBundle.tensorRS_riemannianBundle
     g₀ 2 2` (this probe) — same failure (currently left in the file as the
     reproducing setup).
- **KEY CLUE:** `Analysis/Sobolev/TensorHilbert/DeTurckLieKernelL2JetBound.lean`
  does the IDENTICAL `apply SmoothCcTensor.ext; apply ContMDiffSection.ext` at
  :82-83 with NO letI and BUILDS — `FiberBundle` resolves AMBIENTLY there. Its
  import cone is rich (CovGrad/`OperatorFieldFibreNormJet`,
  `IteratedCovGradFibreNormPermutationInvariance`, …); Split imports only
  `LieCorr0Core` + `RiemannCoefficientPalatiniRefold`.
- **Hypotheses for GPT Pro:** (i) eta / instance-form mismatch — the global
  instance's conclusion is the partially-applied `TensorRSSpace r s I (M := M)`
  while the goal is the eta-expanded `fun x ↦ TensorRSSpace 2 2 I x`, and
  synthesis won't bridge it; (ii) the `FiberBundle` synthesis needs the
  `TopologicalSpace (TotalSpace …)` prerequisite to resolve to the SAME topology
  instance the ambient file uses, which a competing topology instance in Split's
  (different) open/import context blocks. Recommended next: a
  `set_option trace.Meta.synthInstance true in` run on `insert_base` to see the
  exact rejected candidate.

STOPPED per P3. Split left with: hygiene opens + `← insert_base` + the two
RiemannianBundle `letI`s (reproducing setup); still does NOT build.
`LieCorr0LowJet` untouched. `(N)` 0%. No commit.

## D-ROUND RESULT (2026-07-24, ruling №21) — ROOT CAUSE = TopologicalSpace-instance DIAMOND (not eta).

Ran D1 (synthInstance trace) + D3 (import). D2 (eta letI) is RULED OUT by the
trace. Decisive trace excerpt (`insert_base`/`lc0_decomp` `.ext` FiberBundle synth):
```
6078  [synthInstance] result tensorRSSpace_topologicalSpace 2 2          -- goal's TotalSpace topology
6079  [synthInstance] ❌ FiberBundle (TensorRSModel 2 2 ℝ E) fun x ↦ TensorRSSpace 2 2 I x
6081    instances #[@tensorRSBundle_fiber, @…TensorRSRiemannianBundleContinuous.tensorRSSpace_fiberBundle]
6082  ❌ apply tensorRSSpace_fiberBundle
6084    tryResolve ❌ …fun x ↦ TensorRSSpace 2 2 I x  ≟  …(TensorRSSpace ?178 ?179 ?173)   -- eta-CONTRACTED fiber, no unify
6087  ❌ apply tensorRSBundle_fiber
6089    tryResolve ❌ …fun x ↦ TensorRSSpace 2 2 I x  ≟  …fun x ↦ TensorRSSpace ?180 ?181 ?175 x  -- eta OK, but…
6093  error: failed to synthesize FiberBundle …
```
Diagnosis: BOTH FiberBundle candidates are found and tried against the
eta-expanded goal. `tensorRSSpace_fiberBundle` is stated with the eta-CONTRACTED
fiber `TensorRSSpace ?r ?s ?I` and won't unify. `tensorRSBundle_fiber` IS stated
eta-expanded (`fun x ↦ TensorRSSpace ?r ?s ?I x`) and its fiber DOES unify — yet
`tryResolve` still ❌, because the goal's `TotalSpace` topology was already
resolved (line 6078) to **`tensorRSSpace_topologicalSpace`**, which is a
DIFFERENT instance than the one `tensorRSBundle_fiber` carries
(`tensorRSBundle_topology`). The `FiberBundle` type bakes the `TopologicalSpace
(TotalSpace …)` instance, so the two don't defeq-match ⟹ synthesis fails.

**Root cause = a `TopologicalSpace`-instance DIAMOND on
`TotalSpace (TensorRSModel r s ℝ E) (TensorRSSpace r s I)`** — at least three
competing instances are in scope (`tensorRSSpace_topologicalSpace`,
`tensorRSBundle_topology`, `…tensorRSSpace_totalSpace_topologicalSpace`; the
massive `synthInstance.instances` list at trace :2383). In Split's minimal
import context `tensorRSSpace_topologicalSpace` wins the topology race, but no
in-scope `FiberBundle` instance is paired with it. The working
`DeTurckLieKernelL2JetBound` avoids this only because its rich import context
makes the paired topology win.

- **D2 (eta letI): contraindicated** — `tensorRSBundle_fiber` is already
  eta-expanded and still fails on the topology, so an eta-form letI cannot fix it.
- **D3 (import `TensorRSContRiemannianBundle`): FAILED and WORSENED it** — it adds
  `tensorRSSpace_totalSpace_topologicalSpace` + `tensorRSSpace_fiberBundle` to the
  diamond; with it, even the four `lc0*` DEF constructions fail FiberBundle
  (:47/:58/:69/:80), not just the `.ext` proofs. Import reverted.
- **A `letI`-pin of the topology** (force `tensorRSBundle_topology` before the
  synthesis) could band-aid ONE `.ext` site — but this is a codebase-level
  instance diamond: **`LieCorr0LowJet` (1832 lines) uses `.ext` pervasively across
  its refolds, so it would need the pin at DOZENS of sites** (and any file
  building on this fiber inherits the diamond). That is not a bounded patch.

**This is a planner/codebase-owner (or GPT Pro) decision, not a mechanical
repair:** either (i) dedupe the competing `TotalSpace` topology instances so the
`FiberBundle` instance's topology is the unique/winning one (the clean fix, at
the bundle-definition layer — out of this lane's scope), or (ii) accept a
pervasive per-`.ext` topology-pin across Split + LowJet (band-aid). Full trace at
`scratchpad/split_trace.txt`. Split cleaned back to the hygiene state (opens +
`← insert_base`; import/letI/set_option all reverted); does NOT build. `(N)` 0%.
No commit.

## T1 (ruling №21, band-aid TEST) — paired topology+FiberBundle pin FAILED; band-aid (ii) is DEAD.

Installed the paired pin at both `.ext` sites (topology first, eta-expanded):
```
letI : TopologicalSpace (Bundle.TotalSpace (TensorRSModel 2 2 ℝ E) (fun x : M => TensorRSSpace 2 2 I x)) :=
  Tensor0SBundle.tensorRSBundle_topology 2 2
letI : FiberBundle (TensorRSModel 2 2 ℝ E) (fun x : M => TensorRSSpace 2 2 I x) :=
  Tensor0SBundle.tensorRSBundle_fiber 2 2
```
`lake build +Split` STILL fails FiberBundle at THREE sites: `:79` (the `lc0Riem`
DEF `toSection` construction — the diamond breaks the DEFS too, not just `.ext`;
earlier `tail`-truncated logs hid the def errors) and `:122`/`:179` (the two
PINNED `.ext` proofs). The `letI`s elaborate with no error, but do not fix synth.

**Why the band-aid cannot work (two independent reasons):**
1. The winning `TotalSpace` topology `tensorRSSpace_topologicalSpace` has **NO
   paired FiberBundle instance in scope** — the only two FiberBundle candidates
   pair with `tensorRSBundle_topology` and
   `…tensorRSSpace_totalSpace_topologicalSpace`. So even a correct topology pin
   points at a topology with no matching FiberBundle.
2. The `TotalSpace` topology is baked into `SmoothCcTensor` / `ContMDiffSection`
   at their UPSTREAM definitions; when the goal (a `SmoothCcTensor 2 2` equality,
   or the def's `toSection`) is formed, its FiberBundle-requirement topology is
   already fixed to the ambient winner — a LOCAL `letI` in the proof/def arrives
   too late to change it. Hence `:122`/`:179` fail even WITH the pin.

**Conclusion: band-aid (ii) is dead; only the clean fix (i) works** — align/dedupe
the competing `TotalSpace`-topology instances at the bundle-definition layer
(`RSTensor/Defs.lean` `tensorRSBundle_topology` / the `TensorRSContRiemannianBundle`
`tensorRSSpace_totalSpace_topologicalSpace` / `tensorRSSpace_topologicalSpace`) so
the FiberBundle instance's topology is the unique/winning one. That is a
bundle-layer / codebase-owner change, out of this lane. Split reverted to the
hygiene state (opens + `← insert_base`); does NOT build. T3 → GPT Pro consult.
`(N)` 0%. No commit.
