# DirectLimitManifold.lean — notes (MSM135 Ch4 Step D, D3 = `lbl408`)

The smooth/manifold structure on the sequential topological direct limit
(`Geometry/Topology/DirectLimit.lean`'s `SeqSystem`/`Lim`, consumed read-only).
Abstract infrastructure, no Step A/B/C imports (promotability acceptance test PASSES:
imports are Mathlib manifold + `DirectLimit` + `FiberBundleT2` + `Metric/Basic` +
`Bundle/ClmSectionSmooth` — general layers only).

## State (2026-07-07, 3rd session): **D3 COMPLETE — D3d metric transport DONE, all of D3a–D3e green**

Full `lake build` green (2738 jobs), zero warnings, axiom-clean
(`limitPointedCoc`, `limitMetric`, `limitMetric_pullback`, `stageInner_congr`,
`contMDiffAt_invIncl` all `[propext, Classical.choice, Quot.sound]`, no `sorryAx`).

### D3d — `SmoothSeqSystem.limitMetric` (the `g∞` construction), landed this session
Given `g : ∀ k, SmoothRiemannianMetric I (A k)` and the isometry cocycle
`MetricCocycle g` (`(F h)^* g ℓ = g k` pointwise on inner products — D2c's conclusion shape;
honest-input three-part note in its docstring), `limitMetric g hg : SmoothRiemannianMetric I S.Lim`
with the defining pullback property `limitMetric_pullback : (incl k)^* g∞ = g k`.

Route (all four planned ideas worked):
- **No derivative inverses anywhere**: the fiber form is the *pullback along the smooth local
  inverse* `φ_k := Function.invFun (incl k)` — `stageInner g k z := (precomp (mfderiv φ_k z)) ∘
  ((g k).inner (φ_k z)).comp (mfderiv φ_k z)`, verbatim the `Diffeomorph.pullbackInner` shape with
  `Φ` replaced by `φ_k`.  `contMDiffAt_invIncl` proves `φ_k` is `C^∞` on the open range (it agrees
  there with `(chartAt H a).symm ∘ limChart k a`).
- **Stage-independence** (`stageInner_mono`/`stageInner_congr`): the FORWARD factorization
  `F_{k≤m} ∘ φ_k =ᶠ φ_m` near the range of `incl k` (no `invFun F` needed!), then
  `EventuallyEq.mfderiv_eq` + `mfderiv_comp` + the cocycle at the point `φ_k z`.  Base-point
  mismatches (`φ_k (incl k a) = a` etc., propositional because `invFun` is choice-based) are
  crossed by two subst-based helpers `inner_base_eq`/`mfd_base_eq` stated at ascribed type
  `E →L[ℝ] E →L[ℝ] ℝ` (TangentSpace ≡ E definitionally) — no dependent-`rw` fights.
- **`symm`/`pos`/`isVonNBounded`** at the chosen representative stage (`rep z`), via the generic
  chain-rule helper `mfd_comp_id` (`g' ∘ f =ᶠ id near x ⟹ mfderiv g' ∘ mfderiv f = id`):
  `pos` from injectivity of `mfderiv φ_k` (left-composed to id by `mfderiv (incl k)`),
  bounded-set via image under `mfderiv (incl k)` + `IsVonNBounded.image`.
- **`contMDiff` (the flagged wall — dissolved by the test-section engine)**:
  `cotangentCov_clmSection_smooth_aux` (PUBLIC, `Bundle/ClmSectionSmooth.lean`, works on any
  σ-compact T2 manifold — Lim qualifies) applied twice reduces the metric-section smoothness to
  scalar smoothness against arbitrary smooth tangent sections `Y W`; at each `z₀` localize to the
  stage `k₀ := (rep z₀).1` (`stageInner_congr` on the open range — this is where the cocycle
  enters smoothness), then the stage scalar is `clm_bundle_apply₂` (At-version) of
  `(g k₀).contMDiff ∘ φ` against `z ↦ ⟨φ z, mfderiv φ z (Y z)⟩`, the latter smooth via
  `ContMDiffOn.contMDiffOn_tangentMapWithin` (with `IsOpen.uniqueMDiffOn`, `le_rfl` for `∞+1 ≤ ∞`)
  + `mfderivWithin_of_isOpen`; extract the scalar by `contMDiffAt_totalSpace` and rebundle by
  `Bundle.contMDiffAt_section` (trivial-bundle readout is the bare scalar, `rfl`).

### Lean lessons (this session)
- `TotalSpace.mk'` cannot infer the bundle family from a dependent fiber value — annotate
  `(E := fun b : A k₀ => …)` at every `mk'` in `have`-statements.
- `ContMDiffAt.comp` produces the `∘`-form; restate via `have h := …; exact h` to defeq-cast to
  the λ-form the next combinator expects.
- `Bundle.contMDiffAt_section` is in namespace `Bundle` (file opens `Set Topology` only).
- `∞ + 1 ≤ ∞` in `WithTop ℕ∞` is `le_rfl` (defeq `⊤ + 1 = ⊤` inside the coercion).

## State (2026-07-07, 2nd session): D3a + D3b + **D3c COMPLETE** + D3e assembly GREEN, axiom-clean

## State (2026-07-07): D3a + D3b + **D3c COMPLETE** + D3e assembly GREEN, axiom-clean

`#print axioms` on all capstones (`instIsManifoldLim`, `instChartedSpaceLim`,
`transitionHomeo_contMDiffOn`, `FiberBundle.t2Space_totalSpace`, `instT2SpaceTangentBundleLim`,
`limitPointed`) = `[propext, Classical.choice, Quot.sound]` (no `sorryAx`).  Full `lake build` green.

**Update 2026-07-07 (2nd session):**
- **D3c COMPLETED** — `T2Space (TangentBundle I S.Lim)`.  The missing producer was a general
  topology fact: NEW `Geometry/Topology/FiberBundleT2.lean` `FiberBundle.t2Space_totalSpace`
  (`[T2Space B] [T2Space F] [FiberBundle F E] ⟹ T2Space (TotalSpace F E)`; ~35 lines: same base
  point → separate inside a trivialization's source (open embedding into the `T2` product `B × F`),
  different base point → pull back separating base opens).  Corollary instance
  `SmoothSeqSystem.instT2SpaceTangentBundleLim` fires it automatically (`IsManifold I 1` lowered
  from `∞` for the tangent `FiberBundle` structure; fibre `E` normed hence `T2`).
- **`SmoothSeqSystem.contMDiff_incl`** — the stage inclusion `incl k : A k → S.Lim` is `C^∞` (in the
  atlas it reads as the identity: `incl k =ᶠ (limChart k a).symm ∘ chartAt a`, both `C^∞` via the
  maximal atlas).  A D3d/D4 prerequisite.
- **D3e — `C4/StepDLimit.lean` `limitPointed`** — assembles the `PointedRiemannianManifold` bundle
  (carrier `S.Lim`, basepoint `incl 0 O₀`, metric `ginf` supplied as input).  ALL structure fields
  (`charted`/`smooth`/`sigmaCompact`/`t2`/`t2TangentBundle`) auto-synthesize from the D3a–D3c
  instances; sorry-free, conditional only on the `ginf` input (= the D3d producer).

## State (2026-07-07, 1st session): D3a + D3b + D3c-part GREEN, axiom-clean, real `lake build`

`#print axioms` on `instIsManifoldLim`, `instChartedSpaceLim`, `transitionHomeo_contMDiffOn`
= `[propext, Classical.choice, Quot.sound]` (no `sorryAx`). Full `lake build` green (2329 jobs).

### DONE
- **D3a — `SeqSystem.instChartedSpaceLim : ChartedSpace H S.Lim`.** Charts `limChart k a :=
  (inclHomeo k).symm ≫ chartAt H a`, where `inclHomeo k := (incl_isOpenEmb k).toOpenPartialHomeomorph
  (incl k) : OpenPartialHomeomorph (A k) Lim`. `chartAt z := limChart (rep z).1 (rep z).2` with
  `rep z` a `Classical.choose` representative (`exists_sigma_incl`). Supporting: `inclHomeo_{apply,
  source,target,symm_apply}`, `mem_limChart_source`, `mem_atlas_iff`, `chartAt_lim`.
- **`SmoothSeqSystem I A` structure** (extends `SeqSystem`): factors are `C^∞` manifolds; fields
  `contMDiff_F` (each `F h` is `ContMDiff`) + `contMDiffOn_invFun_F` (its inverse `Function.invFun
  (F h)` is `ContMDiffOn` on `range (F h)`) — i.e. the `F h` are `C^∞` diffeos onto open images
  (the book's `Ψ_k`). Needs `[∀ k, Nonempty (A k)]` (honest: the balls contain their centres).
- **D3b crux `transitionHomeo_contMDiffOn` (`lbl409`).** The factor transition
  `transitionHomeo k ℓ := (inclHomeo k) ≫ (inclHomeo ℓ).symm : OpenPartialHomeomorph (A k) (A ℓ)`
  is `ContMDiffOn` on its source. On the overlap it equals `Function.invFun (F_{ℓ≤m}) ∘ F_{k≤m}`
  (`m = max k ℓ`), proved via `incl`-injectivity at stage `m` + `incl_comp` + `leftInverse_invFun`,
  then `ContMDiffOn.comp` of the two smooth pieces. This is the mathematically meaningful content.
- **`limChart_symm_trans`**: the Lim-chart transition `(limChart k a)⁻¹ ≫ (limChart ℓ b)` equals
  `(chartAt a)⁻¹ ≫ (transitionHomeo k ℓ) ≫ (chartAt b)` ON THE NOSE (`trans` associative,
  `trans_symm_eq_symm_trans_symm` is `rfl`, `symm_symm`).
- **`modelSpace_contDiffOn`** (model-space bridge, `[Nonempty H]`): `ContMDiffOn I I ∞ (f : H → H) s`
  ⟹ `ContDiffOn ℝ ∞ (I ∘ f ∘ I.symm) (I.symm ⁻¹' s ∩ range I)` — the exact `contDiffPregroupoid`
  form `isManifold_of_contDiffOn` consumes. Route: `contMDiffOn_iff_of_subset_source'` (single model
  chart, `extChartAt I x₀ = I`) + `ModelWithCorners.image_eq` (`I '' s = I.symm ⁻¹' s ∩ range I`) +
  `extChartAt_coe`/`extChartAt_coe_symm`/`chartAt_self_eq`.
- **D3b — `SmoothSeqSystem.instIsManifoldLim : IsManifold I ∞ S.Lim`.** `isManifold_of_contDiffOn`;
  each transition → `limChart_symm_trans` → `modelSpace_contDiffOn` of `ContMDiffOn T'` (compose
  `contMDiffOn_chart_symm` + `transitionHomeo_contMDiffOn` + `contMDiffOn_chart` via `ContMDiffOn.comp'`,
  domain matched by `trans_source`). `Nonempty H` from `Nonempty (A 0)` + a chart.
- **D3c (part) — `instSigmaCompactSpaceLim`, `instT2SpaceLim`** (thin wrappers of engine
  `SeqSystem.sigmaCompact`/`t2Space`, need `[∀ k, SigmaCompactSpace/T2Space (A k)]`).

### (RESOLVED 2026-07-07 3rd session) D3d metric transport — see the DONE entry at the top
The bridge described here was built (as the *pullback along the smooth local inverse*, which avoids
every derivative inverse): `MetricCocycle` + `stageInner` + `limitMetric` + `limitMetric_pullback`.
D3e consumes it via `C4/StepDLimit.lean` `limitPointedCoc`.  D3 is COMPLETE; the remaining Step D
lanes are D1/D2/D4/D5/D6 (see `STEPD_PLAN.md`).

## Lessons
- Charts hide `H` behind `.source`: statements like `x ∈ (limChart k a).source` cannot infer `H`
  (metavar → stuck instance). Fix: `(limChart (H := H) k a)` or an `atlas H _`-mentioning goal.
- `set` over-rewrites: `rw [← hz]` where `hz : incl (rep z)… = z` also hits the `rep z` inside
  `chartAt z`. Rewrite the HYPOTHESIS (`rwa [hz] at hmem`) instead.
- `SmoothSeqSystem` needs `contMDiffOn_invFun_F` — a `C^∞` open embedding does NOT have a `C^∞`
  inverse automatically (`x ↦ x³`), so requiring smooth-onto-open-image is honest, not gratuitous.
