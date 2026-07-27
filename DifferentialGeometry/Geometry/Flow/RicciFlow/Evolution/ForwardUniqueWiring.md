# `ForwardUniqueWiring.lean` — Route-K brick K7 (the endgame wiring)

Lane: `ricci_flow_forward_unique` (black box (B)), `ShortTime/FORWARD_UNIQUE_PLAN.md` dispatch
№44 (the wiring spec).  Companion notes: `ForwardUniqueAssembly.md` (the bundle and its
provenance ledger), `ForwardUniqueLifts.md`, `ForwardUniqueSdec.md`, `ForwardUniqueDensReg.md`.

## Status

### Sixth pass (2026-07-27, REMAINDER): argument-free `fuSlab_of_gram` CLOSED

`fuRemSlab` now bounds the actual `sdecRemFam` carrier on every compact subslab
using only the two chart-Gram regularity hypotheses.  The proof reconstructs the
solution component families as the invariant quadratic-curvature, Ricci-drift,
and own Uhlenbeck-speed tensors (`fuB_low`, `fuDrift_low`, `fuSpeed_low`), then
combines the four `sdecRem` summands with coefficients `8, 8, 4, 2`.  All
background factors come from the closed-slab supremum layer.

`fuSlab_of_gram` now takes only `h1smooth`, `h2smooth`, `h1pde`, and `h2pde`;
it produces `remLe` through `fuRemSlab` and `adotLe` through `fuAdotSlab`
internally.  The source contains no `sorry`, passes both the focused check and
targeted module build without local warnings, and both `fuRemSlab` and
`fuSlab_of_gram` depend on exactly `[propext, Classical.choice, Quot.sound]`.

The dedicated forward-uniqueness machinery is now **100%**.  The public
`ricci_flow_forward_unique` theorem remains **0% proved** until its existing
`sorry` is replaced in `ExtendViaUniqueness.lean`; that one-line endpoint wiring
is the only remaining lane step.  The whole HCG compactness project remains
about **10%**.

### Fifth pass (2026-07-27, ADOT): `fuAdotSlab` CLOSED

`fuAdotSlab` now supplies the `ForwardUniqueSlab.adotLe` field at the real
`fuAvec`/`fuSfield` carriers from the black-box chart-Gram regularity and PDE inputs alone.
It combines `ricciSlabSup`, `metricCompSlab`, and `nablaRicSlabSup` with
`connDiffDot_normSq_le`.  The two realization obligations use the same intrinsic
Ricci sections: `nablaRicReal_frame` identifies their chart components, while `fuGamma`
supplies the coefficient identity and, through `connDiffVec_hasDerivAt`, the derivative of
the connection-difference vector.  A single maximum constant absorbs both the density and
the zeroth-order terms.

The proof now passes both a focused check and the targeted module build with no
local warnings or errors and contains no `sorry`.  Its direct axiom audit is exactly
`[propext, Classical.choice, Quot.sound]`.
The stable elaboration requires a direct `ForwardUniqueConnBound` import, an explicit
reference-interval argument for `localFrameInv_real`, and a finite slot-map equality that
normalizes the `vec3` realization from `nablaRicReal_frame` to the `component0S` if-slot
form.  The `fuGamma` call uses the direct lower bound `ht.1` and the composed upper bound
`lt_trans ht.2 hc.2`.  The final estimate unfolds the metric- and curvature-difference
squared-norm definitions for nonnegativity and normalizes multiplication associativity
before applying the pointwise connection-speed bound.

This theorem itself and its dedicated `adotLe` machinery are **100%**.  The public
`ricci_flow_forward_unique` theorem remains **0% proved** until its existing `sorry` is
actually replaced; its dedicated forward-uniqueness machinery is about **95%**, with
`hrem`/final argument-free slab assembly still to be closed.  The whole HCG compactness
project remains about **10%**.  In this file, `fuSlab_of_gram` still accepts both `hrem` and
`hadot`; final assembly should feed it `fuAdotSlab` rather than retain `hadot` as an input.

### Fourth pass (2026-07-26, FINAL-FIELDS): `hbounds` ASSEMBLED modulo **two** `ForwardUniqueSlab` fields

Three new endpoints here, all unconditional given (B)'s own fields:

* `fuVolSlab` — the **`volLe`** field.  `fuTraceRd` (this file's own private bridge, second
  pass) reads the chart-defined volume drift as `−2·tr_{g₁}Ric₁`, and `volSlabSup`
  (`Evolution/ForwardUniqueSup.lean`) converts the `ricciSlabSup` constant into `C_V = √(n·B)`.
  The "port `traceTimeDerivMetricAt_eq_neg_two_scalar_of_metricDeriv` from the
  `RealizedMetricFamily` currency" plan was unnecessary — the bridge was already in this file.
* `fuReactSlab` — the **`reactLe`** field, from `reactSlabLe` + `ricciSlabSup g₁ g₁` + (B)'s PDE
  field.  The plan-№25 micro-bound `movingReactAbs_le` is proved in-lane at every rank;
  `movingReact_le` (false-green, no olean) is **not** imported.
* `fuSlab_of_gram` — **`hbounds` itself**, taking exactly two arguments: `hrem` (the `remLe`
  field at `fuRem`) and `hadot` (the `adotLe` field at `connSpeed … fuAvec`).  The other four
  fields are supplied internally (`ricciSlabLe`, `fuFluxSlab`, `fuVolSlab`, `fuReactSlab`).

A scratch `example` (not in the repo) machine-checks
`forward_unique_of_gram … (fuSlab_of_gram … hrem hadot) (energyEdgeCont …)` against
`ricci_flow_forward_unique`'s **verbatim** hypothesis list.  So the endpoint at
`Evolution/ExtendViaUniqueness.lean:189` is one `exact` away from whoever produces `hrem` and
`hadot` — and both of those bottom out on the **same** missing `∂(chart Riemann)` derivative
layer (see `ForwardUniqueSup.md` §"What is left").

`ForwardUniqueSup.lean`'s `volSlabLe` was deleted in this pass (unused; its `hdrift`
regularity hypothesis is superseded by the unconditional `volSlabSup`).  Nothing in this file
referenced it.

### Third pass (2026-07-26, SLAB-2): `hedge` DISCHARGED — the residual list is now **ONE**

```
forward_unique_of_gram : (B)'s hypotheses + h0 + hbounds → ∀ t ∈ Ico a b, g₁ t = g₂ t
```

`hedge` is supplied by `energyEdgeCont` (`Evolution/ForwardUniqueSup.lean`) from (B)'s two
chart-Gram fields alone; a scratch `example` machine-checks
`forward_unique_of_gram … hbounds (energyEdgeCont g₁ g₂ hab h1smooth h2smooth)`.

Two additions in this file, plus one import (`Evolution.ForwardUniqueSup`):

* `fuP_eq` — the `P` slot of the constructed flux is the **cross-lowered** background
  curvature: `fuTf g₁ t − fuSfield g₁ g₂ t = riemannCurvature04At (g₁ t) (metricCov (g₂ t))`.
  Proof is `sub_sub_cancel` after `fuTf_apply`/`fuSfield_apply`, because `rmDiffLowAt` is
  *defined* as that very difference.
* `fuFluxSlab` — the **`fluxLe` field of `ForwardUniqueSlab` at `fuUflux`, unconditional**:
  restrict (B)'s fields to `Icc a c`, take the three background sups (`rm04SlabSup` at
  `(g₁,g₂,g₂)` and `(g₁,g₁,g₂)`, `metricSlabSup`), and apply `fluxSlabLe`.

One adaptation: `fuFrozenJoint` lost its `isOpen_Ioo` arguments (the DensReg brick and
`rmChartJoint` no longer take `IsOpen J`), and the `Ioo (t−1) (t+1)` dance it used to satisfy
`t ∈ J` for an open `J` is gone — `J := Ioo a b` with the supplied `ht` now works directly.

`hbounds` is still short four of six fields (`volLe`, `remLe`, `reactLe`, `adotLe`); the
field-by-field state, with the smallest missing brick for each, is in `ForwardUniqueSup.md`
§"What is still missing".

### Second pass

**Second pass (2026-07-26): the three integrability slots and the interior half of `energyCont`
are CLOSED.**  1220 lines, 0 `sorry`, warning-free.  Focused check GREEN; targeted module build
GREEN (9534 jobs).  Every public endpoint is 3-axiom clean
(`[propext, Classical.choice, Quot.sound]`), including the five new ones (`fuPairInt`,
`fuRestInt`, `fuRemInt`, `fuEnergyDeriv`, `fuEnergyCont`).

`forward_unique_of_gram`'s residual list went from **five** hypotheses to **two**:

```
forward_unique_of_gram : (B)'s hypotheses + hbounds + hedge → ∀ t ∈ Ico a b, g₁ t = g₂ t
```

where `hedge : ContinuousWithinAt (forwardUniqueEnergy g₁ g₂) (Ico a b) a` is a **one-point**
statement (previously the whole-interval `henergy`).

The endpoint `Evolution/ExtendViaUniqueness.lean:189` (`ricci_flow_forward_unique`; its
`sorry` token sits at `:215`) is still **untouched** — two residual gaps remain (below), so
replacing the `sorry` would still mean smuggling them in as new hypotheses of the public
black-box interface, which the statement is not allowed to carry.

## What this file does

`forward_unique_of_inputs` (K6a, `ForwardUniqueAssembly.lean`) is (B)'s statement plus five
data carriers and a 16-field `Prop` bundle.  This file **constructs the five carriers from
(B)'s own fields** and discharges **15 of the 16** bundle members outright; the sixteenth
(`energyCont`) is reduced to its single closed-edge point.  What is left is

```
forward_unique_of_gram : (B)'s hypotheses + hbounds + hedge → ∀ t ∈ Ico a b, g₁ t = g₂ t
```

so the endpoint is one `exact` away from whoever produces those two.

### Carriers (all built from the two metric families alone)

| carrier | definition |
| --- | --- |
| `fuAvec` | `christoffelDiffSpeed` at `chartFrameInv`/`chartNablaRic` of the two flows |
| `fuSvec` | `uhlRmDiffSpeed` at the per-point-centred coordinate families `fuRm04/fuLapRm/fuBRm/fuRicUp` |
| `fuSfield` | `rm04Section g₁ (metricCov g₁) − rm04Section g₁ (metricCov g₂)` |
| `fuUflux` | `sdecUflux` at `fuTf g₁`, `fuTf g₂`, `fuSfield` |
| `fuRem` | `sdecRemFam` at the same data |

### Discharged bundle members (15 of 16, plus the interior of the 16th)

First pass: `gamma` (`gamma_of_gram`), `rm` (`rm_of_uhlenbeck` + `rm04EvolFamTail`), `sdec`
(`sdec_of_uhlenbeck`), `car` (by construction), `dens` (`dens_jointContMDiffOn`), `densCont`
and `densInt` (`dcont_idens`, unconditional), `lapInt`, `divInt`, `nabInt`, `disInt`
(the four hypothesis-free `Integrable` slots of `ForwardUniqueDensReg.lean`) — plus
`fuRmContAt`, which is not a bundle field but was the last standing input of `rm`/`sdec`.

Second pass: `pairInt` (`fuPairInt`), `restInt` (`fuRestInt`), `remInt` (`fuRemInt`), and
`energyCont` at every *interior* time (`fuEnergyDeriv`, assembled by `fuEnergyCont`).

### Historical residual after the second pass (closed by later passes)

The following was the exact residual at that earlier checkpoint.  It is retained
as route history; the sixth pass above closes `hbounds`, while the third pass
closed `hedge`.

1. **`hbounds`** — `∀ c ∈ Ioo a b, ∃ C…, ForwardUniqueSlab … a c …`, i.e. K4's six
   slab-uniform pointwise estimates (`fluxLe`, `remLe`, `reactLe`, `ricciLe`, `adotLe`,
   `volLe`) at the constructed carriers.  **No producer of `ForwardUniqueSlab` exists
   anywhere in the tree** (grep-verified: the structure occurs only in
   `ForwardUniqueAssembly.lean` and here).  Per plan №25 the `reactLe` micro-bound
   (`movingReact_le`) was *deliberately deferred* with a solid classification —
   `movingReact0S` is frame-pinned by definition and needs a new slot-composition layer.
   The other five have named producers (`fluxNormSq_le`/`rmFluxNormSq_le`,
   `remNormSq_le`/`rmRemNormSq_le`, `ricciDiffSq_le` + `ricciDiff_eq_trace`,
   `connDiffDot_normSq_le`, and compactness of `Icc a c` for `volLe`) but every one of them
   consumes *slab-uniform background norms* as named arguments, so a genuine
   compactness-of-`Icc a c × M` sup-bound layer is still missing.  **This is the dominant
   remaining brick of the lane.**  (`Evolution/ForwardUniqueSup.lean` is the sibling lane
   attacking exactly this.)
2. **`hedge`** — `ContinuousWithinAt (forwardUniqueEnergy g₁ g₂) (Ico a b) a`, i.e. continuity
   of the energy at the **single** initial time.  Precise obstruction: the whole joint
   `(t, x)`-regularity tower bottoms out at `gen_joint_christoffel` / `gen_joint_riemann`
   (`Analysis/Parabolic/RicciLinearization/RicciDifferenceMeanValue.lean`), which conclude
   `ContDiffAt` on an **open** time window; hence `dens_jointContMDiffOn` lives on `Ioo a b`
   and nothing controls the density as `t ↓ a`.  Black box (B) *does* supply
   `ContMDiffOn … ∞ (chartGram) (Ico a b ×ˢ baseSet)` — one-sided `C∞` at the edge — so the
   fix is a `ContDiffWithinAt`-on-`Ici a` variant of that generic tower, which lives in a
   foreign file.  Note also that `E(a) = 0` under (B)'s `h0`, so the edge statement is really
   "`E(t) → 0` as `t ↓ a`", which needs quantitative control and is *not* free from continuity
   alone.

Both residuals sit in files this lane does not own, so they are correctly left as named
hypotheses rather than smuggled into the endpoint.

## The one piece of new mathematics: `fuRmContAt`

`rm_of_uhlenbeck` and `sdec_of_uhlenbeck` both carry a `hcont` input — time-continuity of
`r ↦ riemannOp (metricCov (g r)) y (b i) (b j) (b k)` — which every prior note treated as a
standing hypothesis.  **It is not one.**  On a positive-time tail:

* `raiseAt_lower` (`ForwardUniqueRmBridge.lean`) says the vector whose `g`-lowered components
  are those of `V` is `V`; with `metricRm04At_inner` the lowered components of the raised
  curvature *are* the component family `fuRm04`;
* `fuRm04` is differentiable in time by the tail Uhlenbeck evolution (`fuEvolTail`), hence
  continuous;
* the Gram matrix `G(r)_{lm} = g(r)(b l, b m)` is differentiable in time by the Ricci-flow
  equation, hence continuous, and `basisInvMetric` is its matrix inverse
  (`basisInvMetric_real` + `Matrix.inv_eq_right_inv`);
* `continuousAt_matrix_inv` (Mathlib) plus `Ring.inverse_eq_inv'`/`continuousAt_inv₀` at the
  nonzero determinant closes it.

So `rm` and `sdec` are now discharged from (B)'s own fields with **no auxiliary input at all**.

## Second pass: how the three bare-pointwise slots fell (the key idea)

`pairInt`, `restInt`, `remInt` were recorded as needing "*spatial* continuity of a per-point-centred
frame construction".  **That framing was wrong** — the frame-pinned carriers `fuSvec` / `fuAvec` /
`fuRem` never have to be touched.  Observe:

* `normSq0S_moving_deriv` (`ForwardUniqueEnergy.lean`) states
  `∂ₜ|T|²_{g₁} = movingReact0S (g₁ t) x s Ric₁ (T t) + 2⟨Ṫ, T⟩`, and **every** occurrence of an
  invariant speed inside `rateRest` / the pair integrand is in exactly that combination.  So each
  such group *is* the time partial of one of the three energy thirds — scalars whose joint
  `C∞`-ness `ForwardUniqueDensReg.lean` already proves.
* Specialising the same lemma to a **constant** tensor family (`Tdot := 0`) shows
  `movingReact0S (g₁ t) x s Q W = ∂ᵣ|W|²_{g₁ r}|_{r=t}` — a basis-free characterisation of the
  frame-pinned `movingReact0S`.  Its joint smoothness comes from the brick
  `normSq0S_jointContMDiffOn` with the *moving* metric `g₁` and the *frozen* carrier, whose chart
  components are supplied by `rmChartJoint` at two constant metric families (the `dens_continuous`
  trick).  This is `fuFrozenJoint`.

The only genuinely new analysis is `tderivCont`:

> `F` jointly `C∞` on `J ×ˢ univ` (`J` open), `t ∈ J` ⟹ `x ↦ ∂ᵣF(r,x)|_{r=t}` is continuous.

proved by transporting `F` through `extChartAt x₀` to `ℝ × E` (the `hσ` construction copied from
`genGram_of_joint`), applying `ContDiffOn.continuousOn_fderiv_of_isOpen`, and reading the time
partial as `fderiv … (1, 0)`.

The ledger then is purely algebraic:

| slot | identity used |
|---|---|
| `pairInt` | `2⟨Ṡ, S₀₄⟩ = ∂ₜ|S₀₄|² − movingReact₄` (`fuRmSqD`, `fuReactCont`) |
| `remInt` | `fuSdec` + `inner0S_add_left` twice: `⟨rem, S⟩ = ⟨Ṡ, S⟩ − ⟨Δ S, S⟩ − ⟨div U, S⟩`, the last two smooth by type |
| `restInt` | `rateRest = ∂ₜ|h₀₂|² + ∂ₜ|A₀₃|² + movingReact₄ + ½·tr_g(ġ)·ρ` |

For the volume term `restInt` needs spatial continuity of `traceTimeDerivMetric g₁ t ·`, which is
frame-pinned in the same way (the chart at `x` evaluated at `x`).  It is dissolved by the same
kind of invariance statement: under `∂ₜg = −2Q`, `traceTimeDerivMetric g t x = −2 tr_{g t} Q`, and
`metricTracePair0SAt g B = inner0S g x 2 (metricTensor0S g x) B` is a pairing of two smooth
`(0,2)` fields (`metricTensorField` and `CovariantDerivative.ricciSection`), so
`inner0S_continuous` finishes.

`energyCont`'s interior half turned out to be **free**: `forwardUniqueEnergy_hasDerivAt`
(`ForwardUniqueEnergy.lean:368`) is already stated with purely window-local hypotheses (open `U`,
chart-Gram and joint density on `U`, the two flow equations and two carrier speeds at the single
time `t`) — all of which the wiring supplies.  Differentiability ⟹ continuity at every interior
time, leaving only `t = a`.

## Design decisions worth keeping

* **The interval index is a phantom.**  `rm04Fam`/`rm04LapFam`/`rm04BFam`/`ricUpFam` and
  `solOfMetric` read their `RealTimeInterval` argument only through the metric family, so
  `fuRm04_eq` … `fuRicUp_eq` transport a tail-interval statement to a fixed reference interval
  `refD := RealTimeInterval.univ 0` **by `rfl`**.  This is what lets one fixed `Svec` serve
  every interior time while the producers are only available on tails.
* **The midpoint tail, reused verbatim from `gamma_of_gram`.**  Each bundle member is a
  pointwise-in-`t` statement, so for `t ∈ Ioo a b` one takes `t₀ := (a+t)/2`, applies the tail
  producer on `Ico t₀ b`, and evaluates at `t ∈ Ioo t₀ b`.  Nothing is lost: the carriers do
  not depend on `t₀`.
* **`Sfield` and `Tf` are *constructed*, not supplied.**  `ForwardUniqueSdec.md` recorded
  "a smooth `(0,4)` field realizing `metricRm04At` is not available as a producer in the
  tree"; that is **wrong** — `metricRm04 = rm04Section g (metricCov g) …`
  (`Geometry/Curvature/Riemann/Basic/Sections.lean:528`) is exactly it, and
  `rm04Section g₁ (metricCov g₂)` gives the second term of `S₀₄`.  Both `car` and `hT₁`/`hT₂`
  are then `rfl`.  (Fifth-plus confirmed false wall in this project; the rule stands — grep
  for the *section-level* producer before declaring a field unconstructible.)

## Lean lessons

* `ContinuousAt.comp_continuousWithinAt` mis-unifies against a goal of the form
  `ContinuousWithinAt (fun r ↦ (F r)⁻¹) …` when `F r` is a `Matrix.of` application: the
  elaborator picks `g := Matrix.of`.  `Filter.Tendsto.comp` on the two unfolded
  `Tendsto` statements elaborates immediately (both `ContinuousAt` and `ContinuousWithinAt`
  are defeq to `Tendsto`).
* `Matrix m n R`'s topology is `inferInstanceAs (TopologicalSpace (m → n → R))`, so
  `continuousWithinAt_pi` applies to matrix-valued families with no glue.
* `Matrix.of f p l = f p l` is *not* closed by `rw`'s trailing `rfl` (the `Equiv` coercion is
  not reducible enough); append an explicit `rfl`.
* Mathlib has no `ContinuousWithinAt` analogue of `continuous_finset_sum`; the three-line
  `Finset.induction` helper (`cwaSum` here, `cwa_finset_sum` in
  `ShortTimeFlow/ConjugatingFlowProperties.lean`) is now duplicated — relocation TODO, the
  canonical home is a topology-algebra file.
* `uhlRmDiffSpeed`/`sdecRemFam` applications need `set_option synthInstance.maxHeartbeats
  1000000` **and** `maxHeartbeats 1000000` even to state a definition; without them the
  elaborator times out at 200000 heartbeats on the carrier definitions.
* The endpoint's own variable block (`ExtendViaUniqueness.lean`) already synthesizes
  `CompleteSpace E`, `Module.Finite ℝ E`, `IsManifold I 1 M`, `IsManifold I 2 M` and
  `IsManifold I (∞+1) M` from `FiniteDimensional ℝ E` / `IsManifold I ∞ M` — verified by
  probe, so wiring the endpoint needs no `haveI` scaffolding.

## Lean lessons (second pass)

* **`simpa only [foo_def] using h.deriv` beats `have h : HasDerivAt … _ t`.**  Writing the
  derivative slot as `_` in a `have` makes Lean try to *synthesize* `f'` from nothing and fail
  with "don't know how to synthesize placeholder for argument `f'`".  Convert the `HasDerivAt`
  to the `deriv = …` equation first, then `simpa only` on the equation.
* **Do not `set` a local abbreviation that a Mathlib lemma has to unify against.**  `set U :=
  interior (extChartAt I x₀).target` made `interior_subset hp.2` elaborate against the wrong
  `interior _`; stating the `Set.MapsTo` as its own type-ascribed `have` (exactly the
  `genGram_of_joint` shape in `ForwardUniqueDensReg.lean`) fixes it.
* `ContDiffOn.differentiableOn` in this Mathlib takes `n ≠ 0`, not `1 ≤ n`;
  `ContDiffOn.continuousOn_fderiv_of_isOpen` takes `1 ≤ n`.  Keep both `have`s around.
* The stack-wide rule "never `rw` on `Tensor0SSpace` FunLike coercions" bit again:
  `ContinuousMultilinearMap.ext fun v => by rw [metricTensor0S_apply, …]` fails; the term form
  `(metricTensor0S_apply … v).trans (metricTensorField_apply … v).symm` works.
* `simp only [vec2]` is reported *unused* even when `vec2 X Y` is visibly in the goal; the two
  sides are definitionally equal, so a bare trailing `rfl` is the fix.
* `ContinuousAt.clm_apply` exists and is the clean finisher for `x ↦ (fderiv … (φ x)) v`.

## Relocation TODOs

* `cwaSum` → a topology-algebra layer (duplicate of `cwa_finset_sum`).
* `fuRmContAt`'s raising-continuity core is generic (any metric family with a differentiable
  Gram and a continuous lowered-component family); it belongs next to `raiseAt_lower` in
  `ForwardUniqueRmBridge.lean` once that file is next touched.
* **`tderivCont`** is completely generic (any jointly-`C∞` scalar on `J ×ˢ univ`); canonical home
  is an analysis/manifold layer such as `Analysis/Integration/Measure/` or a
  `Geometry/Coordinates/` joint-regularity file.  Kept `private` here for now.
* **`fuTraceRd` duplicates `IntrinsicSpectral.traceTime_rd`**
  (`Analysis/Spectral/Intrinsic/DeTurck/MovingEdgeEnergy.lean:760`).  That file sits *above*
  `Evolution/` in the import order, so importing it here would invert the layering; the copy is
  `private` and carries the TODO in its docstring.  Both copies belong next to
  `traceTimeDerivMetric` in `Analysis/Integration/Measure/Family.lean` — that is the real fix.
* `fuReactDeriv` (`movingReact0S` as a frozen-carrier time derivative) is a rank-uniform fact
  about `normSq0S_moving_deriv` with nothing forward-uniqueness-specific; it belongs beside
  `movingReact0S` (which itself is queued for `Tensor/RSTensor/FiberMetric/Tensor0SMetricDeriv`).

## Next targets, in order of leverage

1. Replace the unchanged-statement `ricci_flow_forward_unique` `sorry` with the
   checked `forward_unique_of_gram` application, supplying `fuSlab_of_gram` and
   `energyEdgeCont`.
2. Audit the public theorem directly for the exact three permitted axioms, then
   run the full locked build.  Do not route the proof through black box (N).
