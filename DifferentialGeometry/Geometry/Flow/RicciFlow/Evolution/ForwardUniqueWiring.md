# `ForwardUniqueWiring.lean` — Route-K brick K7 (the endgame wiring)

Lane: `ricci_flow_forward_unique` (black box (B)), `ShortTime/FORWARD_UNIQUE_PLAN.md` dispatch
№44 (the wiring spec).  Companion notes: `ForwardUniqueAssembly.md` (the bundle and its
provenance ledger), `ForwardUniqueLifts.md`, `ForwardUniqueSdec.md`, `ForwardUniqueDensReg.md`.

## Status

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

### Residual (2 hypotheses)

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

1. `hbounds` — the slab-uniform background-norm layer (compactness of `Icc a c`, then the six
   named producers).  Dominant; includes the deferred `movingReact_le` decision.  Lane file:
   `Evolution/ForwardUniqueSup.lean`.
2. `hedge` — continuity of the energy at `t = a`.  Requires the `ContDiffWithinAt`-on-`Ici a`
   variant of `gen_joint_christoffel` / `gen_joint_riemann`, plus a decay estimate for
   `E(t) → E(a) = 0`; i.e. it is really a sub-problem of (1).
