# `ForwardUniqueWiring.lean` — Route-K brick K7 (the endgame wiring)

Lane: `ricci_flow_forward_unique` (black box (B)), `ShortTime/FORWARD_UNIQUE_PLAN.md` dispatch
№44 (the wiring spec).  Companion notes: `ForwardUniqueAssembly.md` (the bundle and its
provenance ledger), `ForwardUniqueLifts.md`, `ForwardUniqueSdec.md`, `ForwardUniqueDensReg.md`.

## Status

**Outcome (B).**  612 lines, 0 `sorry`, warning-free.  Focused check GREEN; targeted module
build GREEN (9534 jobs); the consumer chain
(`ExtendViaUniqueness` + `MaximalTime`) rebuilt GREEN (9975 jobs) with the endpoint's two
`sorry`s unchanged.  Every public endpoint is 3-axiom clean
(`[propext, Classical.choice, Quot.sound]`).

The endpoint `Evolution/ExtendViaUniqueness.lean:189` (`ricci_flow_forward_unique`; its
`sorry` token sits at `:215`) is **untouched** — three residual gap families remain (below), so replacing the `sorry` would
have meant smuggling them in as new hypotheses of the public black-box interface, which the
statement is not allowed to carry.

## What this file does

`forward_unique_of_inputs` (K6a, `ForwardUniqueAssembly.lean`) is (B)'s statement plus five
data carriers and a 16-field `Prop` bundle.  This file **constructs the five carriers from
(B)'s own fields** and discharges **12 of the 16** bundle members, leaving

```
forward_unique_of_gram : (B)'s hypotheses + hbounds + henergy + hpair + hrest + hrem
                       → ∀ t ∈ Ico a b, g₁ t = g₂ t
```

so the endpoint is one `exact` away from whoever produces those five.

### Carriers (all built from the two metric families alone)

| carrier | definition |
| --- | --- |
| `fuAvec` | `christoffelDiffSpeed` at `chartFrameInv`/`chartNablaRic` of the two flows |
| `fuSvec` | `uhlRmDiffSpeed` at the per-point-centred coordinate families `fuRm04/fuLapRm/fuBRm/fuRicUp` |
| `fuSfield` | `rm04Section g₁ (metricCov g₁) − rm04Section g₁ (metricCov g₂)` |
| `fuUflux` | `sdecUflux` at `fuTf g₁`, `fuTf g₂`, `fuSfield` |
| `fuRem` | `sdecRemFam` at the same data |

### Discharged bundle members (12 of 16)

`gamma` (`gamma_of_gram`), `rm` (`rm_of_uhlenbeck` + `rm04EvolFamTail`), `sdec`
(`sdec_of_uhlenbeck`), `car` (by construction), `dens` (`dens_jointContMDiffOn`), `densCont`
and `densInt` (`dcont_idens`, unconditional), `lapInt`, `divInt`, `nabInt`, `disInt`
(the four hypothesis-free `Integrable` slots of `ForwardUniqueDensReg.lean`) — plus
`fuRmContAt`, which is not a bundle field but was the last standing input of `rm`/`sdec`.

### Residual (3 families, 5 hypotheses)

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
   remaining brick of the lane.**
2. **`henergy`** — `ContinuousOn (forwardUniqueEnergy g₁ g₂) (Ico a b)`, i.e. continuity of
   `t ↦ ∫ density dμ_{g₁ t}` **up to the closed initial edge**.  `dens_jointContMDiffOn`
   lives on the *open* window and `dens_continuous` is fixed-time only, so this needs a
   dominated-convergence argument on the compact subslab plus a closed-edge input.  Medium.
3. **`hpair` / `hrest` / `hrem`** — the three `Integrable` slots whose integrand pairs a
   **bare pointwise family** (`rmSpeed … fuSvec`, `connSpeed … fuAvec`, `fuRem`).  The four
   sibling slots are free because their carriers are `Tensor0SField`s (smooth by type).
   These three need *spatial* continuity of a per-point-centred frame construction: the
   objects are frame-independent tensors, but that tensoriality is not yet a Lean fact.
   `ForwardUniqueDensReg.md` already classified them as "not density-regularity questions".

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

## Relocation TODOs

* `cwaSum` → a topology-algebra layer (duplicate of `cwa_finset_sum`).
* `fuRmContAt`'s raising-continuity core is generic (any metric family with a differentiable
  Gram and a continuous lowered-component family); it belongs next to `raiseAt_lower` in
  `ForwardUniqueRmBridge.lean` once that file is next touched.

## Next targets, in order of leverage

1. `hbounds` — the slab-uniform background-norm layer (compactness of `Icc a c`, then the six
   named producers).  Dominant; includes the deferred `movingReact_le` decision.
2. `hpair`/`hrest`/`hrem` — spatial continuity of the constructed speed families.
3. `henergy` — closed-edge continuity of the energy.
