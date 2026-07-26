# `ForwardUniqueLifts.lean` — Route-K brick K6b (the two missing-API lifts)

Lane: `ricci_flow_forward_unique` (black box (B)), dispatch `ShortTime/FORWARD_UNIQUE_PLAN.md` №28.
Ledger this brick discharges: `Evolution/ForwardUniqueAssembly.md` §"Ledger", the two members
labelled **missing-API** (`rm`, `gamma`).

## Outcome

**(A), and stronger than commissioned on item 2.**  630 lines, 19 public declarations (+1 private),
0 `sorry`.

| bundle member | before | after |
| --- | --- | --- |
| `rm` | "producer exists (`rmDiffVec_deriv`) but its conclusion is frame-shaped; needs the quadrilinear lift" | **collapsed** to the two per-flow own-lowered Uhlenbeck interfaces + the two per-flow PDEs (ruling-R1 standing inputs, unchanged) |
| `gamma` | "K2-B standing input; missing the `SolutionOn`-package bridge" | **fully discharged from (B)'s own fields** — no standing input at all |
| `sdec` | K2-B | untouched; classified below (planner carrier decision, per the mission's stop rule) |

## What was built

### Part 1 — the rank-3 lift (`NormedSpace` section)

* `tri_expand` — trilinear basis expansion, the rank-3 `bilin_expand`.
* `quadOfComp b c` — the continuous trilinear vector-valued map with prescribed components,
  `quadOfComp b c (b i) (b j) (b k) = ∑ l, c i j k l • b l`.  Exact one-rank-up mirror of
  `bilinOfComp` (`ForwardUniqueConnDot.lean`), same `Basis.constr`+`toContinuousLinearMap`
  nesting, one level deeper.  Read-back: `quadOfComp_basis` (`@[simp]`), `coeff_quadOfComp`
  (frame-coefficient form, mirrors `coeff_bilinOfComp`), and `quadOfComp_vec` — the form the
  collapse actually uses, since the rank-3 producer supplies **vectors**, not scalar
  components (`c i j k l := b.repr (V i j k) l` reproduces `V` at basis triples).
* `rmDiffVec_hasDerivAt_of_basis` — **the lift**.  Basis-triple derivatives of `rmDiffVec` give
  the derivative at every `(X,Y,Z)` with the invariant speed.  Simpler than the rank-2 analogue
  `connDiffVec_hasDerivAt` because no coefficient bookkeeping is needed.

### Part 1b — the `rm` collapse

* `uhlRaisedDeriv` — names the right-hand side that `rmVecComp_deriv`
  (`ForwardUniqueRmBridge.lean`) produces per flow: own-raise of `roughLap − 2·B-comb − Ricci
  drift`, plus the `∂ₜg = −2Ric` reaction.
* `uhlRmDiffSpeed` — the constructed `Svec`: `quadOfComp` of the difference of the two
  `uhlRaisedDeriv` families.  The Assembly bundle's `Svec` carrier is therefore **constructed,
  not supplied**.
* `rm_of_uhlenbeck` — the `rm` member verbatim.  Residual hypothesis set (per flow, symmetric,
  no cross-metric lowering — ruling R4 respected):
  `Riemann04BTensorWithRicciDriftEvolutionInFrameOn` + `hreal` (which curvature the component
  family is) + `hcont` (continuity of the `(1,3)` curve, strictly weaker than the concluded
  differentiability) + the Ricci-flow PDE within `D.carrier`.  Plus `Ioo a b ⊆ D.regular`, which
  is what turns `HasDerivWithinAt` into `HasDerivAt` (`RealTimeInterval.regular_mem_nhds`).

### Part 2 — the `SolutionOn` bridge and `gamma` (`InnerProductSpace` section)

* `solOfMetric g = ⟨⟨g⟩⟩` — **the "K1 solution-package bridge" is trivial**, exactly as the
  mission suspected: `SolutionFamily` has the single field `metric`, `SolutionOn` the single
  field `base`.  `christoffelInFrame_solOfMetric` is `rfl`.  Nothing analytic was hidden in the
  ledger entry that called this a missing link.
* `christoffelDiffSpeed` — the constructed `Avec`: `bilinOfComp`, in the chart frame centred at
  each point, of the difference of the two Christoffel evolution right-hand sides.
* `gamma_of_fields` — the `gamma` member from the two per-flow
  `ChristoffelEvolutionEquationInFrameOn`s (K1's `christoffelEvolutionDiffInFrameOn` +
  `coeff_bilinOfComp`).  This is the level-matched analogue of `rm_of_uhlenbeck`.
* `chartFrame_isFrameTop` — the chart frame is `C^∞`, not merely `C¹` (Assembly only needed
  `C¹`); this is what lets `tailChristoffel` accept it.
* `chrEvo_of_gram` — **the per-flow interface is not a standing input**: `solutionOn_of_joint`
  (`ExtendedSolutionRegularity.lean:1121`) then `tailChristoffel`
  (`Evolution/Connection/TailChristoffel.lean:63`) produce it from a metric family + joint
  chart-Gram `C^∞` on `Ico a b` + the Ricci-flow PDE — i.e. from (B)'s `h1smooth`/`h1pde`.
* `gamma_of_gram` — **the `gamma` member from (B)'s own four fields only.**  The tail
  restriction of `tailChristoffel` (`a < t₀`) is paid with `t₀ := (a+t)/2` at each interior
  time; `gamma` is only ever needed on `Ioo a b`, so it costs nothing.

## Recon finding that changed the plan (worth propagating to `PROJECT_MAP`/`Assembly.md`)

`ForwardUniqueAssembly.md` labels `gamma` **K2-B** (a standing input).  That is **wrong**: the
`Christoffel.lean:397/:447` `_of_pairing` route the ledger points at is indeed a dead end (its
`ConnectionVariationPairingEquationInFrameOn` needs `ConnectionPairingDerivativeInFrameOn`,
which has **zero producers** anywhere in `DifferentialGeometry/`), but two other routes bypass
the pairing layer entirely and are already exercised in-tree (`coordRicciEvol`,
`rm04Var_of_solution` both build `hGamma` from `IsSolutionOn` alone):

* `coordGammaEvol` (`Evolution/Ricci/CoordinateRegularity.lean:964`) — coordinate frame, no tail
  restriction, but needs a `MetricCovDerivDerivativeComponentsInFrameOnLocal` input;
* `tailChristoffel` (`TailChristoffel.lean:63`) — **any** `C^∞` local frame on any open set, no
  input beyond `IsSolutionOn`, at the price of a positive-time tail.  Used here.

So the bundle's honest K2-B debt is `rm` and `sdec` only.

## Classification of item 3 (`sdec`) — STOPPED deliberately, not attempted

The mission's stop rule fired.  `sdec` is *not* blocked by a missing lift: `rmLowComp_deriv`
(`ForwardUniqueRmDot.lean:649`) already produces the componentwise statement, and the
quadrilinear lift built here would package it.  It is blocked by the **carrier decision**
recorded in `ForwardUniqueRmDot.md` §"Realization-hypothesis classification": the two honest
Uhlenbeck interfaces are **own-metric-lowered**, so their difference is
`metricRm04At g₁ − metricRm04At g₂`, not the Kotschwar carrier `S₀₄ = rmDiffLowAt g₁ g₂`.  The
gap is `(g₁ − g₂)(Rm¹³₂ ·,·)`; `∂ₜ` of it is harmless for the energy, but `Δ₁` of it produces
`∇¹∇¹h₀₂`, which the energy does not control — so carriers cannot be swapped after the fact.
Either (i) the flow-2 interface is taken at the `g₁`-lowered representative (a *different*
standing input, whose producer is K2-B at mixed lowering), or (ii) K3's carrier changes to the
own-metric difference, rippling into `ForwardUniqueFields.lean`'s `rmDiffSq` and all of
K2.4/K2.5.  **Planner decision.**  Note that `rm_of_uhlenbeck` here has *no* such gap — Part 1
of the R4 bridge works directly on the raised difference.

## Lean lessons (durable)

* **The `InnerProductSpace`/`NormedSpace` split must be a section split, not a variable
  addition.**  Adding `[InnerProductSpace ℝ E]` to a section that already declares
  `[NormedSpace ℝ E]` produces a genuine diamond and the error surfaces as an *application type
  mismatch on `I`*: `ModelWithCorners ℝ … E inst✝¹²` vs
  `ModelWithCorners ℝ … ?m InnerProductSpace.toNormedSpace ?m`.  The fix is two sibling
  top-level sections, each re-declaring `E H I M` with its own instance path.  Part 1 stays
  `NormedSpace`-only (matching `ForwardUniqueRmDot`/`RmBridge`) and is therefore reusable from
  either world; Part 2 mirrors `ForwardUniqueAssembly`'s block verbatim.
* `Assembly.chartFrame_isFrame` really does depend on `[InnerProductSpace ℝ E]` and
  `[NeZero (finrank ℝ E)]` — the failure mode when they are absent is
  `failed to synthesize NeZero (Module.finrank ℝ ?m)` with an unassigned metavariable, i.e. the
  *elaboration order* hides which argument is at fault.  Read the companion `ModelWithCorners`
  mismatch on the same line to identify it.
* A file-level `set_option synthInstance.maxHeartbeats 1000000` is the right granularity here:
  the very first failure was a 20000-heartbeat timeout synthesising
  `SeminormedAddCommGroup (TangentSpace →L TangentSpace →L TangentSpace)` inside `tri_expand`'s
  `simp only [map_sum, …]`.  Iterated CLM spaces blow the default budget immediately.
* `variable (I) in` is load-bearing for frame lemmas: without it `I` stays implicit and the call
  site `chartFrame_isFrameTop I x₀` fails with "Function expected".  Mirror the neighbouring
  declaration's binder style.
* `SolutionOn.timeRestrict` only changes the interval (`base := S.base`), and `localFrameInv` /
  `ricciCovDerivCompInFrame` depend on the package solely through `S.family.metric` /
  `S.family.connection` / `S.ricciAt`.  Consequently `tailChristoffel`'s output at
  `S.timeRestrict D'` is *definitionally* the same component family as at a reference interval,
  and a bare `exact h` closes `chrEvo_of_gram` across the interval change.  This is why
  `chartFrameInv` / `chartNablaRic` can be named at a fixed `refInterval` and still be the `t₀`
  -dependent objects the tail producer returns — which is what keeps `Avec` free of `t₀`.
* `IsLocalFrameOn` is a `Type`-valued structure whose three fields are all `Prop`s, so structure
  eta plus definitional proof irrelevance make any two instances defeq.  `tailChristoffel`'s
  existentially-produced `hframe1` can therefore be discarded (`obtain ⟨_, h⟩`) and `h` used
  directly against `chartFrame_isFrame I x₀`.
* Reused, not reproved: `bilinOfComp`/`coeff_bilinOfComp` (`ForwardUniqueConnDot.lean`),
  `rmVecComp_deriv`/`raiseAt` (`ForwardUniqueRmBridge.lean`), `rmDiffVec` (`ForwardUniqueRmDot`),
  `christoffelEvolutionDiffInFrameOn` (`ForwardUniqueConnectionDiff.lean`),
  `solutionOn_of_joint`, `tailChristoffel`.  Nothing was duplicated.

## Relocation TODO

`tri_expand`, `quadOfComp`, `quadOfComp_basis`, `quadOfComp_vec`, `coeff_quadOfComp` are generic
fiber algebra belonging next to `bilin_expand`/`bilinOfComp`; they live here only because the
brick protocol forbids editing existing files.

## Verification

Focused check green; authoritative targeted build of the module GREEN and warning-free.  Zero
`sorry`.  `#print axioms` on all 19 public declarations returns exactly `[propext,
Classical.choice, Quot.sound]`.

Style note: the `synthInstance.maxHeartbeats` bump is scoped per declaration (the project's
`linter.style.setOption` rejects the file-level form); only the Part-1 CLM-tower declarations
need it, Part 2 does not.

The module is **not** wired into the root aggregate — planner's step, as for the other lane files.

## Next targets

1. `sdec` — blocked on the planner carrier decision above, not on missing API.
2. The hdens tower (`dens` + ten of sixteen bundle members) — `Evolution/ForwardUniqueDensReg.lean`.
3. `ForwardUniqueConnBound.lean:496` — the one live `sorry` under `adotLe`.
4. Update `ForwardUniqueAssembly.md`'s ledger: `gamma` is no longer K2-B; `rm`'s "missing link"
   row is closed; `Svec`/`Avec` are constructed carriers, not supplied ones.
