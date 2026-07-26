# `ForwardUniqueAssembly.lean` — Route-K brick K6a (the endgame assembly)

Lane: `ricci_flow_forward_unique` (black box (B)), `ShortTime/FORWARD_UNIQUE_PLAN.md` dispatch
№24 → K6a.  Planner ruling context: `ShortTime/FORWARD_UNIQUE_PRO_RULING.md` §6.

## What this brick is

`forward_unique_of_inputs` is black box (B)'s hypothesis interface — verbatim, including the two
redundant C⁰ chart-Gram fields and `h2smooth`, which nothing consumes — plus one residual
standing-input bundle `ForwardUniqueInputs`, concluding `∀ t ∈ Ico a b, g₁ t = g₂ t`.

**It does not discharge the endpoint.**  `Evolution/ExtendViaUniqueness.lean` is untouched and its
`sorry` at `ricci_flow_forward_unique` is still live.  This file is the wiring that says exactly
what is left, in types Lean has checked.

## What (B)'s own fields discharge (nothing of this is in the bundle)

| K3/K4/K5 slot | discharged from |
| --- | --- |
| `hgram` | `h1smooth`, restricted `Ico a b → Ioo a c` by `ContMDiffOn.mono` |
| `hPDE₁`, `hPDE₂` | `h1pde`/`h2pde` via `pde_hasDerivAt`: `Ici a ∈ 𝓝 t` for `t > a` (`HasDerivWithinAt.hasDerivAt` + `Ici_mem_nhds`) and `metricRicciAt_apply_eq_ricciTensor` for the currency change |
| `hinit` | `h0` |
| `hA` | `connSpeed_hasDerivAt` = `connDiffLow_hasDerivAt_frame` at the canonical chart frame, fed by the bundle's `gamma` + the upgraded `hPDE₁` |
| `hS` | `rmSpeed_hasDerivAt` = `rmDiffLow_hasDerivAt`, fed by the bundle's `rm` + the upgraded `hPDE₁` |
| `hε`, `hδ`, `habs` | CHOSEN: `ε = 1/2`, `δ = 1/(2(C_A+1))` with `C_A` normalised to `max C_A 0`; `habs` is proved arithmetic, never assumed |
| `hAdot` | the bundle's `adotLe` with the constant normalised upward (`density ≥ 0`, `normSq0S ≥ 0`) |
| continuation `Icc a c → Ico a b` | `metrics_eq_ico`, with `c := (t+b)/2` |

The `C_A ≥ 0` normalisation is worth recording: `adotLe`'s right-hand factor
`density + |∇S|²` is nonnegative, so the bound self-improves to `max C_A 0`, and the Young
condition `δ·C_A + ε ≤ 1` becomes `max C_A 0/(2(max C_A 0+1)) ≤ 1/2`.  No `0 ≤ C_A` input.

## Ledger: the standing bundle and the named producer that will discharge each member

Provenance labels: **K2-B** = the second-Bianchi / evolution-interface brick recorded as a
standing input by planner ruling R1 (plan №2); **tower** = the hdens joint-regularity tower plus
compactness of the closed subslab (K3's recorded debt (i)); **realization** = which intrinsic
object a supplied field is.

### Data carriers (∀-args, not part of the Prop bundle)

| carrier | what it is | named producer |
| --- | --- | --- |
| `Avec` | raised speed of `∇¹ − ∇²` | `bilinOfComp` of K1's two component right-hand sides (`ForwardUniqueConnDot.lean`); `coeff_bilinOfComp` gives `gamma` |
| `Svec` | raised speed of `rmDiffVec` | `rmDiffVec_deriv` (`ForwardUniqueRmBridge.lean`) — **needs the frame → invariant lift** (below) |
| `Sfield`, `Uflux` | smooth `(0,4)`/`(0,5)` fields | K2's `U₀₅` construction (`ForwardUniqueRmDiff.lean`, `lapDiffFlux`) + the joint smoothness tower |
| `rem` | K2 remainder | `ForwardUniqueRmDiff.lean`'s `R` summands |

### Prop members

| field | label | named producer / what is missing |
| --- | --- | --- |
| `gamma` | K2-B | `christoffelEvolutionDiffInFrameOn` (`ForwardUniqueConnectionDiff.lean`) applied to the two per-flow `ChristoffelEvolutionEquationInFrameOn` (`Evolution/Connection/Christoffel.lean:142`, producers in `Connection/Producers.lean`), plus `christoffelInFrame_sol` and `coeff_bilinOfComp`.  **Missing link:** the `SolutionOn`-package bridge from (B)'s chart-Gram fields (plan Stage-2 "K1 solution-package bridge", never executed — K1 delivered only the subtraction) |
| `rm` | K2-B | `rmDiffVec_deriv` (`ForwardUniqueRmBridge.lean:409`) from the two own-lowered Uhlenbeck interfaces `Riemann04BTensorWithRicciDriftEvolutionInFrameOn` (`Evolution/Uhlenbeck.lean:727`) + time-continuity of `riemannOp`.  **Missing link:** the frame → invariant lift of its pointwise conclusion into a trilinear bundled speed — the quadrilinear analogue of `bilinOfComp` (`ForwardUniqueRmDot.md` "Next smallest steps" item 2) |
| `car` | realization | free once `Sfield` is *constructed* as the `S₀₄` field rather than supplied |
| `sdec` | K2-B | `rmLowComp_deriv` (`ForwardUniqueRmDot.lean`) + `lapComm_reLower_flux` (`ForwardUniqueReLower.lean`) + `lapDiff_eq_div_flux` (`ForwardUniqueRmDiff.lean`).  **Missing links:** (i) componentwise → invariant lift, (ii) the planner decision on the mixed-lowering carrier gap (`ForwardUniqueRmDot.md` "Realization-hypothesis classification": the two honest Uhlenbeck interfaces are own-metric-lowered, and their difference is not `S₀₄`) |
| `bounds` (`ForwardUniqueSlab`, 6 fields) | tower | `fluxLe` ← `fluxNormSq_le`/`rmFluxNormSq_le`, `remLe` ← `remNormSq_le`/`rmRemNormSq_le` (`ForwardUniqueRmBounds.lean`), both taking the slab-uniform background norms as named arguments; `ricciLe` ← `ricciDiffSq_le` (`ForwardUniqueRateLe.lean:351`) + the tensor-level `Ric = tr_g(Rm₀₄)` bridge (`ForwardUniqueRatePro.lean`'s `ricciDiff_eq_trace`, in flight per plan №22); `reactLe` ← the `movingReact0S` micro-bound named OWED by K4 (`movingReact_le`, same in-flight file); `adotLe` ← `connDiffDot_normSq_le` (`ForwardUniqueConnBound.lean`, ONE live `sorry` at `:496`); `volLe` ← compactness of `Icc a c` applied to `traceTimeDerivMetric` |
| `dens` | tower | the chart-Gram → Γ → Rm joint `(t,x)` smoothness tower — does not exist; K3's recorded debt (i) |
| `energyCont` | tower | continuity of `t ↦ ∫ density` up to the closed edge; from `dens` + dominated convergence on the compact slab |
| `densInt`, `densCont` | tower | from `dens` + `CompactSpace M` (continuous ⟹ integrable against a finite measure) |
| `restInt`, `pairInt`, `lapInt`, `divInt`, `remInt`, `nabInt`, `disInt` | tower | same source: each integrand is continuous in `x` once the joint tower exists, and `M` is compact |

Once `dens` is produced, ten of the sixteen Prop members (`dens`, `energyCont`, `densInt`,
`densCont` and the seven integrability fields) should fall together — they are one obligation
wearing ten hats.  The genuinely separate obligations are `gamma`, `rm`, `sdec` (K2-B) and
`bounds` (the quantitative slab layer).

## Design decisions worth keeping

* **Constants are slab-local by construction.**  `bounds : ∀ c ∈ Ioo a b, ∃ C_A …, ForwardUniqueSlab … a c …`.
  Making them global over `Ico a b` would be a silent strengthening: the ruling's discipline is
  that no constant is uniform up to `b`.  This is why `ForwardUniqueSlab` is a second structure —
  it exists only to carry the six constants as parameters.
* **The canonical chart frame is baked into `gamma`.**  `chartFrame I x` = the local frame of the
  trivialization centred at `x`.  Requiring the Christoffel fact in *this one frame per point*
  rather than in every frame keeps the standing input as weak as possible;
  `connDiffLow_hasDerivAt_frame` only ever needs one.
* **`hA`/`hS` are derived, not assumed.**  The bundle carries the *frame-component* (`gamma`) and
  *raised* (`rm`) facts; the invariant `(0,3)`/`(0,4)` speeds — including the moving-carrier
  reaction terms `−2Ric₁(…)` that `connDiffDot`/`rmDiffDot` add — are produced here.  Assuming
  `hA`/`hS` directly would have been a wrapper that moves no mathematics.
* **`hPDE₂` is genuinely needed** (K3 consumes it in `metricDiff_hasDerivAt`), even though K1C-a
  and K2.1 do not use it.  Both PDE upgrades are therefore performed.

## Lean lessons from this pass

* `positivity` cannot see through a `set`-introduced local definition: after
  `set CA := max C_A 0`, the goal `0 < 1/(2*(CA+1))` fails because `CA` is opaque.  Writing
  `max C_A 0` out lets positivity's `max` extension fire.  Same for the `div`-comparison side
  goals.  Do not `set` a quantity whose positivity a tactic must rediscover.
* The Young parameters must be passed to `metrics_eq_on` as **named implicit arguments**
  (`(ε := 1/2) (δ := …) (C_A := max C_A 0)`).  Supplying them by `(by norm_num)` against the slot
  `0 < ?ε` cannot work — the tactic has nothing to prove against.
* `metricRicciAt_apply_eq_ricciTensor` is stated with `vec2 v w`; the lane's PDE slots use
  `fun i : Fin 2 => if i = 0 then X else Y`.  These are definitionally equal (`vec2` is exactly
  that lambda), so a `have … : … := metricRicciAt_apply_eq_ricciTensor …` with the lambda form
  ascribed elaborates without any rewriting.
* `ricciTensor` lives in `DifferentialGeometry.Integral.Connection`, NOT in the root
  `DifferentialGeometry` namespace, so inside `namespace DifferentialGeometry.PDE.RicciFlow` it is
  *not* in scope without an `open`.  The endpoint gets it from its own `open
  DifferentialGeometry.Integral.Connection`; here it is written out qualified, matching the lane
  style of `ForwardUniqueRmDot.lean` (`…Connection.riemannOp`).
* `div_le_div_iff` no longer exists in this Mathlib; the current name is `div_le_div_iff₀`.
* `set_option … in` must come **before** the docstring, not between the docstring and the
  `theorem`: `/-- … -/ set_option … in theorem …` is a parse error ("unexpected token 'set_option';
  expected 'lemma'").
* Four of (B)'s fields (`hab`, `h1cont`, `h2smooth`, `h2cont`) are genuinely unused — the smooth
  class makes the C⁰ fields redundant, only the lowering flow's chart-Gram smoothness is consumed,
  and `metrics_eq_ico` needs no `a < b`.  They are kept for interface fidelity with a scoped
  `set_option linter.unusedVariables false in`, which is the right trade here: renaming them to
  `_h1cont` would destroy the point of the theorem.

## Verification

Focused check green; authoritative targeted build of the module GREEN.  `#print axioms` on all six
public theorems (`chartFrame_isFrame`, `chartFrame_mem`, `connSpeed_hasDerivAt`,
`rmSpeed_hasDerivAt`, `pde_hasDerivAt`, `forward_unique_of_inputs`) returns exactly
`[propext, Classical.choice, Quot.sound]`.  Zero `sorry` in the file.

The module is **not** wired into the root aggregate — that is the planner's step, as for the other
lane files.

## Next targets

1. `dens` (the hdens tower) — highest leverage: ten of sixteen bundle members.  A brick aimed at
   exactly this (`Evolution/ForwardUniqueDensReg.lean`) was in flight in a concurrent lane session
   at the time this file landed; check it before re-deriving anything.
2. The two frame → invariant lifts (`rm`, `sdec`): the quadrilinear `bilinOfComp` analogue.
3. The `SolutionOn`-package bridge from (B)'s chart-Gram fields, which unblocks `gamma`.
4. `ForwardUniqueConnBound.lean:496` — the one live `sorry` under `adotLe`.
