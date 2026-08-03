# LowRegLadderRung.lean — E0a′, the `k`-uniform ladder for the low-base `a₂` arm

Status: **GREEN, and `a2_ladder` is now UNCONDITIONAL** (2026-08-03; gate
lowered to `3 ≤ a` the same day by the threshold brick, see "The `a = 3`
bottom" below; `c2_jet_tower` proved the same day by the reduction brick, and
its last input `topKer_jet` proved by TK3 — see "The frontier, closed" below).
Focused check clean with zero warnings; targeted module builds clean.  No
`maxHeartbeats` bump, no `set_option` beyond the sibling file's
`backward.isDefEq.respectTransparency false`.

Axioms: `appCc_cap_hs_le`, `c2_jet_tower` and **`a2_ladder`** are all
**axiom-clean** (`propext, Classical.choice, Quot.sound`).  Nothing in this
file, or in anything it depends on, carries `sorryAx`.

Brick: **E0a′** of `ShortTime/F6_ESTIMATE_RECON.md` §5 — the ladder assembly that
turns `LowRegDissipRung.lean`'s `k = 0` rung into a rung-uniform family.

## What is proved

### `a2_ladder` (`:232`) — the ladder, `k`-uniform top constant

```
hDim : finrank ℝ E = 3,  a : ℕ,  ha : 3 ≤ a,  hR₀ : 0 ≤ R₀,
0 ≤ δ,  δ ≤ 1/3
⊢ ∃ κ (Clower : ℕ → ℝ), 0 ≤ κ ∧ (∀ m, 0 ≤ Clower m) ∧
    ∀ T symmetric, ∀ (the two gFibreOpBound certificates at δ),
      ‖T‖_{H^{a+2}} ≤ R₀ →
      ∀ m : ℕ,
        ‖(lowBaseData g₀ g₀ T …).a2 T‖_{H^m}
          ≤ κ * (δ / (1 - δ)^2) * ‖T‖_{H^{m+2}}
            + Clower m * ‖T‖_{H^{m+1}}
```

all norms spelled `‖smoothCcToTensorHs g₀ · T‖`.  Realized `κ` is exactly
`lowData_split`'s cap constant `K`.

**The top constant `κ · δ/(1-δ)²` contains no `m`.**  That is the whole point:
one smallness threshold on `δ` makes the arm a contraction *simultaneously at
every rung*, which is what `F6_ESTIMATE_RECON.md` §5.3 clause 1 left open and
what `AppCcSplitEnvelope.lean`'s Leibniz-grid route provably could not give
(its `C k ≳ (2(n+1))^{(k+1)/2}`).  All rung-dependent cost sits in `Clower m`,
multiplying only the lower order `H^{m+1}` — which is exactly L4's own shape
(`Crem : ℕ → ℝ` is `k`-dependent there too).

### `appCc_cap_hs_le` (`:77`) — the de-gated `m`-form of the engine, sorry-free

```
ha : max 2 (finrank ℝ E / 2 * 2 + 1) ≤ a          -- dim 3: 3 ≤ a
⊢ ∃ Cop, (∀ m, 0 ≤ Cop m) ∧ ∀ C₂ T₀,
    ‖T₀‖_{H^{a+2}} ≤ R₀ →
    (∀ x, rfns g₀ 4 2 x (C₂.toSection x) ≤ εC²) →
    (∀ i, ‖∇ⁱC₂‖² ≤ Kc i (1 + ∑_{j<i+2} ‖∇ʲT₀‖²)) →
    ∀ m, ‖appCc C₂ (∇²T₀)‖_{H^m} ≤ εC ‖T₀‖_{H^{m+2}} + Cop m ‖T₀‖_{H^{m+1}}
```

This is the object the autopsy pointed at, but **two notches better than the
shipped wrapper** `exists_smoothCcToTensorHs_appCc_fibreSmallCoeff_opNorm_le`
(`DeTurckRemainderPrincipalArmOpNorm.lean:5129`):

* **gate halved, then sharpened**: `finrank ℝ E + 5 ≤ a` instead of
  `2·finrank ℝ E + 10 ≤ a`, and — after the threshold brick below —
  `max 2 (finrank ℝ E / 2 * 2 + 1) ≤ a`.  In dim 3 the a-priori ball drops
  `H^{18} → H^{10} → H⁵`.
* **fibre factor dropped**: top constant `εC`, not `deTurckArmFibreConst n · εC
  = √(n³)·εC` — a factor `√27 ≈ 5.2` off the smallness threshold in dim 3.

## The engine instance used, and what the de-gating actually was

Producer: `exists_appCc_secondCovGrad_fibreSmallCoeff_Hs_family_le`
(`Sobolev/TensorHilbert/ConnLapCommutatorCoefficientTame.lean:1334`), the
order-generic coefficient-abstract engine, **called verbatim** at its own gate.
Two gate-free closers finish the `m`-form:

* `oneMinusConnLapSmoothIter_zero` (`Garding/SobolevScaleSummable.lean:124`,
  `:= rfl`) — read the resolvent family at `p = 0`, i.e. `S = T₀`, so the
  membership side condition is literally `⟨0, rfl⟩`;
* `smoothCcToTensorHs_rawTensorConnLapSmooth_le`
  (`DeTurckRemainderPrincipalArmOpNorm.lean:48`) — the constant-one spectral
  shift `‖Δ_raw T‖_{H^σ} ≤ ‖T‖_{H^{σ+2}}`, all real `σ`, gate-free;
* one cast repair `((m+1 : ℕ) : ℝ) = (m : ℝ) + 1` via
  `smoothCcToTensorHs_norm_order_congr`
  (`DeTurckPrincipalArmEnergyCrossTerm.lean:64`).

**Why the shipped wrapper's gate was excess, and how the excess was found.**
`exists_…opNorm_le` (`:5129`) composes two halves.  `…_le_zero` (`:4875`) binds
`ha_super : 2n+10 ≤ a` and then **never uses it** — its body calls only
`exists_Ccross_for_secondCovGrad` and
`exists_iteratedCovGrad_sum_le_smoothCcToTensorHs_general`, both gate-free.
`…_le_succ` (`:5055`) forwards `ha_super` to `:1323` through a single
`(by omega)` proving `n+5 ≤ a`.  So the `2n+10` on the public wrapper is a
vestigial binder, not an analytic requirement.  Since the task forbade editing
the supercritical statements, `appCc_cap_hs_le` re-derives the `m`-form from
`:1323` directly rather than weakening those two signatures — 20 lines, no proof
body copied.

**The `a = 2` de-gate, honestly: it does NOT close, and the autopsy §5 risk 2 is
partly refuted.**  The autopsy expected `n+5 ≤ a` to be "mechanical but wide"
bookkeeping re-derivable at fixed dim-3 orders.  Traced to the leaf, the
obligation is not merely wide — at `a = 2` it is **arithmetically false**:

* `master_appCc_jet_le_sharp` (`ConnLapCommutatorCoefficientTame.lean:475`)
  splits the Leibniz index at `t := n/2 + 3` and uses the sup-window
  `w := n/2 + 2`.  On region 1 (`i ≤ t`) its budget step
  `hbound : i + m + dc ≤ a + 2` (`:563`) is worst-case
  `t + (w−1) + dc ≤ a + 2`.  Dim 3, `dc = 3`: `4 + 2 + 3 = 9 ≤ a + 2`, i.e.
  `a ≥ 7`.  At `a = 2` this reads `9 ≤ 4`.  There is no `omega` to re-derive.
* Region 2 is fine at `a = 2`: `hsum_ok` (`:716`) needs only
  `dc + (w−1) + dd ≤ a + 5`, i.e. `3+2+2 = 7 ≤ 7`.  The binding constraint is
  region 1's need for a **numeric** coefficient-sup bound, which log-convexity
  (`hs_extreme_interp`, `:306`) cannot supply there because that branch has no
  `f γ` on the right to trade against.
* Making the split threshold `t` a *parameter* of the private leaf, the two
  `master_…` call sites need `0 ≤ t' ≤ a−3` (`dc,dd = 3,2`) and
  `1 ≤ t' ≤ a−2` (`dc,dd = 2,3`); both close **iff `a ≥ 3`**, i.e. ball `H⁵`.
  So the reachable bottom in dim 3 is `a = 3`, not `a = 2`.

De-gating obligations re-derived in the original pass: **one** — the single
`(by omega)` that `…_le_succ` used, replaced by calling `:1323` at its own gate.

## The `a = 3` bottom, realized (threshold brick, same day)

The six gated call sites the autopsy listed have since been re-derived, by
parameterizing the leaf's split threshold.  `master_appCc_jet_le_sharp`
(`ConnLapCommutatorCoefficientTame.lean:475`) now takes `t : ℕ` with

```
ht1 : t + finrank ℝ E / 2 + 1 + dc ≤ a + 2     -- region 1 (i ≤ t)
ht2 : finrank ℝ E / 2 + 1 + dd ≤ t + 4         -- region 2 (t < i)
```

and **no `ha` at all**: those two hypotheses discharge all three budget `omega`s
in the body (`hbound` at region 1, `hβγ` and `hsum_ok` at region 2).  The private
forwarder `appCc_term_Hs_bound_sharp` threads `t` through unchanged.  The three
public theorems of that file now gate on the sharp, dimension-general
`max 2 (finrank ℝ E / 2 * 2 + 1) ≤ a`, and `appCc_cap_hs_le` inherits it;
`a2_ladder` reads it off `hDim` as **`3 ≤ a`**.

Per-call-site `t` is essential, not cosmetic: the six windows are
`0 ≤ t ≤ a−3` (3,2), `1 ≤ t ≤ a−2` (2,3), `0 ≤ t ≤ a−1` (1,2) twice, and
`1 ≤ t ≤ a` (0,3) twice.  Their **intersection** is `1 ≤ t ≤ a−3`, empty until
`a ≥ 4`; choosing `t` per site (`finrank/2 − 1` for `dd = 2`, `finrank/2` for
`dd = 3`) is what buys the last order.  The top constant is untouched — `t`
only redistributes index mass between `S1` and `S2`, both of which feed the
*lower*-order constant `Cm → CEcomm → ClowerFn`.

## The frontier, closed (TK3, same day)

`topKer_jet` is **proved**, so `c2_jet_tower` and `a2_ladder` are
**unconditional**.  The route was ruling No. 104's ball-free Moser route: the
all-order jet windows of `LowRegOpJetWindows.lean` (TK2 + TK3) for the four
summands of `topKernel_eq`, glued by `moserWin_add`/`moserWin_smul` over the
radial path, whose perturbation `s • T` carries the same fibre bound `δ ≤ 1/3`
for every `s ∈ [0,1]` (`pathPert_rad`).  No Sobolev ball, no `finrank` gate,
and in particular the `a ≥ 3` bottom is untouched.  Details:
`LowRegC2JetTower.md`, `LowRegOpJetWindows.md`.

The campaign's F6 chain now has **zero** `sorry`.  The remaining campaign
`sorry` is `lowreg_spatialMass` (`ShortTime/LowRegAllOrderJet.lean:1053`),
upstream of this file and the target of brick E1′.

## The frontier, moved (reduction brick, same day — historical)

`c2_jet_tower` is **proved**.  Both integral layers landed in the sibling
`LowRegC2JetTower.lean`; the frontier moved *inside* the path integral and was
then `topKer_jet` there — the integrand's per-order jet tower, uniform in the
path parameter.  Campaign frontier count unchanged at exactly ONE (until TK3
closed it).

Two findings from that brick that correct the sketch below:

1. **The differentiation-under-the-integral layer was already complete and
   order-generic.**  `path_jetL2_le` (`ParametricJetIntegral.lean:331`), resting
   on `icg_path_comm` (`:291`, the genuine `∇ⁱ∫ = ∫∇ⁱ` by induction on `i`),
   needed nothing new.  Only the additive rearrangement
   `∫Φ + ∫Ψ − C = ∫(Φ + Ψ − C)` had to be re-derived, because the two existing
   copies are a `private` in `DeTurckRemainderLowBaseAction.lean` and a
   fibre-pointwise (not jet) public lemma.  The new order-generic wrapper is
   `path_add_sub_jet` (`LowRegC2JetTower.lean:78`), axiom-clean.
2. **The `H^{a+2}` ball in `c2_jet_tower` is vestigial.**  `a2_ladder` calls
   `c2_jet_tower` without forwarding `ha : 3 ≤ a`, so `a` is arbitrary and at
   `a = 0` the ball gives nothing.  What actually drives the estimate is
   `δ ≤ 1/3`, which through `hδg` is a pointwise operator bound
   `‖T‖_{L^∞} ≤ 1/3` — the Moser/Gagliardo–Nirenberg input.  `topKer_jet` is
   therefore stated ball-free.

Of the integrand's three summands, `lieRefold2` already has an all-order tower
of exactly the right shape
(`exists_deTurckLieCovDerivRefoldC2Family_cap_l2JetWindow`,
`RiemannCoefficientPalatiniRefold.lean:18865`) — but gated at
`2·finrank ℝ E + 10 ≤ a` and phrased over a *pointwise jet window*, so reusing
it would undo the `a ≥ 3` bottom.  The other two (`ricciTop`, the `Φmet`
deviation) have only fixed-order-two producers.  Full inventory and the
smallest next statement: `LowRegC2JetTower.md`.

## The frontier as it stood before the reduction (historical)

`c2_jet_tower` (`:144`, then a `sorry`) — hypothesis (b) of the engine for
the low-base coefficient:

```
hDim : finrank ℝ E = 3, a : ℕ, hR₀ : 0 ≤ R₀
⊢ ∃ Kc : ℕ → ℝ, (∀ i, 0 ≤ Kc i) ∧
    ∀ T symmetric, ∀ 0 ≤ δ ≤ 1/3 + the two gFibreOpBound certificates,
      ‖T‖_{H^{a+2}} ≤ R₀ →
      ∀ i, ‖∇ⁱ (lowBaseData g g T …).C2‖²
             ≤ Kc i * (1 + ∑_{j < i+2} ‖∇ʲ T‖²)
```

`i = 0` is the second clause of `c2_h2_small`
(`DeTurckRemainderLowBaseAction.lean:13268`).  Route sketch (also in the Lean
docstring): `A.C2 = rhsRefoldTopInt + selfTopInt − deTurckPhiMetTotal`
(`same:3359`) is a **path integral**, so `∇ⁱ` requires differentiating under the
integral sign and bounding the integrand's per-order jets uniformly in the path
parameter; the radial parameter enters only through fibre-resolvent factors,
whose denominators are bounded below on `δ ≤ 1/3`, so the stated uniformity in
`δ` is the right contract.  The supercritical analogue
`deTurckPrincipalCometricCoeff_perOrder_l2_tame_generic`
(`Sobolev/TensorHilbert/AppCcJetWindowTame.lean:1008`) is **not** a template —
its coefficient is algebraic with a Neumann-series tower (autopsy risk 1).  The
`LowRegDissipRung.md` opacity lesson is live: bind the path-integral witness
opaquely before any arithmetic.

Difficulty assessment: this is a genuine estimate, not a routine local proof.
It needs a parametric jet-integral lemma (`ParametricJetIntegral.lean` is
already imported transitively by `DeTurckRemainderLowBaseAction`) plus per-order
envelopes for three summands.  Expect it to be its own brick.

## Home

New sibling of `LowRegDissipRung.lean` in
`Analysis/Spectral/Intrinsic/DeTurck/`, same reasons: the producers live at or
below this layer, `DeTurckRemainderLowBaseAction.lean` is 13.8k lines and cannot
absorb declarations under the 3000-line rule, and F6's eventual consumer
(`HeatSemigroup/GalerkinParabolicEnergyDeTurck.lean`) imports `DeTurck/` but not
`ShortTime/`.

Two imports: `DeTurck.DeTurckRemainderLowBaseAction` (the split, the coefficient
bundle) and `DeTurck.DeTurckRemainderPrincipalArmOpNorm` (which re-exports the
engine from `Sobolev/TensorHilbert/ConnLapCommutatorCoefficientTame` and carries
the two gate-free closers).  Not added to the root aggregate, matching the
sibling.

## Hotspots / Lean lessons

* **`⟨0, rfl⟩` is the whole resolvent-family side condition.**  The engine's
  `(∃ p, S = oneMinusConnLapSmoothIter g₀ 0 2 p T₀)` looks like it forces the
  consumer into the spectral-iterate bookkeeping; it does not, because
  `oneMinusConnLapSmoothIter_zero` is `rfl`.  Reading the family at `p = 0` is
  what turns the `j`-family statement into the usable `m`-form.
* **Cast spelling, again.**  The engine states `((j : ℕ) : ℝ)` and
  `((j + 1 : ℕ) : ℝ)`.  `((m : ℕ) : ℝ)` and `(m : ℝ)` are the *same term* (both
  `Nat.cast m`), so the top slot needs no repair; only `((m+1 : ℕ) : ℝ)` vs
  `(m : ℝ) + 1` needs `smoothCcToTensorHs_norm_order_congr (by push_cast; ring)`.
* **`4` vs `2 + 2` is free.**  `A.C2 : SmoothCcTensor g 4 2` feeds the engine's
  `SmoothCcTensor g₀ (2+2) 2` slot with no coercion work, and
  `A.a2 T = appCc g₀ (2+2) 2 A.C2 (∇²T)` is `rfl`.  Stating that `rfl` as a
  named `hshape` and rewriting is more robust than relying on `exact` to unify
  the two spellings deep inside a norm.
* **The opacity pattern generalizes to a concrete goal.**  E0 rewrote a goal
  whose LHS was `N T − N 0`; here the goal already mentions `lowBaseData …`.
  Wrapping the producers in
  `obtain ⟨A, hAdef, …⟩ : ∃ A, lowBaseData … = A ∧ …` (witness `rfl`), then
  `rw [hAdef]; clear hAdef`, gives the same opaque fvar with a concrete
  statement.  File checks in 19 s with no heartbeat bump.
* `hδ0 : 0 ≤ δ` is needed twice and for different reasons: `lowData_split`
  consumes it, and `0 ≤ K·δ/(1−δ)²` is `mul_nonneg hK (div_nonneg hδ0
  (sq_nonneg _))` — note `sq_nonneg`, not a positivity argument, so no
  `δ ≠ 1` side condition is incurred.

## Where this leaves the ladder

The mathematical claim E0a′ existed to settle — *a rung-uniform top constant
exists for the low-base second-order arm* — is **settled affirmatively and
unconditionally**.  Both residuals are closed:

1. ~~`topKer_jet`~~ — **PROVED** (`LowRegC2JetTower.lean:196`, TK3).  Autopsy
   risk 1 is discharged: the integral layer and the integrand's per-order jet
   tower are both proved, the latter ball-free on the Moser route.
2. ~~The a-priori ball order~~ — **settled**: `H^{a+2}` with `3 ≤ a`, i.e. `H⁵`
   at the bottom in dim 3 (see "The `a = 3` bottom, realized" above).  `H³`/`H⁴`
   is **not** reachable through this engine at all, since region 1 of the leaf
   needs a numeric coefficient-sup bound at order `t + (w−1) + dc ≥ 5`; the
   autopsy §3.3 clause (c) `H³` target stays refuted.  Per planner No. 103 this
   is exactly the right bottom: rungs `m = 0, 1` are covered by the fixed-order
   members, and the ladder takes over from `m ≥ 2`.

Not done here, by design: wiring into `lowreg_spatialMass` (brick E1′, Galerkin
plumbing), and the `a₁` arm's ladder (the lower-order arm; `a1_h2_h1` is the
`m = 0` member).
