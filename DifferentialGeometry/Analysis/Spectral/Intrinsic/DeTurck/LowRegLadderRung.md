# LowRegLadderRung.lean — E0a′/A1c/A1d, the `k`-uniform ladders of the low-base arms

Status (2026-08-04): **GREEN and complete — the ladder layer of F6 is closed.**
`a2_ladder` (`a₂` arm), `a1_ladder` (`a₁` arm, A1c) and `n_diff_hm_rung` (the
assembled `N T − N 0` ladder at every rung, A1d) are all proved and
unconditional.  See "A1c/A1d" near the end of this note for the two new
theorems, the `κ`-free ruling, and the engine re-gating that A1c required
(recorded in `DeTurckRemainderPrincipalArmOpNorm.md`).

Status (2026-08-03): **GREEN, and `a2_ladder` is now UNCONDITIONAL** (gate
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
plumbing).  ~~and the `a₁` arm's ladder~~ — **done 2026-08-04, see below.**

## A1c `a1_ladder` + A1d `n_diff_hm_rung` (2026-08-04)

Both proved, both first-try green.  File is 586 lines, zero `sorry`.

### `a1_ladder` — the shape ruling: **`κ`-free**

The dispatch asked for a reconciliation between two recorded shapes: the
PLAN4-tail `κ`-form
`‖a₁ T‖_{H^m} ≤ κ·(δ/(1−δ)²)·‖T‖_{H^{m+1}} + Clower m·‖T‖_{H^m}`
and the №111-era `κ`-free consumer signature
`‖a₁ T‖_{H^m} ≤ Clower m·‖T‖_{H^{m+1}}`.  **The `κ`-free form is what landed**,
and the reason is structural, not a matter of convenience:

* `A.a1 W = appCc g 2 2 A.C0 W + appCc g 3 2 A.C1 (∇W)`.  Its top slot is the
  `C1` arm at order **one**, so the honest top norm is `H^{m+1}` — there is no
  `H^{m+2}` term to make small, and the `+1/+0` pair the PLAN4 tail proposed
  would have put the top term at `H^{m+1}` and the lower one at `H^m`, i.e. it
  would have claimed the whole arm is *small*.
* No smallness is available for `A.C0`/`A.C1` anyway.  `lowData_split` caps only
  `A.C2` (`K·δ/(1−δ)²`); the C0/C1 towers give jet control with constants
  depending on `R₀`, not a `δ`-small fibre cap.  A `κ`-form would have been an
  over-claim.
* Nothing downstream wants one.  The ladder needs exactly **one** small
  constant, and it lives on `a₂`, where the contraction is proved.  `a₁` is a
  lower-slot arm; charging it entirely to a rung-dependent `Clower m` is what
  `n_diff_hm_rung` and the hierarchy consume.

Final statement (`:407`):

```text
a1_ladder (hDim : finrank ℝ E = 3) (g₀) (a) (ha : 2 ≤ a) {R₀} (hR₀)
    {δ} (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1/3) :
  ∃ Clower : ℕ → ℝ, (∀ m, 0 ≤ Clower m) ∧
    ∀ T (hT : symmetry) (hδg) (hδZ),
      ‖T‖_{H^{a+2}} ≤ R₀ →
      ∀ m, ‖(lowBaseData g₀ g₀ T … ).a1 T‖_{H^m} ≤ Clower m * ‖T‖_{H^{m+1}}
```

### Gate: `2 ≤ a`, not `1 ≤ a`

The dispatch predicted `1 ≤ a` (the towers' gate).  The honest ladder gate is
one higher.  `c0_jet_tower`'s `1 ≤ a` only buys `H^{a+2} ↪ C¹` for the *state*;
the ladder additionally has to keep the **coefficient's** Sobolev jet window
inside the a-priori ball, and the binding case `q = 1, m = 1` in dimension three
needs `∇³ C₁`, whose tower window reaches `‖T‖_{H⁴} ≤ ‖T‖_{H^{a+2}}`, i.e.
`a ≥ 2`.  This is sharp for the route, and it is one *below* `a2_ladder`'s
`3 ≤ a`, so it never binds in `n_diff_hm_rung`.

### The engine had to be re-gated first (the one non-routine part of A1c)

The order-generic first-order engine
`exists_appCc_iteratedCovGrad_l2_coeffJetEnvelope_dataJetWindow_le`
(`DeTurckRemainderPrincipalArmOpNorm.lean:4660`) advertised
`2 * finrank ℝ E + 10 ≤ a` (= 16), which would have put the ladder's a-priori
ball at `H^18` — the outcome `A1CUR_PLAN.md:283` warned against.  That gate was
an artefact of a hard-wired band split, **not** a real requirement: `ha_super`
was textually dead in the low half and entered the high half only through two
`omega`s about the split.  Re-splitting at `finrank ℝ E / 2 + m` makes the two
halves exhaustive at `2 * (finrank ℝ E / 2) ≤ a`.  Full record, including the
cost measure (3 direct importers, no external callers of the three
declarations), in `DeTurckRemainderPrincipalArmOpNorm.md`.

**Lesson, and it is the same one the campaign keeps re-learning:** before
accepting an advertised derivative budget, check whether the hypothesis is
*used*.  Here `grep -c ha_super` over the two proof bodies returned zero, and
the two `omega`s that did consume it were visible in one screenful.  The
difference between `16 ≤ a` and `2 ≤ a` was ~10 edited lines and one 267 s
module build.

### `n_diff_hm_rung` (`:542`) — pure assembly, as advertised

```text
n_diff_hm_rung (hDim : finrank ℝ E = 3) (g₀) (a) (ha : 3 ≤ a) {R₀} (hR₀)
    {δ} (hδ0) (hδ_le : δ ≤ 1/3) :
  ∃ (κ : ℝ) (Clower : ℕ → ℝ), 0 ≤ κ ∧ (∀ m, 0 ≤ Clower m) ∧
    ∀ T (hT) (hδg) (hδZ), ‖T‖_{H^{a+2}} ≤ R₀ →
      ∀ m, ‖deTurckSmoothRemainder g₀ g₀ T … − deTurckSmoothRemainder g₀ g₀ 0 …‖_{H^m}
        ≤ κ * (δ/(1−δ)^2) * ‖T‖_{H^{m+2}} + Clower m * ‖T‖_{H^{m+1}}
```

Proof is literally `rw [lowData_split.1, smoothCcToTensorHs_add]` then
`norm_add_le` over `a2_ladder` and `a1_ladder`, with
`Clower m := C2low m + C1low m` and `κ` inherited unchanged from `a2_ladder`.
Gate `3 ≤ a` is `a2_ladder`'s and subsumes `a1_ladder`'s.  This is
`F6_ESTIMATE_RECON.md` §7.3 row **E0e**.

### New private helper `coeffCap` (`:308`)

The engine wants a *uniform pointwise fibre cap* on the coefficient
(`∀ x, riemannianFiberNormSq … C ≤ Λ²`).  For `a₂` that cap is the smallness
clause of `lowData_split`; for `a₁` there is none, so `coeffCap` manufactures a
non-small one from the tower plus the ball: supercritical Sobolev
(`exists_riemannianFiberNorm_le_iteratedCovGrad_l2_jetSum_supercritical`) needs
only `∇ʲ C`, `j ≤ finrank/2 + 1`, and each tower window
`∑_{l<j+2}‖∇ˡT₀‖²` sits inside `range (a+3)`, bounded by `(C2·R₀)²` through
`exists_iteratedCovGrad_sum_le_smoothCcToTensorHs_general`.  Needs
`finrank ℝ E / 2 ≤ a` only.  `hR₀ : 0 ≤ R₀` turned out **not** to be needed and
was dropped from the helper (weakest-assumptions rule; the caller passes `R₀`
by name).

### Lean details worth keeping

* The engine's `C : SmoothCcTensor g₀ (2 + m) 2` accepts `A.C0 : … 2 2` at
  `m = 0` and `A.C1 : … 3 2` at `m = 1` by plain defeq — no `Nat.add_zero` /
  `Nat.reduceAdd` massaging was needed anywhere, and likewise
  `iteratedCovGrad g₀ 0 2 0 T` unified with `T` (`iteratedCovGrad_zero` is
  `rfl`).  The file's `backward.isDefEq.respectTransparency false` helps here.
* `A.a1 T = appCc g₀ 2 2 A.C0 T + appCc g₀ 3 2 A.C1 (∇T)` is `rfl`, exactly like
  `a2_ladder`'s `hshape`.
* Jet ↔ `Hs` in **both** directions is available directly in the
  `smoothCcToTensorHs` currency — `exists_smoothCcToTensorHs_le_iteratedCovGrad_sum_general`
  and `exists_iteratedCovGrad_sum_le_smoothCcToTensorHs_general` — so no detour
  through `ccTensorToHs` / `hsJet_le` / `hs_le_jet` was needed.  `choose` over
  `n` turns each into the constant *family* the rung-dependent `Clower` wants.
* `refine … (le_of_eq ?_); rw [Finset.sum_mul]` is more robust than
  `rw [← Finset.sum_mul]` at the end of a `≤` chain: the latter relies on `rw`'s
  trailing `rfl` closing an `a ≤ a` goal through the `@[refl]` extension.
* The coefficient bundle is bound opaquely (`obtain ⟨A, hAdef, …⟩ … ; rw [hAdef]`)
  for the same reason as in `a2_ladder`: nothing may unfold the path-integral
  witnesses.

### Verification

Focused check of `LowRegLadderRung.lean`: clean in 20.3 s, **zero warnings**.
Targeted module build of the re-gated engine: green.  Axiom census via
`ScratchC01Census.lean`.  No `maxHeartbeats` added.


## Adapter D — the A2-ABS binder hoist (2026-08-04, Galerkin-lane brick)

`PSTOP_PROPOSITION.md` §10 adapter D / planner No. 128–129.  The three ladder
theorems used to bind `{δ}` **before** their existentials, so the intended
downstream choice "pick the fibre threshold `δ*` from the absorption constant
`κ`" (`κ · δ*/(1-δ*)² < 1 - 2ε`) was formally circular: `κ` was produced only
after `δ` was already fixed.

### New binder order

* `a1_ladder` — **fully hoisted**:
  `∃ Clower, (∀ m, 0 ≤ Clower m) ∧ ∀ {δ} (hδ0) (hδ_le) (T) (hT) (hδg) (hδZ), ball → ∀ m, …`.
  Every input of the first-order arm (`c0_jet_tower`, `c1_jet_tower`,
  `coeffCap`, the coefficient-abstract engine, the two `smoothCcToTensorHs ↔
  iteratedCovGrad` conversions) is `δ`-free, so the constant family is genuinely
  `δ`-free.
* `a2_ladder` — **`κ` hoisted, `Clower` not**:
  `∃ κ, 0 ≤ κ ∧ ∀ {δ} (hδ0) (hδ_le), ∃ Clower, (∀ m, 0 ≤ Clower m) ∧ ∀ T …`.
* `n_diff_hm_rung` — same shape as `a2_ladder`; it just forwards.

Both are `intro`-motion refactors: no estimate was reproved, and the proof
bodies are byte-for-byte the old ones after the `refine`/`intro` split.

### Why `a2_ladder`'s `Clower` could not be hoisted (honest record)

`κ` is `lowData_split`'s `K` (`DeTurckRemainderLowBaseAction.lean:3841`), whose
own statement is already in the hoisted shape `∃ K, 0 ≤ K ∧ ∀ T hT {δ} …` — so
`κ` is `δ`-free by construction, and the absorption threshold is certifiable.
`Clower` is `appCc_cap_hs_le`'s `Cop`, obtained from
`exists_appCc_secondCovGrad_fibreSmallCoeff_Hs_family_le` at the fibre cap
`εC = K · δ/(1-δ)²`.  In that engine
(`ConnLapCommutatorCoefficientTame.lean:1362`) the lower constant is

  `ClowerFn j = Mbase + ∑_{i<j} CEcomm i`,
  `Mbase = εC(1 + Cj0) + (Cgrad + εC·Cj1) + εC·Cj0 + 1`,

i.e. **affine and monotone in `εC`**, with `CEcomm, Cgrad, Cj0, Cj1` all
`εC`-free.  Since `δ ≤ 1/3` gives `δ/(1-δ)² ≤ 3/4`, a `δ`-free bound
`Clower(δ) ≤ Mbase((3/4)K) + ∑ CEcomm` exists mathematically — but the engine
returns `ClowerFn` under an `∃`, so it is not accessible from outside.

Routes that do **not** work, recorded so they are not re-tried:

* calling the engine at `εmax = (3/4)K` gives the `δ`-free lower constant but
  destroys the small top constant (the two are tied to the same `εC`);
* rescaling the coefficient `C₂ = (εC/εmax)·C₂'` fixes the fibre cap but
  multiplies the coefficient's jet tower constant by `(εmax/εC)²`, which is
  `δ`-dependent again.

Smallest bridge that would give a fully `δ`-free `Clower` (NOT done here — it is
a re-proof inside another lane's file, not a binder hoist):
add `exists_appCc_secondCovGrad_fibreSmallCoeff_Hs_family_le_unif`, the same
statement with `(εmax) (hεmax : 0 ≤ εmax)` bound first and `∀ εC, 0 ≤ εC → εC ≤
εmax → …` inside, proved by evaluating `Mbase` at `εmax`; the three `nlinarith`
steps only need `εC ≤ εmax` plus nonnegativity.

**This is not a RULING2 stop-signal-8 event.**  Stop-signal 8 fires if the
*absorption* constant depends on `δ`; it does not.  A rung constant chosen after
`δ*` is exactly the order of choices of `PSTOP_PROPOSITION.md` §5.

### Consumers

None outside this file: `n_diff_hm_rung` is the only consumer of `a2_ladder`
and `a1_ladder`, and nothing consumes `n_diff_hm_rung` yet.  `ScratchC01Census.lean`
only `#print axioms` them, so no `'`-variants were needed — the theorems were
restated in place.

### Verification

Focused check clean; targeted module build green; the ladder trio re-censused
after the hoist: `propext, Classical.choice, Quot.sound` only.  No new
`maxHeartbeats`.

## M3 — the ball-free (quad) ladder layer (2026-08-04)

### What landed

Five new sorry-free, axiom-clean declarations; the four original statements are
byte-identical and their census is unchanged.

* `c2JetTowerQ` — `c2_jet_tower` with the `a`, `R₀`, `hball` binders **gone**.
  The diagnosis of PLAN5 No. 146-executor is CONFIRMED: those binders were
  vestigial.  The proof runs through `topKer_jet`, which takes only `hDim` and
  the background metric; `hball` was `intro`-ed and never used.  `c2_jet_tower`
  is now a four-line wrapper of `c2JetTowerQ`.
* `c1JetTowerQ` (in `LowRegC01JetTower.lean`) — the same exorcism for
  `c1_jet_tower`, whose ball was likewise inert (`low1Ker_jet` needs only
  `hδ_le : δ ≤ 1/3`).
* `a2LadderQ`, `a1LadderQ`, `nDiffHmQ` — the ladder layer with the a-priori-ball
  *binder* removed.  Shape:

  ```
  ∃ κ, 0 ≤ κ ∧ ∀ {δ} hδ0 hδ_le,
    ∃ Clower : ℝ → ℕ → ℝ, (∀ R m, 0 ≤ Clower R m) ∧
    ∀ T hT hδg hδZ {R} (hR : ‖T‖_{H⁵} ≤ R) m,
      ‖…‖_{H^m} ≤ κ·δ/(1-δ)²·‖T‖_{H^{m+2}} + Clower R m·‖T‖_{H^{m+1}}
  ```

  No `a`, no `R₀` fixed before the state, **no admissibility hypothesis on `T`**:
  the estimate holds for every state, and the consumer supplies the radius after
  seeing the state (`R := ‖T‖_{H⁵}` is always legal).  `κ` is still produced
  before `δ` (A2-ABS) and `Clower` before the state (TK3), now as a function of
  the radius.  `a1LadderQ`'s sharp radius is `H⁴`; `nDiffHmQ` merges the two into
  the single `H⁵` slot by `hsMono`.

  `a2_ladder` is now a **corollary** of `a2LadderQ` (instantiate `R := R₀`, use
  `hsMono` for `5 ≤ a + 2`), so the ball form costs no duplicated proof.
  `a1LadderQ` goes the other way (`choose` over `R` applied to `a1_ladder`), and
  `nDiffHmQ` is the same one-line triangle inequality over `lowData_split`.

### THE OBSTRUCTION — the lower constant CANNOT be made `H²`/`H³`-only

This is the M3 dispatch's stop condition, and it fires.  The dispatch asked for
a lower constant depending "only on the H² state ball / the quad towers'
`(K₀ + K₂‖T‖²_{H³})` data".  That is not available, for a reason that is
arithmetic, not tooling.

**Sharp exponent count (route-independent).**  `a₂T = appCc C₂ (∇²T)`.  Leibniz
at rung `q ≤ m` gives `∑_{l≤q} ‖∇^l C₂ ⊗ ∇^{q-l+2}T‖_{L²}`.  The `l = 0` term is
the top term and is charged to the pointwise fibre cap `εC = κδ/(1-δ)²` — that
part is genuinely `δ`-only and ball-free.  For `l ≥ 1` one of the two factors
must go to `L^∞`, which in dimension three costs `finrank/2 + 2 = 3` extra
`L²`-orders, i.e. two extra derivatives:

* `‖∇^l C₂‖_{L^∞}·‖∇^{q-l+2}T‖_{L²}`: the tower gives
  `‖∇^i C₂‖_{L²} ≲ 1 + ‖T‖_{H^{i+1}}`, so the first factor costs `‖T‖_{H^{l+3}}`
  and the product sits at total order `(l+3) + (q-l+2) = q + 5`;
* `‖∇^l C₂‖_{L²}·‖∇^{q-l+2}T‖_{L^∞}`: `(l+1) + (q-l+4) = q + 5` — identical.

The conclusion's lower slot is `‖T‖_{H^{q+1}}`, so a log-convexity trade
`f α · f β ≤ f A · f Γ` (valid exactly when `α + β ≤ A + Γ`) needs
`q + 5 ≤ A + (q+1)`, i.e. **`A ≥ 4`**.  No choice of Hölder split, no re-gating
and no quad tower lowers this: it is the same count on both sides.  So the a₂
arm's lower constant needs an `H⁴` anchor at minimum, and the landed engine
realizes `A = a + 2 = 5`.

**Where the engine spends the extra derivative** (grep-verified, for the record).
`master_appCc_jet_le_sharp` (`ConnLapCommutatorCoefficientTame.lean:475`) is
called at exactly two shift pairs, `(dc, dd) = (3, 2)` and `(2, 3)` (`:1022`,
`:1026`) — `dc` is the coefficient's own order shift, `1` for `C₂` itself
(`coeff_jet_linear_of_sq`, `:820`) plus up to two commutator derivatives.  Its
two gates are `ht1 : t + finrank/2 + 1 + dc ≤ a + 2` (region one, the `L^∞` cap
on low coefficient jets) and `ht2 : finrank/2 + 1 + dd ≤ t + 4` (region two, the
`hs_extreme_interp` trade at `:719`).  In dimension three these read
`t + dc ≤ a` and `dd ≤ t + 2`, which for `(3,2)` force `a ≥ 3` at `t = 0` and for
`(2,3)` force `a ≥ 3` at `t = 1`.  Hence
`exists_appCc_secondCovGrad_fibreSmallCoeff_Hs_family_le`'s advertised gate
`max 2 (finrank/2*2+1) ≤ a` is not slack — it is exactly the binding constraint,
and `appCc_cap_hs_le`'s `H⁵` is one above the sharp `H⁴`.

The a₁ arm is one order better but still above `H³`: the low band of
`exists_appCc_iteratedCovGrad_l2_coeffJetEnvelope_dataJetWindow_le` (`:4670`)
splits at `finrank/2 + m`, leaving `q ≤ 1` to the ball side, which needs the
coefficient window `∇^{i+j}C`, `i ≤ q`, `j ≤ finrank/2 + 1`, inside the ball —
i.e. `a ≥ 2`, ball `H⁴`.

**Correction to the No. 146-executor feasibility note.**  `coeffCap`'s
coefficient-jet window is indeed `range (finrank/2 + 2) = range 3` (`j ≤ 2`), but
each such `j` drags the tower's *state* window `∑_{l < j+2}`, i.e. `l ≤ 3`.  So
even the arm the note called "H²" is an `H³` quantity, and `coeffCap` is in any
case only one of the two ball uses in `a1_ladder`.  The `H²`-only reading
conflated the coefficient index with the state index.

### Consequence for J4 (rung-3..5) — planner ruling needed

`n_diff_hm_rung`/`nDiffHmQ` at `m = 2` gives a lower coefficient depending on
`‖U_N(t)‖_{H⁵}`.  For the projected trajectory the available a-priori data are
`‖U_N(t)‖_{H²} ≤ R` and `‖U_N‖_{L²_tH³} ≤ B₃` (`PSTOP_PROPOSITION.md` §6.1(i),
(ii)); `H⁵` is exactly what rung 5 is supposed to *produce*, so feeding it back
in at rung 3 is circular.  The quad ladders therefore do **not** unblock J4's
rung closures, and no re-derivation of them will.

Two readings, both consistent with the landed code:

1. **PSTOP §6.1 already says so.**  Its rung-3..5 closure is "tower-direct", and
   it explicitly hands the `H⁵` ball radius `R₅ := (2Φ₅)^{1/2} + 1` to the
   `a2_ladder`-based HIGH rungs `k ≥ 6`.  On that reading M3's premise (ladders
   at rungs 3–5) was the under-count, and the ladders are already correctly
   scoped — the quad forms landed here are then a convenience: the `k ≥ 6`
   consumer no longer has to fix `R₅` before the state.
2. If the rung-3..5 pairing is nevertheless to be routed through a ladder, the
   ladder's lower slot has to be widened from `‖T‖_{H^{m+1}}` to something the
   `L^∞` cost can be paid from — e.g. a Moser/tame form
   `Clower m · (1 + ‖T‖_{H^{m+3}})·‖T‖_{H^{m+1}}` — which is a different rung
   design and changes §3's absorption arithmetic.  That is a planner decision.

Independently, §6.3's BUDGET CHECK ("the towers' `range (i+2)` window at
`i = k−1` reaches state jets `j ≤ k`, strictly BELOW `E_{k+1}`") omits the same
`L^∞` embedding cost, so the tower-direct route at rungs 3–5 should be re-priced
with `+2` orders before it is treated as settled.

### The one remaining cheap improvement (not done)

`Cm q = √(appCcGdiag q · (S1 q + S2 q))` with `S1, S2` each carrying a factor
`(1 + R₀)²` (`master_appCc_jet_le_sharp`, `:502`/`:512`), so the engine's lower
constant is **affine in `(1 + R₀)`**.  If that factorization were exposed —
`Clower = (1 + R₀)·Ĉ` with `Ĉ` radius-free — `a2LadderQ` would upgrade from an
opaque `Clower R m` to the genuine tame form
`Ĉ(m)·(1 + ‖T‖_{H⁵})·‖T‖_{H^{m+1}}`.  It requires threading the factorization
through `exists_appCc_covGradCoeff_secondCovGrad_l2_le` and the commutator chain
inside `ConnLapCommutatorCoefficientTame.lean`, i.e. edits in a low shared file
(full-cone rebuild).  It does not change the `H⁵` obstruction above.

### Lean lessons

* `tensorHs.ext` does not resolve in this file; the namespace is
  `DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation`, so the local
  `hsMono` uses `Analysis.Parabolic.TensorHeatEquation.tensorHs.ext`.
  `smoothCcToTensorHs_norm_mono` already exists but is `private` in
  `DeTurckPrincipalArmEnergyCrossTerm.lean`; `hsMono` is the third private copy
  of a five-line fact — worth making the original public the next time that file
  is edited for another reason.
* Passing a `ℕ` literal `a := 3` makes the ball read `((3 : ℕ) : ℝ) + 2`, not
  `(5 : ℝ)`; bridge with `smoothCcToTensorHs_norm_order_congr … (by push_cast;
  norm_num)`.  Stating the quad radius at the honest literal `(5 : ℝ)` keeps the
  public statement readable.
* `choose … using fun R : ℝ => <engine> (R₀ := |R|) (abs_nonneg R)` is the whole
  ball-binder hoist: `|R|` supplies the engine's `0 ≤ R₀` for free and
  `le_abs_self` discharges the ball at the call site.

### Verification

Focused checks green on `LowRegC01JetTower.lean` and `LowRegLadderRung.lean`;
targeted builds green for both modules, for `ScratchC01Census`, and for the
downstream consumer `LowRegAllOrderJet` (whose only `sorry` remains the
pre-existing `lowreg_loMass`).  Axiom census re-run over the whole census file:
**zero `sorryAx`**; the five new declarations and the five originals
(`a1_ladder`, `a2_ladder`, `n_diff_hm_rung`, `c1_jet_tower`, `c2_jet_tower`) all
depend on `[propext, Classical.choice, Quot.sound]` only.  No new
`maxHeartbeats`.

## 2026-08-05 — `c2JetTowerSharp` (PSTOP adapter G / (B-WIN))

`c2JetTowerSharp` is the sharp-window form of the a₂ coefficient tower,
`‖∇^i A.C2‖² ≤ Kc i (1 + ∑_{j ∈ range (i+1)} ‖∇^j T‖²)`, proved from
`topKerJetSharp` by the same proof the `range (i+2)` version used (only the
window constant changed).  `c2JetTowerQ` is now a four-line weakened wrapper
with a **byte-identical** statement, so `c2_jet_tower`, `a2LadderQ` and every
hypothesis-style consumer (the operator-norm engines that take the tower in the
`range (i+2)` shape) are untouched; their axiom census is unchanged.

Load-bearing use: `LowRegA2PerIndex.lean`'s `c2SupJet` reads the tower at index
`i+2` (the sup embedding's `+2`) and needs the state window to stop at `i+2`,
not `i+3`.  That is the whole difference between an absorbable rung-`k` pairing
against `‖T‖_{H^{k+1}}` and a circular one against `‖T‖_{H^{k+2}}`.

Note on `a2LadderQ`: it still consumes the **weak** `c2JetTowerQ`, deliberately.
Its `H⁵` ball is structural (the log-convexity swap `A ≥ 4` of M3), so sharpening
the tower does not help it; the sharp window is only useful on the tower-direct
route, which does not collapse onto a lower slot.

## 2026-08-05 — explicit ordered high-rung package

`IsHmRungOrd g κ` now records the exact universal continuation of `nDiffHmQ`
with its top coefficient selected before `δ`, the state, the `H⁵` radius, and
the rung.  `lowregHmPack` selects that coefficient once.  The package adds no
new assumption and deliberately stores no solve witness, horizon, realization,
or lower-radius data.

This is only the generic high-rung certificate.  It is not a partial common
gate package: the honest common package must wait for the still-missing q=3 and
q=4 ordered certificates, then dominate all fixed-rung and high-rung gates in
one envelope before the solve is recalibrated.

Focused verification and the targeted export refresh passed.  The package is
a wrapper around the already-checked theorem and introduces no new proof
frontier.
