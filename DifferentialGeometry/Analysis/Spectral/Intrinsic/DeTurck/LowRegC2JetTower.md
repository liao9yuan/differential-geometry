# LowRegC2JetTower.lean — the two layers under `c2_jet_tower`

Status: **GREEN, sorry-free** (2026-08-03, TK3).  Focused check clean, no
warnings; targeted module builds of this module and of `…LowRegLadderRung`
clean.  No `maxHeartbeats` above 800 000; no `set_option` beyond the sibling
files' `backward.isDefEq.respectTransparency false`.

Axioms: `path_add_sub_jet`, `topKer_jet`, and downstream `c2_jet_tower` and
`a2_ladder` (both in `LowRegLadderRung.lean`) are **all axiom-clean**
(`propext, Classical.choice, Quot.sound`).  **`a2_ladder` is unconditional.**

Brick: the main estimate brick of front 2's F6 — the reduction half.  Entry
points: `ShortTime/F6_ESTIMATE_RECON.md` §5.1e–§5.1h, `LowRegLadderRung.md`,
`LowRegOpJetWindows.md`.

## What this file changed

Before (reduction brick): `c2_jet_tower` (`LowRegLadderRung.lean:144`) was a
bare `sorry`; this file proved it modulo the named frontier `topKer_jet`,
moving the frontier *inside* the path integral — from "the `i`-th jet of a
path-integrated coefficient" to "the `i`-th jet of the integrand, uniformly in
the path parameter".

After (TK3): `topKer_jet` is proved too, on the ball-free Moser route, so the
whole F6 estimate chain `a2_ladder ⇐ c2_jet_tower ⇐ topKer_jet` is
unconditional.

## `path_add_sub_jet` (`:78`) — differentiation under the integral, all orders

```
hSI : uIcc 0 1 ⊆ realizedSmallSet,  hΦ hΨ : threeArmHjoint,  0 ≤ Λ,
hcap : ∀ t ∈ Icc 0 1, lowJetSq g n (Φ t + Ψ t − C) ≤ Λ
⊢ lowJetSq g n (∫₀¹Φ + ∫₀¹Ψ − C) ≤ Λ
```

Same constant, every order `n`, arbitrary tensor rank `r`.  Two ingredients,
both already in the tree and both order-generic:

* `path_jetL2_le` (`Tensor/CovGrad/ParametricJetIntegral.lean:331`) — the
  transfer, resting on `icg_path_comm` (`:291`), which is the actual
  `∇ⁱ ∫ = ∫ ∇ⁱ` commutation, proved by induction on `i` from
  `covGrad_pathIntegral_comm`.  **This was the layer the recon expected to be
  missing; it is not.  It is complete and order-generic.**
* the additive rearrangement `∫Φ + ∫Ψ − C = ∫(Φ + Ψ − C)`, re-derived here from
  public API (`SmoothCcTensor.ext`, `pathIntegralCoeffField_toModel`,
  `intervalIntegral.integral_add/sub/const`) because the two existing copies
  are unusable: `path_add_sub_h2` is `private` in
  `DeTurckRemainderLowBaseAction.lean` (another lane's claim, not editable) and
  `path_add_sub_cap` (`LowRegPathSplit.lean:334`) is fibre-pointwise, not jet.

Interface improvement over both siblings: they take the joint smoothness of the
*combined* integrand as a third hypothesis `hK`; here it is derived internally
from `hΦ`, `hΨ` by `threeArmJoint_add`/`threeArmJoint_sub` plus the private
one-liner `armConst`.  Callers supply two joint-smoothness facts, not three.

Canonical home, honestly: this belongs next to `path_add_sub_cap` in
`LowRegPathSplit.lean`.  It is here instead because `LowRegPathSplit.lean` sits
under the 13.8k-line `DeTurckRemainderLowBaseAction.lean`, so editing it forces
a multi-minute rebuild of a module another lane has claimed.  Move it when that
lane closes.

## `topKer_jet` (`:196`) — PROVED (TK3)

```
hDim : finrank ℝ E = 3
⊢ ∃ Kk : ℕ → ℝ, (∀ i, 0 ≤ Kk i) ∧
    ∀ T symmetric, ∀ 0 ≤ δ ≤ 1/3 + the two gFibreOpBound certificates,
      ∀ i, ∀ s ∈ Icc 0 1,
        lowJetSq g i (rhsRefoldTop g g T s + rhsSelfTop g T s
                        − deTurckPhiMetTotal g g g)
          ≤ Kk i * (1 + ∑_{j < i+2} ‖∇ʲ T‖²)
```

### Why it carries no a-priori ball

`c2_jet_tower` quantifies over an **arbitrary** `a` — `a2_ladder` calls it
without forwarding `ha : 3 ≤ a`.  At `a = 0` its `H^{a+2} = H²` ball supplies no
usable low-order control, so a ball hypothesis on the leaf would buy nothing
that the consumer can actually deliver.  What the consumer *does* deliver is
`hδ_le : δ ≤ 1/3` together with `hδg`, and
`gFibreOpBound g (ccTensorBilinSymm g T) δ` unfolds to
`|T(v,w)| ≤ δ·|v|_g·|w|_g` at every point — i.e. a pointwise operator bound,
`‖T‖_{L^∞} ≤ 1/3`.  That is exactly the input a Moser/Gagliardo–Nirenberg
product estimate needs: a monomial `∇^{j₁}T ⋯ ∇^{jₚ}T` with `∑ jₖ = i` is
`L²`-controlled by `‖T‖_{L^∞}^{p−1}‖∇ⁱT‖_{L²}`.  So the ball-free statement is
the honest minimal frontier, and the ball in `c2_jet_tower` is **vestigial** —
kept only because the operator-norm engine downstream carries it.

### The proof, in one paragraph

`topKernel_eq` (`…LowBaseAction.lean:3769`, needs the `LowBaseInternal.`
prefix) splits the integrand into `lieRefold2 g T s`, `Φmet(gm) − Φmet(g)` and
`(−2s) • ricciTop g gm T`, with `gm = realizedFam g T 0 s`.  Along that radial
path the perturbation is `s • T`, so `pathPert_rad` supplies `IsPathPert` with
the *same* `δ₀ = 1/3` for every `s ∈ [0,1]`; the three summands are then the
all-order Moser windows `moserWin_lieRef2`, `moserWin_phiDev`,
`moserWin_ricciTop` of `LowRegOpJetWindows.lean`.  `moserWin_smul` +
`moserWin_mono` absorb the scalar `−2s` (`(−2s)² ≤ 4`, `|−2s| ≤ 2`), two
`moserWin_add`s assemble, and one `Finset.sum_le_sum_of_subset_of_nonneg`
throws away the spare order (`w = 0` windows against a `range (i+2)` budget).

The realized constant is

```
Kk i = |2 * (2 * (A_lie i + A_phi i) + 4 * A_ric i)|
```

with `A_lie`, `A_phi`, `A_ric` the three windows' envelopes.  The absolute value
is what makes `∀ i, 0 ≤ Kk i` provable *before* `T` is introduced — the windows
give nonnegativity only through `moserWin_nnA`, which needs a window instance
and hence a state; `le_abs_self` sidesteps that at zero cost.

**The one structural obstacle**, and the reason TK3 was not pure assembly:
`topKer_jet` binds `Kk` **before** `T`, while every TK2 family window bound `T`
before its `∃ A S`.  `∀ T, ∃ A` does not give `∃ A, ∀ T`.  All the constants
were already state-free, so TK3 hoisted `T` inside the existential in twelve
window statements; see `LowRegOpJetWindows.md` for the list and the mechanics.

### The `lieRefold2` producer, still rejected

`exists_deTurckLieCovDerivRefoldC2Family_cap_l2JetWindow`
(`RiemannCoefficientPalatiniRefold.lean:18865`, 3rd clause) is literally this
shape, `K i * (1 + ∑_{j<i+2}‖∇ʲT‖²)`, but gates on `2·finrank ℝ E + 10 ≤ a`
(dim 3: `a ≥ 16`) and takes a *pointwise jet window* `∀ j ≤ a+2, ‖∇ʲT‖ ≤ R`
rather than an `L^∞` bound.  Reusing it would have undone the `a ≥ 3` bottom
that brick E0a″ bought.  Ruling No. 104 rejected it; the Moser route reached the
same conclusion ball-free and gate-free, so the rejection cost nothing.

## Lean lessons

* **`LowBaseInternal` is a real namespace, and it shadows.**
  `DeTurckRemainderLowBaseAction.lean` declares `rhsSelfTop`, `selfTopInt`,
  `topKernel_eq`, `c2_eq`, `selfTop_joint` **twice**: once `private` at
  `IntrinsicSpectral` level (:2256, :2611, :2269 — these are what `c2_h2_small`
  uses) and once public inside `namespace LowBaseInternal` (3372–3835).  From
  outside the file only the second set is reachable, and it needs the
  `LowBaseInternal.` prefix.  The failure mode is *not* "unknown identifier":
  the unqualified name resolves to something else and you get
  `Invalid argument name 'I' for function`.  Consumers that look like they use
  the public names (`c2_h2_small`) are in fact using the private twins.
  Sibling names that need **no** prefix, because they live one namespace up or
  in other files: `lowJetSq`, `lowBaseData`, `rhsRefoldTop`,
  `rhsRefoldTop_joint`, `rhsRefoldTopInt`, `deTurckPhiMetTotal`.
* **`Finset.single_le_sum` needs its `f` pinned.**  `exact Finset.single_le_sum
  (fun q _ => sq_nonneg _) …` elaborates the nonnegativity argument before `f`
  is determined and dies on `typeclass instance problem is stuck / AddLeftMono
  ?m`.  Write the body out: `fun q _ => sq_nonneg ‖iteratedCovGrad … q X‖`.
  Binding `X` opaquely first (below) is what makes that spelling short enough
  to be readable.
* **The opacity pattern, again, and it is what made the last step work.**
  `obtain ⟨X, hXdef, hXjet⟩ : ∃ X, (lowBaseData …).C2 = X ∧ lowJetSq g i X ≤ …`
  with witness `rfl` (legitimate because `LowBaseInternal.c2_eq` is `:= rfl`),
  then `rw [hXdef]; clear hXdef`.  This is the same move `a2_ladder` makes on
  the whole `LowBaseActionData` bundle, and it is what keeps the path-integral
  witness from being unfolded by the arithmetic that follows.
* **`realizedSmallSet` is not in scope by default at this layer.**  It lives in
  `DifferentialGeometry.PDE.DeTurck.RicciLinearization`, which
  `LowRegLadderRung.lean` did not open; one `open` line was added there.
* **`ricciTop` also needs the `LowBaseInternal.` prefix here**, even though
  `LowRegOpJetWindows.lean` writes it bare — that file has `open
  LowBaseInternal`, this one does not.  Same for `topKernel_eq`.
* `symmS_eq_self_of_ccTensorBilin_symm` (`SobolevNonlinearityExistence.lean`)
  **is** reachable from `DeTurckRemainderLowBaseAction`; it turns `hT` plus
  `rfns_symmS_zero_le_fibreSmall` into the `L^∞` certificate on `T` itself in
  three lines.  Probing with a scratch `#check` file against exactly the target
  file's imports is the cheap way to settle such reachability questions.
* File checks in ~21 s.
