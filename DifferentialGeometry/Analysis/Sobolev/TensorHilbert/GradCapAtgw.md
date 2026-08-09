# `GradCapAtgw.lean` — the `Λ₁`-capped (`∇P`-capped) grid currency

Brick **A1-CUR-2 SESSION 1** of the (N) uniform-existence campaign.  Foundation
only: this module builds the currency that the two QUADRATIC summands of the C0
estimate (`selfLow_jet`) consume.  `selfLow_jet` itself is untouched and stays
`sorry` (brick A1-CUR-2 assembly, session 2).

## 1. The mathematical finding that shaped the whole design

The two quadratic summands (`ricciAAArm` inside `ricciGoodLow`, and `lc0VB`)
carry two connection differences.  In the state's own grid base
`bP j = |∇ʲP|²(x)` their arms sit at offset `+1` each, the Leibniz fold adds the
offsets, and the window lands at `atgw bP (n+3)` — one order over the
`range (i+2)` budget.

**A purely pointwise/combinatorial repair is impossible.**  The over-budget term
is `∫ |∇^{α}P|² |∇^{β}P|²` with `α + β = n + 2`, `α, β ≥ 1`; at `α = β ≈ n/2`
neither factor is capped, and no pointwise inequality of the form
`|∇^{α}P|²|∇^{β}P|² ≤ C Λ² · (weight ≤ n+1 entries)` is true.  The improvement is
an INTEGRAL fact: Gagliardo–Nirenberg with interpolation endpoint `‖∇P‖_∞`
instead of `‖P‖_∞`.

**Consequence.**  The capped currency is the ordinary radius-free currency run on
the base tensor `Q = ∇P` at valence `(0,3)`, with `Λ₁ = ‖∇P‖_∞` in the role
`Λ₀ = ‖P‖_∞` plays at `(0,2)`.  Everything else follows.

## 2. What was found in the tree (scout results, all reused, nothing duplicated)

* `exists_riemannianFiberNorm_le_iteratedCovGrad_l2_jetSum_supercritical`
  (`Analysis/Sobolev/Embedding/SobolevEmbeddingSharpC0JetSum.lean:717`) — PUBLIC,
  valence-generic, **and ungated**: it needs the jets of the tensor through order
  `finrank/2 + 1` only.  This is the sharp fibre Sobolev embedding and it is the
  whole content of D1.  It is what the `private jet_fibreNormSq_sup_le_sharp`
  (`ConnLapCommutatorCoefficientTame.lean:443`) wraps.
* The `a ≥ 16` gate of
  `deTurckSmoothRemainderDiff_supercritical_pointwise_jet_le_fixedWindow`
  (`DeTurckRemainderHigherOrderTame.lean:604`) comes from its own route
  (`L = 4K+4 ≤ a+1` with `K = finrank/2+1`), NOT from the embedding.  It was
  correctly NOT inherited — see the STOP-SIGNAL constraint.
* `rfns_iteratedCovGrad_comp`
  (`Geometry/Connection/TensorNabla/HomFieldActionIteratedCovGradWindow.lean:308`)
  — PUBLIC pointwise composition of iterated gradients.  It is *exactly*
  `gridBase g₀ (∇P) x j = gridBase g₀ P x (1+j)`, one `exact` away.
* `exists_iteratedCovGrad_sum_le_smoothCcToTensorHs_general`
  (`SobolevNonlinearityExistence.lean:774`) — the `H^s` ball → jet ball bridge.
* `exists_gagliardoNirenberg_iteratedCovGrad_lpFiberNorm_le_rs` — already
  `(r,s)`-generic; this is why the valence generalization below was mechanical.

## 3. What was changed upstream (one canonical API, zero downstream churn)

The base valence of the grid engines was hard-wired to `(0,2)`.  Generalized in
place, with the old `(0,2)` statements kept verbatim as one-line instances, so
that **no call site anywhere changed** (this matters: one call site lives in the
read-only `DeTurckRemainderLowBaseAction.lean`):

| file | change |
| --- | --- |
| `Analysis/Spectral/Tensor/CovGrad/JetProductIntegral.lean` | `grid_prod_int_le` valence made `{r s}` implicit (inferred from `P`) — all 5 call sites unchanged |
| `.../CurvatureCoefficientDifferenceJetTower/ResidualFree.lean` | new generic `atgGridIntRs` and `bfGridWinIntRs`; `antidiagonalTupleGrid_integral_radiusFree` and `boundedFactorGridWindow_integral_radiusFree_topSeparated` are now their `(0,2)` instances |
| `Analysis/Sobolev/TensorHilbert/AtgwArmFold.lean` | `gridBase`, `gridBase_nn`, `atgwFold` base valence `{rb sb}` implicit; new generic `atgwToJetRs`, with `atgwToJet` its `(0,2)` instance |

## 4. This module

* `icgNormComp` — `‖∇ᵐ(∇ˡΨ)‖ = ‖∇^{l+m}Ψ‖` (public re-derivation of a lemma the
  tree carries as `private` in three places; dedup TODO below).
* `gradBase_eq` — the shifted grid base.
* `gradCapOfJets` / `gradCapOfBall` — **D1**, the `Λ₁` producer, at gate `1 ≤ a`.
* `shiftConst`, `prodShift`, `gridShift`, `atgwShift` — **the base shift**: an
  arm's existing radius-free window at level `k+1` in the state's base is a
  window at level `k` in the shifted base, at the price of the two caps
  `|P| ≤ Λ`, `|∇P| ≤ Λ`.  Sharp for arms LINEAR in `∇P` (every grid entry then
  has at least one factor, and the level really does drop by one).
* `atgwCapToJet` — **the capped integration step**: a shifted-base window at
  offset `w` integrates into `range (n + w + 1)` in `P`'s own jets.  At `w = 1`
  this is `range (n + 2)`.
* `armShift` — an arm's EXISTING window at `bP`-offset `u + 2` becomes a
  shifted-base window at level `i + u + 1`.  No arm is re-derived.
* `atgwCapArm` / `atgwCapFold` — the capped two-arm workhorse, pointwise and
  integrated: two arms each carrying one derivative of the state produce
  `range (n + 2)`.  `atgwCapArm` is exposed separately because a nested product
  has to feed the inner fold's output into the outer one before integrating.

## 5. How the two quadratic summands consume it (route, for session 2)

`lc0VB` is the clean one and is the intended smoke test:

```
vbMcdArm            : atgw bP (i'+2)  --atgwShift-->  atgw b'P (i'+1)   (offset 0)
ipLowCc (wOmega)    : atgw bP (q+2)   --atgwShift-->  atgw b'P (q+1)    (offset 0)
  fold (atgwFold u=0 v=0, base ∇P)  ->  lc0VBPass : atgw b'P (n+1)
live cometric arm   : atgw bP (i'+1)  --atgwShift/mono-->  atgw b'P (i'+1)
  fold (atgwFold u=0 v=0, base ∇P)  ->  lc0VB     : atgw b'P (n+1)
  atgwCapToJet (w = 1)              ->  range (n+2)   ✓ IN BUDGET
```

`ricciAAArm` is NOT reachable this way as stated: `ricciAAKer` is a single arm
that is itself quadratic, so its `bP` window at `atgw (q+3)` is one order lossy
under the generic shift (the shift is sharp only when every grid entry has a
factor, which the *bound* for a quadratic arm no longer records).  Session 2 must
descend into `aaKer_eq`'s six `appCcRS` nests (`DeTurckRemainderLowBaseAction.lean:4400`,
all `private`) and shift the individual `connDiffContrInsertionField` factors.

## 6. Smoke test: LANDED

`Lc0VBCapWindow.lean` — `lc0VBCapAtgw` (pointwise, shifted window at `i+1`) and
`lc0VBCapJet` (`range (i+2)` in `L²`).  Both sorry-free.  It cost exactly ONE
promotion (`b4_wOmega_atgw`, collision-scanned, three references all in its own
file); the other six ingredients (`vbSplit`, `lc0VB_eq_app`, `vbMcdArm_rfns_le`,
`lc0RiemLive_rfns_le`, `rfns_icg_ipLow_le`, `rfns_iCG_cometricCastG0_atgw_rf`)
and `b4_mcd_atgw` were already public.  Not one line of `lc0VB`'s geometry was
re-proved: the SAME three arm windows are fed in, only the grid's base changes.

## 7. Open / TODO

* **Relocation.**  `shiftConst` / `prodShift` / `gridShift` / `atgwShift` are
  pure combinatorics of `antidiagonalTupleGrid`; canonical home is
  `Analysis/Sobolev/AntidiagonalTupleProductGrid.lean`.  Kept here only to bound
  this brick's rebuild scope.
* **Dedup.**  `iteratedCovGrad_norm_comp` exists `private` in
  `ConnLapCommutatorCoefficientTame.lean:331` and
  `DeTurckPrincipalArmEnergyCrossTerm.lean:647`, and as `norm_iteratedCovGrad_comp`
  in `AllOrderGardingConstant.lean:143`.  `icgNormComp` should replace all three.
* **Collapse.**  `antidiagonalTupleGrid_integral_radiusFree` /
  `boundedFactorGridWindow_integral_radiusFree_topSeparated` are now thin
  instances; the `Rs` forms are the canonical ones.
* **`ricciAAArm` (the OTHER quadratic summand) is session 2.**  It is not
  reachable by shifting its folded window: `ricciAAKer` is a single arm that is
  itself quadratic, and the generic shift is sharp only when every grid entry of
  the arm has at least one factor — which the *bound* for a quadratic arm no
  longer records.  Session 2 must descend into `aaKer_eq`'s six `appCcRS` nests
  (`DeTurckRemainderLowBaseAction.lean:4400`, all `private` in a READ-ONLY file)
  and shift the individual `connDiffContrInsertionField` factors, or obtain a
  public two-arm split of `ricciAAKer`.

## 8. Verification status

Recorded at the end of the session in `ShortTime/UNIF_EXISTENCE_PLAN3.md`.
Everything in this module and in `Lc0VBCapWindow.lean` is sorry-free and
axiom-clean (`[propext, Classical.choice, Quot.sound]`).
