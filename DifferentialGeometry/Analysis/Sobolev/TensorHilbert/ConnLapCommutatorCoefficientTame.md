# ConnLapCommutatorCoefficientTame.lean — the order-generic `appCc` commutator engine

Note created 2026-08-03 by the F6 threshold brick (E0a″).  It records only what
that brick touched; the file predates the note and is otherwise unannotated.

Status: **GREEN, sorry-free** (0 `sorry` in the file).  Focused check and one
targeted module build clean; the downstream supercritical consumer
`Spectral/Intrinsic/DeTurck/DeTurckRemainderPrincipalArmOpNorm.lean` rebuilds
clean against the new gate.

## What the file provides

Three public theorems, in dependency order:

* `exists_appCc_covGradCoeff_secondCovGrad_l2_le` (`:863`) — the `∇C₂` arm at
  `L²`;
* `exists_rawConnLap_appCc_secondCovGrad_commutator_Hs_family_le` (`:976`) — the
  rung-raising commutator `[Δ_raw, appCc C₂ ∘ ∇²]` on the resolvent family;
* `exists_appCc_secondCovGrad_fibreSmallCoeff_Hs_family_le` (`:1334`) — the
  coefficient-abstract, order-generic operator-norm engine that consumers use.
  Its top constant is the pointwise fibre cap `εC` and carries **no rung index**;
  all rung-dependent cost sits in `ClowerFn j = Mbase + ∑_{i<j} CEcomm i`.

The engine is the object `L4_UNIFORMITY_AUTOPSY.md` identified as the mechanism
behind `k`-uniformity, and the producer of `LowRegLadderRung.lean`'s
`appCc_cap_hs_le` / `a2_ladder`.

## The 2026-08-03 change: split threshold parameterized, gate sharpened

`master_appCc_jet_le_sharp` (`:475`, `private`) is the Leibniz-grid jet leaf.  It
splits the grid index at a threshold `t` and uses the sup-window `w = n/2 + 2`,
`n = finrank ℝ E`:

* **region 1** (`i ≤ t`) bounds the coefficient jets by a *numeric* sup over the
  a-priori ball, so it needs `i + m + dc ≤ a + 2` — worst case
  `t + (w−1) + dc ≤ a + 2`;
* **region 2** (`t < i`) trades through log-convexity (`hs_extreme_interp`,
  `:306`), so it needs only `(w−1) + dd ≤ t + 4` (for `hβγ`); the interpolation
  side condition `hsum_ok` then follows from the two.

`t` was hard-wired to `n/2 + 3`, which forced `finrank ℝ E + 5 ≤ a` on the whole
chain.  It is now a **parameter** carrying exactly the two budgets it consumes:

```
(b₀ s₀ dc dd t : ℕ) (hdc : dc ≤ 3) (hdd : dd ≤ 3)
(ht1 : t + Module.finrank ℝ E / 2 + 1 + dc ≤ a + 2)
(ht2 : Module.finrank ℝ E / 2 + 1 + dd ≤ t + 4)
```

and `ha` is **gone from the leaf entirely** — `ht1`/`ht2` discharge all three
budget `omega`s (`hbound`, `hβγ`, `hsum_ok`).  Taking `t := n/2 + 3` recovers the
old statement verbatim, so the generalization is faithful.

`appCc_term_Hs_bound_sharp` (`:755`, `private`) threads `t`/`ht1`/`ht2` through
to the leaf, unchanged otherwise.

The three public gates became

```
ha : max 2 (Module.finrank ℝ E / 2 * 2 + 1) ≤ a      -- dim 3: 3 ≤ a
```

which is the **sharp** joint requirement of the six call sites (see below), not a
round-up.  This is a pure hypothesis *weakening*: every prior consumer still
elaborates.  The only external consumer,
`DeTurckRemainderPrincipalArmOpNorm.lean:5078`, passes the gate as `(by omega)`
from `2·finrank ℝ E + 10 ≤ a`, so its call site is byte-unchanged.

## Why `t` must be per-call-site

The six gated call sites inside `:976`, with their windows in `t` (dim 3, where
`w−1 = 2`):

| call site | `(dc,dd)` | window | `t` used |
|---|---|---|---|
| `master_…` (`:1022`) | (3,2) | `0 ≤ t ≤ a−3` | `n/2 − 1` |
| `master_…` (`:1026`) | (2,3) | `1 ≤ t ≤ a−2` | `n/2` |
| `appCc_term_…` (`:1032`) | (1,2) | `0 ≤ t ≤ a−1` | `n/2 − 1` |
| `appCc_term_…` (`:1037`) | (1,2) | `0 ≤ t ≤ a−1` | `n/2 − 1` |
| `appCc_term_…` (`:1042`) | (0,3) | `1 ≤ t ≤ a` | `n/2` |
| `appCc_term_…` (`:1046`) | (0,3) | `1 ≤ t ≤ a` | `n/2` |

Each window is non-empty iff `a ≥ 3`.  Their **intersection**, however, is
`1 ≤ t ≤ a−3`, which is empty until `a ≥ 4`.  So a single global `t` — the old
design — cannot reach `a = 3`; letting every site choose is what buys the last
order.  This is the whole content of the brick.

In general dimension the joint requirement is
`max 2 (2·(n/2) + 1) ≤ a`: site (2,3) needs `n/2 ≤ t` and `t + n/2 + 1 ≤ a`, so
`2·(n/2) + 1 ≤ a`; site (3,2) at `n/2 = 0` degenerates to `2 ≤ a`, which is where
the `max 2` comes from (it is invisible for `n ≥ 2`).

## What did NOT change

* **The top constant.**  `t` only redistributes index mass between `S1` and `S2`,
  and both feed `Cm → CEcomm → ClowerFn`, i.e. the *lower*-order constant.  The
  engine's top constant is still exactly `εC`.  Trading the top constant for
  threshold slack would have defeated the purpose of the ladder.
* **Every proof body.**  Apart from deleting the `set t := n / 2 + 3` line and
  rewriting the six argument lists, no tactic in the file was touched.  The
  three budget `omega`s re-derive at the new gate with no hint.
* **Axiom profile.**  `appCc_cap_hs_le` (the ladder's consumer of `:1334`) stays
  axiom-clean — `propext, Classical.choice, Quot.sound`, no `sorryAx`.

## Lean lessons

* **`set` folds into hypotheses, which is what makes this work.**  `set n :=
  Module.finrank ℝ E with hn` rewrites `ht1`/`ht2` too, so the budget `omega`s see
  `n / 2` in the same normal form as `hwdef : w = n / 2 + 2`.  No manual
  `rw [hn]` is needed anywhere.
* **`omega` handles `max` and `/2` on an atom together.**  The gate
  `max 2 (Module.finrank ℝ E / 2 * 2 + 1) ≤ a` is discharged, and consumed, by
  plain `omega`; downstream `a2_ladder` closes it from `hDim : finrank ℝ E = 3`
  and `ha : 3 ≤ a` the same way.  This is why a `max` gate is affordable in a
  public statement here — it never needs unfolding by hand.
* **ℕ truncated subtraction in the chosen `t` is fine.**  `Module.finrank ℝ E / 2
  − 1` is passed literally; `omega` case-splits on `n/2 = 0` itself when proving
  `ht1`/`ht2`, which is exactly where the `max 2` conjunct earns its keep.
* **Weakening a gate is downstream-free when consumers pass `by omega`.**  Worth
  grepping for before assuming a public-statement change forces a duplicate:
  here it turned a feared three-theorem parallel hierarchy into a one-token
  signature edit.

## Pointers

* Ladder consumer + frontier: `Spectral/Intrinsic/DeTurck/LowRegLadderRung.md`.
* Brick context and status: `ShortTime/F6_ESTIMATE_RECON.md` §5.1c / §5.1d.
* Mechanism analysis: `ShortTime/L4_UNIFORMITY_AUTOPSY.md`.
* Ledger: `ShortTime/UNIF_EXISTENCE_PLAN2.md`, entries No. 102–104.
