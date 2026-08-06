# ParametricAppCcJetBound

## Role

`app_jet_sq_le` gives the sharp squared one-jet action estimate.
`app_jet_of_bdd` turns a supplied pointwise coefficient-jet envelope into one
`L²` action window. `param_app_jet` obtains that envelope from
`joint_jet_bdd` on a compact parameter slab. Constants are independent of the
parameter, the input tensor, and its spectral or spatial support.

## Frontier

`app_jet_sq_le` was promoted from a private implementation lemma to the public
quantitative producer used by spectral smallness estimates; its statement and
proof body are unchanged.  After the upstream parametric-jet dependency was
repaired and refreshed, this file passed focused verification and the public
declaration was exported for downstream use.

Endpoint theorem: 0% (not stated in this module). Dedicated uniform action
machinery: 100%.

## 2026-08-05 (brick 4a): `app_jet_sq_head`, the head/tail sibling

`app_jet_sq_le` puts the coefficient in `L^∞` at *every* Leibniz index.  Added
`app_jet_sq_head`, which makes the opposite Hölder choice from index `1` on:
index `0` keeps one pointwise cap `B` on `Φ` itself with the whole data window in
`L²`, and each index `i ≥ 1` takes a pointwise cap `D i` on the *data window*
`l ≤ j - i` and reads `∇ⁱΦ` in `L²`:

`‖∇ʲ(appCc Φ W)‖² ≤ appCcGdiag j · (B·∑_{l≤j}‖∇ˡW‖² + ∑_{1≤i≤j} D i·‖∇ⁱΦ‖²)`.

Same proof skeleton as `app_jet_sq_le` (diagonal product grid, one dominating
integrable `F`, `normSq_le_integral_of_pointwise_fiberNormSq_le_rs`); only the
per-index pointwise step differs.  Motivation: a coefficient whose `L²` tower
already spends the state's own jets cannot afford the fibre embedding's `+2`
orders at the top Leibniz index — see
`Spectral/Intrinsic/DeTurck/LowRegA1PerIndex.md`.  Consumer: `a1PerIdxJet`.
Focused check and targeted build green; axiom census clean.

## 2026-08-05 (brick 4a-v2, ledger №155): `app_jet_sq_split`, the mixed engine

`app_jet_sq_head`'s uniform "state side from index `1` on" is the wrong Hölder
geometry for the `a₁` arm — it hands the rung a non-small, `R`-free constant
against `E_{k+1}` (see `LowRegA1PerIndex.md`).  The correct split is per-index
and mixed, so the choice is now a *parameter*: for `S ⊆ range (j+1)`,

`‖∇ʲ(appCc Φ W)‖² ≤ appCcGdiag j · (∑_{i∈S} B i·∑_{l≤j-i}‖∇ˡW‖²`
  `+ ∑_{i∈range(j+1)\S} D i·‖∇ⁱΦ‖²)`,

coefficient caps `B i` on `S`, data-window caps `D i` off it.  `app_jet_sq_le`
is `S = range (j+1)`, `app_jet_sq_head` is `S = {0}`, and the `a₁` consumer uses
the threshold `S = range j`.  Same skeleton again (diagonal grid, one dominating
integrable `F`, `normSq_le_integral_of_pointwise_fiberNormSq_le_rs`); the only
new ingredient is `Finset.sum_sdiff` to cut the Leibniz sum in two before the
per-index step.  Neither `B` nor `D` needs a nonnegativity hypothesis — the
pointwise step multiplies by an already-nonnegative fibre norm on each side.

Census sweep before writing it (exhibit-14 discipline): `app_jet_sq_le` and
`app_jet_of_bdd` are coefficient-side only; `appCc_topOrder_l2_twoArm_mixed_le`
(`DeTurck/DeTurckRemainderHigherOrderTame.lean:512`) collapses both sides onto
single constants; `appCc_split_env` (`Estimates/AppCcSplitEnvelope.lean:110`)
collapses the coefficient tail; and the private threshold engine
`master_appCc_jet_le_sharp` (`ConnLapCommutatorCoefficientTame.lean:475`) — the
closest relative, and the same *direction* of threshold (coefficient sup low,
data side high) — is fused to `Hs`-ball hypotheses and collapses its conclusion
onto a single `Hs` norm, which is exactly what destroys the per-index
accounting.  No exhibit sixteen.  Consumers: `a1PerIdxJet`/`a1PerIdxLin`.
Focused check, targeted build and axiom census green.
