# `TameLieCorrJets.lean` — the `lieCorr0` summands in the marked currency

Session 3 of the tame C0 bottom.  Sibling of `TameArmJets.lean` (the Ricci `A·A`
arm); this file does the three `lieCorr0` summands of `selfLow_split`.

Status: **all three diagonal arms are closed end-to-end at the deliverable
shape, and the full arbitrary-background `lc0AMix` arm is closed at the same
tame deliverable shape.**  The arbitrary-background difference is sharp at
offset `n+2`; its new pointwise producers are sorry-free.  The integrated
deliverables still inherit the single declared frontier `gridIntHigh`, while
`lc0Riem` does not.

## The pre-check (planner-mandated, №140) — RESULT: the `g_bg` term VANISHES

`rfns_iCG_wXi_atgw_rf` (`DeTurckVFJetRadiusFree.lean:1050`) splits `wXi` and
bounds its `g_bg` half by a `T`-free per-order constant `SBg l`, obtained from
`exists_bound_riemannianFiberNormSq_smoothCcTensor` — an arbitrary sup bound.
At `u = 1` that constant would be an unmarked monomial and would break the mark
count.

**At the `lc0VB`/`lc0AMix` call sites `g_bg = g₀`, and there the `g_bg` half is
not merely small — it is the ZERO TENSOR.**  The tree already proves this and
throws it away:

* `wXi g₀ g₁ g_bg = connDiffLoweredCc g₀ g₁ − connDiffLoweredCc g₀ g_bg`
  (`DeTurckVFEndoInsertTower.lean:62`);
* `wXi_self_eq` (`LieCorr0VBRefold.lean:40`) proves
  `wXi g₀ g₁ g₀ = connDiffLoweredCc g₀ g₁` **as an equation of tensors**;
* `lc0VBFormRF` (`LieCorr0VBRefold.lean:110`) uses literally
  `ipLowCc g₀ (wOmega g₀ g₁ g₀)`, and `LowRegBgH2.lean:653/710/803` calls
  `lc0AMix g₀ g₁ g₀`.

So no term has to be estimated away at all: `wXiMark` is `connDiffMark` composed
with the valence bridge `connLow_rfns` and transported along `wXi_self_eq`, with
the **same state-free constant**.  This is over-count exhibit SEVEN again in its
sharpest form — the producer proves more than it exports.

## Contents

| name | mark | content |
| --- | --- | --- |
| `wXiMark` | `u = 1` | `wXi g₀ g₁ g₀`, constants state-free — the brick this session was dispatched for |
| `mcdBgAtgw` | `u = 0`, offset `n+1` | `mcd(gB) - mcd(g₀)`; constants depend only on `g₀,gB`, with no `δ` hypothesis |
| `amixBgAtgw` | `u = 1`, offset `n+2` | exact arbitrary-background `lc0AMix` difference, using one fixed-background `mcd` difference and one diagonal marked `mcd` factor |
| `mcdMark` | `u = 1` | `metricConnDiffLoweredCc g₀ g₁ g₀`, via `b4_mcd_eq` + `b4_phi_atgw` |
| `wOmegaMark` | `u = 1` | `wOmega g₀ g₁ g₀ = cometricCastG0 ⋆ wXi` |
| `ipLowMark` | preserves `u` | the interior product; `rfns_icg_ipLow_le` + `markGrid_mono` |
| `lc0VBMark` / `lc0VBJet` | `u = 2` | the vector-bilinear summand, and its tame `L²` jet bound |
| `lc0AMixMark` / `lc0AMixJet` | `u = 2` | the five-factor mixed summand at `g_bg = g₀` |
| `lc0AMixJetBg` | affine tame jet | the full five-factor mixed summand at arbitrary fixed `gB`; the background difference contributes only to `K₀` |
| `lc0RiemMark` / `lc0RiemJet` | `u = 0` | the fixed-curvature summand; **axiom-clean, `K₂ = 0`** |

Deliverable shape (identical to `ricciAAJet`):

```
‖∇ⁱX‖² ≤ (K₀ i + K₂ i·∑_{j<3}‖∇^{1+j}P‖²)·(1 + ∑_{j<i+2}‖∇ʲP‖²)
```

constants chosen BEFORE the state, no `R₀`, no opaque cap, no Galerkin index,
exactly one power of `‖P‖²_{H³}`.  Only extra hypothesis: the δ-anchor
`|P|_∞ ≤ 1` (at `finrank = 3` implied by `‖P‖_∞ ≤ finrank/3`).

## The mark arithmetic

```
wXi g₀ g₁ g₀ = connDiffLoweredCc g₀ g₁         u = 1   wXi_self_eq + connLow_rfns + connDiffMark
  b4Phi (order-0 in P, offset-+1 window)       u = 0   mkOfWin ∘ b4_phi_atgw at Λ₀ = 1
  mcd = wXi + ½Φ_A ⋆ wXi + ½Φ_B ⋆ wXi          u = 1   b4_mcd_eq, mkApp/mkAdd/mkSmul
  cometricCastG0 (offset-+1 window)            u = 0   mkOfWin
  wOmega = cometricCast ⋆ wXi                  u = 1
  ipLowCc (wOmega)                             u = 1   ipLowMark
vbMcdArm  ≤ dim · mcd                          u = 1   vbMcdArm_rfns_le
  lc0VBPass = vbMcdArm ⋆ ipLowCc(wOmega)       u = 2   vbSplit, marks ADD
lc0RiemLive ≤ dim · cometricCastG0             u = 0
  lc0VB = 2·(lc0RiemLive ⋆ lc0VBPass)          u = 2   lc0VB_eq_app          ✓
lc0TraceRF (three moving traces)               u = 0   mkOfWin ∘ trace_grid_rf
slotExtendIter 0 3 w (mcd g₀ g₁ g₀)            u = 1   mkIter
  lc0AMixHalfRF = tr ⋆ tr ⋆ mcd ⋆ tr ⋆ mcd     u = 2   four mkApp
  lc0AMix = 2·(half + half)                    u = 2   amix_refold_rf        ✓
lc0RiemPass (state-free)                       u = 0   mkOfBnd
  lc0Riem = −(lc0RiemLive ⋆ lc0RiemPass)       u = 0   lc0Riem_eq_app        ✓
```

## The sharp arbitrary-background `lc0AMix` extension

At a general DeTurck background,
`wXi g₀ g₁ g_bg = connDiffLoweredCc g₀ g₁ − connDiffLoweredCc g₀ g_bg` keeps a
state-free summand, so `mcd(g₀, g₁, g_bg)` is only `u = 0` and the five-factor
product is `u = 1`: `lc0AMix` is then **affine, not quadratic**, in `∇P`.
The exact arbitrary-background refold makes this loss explicit and recoverable:

* `mcdBgAtgw` now isolates the exact background change and proves the sharp
  radius-free bound
  `|∇ⁿ(mcd(gB) - mcd(g₀))|² ≤ K n · atgw(bP, n+1)`.  The moving part cancels,
  leaving the fixed tensor
  `connDiffLoweredCc g₀ g₀ - connDiffLoweredCc g₀ gB`, acted on by the two
  order-zero `b4Phi(P)` arms.  Bounding the two full `mcd` terms separately
  would leak the larger general-background offset and must not replace this
  cancellation;
* `amix_bg_refold_rf` rewrites the full difference as four once-marked products.
  Each product contains exactly one `mcdBgAtgw` factor (`u = 0`, offset `n+1`),
  one diagonal `mcdMark` factor (`u = 1`), and three moving traces (`u = 0`).
  The local `mark_one_atgw` window calculation closes the result at sharp
  offset `n+2`, without any new `δ` or fibre-operator hypothesis;
* `lc0AMixJetBg` sends that difference through `atgwToJet` with `w = 2` and
  combines it with `lc0AMixJet`.  Consequently the arbitrary-background term
  adds only to `K₀`; the quadratic `K₂` coefficient is exactly inherited from
  the diagonal theorem.  This is the consumer-ready full-background packet.

## Upstream edits made (surgical)

`LieCorr0CoeffDiffRadiusFree.lean`: `private` removed from `b4_mcd_eq` (the `mcd`
fibre split) and `b4_phi_atgw` (its correction operator's offset-`+1` window).
No new content, no line-count growth, no import change.  Both are honest
public-quality statements sitting next to the already-public `b4_mcd_atgw`, and
both are axiom-clean.  The correction operator `b4Phi` and the permutations
`b4PermA/B` stay private: a public theorem may MENTION a private constant in its
type, and the consumer never has to name it (see the Lean lesson below).

`TameMarkWin.lean`: added `mkIter` (the marked `capIter`) and `markJet0` (the
`u = 0` bridge out).

Note: `LieCorr0CoeffDiffRadiusFree.lean` is 3419 lines, over the project's
3000-line limit.  This session did not grow it; splitting it is a separate task
and would touch other lanes.

## Verification

Focused check of the new file: passed, no errors, no warnings.  Targeted builds
of `+…LieCorr0CoeffDiffRadiusFree`, `+…TameMarkWin`, `+…TameLieCorrJets`: all
passed.  Axiom census of every new public declaration:

The later `mcdBgAtgw` extension also passes a focused check at four Lean threads
under the 6144 MB cap.  Its first proof attempt failed only at elaboration:
constructing the anonymous `mkAdd` chain before rewriting the target left the
private `b4Phi` permutation metavariables undetermined.  The checked proof uses
the single local algebra identity `mcd_corr_sub`, rewrites the target first, and
then lets the target determine both private arms.  No new analytic assumption or
frontier was introduced.  The earlier axiom census below was not rerun for this
extension.

The subsequent `amixBgAtgw` and `lc0AMixJetBg` extensions pass the same focused
check.  The exact-algebra dependency `LieCorr0AMixRefold` and this module both
pass targeted refreshes; the final `TameLieCorrJets.olean` is newer than its
source.  The new proof is an adapter over the exact refold, marked-window
calculus, `atgwToJet`, and the existing diagonal theorem; it introduces no new
analytic frontier.  The axiom census below predates these two declarations and
was not rerun for them.

* **clean** (`[propext, Classical.choice, Quot.sound]`): `mkIter`, `markJet0`,
  `wXiMark`, `mcdMark`, `wOmegaMark`, `ipLowMark`, `lc0VBMark`, `lc0AMixMark`,
  `lc0RiemMark`, `lc0RiemJet`, and the two newly-public `b4_mcd_eq`,
  `b4_phi_atgw`;
* `sorryAx` **only** through `gridIntHigh`: `lc0VBJet`, `lc0AMixJet` — the same
  route `ricciAAJet` takes.

## Lean lessons

* **A public theorem may mention a `private` constant in its statement, and
  downstream files can use it** — `private` restricts name RESOLUTION, not the
  term.  This let `b4Phi`/`b4PermA`/`b4PermB` stay private while `b4_mcd_eq` and
  `b4_phi_atgw` went public.  The consumer must then never TYPE the private name:
  state the helper `have` with the operator universally quantified
  (`∀ Φ : SmoothCcTensor g₀ 3 3, (window for Φ) → …`) and let `Φ` be fixed by
  unification against the goal produced by `rw`/`mkCongr`.  Writing
  `have h : … (b4Phi …) …` instead fails with "unknown identifier".
* When a `σ`-indexed family is obtained by `choose Kphi hKphi_nn hphi using
  (fun σ => …)`, the σ inside a later `hphi _ P hsup n y` is solved by unifying
  the LHS of the bound with the goal's `b4Phi g₀ P b4PermA` — so `_` works even
  though the perm is unnameable.  Fold the σ-dependence away with a
  `∑ σ : Equiv.Perm (Fin 5), Kphi σ i` constant plus a `hsingle` helper
  (`Finset.single_le_sum`), the `ricciAAMark` `SP4` pattern.
* For a difference of two `b4_mcd_eq` expansions, do not build an anonymous
  `mkAdd` proof before the target fixes the private permutations: Lean then
  reports unsolved `X`, `Y`, `Φ`, and `σ` metavariables.  First rewrite with the
  generic local identity `mcd_corr_sub` (proved from `appCcRS_sub_right` and
  module algebra), then refine the `mkAdd` chain against the rewritten goal.
* **Do not put an undetermined constant behind `mkMono`.**
  `refine mkMono g₀ P (fun i => le_of_eq (by norm_num)) (mkSmul g₀ P 2 ?_)` fails:
  when the `by norm_num` runs, `mkSmul`'s constant is still a metavariable.  Fix:
  declare the existential constant as EXACTLY what the chain produces
  (`fun i => (2:ℝ)^2 * foldConst 0 0 KC KPass i`) and drop the `mkMono`.  Same
  for a nested `mkAdd` chain — write
  `2*Kwx i + 2*(2*((1/2)^2*F i) + 2*((1/2)^2*F i))` literally; higher-order
  unification of `fun i => 2*Kwx i + 2*?KY i` against it is a Miller pattern and
  succeeds.
* **Never put `_` inside a type ascription for a fold's passenger.**
  `have hmid : HasMarkWin … (appCcRS g₀ 2 3 6 Φ _) 2 Kmid := …` fails with
  "don't know how to synthesize placeholder for argument `W`".  Drop the
  ascription entirely (`have hmid := mkApp g₀ P Φ _ … hΦ hW`); `W` is then fixed
  by `hW`'s type.  Only the final `have` in the chain needs an ascription, and
  the nested `set`-bound constants match it by defeq.
* `set X := e with h` gives a transparent local definition, so a `have` whose
  ascription names `X` typechecks against a term whose type spells out `e`.  Use
  `rw [h]` first only when the goal (not the term) must be unfolded, as in
  `hM2 : … 1 KM2 := by rw [hKM2_def]; exact mkIter …`.
* `markGrid b 0 n = antidiagonalTupleGridWindow b (n+1)` holds by `rfl` (the
  `match` reduces), so an unmarked `HasMarkWin` feeds `atgwToJet` at `w = 1`
  through a bare `simpa`.

## What the assembly session needs

Closed at the deliverable shape so far: `ricciAAArm` (session 2), `lc0VB`,
`lc0AMix`, `lc0Riem`.  NOT closed: the lieCov pair
(`deTurckLieCovDerivArmField − edgeLiePairFam`, residual identity
`lieCov_residual` at `RiemannCoefficientPalatiniRefold.lean:9176`) and the
remaining `∇A ⋆ ∇T` arm of `ricciGoodLow`.

The lieCov pair is a genuinely different shape and should be scoped as its own
brick: its residual is `(−1)•appCcRS g₀ 2 6 2 (lieCovPair g₀ g₁) (…
slotExtendIter 0 4 2 (lieCovR4 g₀ T …))`, where `lieCovR4` carries `∇²T` — one
factor of order TWO rather than two factors of order one — and it is stated in
the `boundedFactorGridWindow` currency, not `atgw`.  Expect a `u = 2` window
whose two marks have orders `(1, 2)`, and check whether `markGrid`'s monomial
inventory at that shape stays inside classes 1–3.
