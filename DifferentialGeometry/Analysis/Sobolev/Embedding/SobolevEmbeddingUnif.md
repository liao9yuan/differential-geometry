# SobolevEmbeddingUnif — Lane E brick E4 (class-uniform fibre-Morrey constant)

Session 1 (Opus 5), branch `codex/short-time-existence-align`, 2026-07-30.
Anchor: Lane E brick list, item **E4**; consumer is E5 (`hs2_op_bound` /
`realize_at_thr`) and, through it, the `τ₀` floor of `partial_sol_tame`.

## STATUS — LANDED, GREEN, AXIOM-CLEAN

Whole-file focused check: **0 errors, 0 warnings**.  Targeted module build
`+DifferentialGeometry.Analysis.Sobolev.Embedding.SobolevEmbeddingUnif`:
**succeeded**.  `#print axioms` on all ten public declarations:
exactly `[propext, Classical.choice, Quot.sound]` — no `sorryAx`.

**Integration probe green.**  `fibreMorrey_unif_base` was fed verbatim, with no
adapter, into the `hmorrey` slot of brick E5's `hs2_fiber_sq_unif`
(`Analysis/Spectral/Tensor/Estimates/H2PointwiseUnif.lean:162`, landed the same
day by the concurrent lane); the composite typechecks with the closed constant
`hs2FibreC (morreyUnifConst Λ (baseMorreyConst gBase 0 s) Kjet n s) Fc n`.  So
the E4/E5 seam is verified, not merely asserted.

## What the brick had to fix

`exists_riemannianFiberNorm_le_iteratedCovGrad_l2_jetSum_supercritical`
(`SobolevEmbeddingSharpC0JetSum.lean:717`) concludes `∃ C, 0 ≤ C ∧ ∀ T x, …`.
The constant is chosen per metric, so two metrics of the same comparability
class receive unrelated constants and the endpoint cannot floor a class-uniform
existence time.  Same disease, same cure as brick E1 in `UnifBochnerGap.lean`:
build the constant-exposed sibling.

## The closed constant

```
morreyUnifConst Λ Cb Kjet n s = √(Λ^s) · (Cb · (n/2+2) · Kjet)
```

with

| factor | origin | status |
|---|---|---|
| `√(Λ^s)` | fibre/Gram comparison, one `Λ` per covariant slot | **proved here** (`fibreNormSq_cross_le`) |
| `Cb` | fibre-Morrey constant of the *fixed* background `gBase` | **discharged** (`baseMorreyConst`, `.choose` at gBase only) |
| `n/2+2` | size of the metric-free supercritical jet window, one Cauchy–Schwarz | **proved here** (dimension only) |
| `Kjet` | cross-metric covariant-jet transfer `gBase`-jets ≼ `g₀`-jets in `L²` | **abstract input** (the S0 seam, see below) |

Nothing in the constant is chosen at a variable metric of the class.  The
Gårding factor that turns this into an `H²` bound (`covsumHsC Fc n 2`) is brick
E5's, not this file's.

## Declarations

* `Integral.L2.SmoothCcTensor.recast` — the metric-free transport of a smooth
  compactly-supported section between metrics.  Neither structure field mentions
  the metric (audit §4 "statement-shape enabler"); this realizes it in Lean.
  *Hoist candidate*: `Analysis/Integration/L2/SmoothSections/Defs.lean`.
* `fibreNormSq_cross_le` — `|T(x)|²_{g₀} ≤ Λ^s · |T(x)|²_{gBase}` for `(0,s)`
  sections under two-sided comparability.  This is audit-piece (a)/(i): the only
  metric-dependence of the Morrey chain that is *not* a jet, and it costs
  comparability alone.
* `morreyUnifConst`, `morreyUnifConst_nonneg`, `morreyUnifConst_sq`.
* `fibreMorrey_unif` — the class-uniform fibre-Morrey bound.
* `baseMorreyConst`, `baseMorreyConst_nonneg`, `fibreNormSq_le_baseMorreyConst`,
  `fibreMorrey_unif_base` — background constant realized at the fixed metric.

A dimension-generic spectral face (`H^{n/2+1}(g₀) → C⁰` with an abstract Gårding
constant) was drafted and then **deleted**: brick E5's `hs2_fiber_sq_unif`
landed concurrently with the same content and an `Fc`-explicit constant, so
keeping both would have created two canonical spectral-fibre endpoints.  One
canonical API per concept; E4 stops at the jet-sum form, which is precisely E5's
`hmorrey` slot.

Private helpers `lowerAllUpper_zero_unit`, `rfns0_eq_normSq0S` are the
generic-`(0,s)` ports of the private `lowerAllUpper_zero_eq_unit` /
`rfns_eq_normSq0S_unit` of `HCGCompactness/MetricCovDerivBridge.lean:159,181`
(there specialized to `metricCcTensor`).  They are the bridge from the Morrey
chain's currency (`riemannianFiberNormSq`) to the comparison layer's currency
(`normSq0S`), which is where `normSq0S_le_of_metric_equiv`
(`Tensor/RSTensor/Tensor0SRiemannian/Comparison.lean:699`) lives.
*Hoist candidate for `rfns0_eq_normSq0S`*: the canonical home is
`Analysis/Elliptic/…/RiemannianFiberNormSq/RiemannianFiberNormSqTensorInnerBridge.lean`;
kept private here to avoid touching a shared file while other lanes are active.

## Why `hjet` is abstract (and not a disguised frontier)

The brick list mandates it: E4's home "must stay in `Analysis/`, so take the jet
input abstractly, as S1 does" — `MetricCovDerivOrderBoundOn` is downstream of
`Analysis/` (Finding C).  The abstract input is a *named, separately-owned
mathematical object* (the S0 cross-metric covariant layer), not a renaming of
the goal: the Gram half of the problem is discharged outright here, and the
Cauchy–Schwarz/dimension bookkeeping is closed.

### Honest-input audit for `hjet` — SATISFIABLE, and cheaper than feared

`hjet` asks: for `j` in the window,
`‖∇^{gBase,j} T‖_{L²(gBase)} ≤ Kjet · Σ_{i<w} ‖∇^{g₀,i} T‖_{L²(g₀)}`.

Available producers (all in `HCGCompactness/`, hence downstream):

1. **pointwise fibre form** — `iterCovG1_two` (`UnifCovSumCross.lean:1249`,
   unconditional `N = 2`) and `iterCovG1_three` (`UnifCovSumN3.lean:290`,
   unconditional `N = 3`), with `g₁ := gBase`, `g₂ := g₀`:
   `|∇_{g₁}^N T|_{g₂} ≤ Dtower(…) · Σ_{k≤N} |∇_{g₂}^k T|_{g₂}`, constant explicit
   in `(Λ, Λ′, Λ″, Λ‴, finrank)`.
2. **fibre-norm change of metric** — `covsumCross_fibNorm`
   (`UnifCovSumCross.lean:211`), or `fibreNormSq_cross_le` in this file.
3. **`L²` assembly** — `tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq`
   (used in `H2Pointwise.lean:52`) plus `volumeMeasure_cross_le`
   (`UnifCovSumCross.lean:1389`, two-sided `√(Λ^n)`) plus Minkowski for the
   finite jet sum inside the integral.

**Order budget (key finding).**  At `finrank ℝ E = 3` the window is
`range (3/2 + 2) = range 3 = {0,1,2}`, so the largest cross-metric jet order
needed by E4 is **2**, and the spectral order is **2** (`H²`).  Therefore
`iterCovG1_two` — which is *unconditional* — already covers the pointwise half;
the lane's only `sorry`, `hAcc_of_jets` (`UnifCovSumN3.lean:384`), is **not** on
E4's path.  This also means E0's metric-jet order for this brick is `≤ 3`
(`hjet`/`hJet1`/`hJet2` at orders 1, 1, 2 as `iterCovG1_two` consumes them), not
`~6`; the `~6` estimate belongs to the Gårding recursion (E1/E3), not to E4.

### The one real gap left in the `hjet` discharge — **CLOSED 2026-07-30**

**Update.**  This gap is discharged.  See
`Geometry/Flow/RicciFlow/HCGCompactness/UnifJetTowerMatch.lean` (+ `.md`):
`iterCovGrad_unit_eq` is the generic-rank tower match described below,
`kjet_of_class` supplies this file's `hjet` slot from `Λ`-class data with the
closed constant `kjetConst`, and `fibreMorrey_unif_class` is brick E4 with **no
abstract input left** — green, warning-free, `#print axioms` clean on all
fourteen public declarations.  Scope: `finrank ℝ E / 2 + 2 = 3` (i.e. the
`dim = 3` window `{0,1,2}`), which is exactly the reach of the unconditional
`iterCovG1_two`; `hAcc_of_jets` is confirmed off the path (no `sorryAx`).
The original diagnosis, kept for the record:

The pointwise producers speak `iterCov`/`covStep` on `Tensor0SField`, while the
Morrey chain speaks `iteratedCovGrad` on `SmoothCcTensor`.  The tower match
between them exists only in the *specialized* private form
`iterCovGrad_unit_eq_iterCov` (`MetricCovDerivBridge.lean:83`, rank `(0,2)`,
`metricCcTensor` only).  The generic-rank version — "the unit-value of
`iteratedCovGrad g 0 s j W` is `iterCov g s (unit-value field of W) j`" — is the
smallest missing lemma for a concrete `hjet`, and its proof is the same
induction (`covGrad_apply_unit_eval_genVal` → `covDeriv_unit_eval_eq_genVal` →
`nabla0SFun_eq_tensor0SCovariantDerivative` → `covStep_apply`), plus packaging
`W`'s unit-value as a smooth `Tensor0SField`.  Difficulty: routine-to-moderate;
no new mathematics, but real Lean plumbing (~200–400 lines).  It belongs in
`HCGCompactness/`, next to `MetricCovDerivBridge`.

## Nothing new mathematically appeared

Per the mission's stop condition: no input beyond Gram-norms + jet conversions
was needed.  In particular no injectivity radius, no `λ₁`, no metric-dependent
covering number entered — as the risk-2 audit predicted, because `chartAtlasPOU`
and `chartAtlasPOU_finset` take no metric argument and `wkpNormChart` discards
its metric argument.  The Morrey chain's *entire* metric dependence is the two
factors tabulated above.

## Lean lessons

* `omit` cascades.  Cleaning `unusedSectionVars` on a private helper can make
  the same instances unused in its *consumers*; the linter reports one layer per
  run, so expect to re-check after each `omit`.  Here `unitZeroSec` looks like it
  needs `[NeZero (finrank)] [CompactSpace M] [I.Boundaryless]` from its file's
  `variable` block, but Lean 4's usage-based variable inclusion had already
  dropped them from its real signature.
* `omit` of an instance that *is* referenced fails with
  `cannot omit referenced section variable inst✝ⁿ`; the index is counted from the
  end of the section-variable list, which is unhelpful — bisect instead.
* `normSq0S_le_of_metric_equiv` concludes with a **zpow** (`C ^ (s : ℤ)`);
  `rwa [zpow_natCast] at h` converts to the `ℕ`-power the Morrey side wants.
* `SmoothCcTensor g r s` is metric-indexed only for instance attachment; the
  anonymous-constructor recast `⟨T.toSection, T.hasCompactSupport⟩` typechecks
  and is `rfl` on `toSection`, which is what makes any cross-metric statement
  about one and the same section expressible.

## For the planner

`UNIF_EXISTENCE_PLAN.md` was **not** edited (it is dirty in the working tree
from the active Codex lane).  Link this file from the Lane E entry when
convenient.

State of the E4 → `P*` chain after this session:

* **E4 (this file)** — closed constant landed; one abstract input `Kjet`.
* **E5** (`H2PointwiseUnif.lean`, concurrent lane) — landed; consumes E4's output
  as `hmorrey` (verified by the integration probe) and E1's `Fc` as `hcurv`, and
  outputs the closed realization radius `unifRealizeRad Cpt Fc d`.
* **`Kjet` — DISCHARGED 2026-07-30** by `HCGCompactness/UnifJetTowerMatch.lean`
  (`kjet_of_class`, constant `kjetConst`), at `finrank ℝ E / 2 + 2 = 3`.
  `fibreMorrey_unif_class` there is this file's endpoint with the input removed.
* **remaining for a `Λ`-only `P*`**: discharge E1's `Fc` from `Λ` (brick E3, the
  curvature-jet lane).  That is now the ONLY abstract input left on the
  E4→E5→`P*` path.

**E7** (`lower_jet_h1` and the tame packet) can quote `fibreMorrey_unif_base`
directly for its Morrey factor.
