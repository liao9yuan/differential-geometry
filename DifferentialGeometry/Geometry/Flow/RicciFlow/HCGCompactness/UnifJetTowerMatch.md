# UnifJetTowerMatch — discharging brick E4's `Kjet`

Session 1 (Opus 5), branch `codex/short-time-existence-align`, 2026-07-30.
Consumer: `Analysis/Sobolev/Embedding/SobolevEmbeddingUnif.lean` (brick **E4**),
whose `.md` §"The one real gap left in the `hjet` discharge" specified exactly
this file.

## STATUS — LANDED, GREEN, AXIOM-CLEAN

Whole-file focused check: 0 errors, 0 warnings.  Targeted module build
`+DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.UnifJetTowerMatch`:
succeeded, warning-free.  `#print axioms` on all fourteen public declarations:
exactly `[propext, Classical.choice, Quot.sound]`.  **No `sorryAx`** — in
particular the lane's open `hAcc_of_jets` (`UnifCovSumN3.lean`) is confirmed off
this path (this file does not import `UnifCovSumN3` at all; only `iterCovG1_le`
at `N = 1` and the unconditional `iterCovG1_two` at `N = 2` are used).

New file only.  **No existing file was edited.**

## What was proved

The chain runs pointwise → `L²` → E4:

1. `ccUnitField g s W` — the unit-value `(0,s)` tensor field of a `SmoothCcTensor
   g 0 s`, i.e. the smooth core the two covariant-derivative formalisms share.
2. `iterCovGrad_unit_eq` — **the generic-rank tower match** (the lemma the E4 note
   named): the unit-value of `iteratedCovGrad g 0 s j W` is `iterCov g s
   (ccUnitField g s W) j`.  Same induction as the private rank-`(0,2)`
   `iterCovGrad_unit_eq_iterCov` of `MetricCovDerivBridge.lean` (read as
   reference; **not** edited), with `2 → s`.
3. `rfns0_unit_eq` — generic-rank fibre-inner bridge `riemannianFiberNormSq =
   normSq0S` of the unit-value; `rfns_iterCovGrad_eq` composes 2 and 3.
4. `sqrtRfns_cross_le` — pointwise cross-metric jet bound at orders `≤ 2`.
5. `jetCross_l2` — its `L²` face, across the two volume measures.
6. `kjet_of_class` — E4's `hjet` slot from `Λ`-class data.
7. `fibreMorrey_unif_class` — brick E4 with **no abstract input left**.

## The closed constants

```
jetTowerPt n Λ Λ' Λ'' r = √(Λ^{r+2}) · (1 + D₁ + D₂)
kjetConst  n Λ Λ' Λ'' s = √(3·√(Λⁿ)) · jetTowerPt n Λ Λ' Λ'' s
```

with `D₁ = Dtower n q r (fun _ => 0) 1`, `D₂ = Dtower n q r Racc₂ 2`,
`q = (3/2)·√(Λ³)·Λ'`, and `Racc₂` the `iterCovG1_two` accumulator family.

| factor | origin |
|---|---|
| `√(Λ^{r+2})` | fibre change of metric on a `(0,r+j)` tensor, `j ≤ 2` (`covsumCross_fibNorm`) |
| `1` | order `j = 0` (the two towers coincide) |
| `D₁` | order `j = 1`, `iterCovG1_le` at `N = 1` (accumulator vanishes) |
| `D₂` | order `j = 2`, unconditional `iterCovG1_two` |
| `√3` | one Cauchy–Schwarz over the three-order window |
| `√(√(Λⁿ))` | volume comparison `volumeMeasure_cross_le`, direction `dV_gBase ≤ √(Λⁿ)·dV_g₀` |

Feeding this into E4 gives the fully closed fibre-Morrey constant
`morreyUnifConst Λ (baseMorreyConst gBase 0 s) (kjetConst dim Λ Λ' Λ'' s) dim s`.

## Hypotheses actually consumed (honest input list)

* `MetricUniformEquivalentOn univ gBase g₀ Λ`
* `MetricCovDerivOrderBoundOn univ 1 g₀ gBase Λ'`  (`∇^{gBase} g₀`)
* `MetricCovDerivOrderBoundOn univ 1 gBase g₀ Λ'`  (`∇^{g₀} gBase`)
* `MetricCovDerivOrderBoundOn univ 2 gBase g₀ Λ''` (`∇²^{g₀} gBase`)
* `0 ≤ Λ'`, `0 ≤ Λ''` — needed only at the `L²` level, where no base point is
  available to extract them from the bound predicates (`M` is not assumed
  nonempty).  Trivial for any caller; they are bounds on `Real.sqrt` quantities.
* `hdim : finrank ℝ E / 2 + 2 = 3` — the window has exactly three orders.  This is
  the honest scope of `iterCovG1_two`: at `dim = 3` (the case of interest) the
  supercritical window is `{0,1,2}` and orders `≤ 2` suffice.  A larger `dim`
  needs `iterCovG1_three` and beyond, hence `hAcc_of_jets`.

So E4's metric-jet order for this brick is `≤ 2` (orders 1, 1, 2), **not** `~6`
— confirming the order budget recorded in `SobolevEmbeddingUnif.md`.

## Lean lessons

* **`Tensor0SField` cannot be built with an anonymous constructor here.**
  `⟨unitEvalSection …, contMDiff_unitEvalSection …⟩` against the expected type
  `Tensor0SField … s` fails with `failed to synthesize NormedSpace ℝ
  (Tensor0SModel s ℝ E)` — even though `example : NormedSpace ℝ (Tensor0SModel s
  ℝ E) := inferInstance` succeeds *in the same local context*, and even after a
  `haveI` of that very instance, and even with `letI :=
  tensor0SBundle_topology …` (the pattern that works verbatim in
  `DeTurckLieArm1CoeffL2JetBound.lieArm1PbLowField`).  The synthesis inside the
  constructor elaboration evidently runs against a metavariable-laden goal; the
  displayed instance is instantiated only for the error message.  **Fix: use
  `MixedSection.toMultilinearSection`** (`Tensor/Mixed/Field.lean`), the
  canonical `(0,s)`-section → multilinear-field map — this is what
  `ccTensorMultilinear` (`TensorHsRealize.lean`, rank 2) does.  It elaborates
  cleanly and keeps `ccUnitField g s W x = W.toSection x (unitZeroSec x)` as
  `rfl`.  Diagnose this class of failure by bisecting with a probe file built
  from the target file's own header.
* The tower-match induction must be stated in the *unfolded* CLM-application
  form `fun x => (T.toSection x) (unitZeroSec x)`, not in `ccUnitField` form:
  the successor step's `rw [ih]` has to match the term
  `covDeriv_unit_eval_eq_genVal` produces, which is the unfolded one.  Bridge to
  `ccUnitField` afterwards with a `have … := congrFun …` (defeq, so it
  typechecks).
* `Finset.range_subset.mpr (by norm_num)` inside a `Finset.sum_le_sum_of_subset_
  of_nonneg` application leaves `by norm_num` staring at the unfolded subset goal
  `∀ x ≤ 1, x < 3` (elaboration postponement).  State the subset as a separate
  `have` with `intro`/`simp only [Finset.mem_range]`/`omega`.
* Same for `Real.sqrt_le_sqrt (pow_le_pow_right₀ hEq.1 (by omega))`: split off
  the `Λ^(s+j) ≤ Λ^(s+2)` step as its own `have`.
* `rw` closes goals by `rfl` automatically — a trailing `ring` after a
  successful `rw` chain becomes a "No goals to be solved" error.
* The `PowerShell` tool's cwd in this session was the **stale** checkout
  `E:\testdifferential-geometry`; every invocation needs
  `Set-Location E:\testdifferential-geometry-ste-align` first, or
  `lake-locked.ps1` silently claims/checks in the wrong repository ("No existing
  Lean files to check").

## Duplication to collapse later (do not leave unrecorded)

`rfns0_unit_eq` here is the generic-rank canonical form of two private replicas:

* `MetricCovDerivBridge.rfns_eq_normSq0S_unit` (`:181`, rank `(0,s)` already, but
  `private`);
* `SobolevEmbeddingUnif.rfns0_eq_normSq0S` (`private`).

Likewise `lowerAllUpper0_unit` triples `lowerAllUpper_zero_eq_unit` /
`lowerAllUpper_zero_unit`, and `covStepZero` / `sqrtNormSq0SZero` /
`dtowerNonneg` replicate private helpers of `UnifCovSumCross.lean`.  All were
re-derived (not copied wholesale) because the originals are `private`.  The
canonical home for the fibre-inner bridge remains
`Analysis/Elliptic/…/RiemannianFiberNormSq/RiemannianFiberNormSqTensorInnerBridge.lean`;
`covStep_zero'` / `sqrt_normSq0S_zero` / `Dtower_nonneg` belong in
`MetricCovDerivLinear.lean` / `UnifCovSumCross.lean` as public lemmas.  Collapse
when those files are next opened by their owning lane.

## Progress in the whole project

End goal: Hamilton–Cheeger–Gromov compactness (MSM135 Ch. 3–4) and, above it,
the Poincaré program.  This file sits in Lane E (the `Λ`-uniform analytic packet
feeding the `τ₀` floor of `partial_sol_tame`), which is itself one input to the
short-time-existence/uniformity spine — not to Lemma 3.11 or Theorem 3.9
directly.

Honest numbers:

* this file ≈ **100%** of the E4 `Kjet` seam it was scoped to;
* **brick E4** — was "landed with one abstract input"; now **unconditional at
  `dim = 3`**.  E4 itself: ~100% for the `dim = 3` case, ~60% order-generic (the
  `dim > 3` window needs `iterCovG1_three` + `hAcc_of_jets`);
* the **E4 → E5 → `P*` chain**: two abstract inputs remained after E4; one
  (`Kjet`) is now discharged, so ~50% of that chain's remaining input debt is
  cleared.  The other, E1's curvature-jet envelope `Fc` (brick E3), is untouched
  and is the larger of the two;
* **Lane E** as a whole: perhaps ~35–45% — E4/E5 are green, E1/E3 and E7 are not;
* the **`(N)` uniform-existence campaign** (`UNIF_EXISTENCE_PLAN.md` №36): its
  machinery ≈72% by the standing estimate, the `(N)` theorem itself **0%** (not
  yet stated in Lean).  This brick does not change either number materially;
* the **whole HCG-compactness project**: unchanged at the low single-digit to
  low-teens percentage the project map records.  One discharged input on one
  analytic brick of one lane is a small fraction of a multi-week frontier.

Do not read the green tree here as progress on Theorem 3.9/3.10.
