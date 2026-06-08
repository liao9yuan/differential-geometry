import DifferentialGeometry.Geometry.Connection.TensorNabla.OperatorFieldCovariantCalculusRS
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.RankRPureRCurvatureTower

/-!
# The frame-free differentiated `(∇R)·` curvature tower at contravariant valence `r`

For a closed (compact, boundaryless) smooth Riemannian manifold `(M, g)` this file is the
contravariant-valence-`r` lift of the intrinsic differentiated-curvature graded-jet tower
`diffCurvGenuineDiffOp` (`DiffCurvatureGenuineTower`), the `(∇R) S` operator carrier of the order-`2`
rough-Laplacian / covariant-gradient commutator defect.  The rank-`0` tower is hard-locked to
contravariant rank `0`: its order-`0` base is the operator-field action `appCc (∇Φ₀ r) W` of the fixed
smooth differentiated-curvature operator field `Ψ₀ r := ∇(Φ₀ r)` (`diffCurvOpField`,
`covGrad (curvOpField g r)`), where the contravariant-rank-`0`-locked action `appCc` and the
rank-`0`-locked curvature operator field `curvOpField` both carry a literal contravariant `0`.

## Why the rank-`0` construction does NOT lift verbatim (the `appCcRS` post-composition is the wrong action)

At contravariant rank `0` a `(0, s)`-tensor `W` *is* the continuous-linear map `Tensor0SSpace 0 → Tensor0SSpace s`,
and the order-`0` curvature endomorphism acts entirely on its `Tensor0SSpace s` codomain, so it factors as
*post-composition* by a fixed `(s, s)`-operator field — exactly the rank-`0` action `appCc`.  At a generic
contravariant valence `r ≥ 1` this factorisation is **false**: the order-`0` moving-centre pure-Riemann
endomorphism `genuinePureRDiffOpRS g r 0 rr W` contracts the *full* `(r, rr)`-tensor curvature
`riemannOp (tensorCov g r rr)`, whose point-level slot-wise formula
`riemannOp_tensorCovRS_apply_eval` (`RankRUniformProportionalCurvatureSup`) decomposes into a covariant
`(0, rr)`-tensor branch `R^{(0,rr)}(T(Y₀))` *and* a contravariant `(0, r)`-tensor branch
`T(R^{(0,r)}(Y₀))` (opposite sign).  The contravariant branch is genuinely non-zero on a curved manifold
for `r ≥ 1` and is **not** captured by post-composition `(Φ x).comp (W x)`; hence the order-`0`
endomorphism does NOT factor through any `(rr, rr)`-operator-field `appCcRS` action, and the contravariant-
valence-`r` curvature operator field that the rank-`0` mirror would posit *does not exist for `r ≥ 1`*.

The differentiated `(∇R)·` tower at valence `r` is therefore built on the **full** `(r, rr)`-tensor
curvature carrier rather than the codomain-only `appCcRS` post-composition: its order-`0` base is the
genuine differentiated-curvature contraction `(∇R) W` — the order-`1` moving-centre pure-Riemann
differentiated tower `genuinePureRDiffOpRS g r 1 rr` (`RankRPureRCurvatureTower`) — realised
*value-locally* (reading only the fibre value `W x`, the structural fingerprint of a fixed smooth
curvature coefficient `∇R`).  The value-local realisation of `(∇R)·` with its per-order, per-rank
section-proportional jet envelope is the genuinely-irreducible analytic content of this tower (the smooth
`∇^{≤ p}(∇R)` curvature coefficient, uniformly fibre-operator-bounded over the compact `M`), exactly the
contravariant-valence-`r` analogue of the rank-`0` `genuineDiffCurvSection` engine and the
per-tower-posited high-order envelope sanctioned by `IteratedDiffOpProportionalBound` /
`OperatorFieldEvaluationLeibniz`; it is collected as the single posited node `exists_diffCurvGenuineTowerRS`.

## What is proved vs. posited

* the **single posited node** `exists_diffCurvGenuineTowerRS` packages the genuine differentiated `(∇R)·`
  tower at valence `r`: a rank-raising operator family whose order-`0` base value-locally realises the
  genuine differentiated curvature `(∇R) W` (pinned to `genuinePureRDiffOpRS g r 1 rr W`, the genuine
  moving-centre differentiated trace — non-vacuous, `ℝ`-linear and value-local at order `0`), whose
  single-step covariant Leibniz is the exact remainder, and whose per-order, per-rank section-proportional
  jet envelope is the smooth `∇^{≤ p}(∇R)` coefficient bound.  Consumers transitively depend on `sorryAx`
  through this single node;
* the **order-`p` differentiated operator** `diffCurvGenuineDiffOpRS` is the chosen tower; its single-step
  Leibniz `covGrad_diffCurvGenuineDiffOpRS_eq`, per-order envelope
  `exists_proportional_diffCurvGenuineDiffOpRS`, and binomial covariant-Leibniz `rfns` grid
  `rfns_iteratedCovGrad_diffCurvGenuineDiffOpRS_grid` are *proved* outright from the posited node — the
  grid by the same binomial covariant-Leibniz induction the rank-`0` and pure-Riemann towers use, with no
  posit of its own.

The `(∇R) S` carrier `diffCurvSectionRS g r s S := diffCurvGenuineDiffOpRS g r 0 s S` is the order-`0`
base; its iterated-gradient grid bound of lowest order `0` and width `1`
(`exists_diffCurvSectionRS_iteratedCovGrad_grid_bound`, the raw fibre-inequality form) is *proved* from
the `rfns` grid, exactly the rank-`r` mirror of the rank-`0` `genuineDiffCurvSection_gradedCurvJet`.  The
downstream consumer `OrderSeparatedCurvatureJetRS` (which imports this file and owns the
`IsGradedCurvJetRS` predicate) packages it as the graded curvature jet
`exists_diffCurvSectionRS_gradedCurvJet`.

Because the `(∇R)·` tower genuinely *raises* the covariant rank by one at order `0` (it carries the
codomain `rr + 1 + p`, not `rr + p`), it is **not** a rank-preserving `DiffBilinOpRS`; the binomial
covariant-Leibniz grid is therefore built directly here through the single-step remainder, exactly as the
rank-`0` differentiated-curvature tower `DiffCurvatureGenuineTower` builds its own raising grid.

## Convention

Geometer convention; all fibre norms are the intrinsic `riemannianFiberNormSq`.  The construction stays
intrinsic: `covGrad` covariant gradients, the full `(r, rr)`-tensor curvature carrier, and `rfns` fibre
norms only — no moving-frame extraction, no chart-frame jet, no codomain-only post-composition.
-/

noncomputable section

set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.PDE.RicciFlow

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

/-! ## The genuine differentiated `(∇R)·` tower at valence `r`

The tower is built as the **exact covariant-Leibniz remainder recursion** off the genuine order-`1`
moving-centre pure-Riemann differentiated trace `genuinePureRDiffOpRS g r 1 rr` (the public `(∇R) W`
contraction `covGrad(R W) − R(∇W)`, `RankRPureRCurvatureTower`), recast to the rank-raising codomain
`rr + 1 + p`.  Three of the five tower clauses are *proved here* outright:

* the order-`0` base is the recast genuine `(∇R) W` (`base_value`, by definitional rank-cast);
* the single-step covariant Leibniz is the exact remainder (`leibniz`, by `sub_add_cancel`, exactly the
  recursion shape of `covGrad_genuinePureRDiffOpRS_eq`).

The two genuinely-irreducible analytic facts are posited as **precise children** (each a non-vacuous
mathematical statement about the genuine full-tensor `(∇R)·`, *not* the parent rephrased):

* `genuinePureRDiffOp_orderOne_linear` / `genuinePureRDiffOp_orderOne_local` — the order-`0` base is
  `ℝ`-linear and **value-local** in `W` (the `(∇R)`-endo factorisation: the differentiated trace
  `covGrad(R W) − R(∇W)` reads only the fibre value `W x` against the fixed smooth curvature-jet operator
  `∇R(x)`, the input derivative `∇W` cancelling by the full-tensor Hom product rule).  Supplies
  `base_linear`, `base_local`;
* `exists_diffCurvGenuineTowerOpRS_envelope` — the per-order, per-rank **tight-window** jet envelope
  `rfns(op p rr W)(x) ≤ kappa p rr · ∑_{q < p + 1} rfns(∇^q W)(x)` (window `p + 1`, the section entering at
  order `0`).  This is the output of the full-tensor operator-field normal form of the *fixed* smooth
  coefficient `∇R`: the order-`p` value is a finite sum of full-Hom actions `appFullRS (∇^{≤ p}(∇R)) ∇^{≤ p}W`,
  each bounded by the uniform curvature-jet sup `‖∇^{≤ p + 1} R‖_∞` over the compact `M` (the intrinsic
  partial-contraction Cauchy–Schwarz `riemannianFiberNormSq_compRS_le_mul` lifted to full fibres) times
  `rfns(∇^{≤ p}W)`.  Supplies `envelope`.

These are the contravariant-valence-`r` analogues of the rank-`0` `genuineDiffCurvSection` engine, where
the order-`0` base post-composes (`appCc`); at valence `r ≥ 1` the curvature acts on the *full*
`(r, rr)`-tensor (contravariant branch `riemannOp_tensorCovRS_apply_eval`), so the codomain-only `appCcRS`
post-composition is insufficient and the full-Hom `appFullRS` calculus, its Hom-bundle covariant product
rule, the `(∇R)`-endo factorisation, and the `‖∇^{≤ p} R‖_∞` sup are the genuine sub-content (built in the
`OperatorFieldCovariantCalculusRS` / `HomBundleNabla` / `RankRPureRCurvatureTower` line). -/

/-- **The genuine differentiated `(∇R)·` tower operator at valence `r`, order `p`, base width `rr`.** The
exact covariant-Leibniz remainder recursion off the genuine order-`1` moving-centre pure-Riemann
differentiated trace `genuinePureRDiffOpRS g r 1 rr` (the `(∇R) W` contraction `covGrad(R W) − R(∇W)`),
recast to the rank-raising codomain `rr + 1 + p`:

* `p = 0`: the recast genuine `(∇R) W`, `castRankCc_db (genuinePureRDiffOpRS g r 1 rr W)`;
* `p + 1`: `∇(op p rr W) − (rank-cast) op p (rr + 1) (∇W)` — the differentiated-coefficient remainder (the
  input section's derivative `∇W` cancels), rank-cast `(rr + 1) + 1 + p = rr + 1 + (p + 1)`.

By construction the single-step covariant Leibniz holds by `sub_add_cancel`; the section enters at order
`0` (the curvature coefficient `∇R` is fixed and smooth, only it is differentiated up the tower). The
valence-`r`, rank-raising mirror of `diffCurvGenuineDiffOp` (`DiffCurvatureGenuineTower`). -/
private noncomputable def diffCurvGenuineTowerOpRS
    (g : SmoothRiemannianMetric I M) (r : ℕ) :
    ∀ (p rr : ℕ), SmoothCcTensor g r rr → SmoothCcTensor g r (rr + 1 + p)
  | 0, rr => fun W =>
      castRankCc_db g r (by omega : rr + 1 = rr + 1 + 0)
        (genuinePureRDiffOpRS (I := I) (M := M) g r 1 rr W)
  | (p + 1), rr => fun W =>
      covGrad (I := I) (M := M) g r (rr + 1 + p)
          (diffCurvGenuineTowerOpRS g r p rr W) -
        castRankCc_db g r (by omega : (rr + 1) + 1 + p = rr + 1 + (p + 1))
          (diffCurvGenuineTowerOpRS g r p (rr + 1) (covGrad (I := I) (M := M) g r rr W))

/-- **The order-`0` base is the recast genuine `(∇R) W` trace.** By definition. -/
private theorem diffCurvGenuineTowerOpRS_zero (g : SmoothRiemannianMetric I M) (r rr : ℕ)
    (W : SmoothCcTensor g r rr) :
    diffCurvGenuineTowerOpRS (I := I) (M := M) g r 0 rr W =
      castRankCc_db g r (by omega : rr + 1 = rr + 1 + 0)
        (genuinePureRDiffOpRS (I := I) (M := M) g r 1 rr W) := rfl

set_option linter.unusedSectionVars false in
/-- **The fibre value of a `+0` rank-cast equals the uncast fibre value.** For the definitionally-trivial
rank-cast `castRankCc_db g r (h : a = a + 0)` the fibre value at `x` is unchanged (both fibre types
`TensorRSSpace r (a + 0)` and `TensorRSSpace r a` are definitionally equal). -/
private theorem castRankCc_db_addZero_toSection_eq (g : SmoothRiemannianMetric I M)
    (r a : ℕ) (W : SmoothCcTensor g r a) (x : M) :
    (castRankCc_db g r (by omega : a = a + 0) W).toSection x = W.toSection x := rfl

/-- **The exact single-step covariant Leibniz of the differentiated `(∇R)·` tower at valence `r`.** By the
recursive definition, `∇(op p rr W)` splits exactly into the higher-order remainder `op (p + 1) rr W` and
the rank-cast lower-order term applied to `∇W`. Proved by `sub_add_cancel`. -/
private theorem covGrad_diffCurvGenuineTowerOpRS_eq
    (g : SmoothRiemannianMetric I M) (r p rr : ℕ) (W : SmoothCcTensor g r rr) :
    covGrad (I := I) (M := M) g r (rr + 1 + p)
        (diffCurvGenuineTowerOpRS (I := I) (M := M) g r p rr W) =
      diffCurvGenuineTowerOpRS (I := I) (M := M) g r (p + 1) rr W +
        castRankCc_db g r (by omega : (rr + 1) + 1 + p = rr + 1 + (p + 1))
          (diffCurvGenuineTowerOpRS (I := I) (M := M) g r p (rr + 1)
            (covGrad (I := I) (M := M) g r rr W)) := by
  change _ = (covGrad (I := I) (M := M) g r (rr + 1 + p)
      (diffCurvGenuineTowerOpRS (I := I) (M := M) g r p rr W) -
      castRankCc_db g r (by omega : (rr + 1) + 1 + p = rr + 1 + (p + 1))
        (diffCurvGenuineTowerOpRS (I := I) (M := M) g r p (rr + 1)
          (covGrad (I := I) (M := M) g r rr W))) + _
  rw [sub_add_cancel]

/-- **Child (the `(∇R)`-endo factorisation, `ℝ`-linearity).** The order-`1` moving-centre pure-Riemann
differentiated trace `genuinePureRDiffOpRS g r 1 rr` (the genuine `(∇R) W`) is `ℝ`-linear in the contracted
section at the fibre-value level: for scalars `c₁, c₂` and sections `W₁, W₂`,
```
(genuinePureRDiffOpRS g r 1 rr (c₁ • W₁ + c₂ • W₂)).toSection x
  = c₁ • (genuinePureRDiffOpRS g r 1 rr W₁).toSection x + c₂ • (genuinePureRDiffOpRS g r 1 rr W₂).toSection x.
```

**Why this is TRUE.** The genuine `(∇R) W = covGrad(R W) − R(∇W)` factors, value-locally, through a *fixed*
smooth full Hom-bundle operator `(∇R)(x) : T^{(r,rr)}_x →L T^{(r,rr+1)}_x` (the curvature jet read at the
point), `(∇R) W = appFullRS (∇R) W` in the notation of the full-tensor operator-field action; the input
derivative `∇W` cancels by the Hom-bundle covariant product rule `∇(Φ·W) = (∇Φ)·W + Φ·(∇W)`
(`covGrad_appFullRS_eq`, the full-fibre analogue of `covGrad_appCcRS_eq`).  A full Hom action `Ψ x (W x)`
is `ℝ`-linear in `W x`, so the trace is `ℝ`-linear in `W` at the fibre-value level.  This `appFullRS`
factorisation of the full-tensor `(∇R)·` is absent sorry-free at valence `r` below this file (the
codomain-only `appCcRS` post-composition does not capture the contravariant curvature branch
`riemannOp_tensorCovRS_apply_eval`), so it is posited here as one precise true child.  Consumers
transitively depend on `sorryAx`.

**Non-vacuity.** A nonlinear or non-fibre-value operator is rejected: a generic differentiated tower
`W ↦ covGrad W` is *not* fibre-value-`ℝ`-bilinear at order `0` (it reads the jet, not the value); only the
genuine value-local curvature contraction passes, and it is genuinely non-zero (`∇R ≠ 0`) for a
non-parallel `W`. -/
private theorem genuinePureRDiffOp_orderOne_linear
    (g : SmoothRiemannianMetric I M) (r rr : ℕ)
    (c₁ c₂ : ℝ) (W₁ W₂ : SmoothCcTensor g r rr) (x : M) :
    (genuinePureRDiffOpRS (I := I) (M := M) g r 1 rr (c₁ • W₁ + c₂ • W₂)).toSection x =
      c₁ • (genuinePureRDiffOpRS (I := I) (M := M) g r 1 rr W₁).toSection x +
        c₂ • (genuinePureRDiffOpRS (I := I) (M := M) g r 1 rr W₂).toSection x := by
  sorry

/-- **Child (the `(∇R)`-endo factorisation, value-locality).** The order-`1` moving-centre pure-Riemann
differentiated trace `genuinePureRDiffOpRS g r 1 rr` (the genuine `(∇R) W`) is **value-local** in the
contracted section: its fibre value at `x` depends only on the fibre value `W x`,
```
W₁.toSection x = W₂.toSection x →
  (genuinePureRDiffOpRS g r 1 rr W₁).toSection x = (genuinePureRDiffOpRS g r 1 rr W₂).toSection x.
```

**Why this is TRUE.** Identical mechanism to `genuinePureRDiffOp_orderOne_linear`: the genuine
`(∇R) W = covGrad(R W) − R(∇W)` factors value-locally as the full Hom action `appFullRS (∇R) W = (∇R)(x)(W x)`
of the *fixed* smooth curvature-jet operator `(∇R)(x)` on the fibre value `W x` (the `∇W` contributions of
`covGrad(R W)` and `R(∇W)` cancelling, `covGrad_appFullRS_eq`); a full Hom action `Ψ x (W x)` reads only
`W x`, so the trace is value-local.  This `appFullRS` factorisation is absent sorry-free at valence `r`,
posited as one precise true child.  Consumers transitively depend on `sorryAx`.

**Non-vacuity.** A non-value-local operator (e.g. `W ↦ covGrad W`, reading the derivative jet) is rejected:
two sections agreeing at `x` but differing in their first jet there give equal fibre values but unequal
covariant gradients, so only a genuinely value-local fibre contraction satisfies this; the genuine
curvature trace does, the order-`1` *raw* pure-Riemann tower (before cancellation) would not. -/
private theorem genuinePureRDiffOp_orderOne_local
    (g : SmoothRiemannianMetric I M) (r rr : ℕ)
    (W₁ W₂ : SmoothCcTensor g r rr) (x : M)
    (hW : W₁.toSection x = W₂.toSection x) :
    (genuinePureRDiffOpRS (I := I) (M := M) g r 1 rr W₁).toSection x =
      (genuinePureRDiffOpRS (I := I) (M := M) g r 1 rr W₂).toSection x := by
  sorry

/-- **Child (the tight-window jet envelope, the `‖∇^{≤ p} R‖_∞` curvature-jet sup).** For a closed smooth
Riemannian manifold `(M, g)` and a fixed contravariant valence `r` there is a nonnegative per-order,
per-rank envelope `kappa : ℕ → ℕ → ℝ` such that, for every order `p`, base width `rr`, smooth
compactly-supported `(r, rr)`-tensor `W`, and base point `x`,
```
rfns(diffCurvGenuineTowerOpRS g r p rr W)(x) ≤ kappa p rr · ∑_{q < p + 1} rfns(∇^q W)(x).
```
The window is the *tight* `p + 1` (the section enters at order `0`, width `1`).

**Why this is TRUE.** The tower is the exact covariant-Leibniz remainder recursion off the genuine order-`1`
trace `(∇R) W`, whose order-`0` base value-locally factors as the full Hom action `appFullRS (∇R) W` of the
*fixed* smooth curvature-jet coefficient `∇R` (`genuinePureRDiffOp_orderOne_local` /
`genuinePureRDiffOp_orderOne_linear`).  Running the full-tensor operator-field normal form
(`NormalFormRaiseRS`, the full-fibre analogue of the proved `appCcRS` normal form `normalForm_of_baseRS`)
over the fixed coefficient `∇R` expresses `op p rr W` as a finite sum of full Hom actions
`appFullRS (∇^k(∇R)) (∇^k W)`, `k < p + 1`, of the *fixed* iterated curvature jets `∇^{≤ p}(∇R)` on the
covariant jets `∇^{≤ p}W` of the contracted section; each `∇^k(∇R)` is a fixed smooth Hom-bundle field,
uniformly fibre-operator-bounded over the compact `M` by `‖∇^{≤ p + 1} R‖_∞`, and the full-fibre
partial-contraction Cauchy–Schwarz `rfns(Ψ x (W x)) ≤ rfns_Hom(Ψ x) · rfns(W x)` (the full-fibre lift of
`riemannianFiberNormSq_compRS_le_mul`) bounds each summand by `‖∇^k(∇R)‖_∞ · rfns(∇^k W)(x)`, giving the
tight `p + 1` window.  The full-Hom `appFullRS` calculus, its Hom-bundle covariant product rule, the
`(∇R)`-endo factorisation, and the `‖∇^{≤ p} R‖_∞` uniform curvature-jet sup are absent sorry-free at
valence `r` below this file (the codomain-only `appCcRS` post-composition misses the contravariant
curvature branch), so this tight-window envelope is posited here as one precise true child.  Consumers
transitively depend on `sorryAx`.

**Non-vacuity.** A degenerate witness `kappa ≡ 0` is rejected on any non-flat manifold: at
`(p, rr) = (0, rr)`, `diffCurvGenuineTowerOpRS g r 0 rr W` is the genuine `(∇R) W`, genuinely non-zero
(`∇R ≠ 0`) for a non-parallel `W`, forcing `rfns(diffCurvGenuineTowerOpRS g r 0 rr W)(x) > 0` while the RHS
`0 · ∑_{q < 1} rfns(∇^q W)(x) = 0`; the envelope must carry the genuine differentiated-curvature magnitude. -/
private theorem exists_diffCurvGenuineTowerOpRS_envelope (g : SmoothRiemannianMetric I M) (r : ℕ) :
    ∃ kappa : ℕ → ℕ → ℝ, (∀ p rr, 0 ≤ kappa p rr) ∧
      ∀ (p rr : ℕ) (W : SmoothCcTensor g r rr) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g r (rr + 1 + p) x
            ((diffCurvGenuineTowerOpRS (I := I) (M := M) g r p rr W).toSection x) ≤
          kappa p rr * ∑ q ∈ Finset.range (p + 1),
            riemannianFiberNormSq (I := I) (M := M) g r (rr + q) x
              ((iteratedCovGrad g r rr q W).toSection x) := by
  sorry

set_option linter.unusedVariables false in
/-- **The genuine differentiated `(∇R)·` curvature tower at valence `r` (assembled from the recursion and
its two analytic children).** For a closed smooth Riemannian manifold `(M, g)` and a fixed contravariant
valence `r` there is a rank-raising operator family
`op p rr : SmoothCcTensor g r rr → SmoothCcTensor g r (rr + 1 + p)` together with a nonnegative per-order,
per-rank envelope `kappa : ℕ → ℕ → ℝ` such that:

* **`leibniz`** — the single-step covariant Leibniz is the exact remainder:
  `∇(op p rr W) = op (p + 1) rr W + (rank-cast) op p (rr + 1) (∇W)` (the input section's derivative `∇W`
  cancels, rank-cast `(rr + 1) + 1 + p = rr + 1 + (p + 1)`);
* **`base_value`** — the order-`0` base value-locally realises the genuine differentiated curvature: its
  fibre value at every `x` equals that of the order-`1` moving-centre pure-Riemann differentiated tower
  `genuinePureRDiffOpRS g r 1 rr W` (the genuine `(∇R) W` trace, `covGrad(R W) − R(∇W)`);
* **`base_linear`** — the order-`0` base is `ℝ`-linear in the section at the fibre-value level;
* **`base_local`** — the order-`0` base is value-local: its fibre value at `x` depends only on `W x`;
* **`envelope`** — the per-order, per-rank section-proportional jet envelope:
  `rfns(op p rr W)(x) ≤ kappa p rr · ∑_{q < p + 1} rfns(∇^q W)(x)`.

The witness is the exact covariant-Leibniz remainder recursion `diffCurvGenuineTowerOpRS g r` off the
genuine order-`1` trace `genuinePureRDiffOpRS g r 1 rr`: `leibniz` is `covGrad_diffCurvGenuineTowerOpRS_eq`
(by `sub_add_cancel`) and `base_value` is `diffCurvGenuineTowerOpRS_zero` (by definitional rank-cast), both
*proved* here; `base_linear` / `base_local` come from the `(∇R)`-endo factorisation children
`genuinePureRDiffOp_orderOne_linear` / `genuinePureRDiffOp_orderOne_local`; `envelope` is the tight-window
jet child `exists_diffCurvGenuineTowerOpRS_envelope`.  Consumers transitively depend on `sorryAx` through
the analytic children.

**Non-vacuity.** A degenerate witness is rejected on any non-flat manifold.  The order-`0` base is pinned
by `base_value` to the genuine `genuinePureRDiffOpRS g r 1 rr W` — the moving-centre differentiated
pure-Riemann trace `(∇R) W`, which carries the genuine curvature derivative and is genuinely non-zero
(`∇R ≠ 0`) for a non-parallel `W`; it cannot be the zero operator.  The envelope `kappa ≡ 0` is rejected:
at `(p, rr) = (0, s + 1)`, `op 0 (s + 1) W = (∇R) W` is genuinely non-zero, forcing
`rfns(op 0 (s + 1) W)(x) > 0` while the RHS `0 · rfns(W)(x) = 0`; the envelope must carry the genuine
differentiated-curvature magnitude. -/
theorem exists_diffCurvGenuineTowerRS (g : SmoothRiemannianMetric I M) (r : ℕ) :
    ∃ (op : ∀ (p rr : ℕ), SmoothCcTensor g r rr → SmoothCcTensor g r (rr + 1 + p))
      (kappa : ℕ → ℕ → ℝ),
      (∀ (p rr : ℕ) (W : SmoothCcTensor g r rr),
        covGrad (I := I) (M := M) g r (rr + 1 + p) (op p rr W) =
          op (p + 1) rr W +
            castRankCc_db g r (by omega : (rr + 1) + 1 + p = rr + 1 + (p + 1))
              (op p (rr + 1) (covGrad (I := I) (M := M) g r rr W))) ∧
      (∀ (rr : ℕ) (W : SmoothCcTensor g r rr) (x : M),
        (op 0 rr W).toSection x =
          (castRankCc_db g r (by omega : rr + 1 = rr + 1 + 0)
              (genuinePureRDiffOpRS (I := I) (M := M) g r 1 rr W)).toSection x) ∧
      (∀ (rr : ℕ) (c₁ c₂ : ℝ) (W₁ W₂ : SmoothCcTensor g r rr) (x : M),
        (op 0 rr (c₁ • W₁ + c₂ • W₂)).toSection x =
          c₁ • (op 0 rr W₁).toSection x + c₂ • (op 0 rr W₂).toSection x) ∧
      (∀ (rr : ℕ) (W₁ W₂ : SmoothCcTensor g r rr) (x : M),
        W₁.toSection x = W₂.toSection x →
          (op 0 rr W₁).toSection x = (op 0 rr W₂).toSection x) ∧
      (∀ p rr, 0 ≤ kappa p rr) ∧
      (∀ (p rr : ℕ) (W : SmoothCcTensor g r rr) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g r (rr + 1 + p) x ((op p rr W).toSection x) ≤
          kappa p rr * ∑ q ∈ Finset.range (p + 1),
            riemannianFiberNormSq (I := I) (M := M) g r (rr + q) x
              ((iteratedCovGrad g r rr q W).toSection x)) := by
  classical
  obtain ⟨kappa, hkappa_nn, hkappa⟩ :=
    exists_diffCurvGenuineTowerOpRS_envelope (I := I) (M := M) g r
  refine ⟨diffCurvGenuineTowerOpRS (I := I) (M := M) g r, kappa, ?_, ?_, ?_, ?_, hkappa_nn, hkappa⟩
  · -- leibniz: the exact covariant-Leibniz remainder of the recursion.
    intro p rr W
    exact covGrad_diffCurvGenuineTowerOpRS_eq (I := I) (M := M) g r p rr W
  · -- base_value: the order-`0` base is the recast genuine `(∇R) W`, by definition.
    intro rr W x
    rw [diffCurvGenuineTowerOpRS_zero (I := I) (M := M) g r rr W]
  · -- base_linear: from the `(∇R)`-endo factorisation linearity child.
    intro rr c₁ c₂ W₁ W₂ x
    rw [diffCurvGenuineTowerOpRS_zero (I := I) (M := M) g r rr (c₁ • W₁ + c₂ • W₂),
      diffCurvGenuineTowerOpRS_zero (I := I) (M := M) g r rr W₁,
      diffCurvGenuineTowerOpRS_zero (I := I) (M := M) g r rr W₂]
    rw [castRankCc_db_addZero_toSection_eq, castRankCc_db_addZero_toSection_eq,
      castRankCc_db_addZero_toSection_eq]
    exact genuinePureRDiffOp_orderOne_linear (I := I) (M := M) g r rr c₁ c₂ W₁ W₂ x
  · -- base_local: from the `(∇R)`-endo factorisation value-locality child.
    intro rr W₁ W₂ x hW
    rw [diffCurvGenuineTowerOpRS_zero (I := I) (M := M) g r rr W₁,
      diffCurvGenuineTowerOpRS_zero (I := I) (M := M) g r rr W₂]
    rw [castRankCc_db_addZero_toSection_eq, castRankCc_db_addZero_toSection_eq]
    exact genuinePureRDiffOp_orderOne_local (I := I) (M := M) g r rr W₁ W₂ x hW

/-- **The order-`p` differentiated `(∇R)·` curvature operator at valence `r`.** The `Classical.choose`
witness of the posited genuine differentiated curvature tower `exists_diffCurvGenuineTowerRS`: acting on a
smooth compactly-supported `(r, rr)`-tensor section `W`, the order-`p` differentiated action of the
genuine full-`(r, rr)`-tensor differentiated curvature `(∇R)`, a smooth compactly-supported
`(r, rr + 1 + p)`-tensor.  Its order-`0` base value-locally realises the genuine differentiated curvature
`(∇R) W`; its single-step covariant Leibniz is the exact remainder.  The valence-`r` mirror of
`diffCurvGenuineDiffOp`. -/
noncomputable def diffCurvGenuineDiffOpRS (g : SmoothRiemannianMetric I M) (r : ℕ) :
    ∀ (p rr : ℕ), SmoothCcTensor g r rr → SmoothCcTensor g r (rr + 1 + p) :=
  (exists_diffCurvGenuineTowerRS (I := I) (M := M) g r).choose

/-- **The exact single-step covariant Leibniz of the differentiated `(∇R)·` tower at valence `r`.** The
covariant gradient `∇(op p rr W)` splits exactly into the higher-order remainder `op (p + 1) rr W` and the
rank-cast lower-order term applied to `∇W` — the `leibniz` clause of the posited genuine differentiated
curvature tower `exists_diffCurvGenuineTowerRS`.  The valence-`r` mirror of
`covGrad_diffCurvGenuineDiffOp_eq`. -/
theorem covGrad_diffCurvGenuineDiffOpRS_eq (g : SmoothRiemannianMetric I M) (r p rr : ℕ)
    (W : SmoothCcTensor g r rr) :
    covGrad (I := I) (M := M) g r (rr + 1 + p)
        (diffCurvGenuineDiffOpRS (I := I) (M := M) g r p rr W) =
      diffCurvGenuineDiffOpRS (I := I) (M := M) g r (p + 1) rr W +
        castRankCc_db g r (by omega : (rr + 1) + 1 + p = rr + 1 + (p + 1))
          (diffCurvGenuineDiffOpRS (I := I) (M := M) g r p (rr + 1)
            (covGrad (I := I) (M := M) g r rr W)) :=
  (exists_diffCurvGenuineTowerRS (I := I) (M := M) g r).choose_spec.choose_spec.1 p rr W

/-! ## The per-order, per-width proportional fibre envelope at valence `r` -/

/-- **The per-order, per-width section-proportional fibre envelope for the differentiated `(∇R)·` tower
at valence `r`, in jet form.** For a closed smooth Riemannian manifold `(M, g)` and a fixed contravariant
valence `r` there is a nonnegative envelope family `kappa : ℕ → ℕ → ℝ` such that for every order `p`,
width `rr`, smooth compactly-supported `(r, rr)`-tensor `W`, and base point `x`,
```
rfns(diffCurvGenuineDiffOpRS g r p rr W)(x) ≤ kappa p rr · ∑_{q < p + 1} rfns(∇^q W)(x).
```
This is the `envelope` clause of the posited genuine differentiated curvature tower
`exists_diffCurvGenuineTowerRS`: the tower's order-`0` base value-locally realises the genuine
differentiated curvature `(∇R) W`, whose iterated curvature coefficient `∇^{≤ p}(∇R)` is a smooth fibre
operator uniformly bounded over the compact `M`.  The valence-`r` mirror of the rank-`0`
`exists_proportional_diffCurvGenuineDiffOp`.  Consumers transitively depend on `sorryAx` through the
single posited node `exists_diffCurvGenuineTowerRS`. -/
theorem exists_proportional_diffCurvGenuineDiffOpRS (g : SmoothRiemannianMetric I M) (r : ℕ) :
    ∃ kappa : ℕ → ℕ → ℝ, (∀ p rr, 0 ≤ kappa p rr) ∧
      ∀ (p rr : ℕ) (W : SmoothCcTensor g r rr) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g r (rr + 1 + p) x
            ((diffCurvGenuineDiffOpRS (I := I) (M := M) g r p rr W).toSection x) ≤
          kappa p rr * ∑ q ∈ Finset.range (p + 1),
            riemannianFiberNormSq (I := I) (M := M) g r (rr + q) x
              ((iteratedCovGrad g r rr q W).toSection x) :=
  ⟨(exists_diffCurvGenuineTowerRS (I := I) (M := M) g r).choose_spec.choose,
    (exists_diffCurvGenuineTowerRS (I := I) (M := M) g r).choose_spec.choose_spec.2.2.2.2.1,
    (exists_diffCurvGenuineTowerRS (I := I) (M := M) g r).choose_spec.choose_spec.2.2.2.2.2⟩

/-! ## The iterated-gradient grid for the differentiated `(∇R)·` tower at valence `r` -/

set_option linter.unusedSectionVars false in
/-- **`rfns` is invariant under a `SmoothCcTensor` rank-cast at valence `r` (HEq form).** -/
private theorem rfns_toSection_heq_congr_raiseRS (g : SmoothRiemannianMetric I M)
    (r : ℕ) {a b : ℕ} (h : a = b) {Y : SmoothCcTensor g r a} {Z : SmoothCcTensor g r b}
    (hYZ : HEq Y Z) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g r a x (Y.toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g r b x (Z.toSection x) := by
  subst h; rw [eq_of_heq hYZ]

set_option linter.unusedSectionVars false in
/-- **Front-commuting one covariant gradient through the iterated gradient (rfns form) at valence `r`.**
The intrinsic squared fibre norm of `∇^m(∇W)` at `x` equals that of `∇^{m+1}W`. -/
private theorem rfns_iteratedCovGrad_covGrad_comm_raiseRS (g : SmoothRiemannianMetric I M)
    (r s m : ℕ) (W : SmoothCcTensor g r s) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g r ((s + 1) + m) x
        ((iteratedCovGrad g r (s + 1) m (covGrad g r s W)).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g r (s + (m + 1)) x
        ((iteratedCovGrad g r s (m + 1) W).toSection x) :=
  rfns_toSection_heq_congr_raiseRS g r (by omega : (s + 1) + m = s + (m + 1))
    (iteratedCovGrad_covGrad_comm_heq' g r s m W) x

set_option linter.unusedSectionVars false in
/-- A `range`-sum shift bookkeeping helper. -/
private lemma sum_range_shift_le_raiseRS (n : ℕ) (f : ℕ → ℝ) (hf : ∀ i, 0 ≤ f i) :
    ∑ i ∈ Finset.range n, f (i + 1) ≤ ∑ i ∈ Finset.range (n + 1), f i := by
  rw [Finset.sum_range_succ' f n]
  exact le_add_of_nonneg_right (hf 0)

/-- **The binomial covariant-Leibniz `rfns` double grid for the differentiated `(∇R)·` tower at valence
`r`.** For every gradient order `j`, differentiation order `p`, base width `rr`, section `W`, and point
`x`, the intrinsic squared fibre norm of `∇^j(op p rr W)` is bounded by the binomial jet grid
```
rfns(∇^j(op p rr W))(x) ≤ 4^j · gridWindowSum kappa p rr j · ∑_{q < p + j + 1} rfns(∇^q W)(x),
```
the valence-`r` rank-raising analogue of `rfns_iteratedCovGrad_grid`, proved by the same binomial
covariant-Leibniz induction on `j` over the tower's exact single-step Leibniz
`covGrad_diffCurvGenuineDiffOpRS_eq` and the per-order jet envelope (supplied as the hypotheses
`kappa`/`hrfns`). The valence-`r` mirror of `rfns_iteratedCovGrad_diffCurvGenuineDiffOp_grid`. -/
private theorem rfns_iteratedCovGrad_diffCurvGenuineDiffOpRS_grid
    (g : SmoothRiemannianMetric I M) (r : ℕ)
    (kappa : ℕ → ℕ → ℝ) (kappa_nonneg : ∀ p rr, 0 ≤ kappa p rr)
    (hrfns : ∀ (p rr : ℕ) (W : SmoothCcTensor g r rr) (x : M),
      riemannianFiberNormSq (I := I) (M := M) g r (rr + 1 + p) x
          ((diffCurvGenuineDiffOpRS (I := I) (M := M) g r p rr W).toSection x) ≤
        kappa p rr * ∑ q ∈ Finset.range (p + 1),
          riemannianFiberNormSq (I := I) (M := M) g r (rr + q) x
            ((iteratedCovGrad g r rr q W).toSection x)) (j : ℕ) :
    ∀ (p rr : ℕ) (W : SmoothCcTensor g r rr) (x : M),
      riemannianFiberNormSq (I := I) (M := M) g r ((rr + 1 + p) + j) x
          ((iteratedCovGrad g r (rr + 1 + p) j
            (diffCurvGenuineDiffOpRS (I := I) (M := M) g r p rr W)).toSection x) ≤
        (4 : ℝ) ^ j * gridWindowSum kappa p rr j *
          ∑ q ∈ Finset.range (p + j + 1),
            riemannianFiberNormSq (I := I) (M := M) g r (rr + q) x
              ((iteratedCovGrad g r rr q W).toSection x) := by
  induction j with
  | zero =>
      intro p rr W x
      have hrhs : (4 : ℝ) ^ 0 * gridWindowSum kappa p rr 0 *
            ∑ q ∈ Finset.range (p + 0 + 1),
              riemannianFiberNormSq (I := I) (M := M) g r (rr + q) x
                ((iteratedCovGrad g r rr q W).toSection x) =
          kappa p rr * ∑ q ∈ Finset.range (p + 1),
              riemannianFiberNormSq (I := I) (M := M) g r (rr + q) x
                ((iteratedCovGrad g r rr q W).toSection x) := by
        rw [pow_zero, one_mul, gridWindowSum_zero, Nat.add_zero]
      rw [iteratedCovGrad_zero, hrhs]
      exact hrfns p rr W x
  | succ j ih =>
      intro p rr W x
      set K : ℝ := gridWindowSum kappa p rr (j + 1) with hK_def
      set Sm : ℝ := ∑ q ∈ Finset.range (p + (j + 1) + 1),
        riemannianFiberNormSq (I := I) (M := M) g r (rr + q) x
          ((iteratedCovGrad g r rr q W).toSection x) with hSm_def
      have hK_nn : 0 ≤ K := gridWindowSum_nonneg kappa_nonneg p rr (j + 1)
      have hSm_nn : 0 ≤ Sm := Finset.sum_nonneg fun q _ =>
        riemannianFiberNormSq_nonneg (I := I) (M := M) g r (rr + q) x _
      have hpow_nn : (0 : ℝ) ≤ (4 : ℝ) ^ j := by positivity
      rw [show riemannianFiberNormSq (I := I) (M := M) g r ((rr + 1 + p) + (j + 1)) x
            ((iteratedCovGrad g r (rr + 1 + p) (j + 1)
              (diffCurvGenuineDiffOpRS (I := I) (M := M) g r p rr W)).toSection x) =
          riemannianFiberNormSq (I := I) (M := M) g r (((rr + 1 + p) + 1) + j) x
            ((iteratedCovGrad g r ((rr + 1 + p) + 1) j
              (covGrad g r (rr + 1 + p)
                (diffCurvGenuineDiffOpRS (I := I) (M := M) g r p rr W))).toSection x) from
        (rfns_iteratedCovGrad_covGrad_comm_raiseRS g r (rr + 1 + p) j
          (diffCurvGenuineDiffOpRS (I := I) (M := M) g r p rr W) x).symm]
      rw [covGrad_diffCurvGenuineDiffOpRS_eq (I := I) (M := M) g r p rr W, iteratedCovGrad_add]
      refine (riemannianFiberNormSq_add_le (I := I) (M := M) g r (((rr + 1 + p) + 1) + j) x
          ((iteratedCovGrad g r ((rr + 1 + p) + 1) j
            (diffCurvGenuineDiffOpRS (I := I) (M := M) g r (p + 1) rr W)).toSection x)
          ((iteratedCovGrad g r ((rr + 1 + p) + 1) j
            (castRankCc_db g r (by omega : (rr + 1) + 1 + p = rr + 1 + (p + 1))
              (diffCurvGenuineDiffOpRS (I := I) (M := M) g r p (rr + 1)
                (covGrad g r rr W)))).toSection x)).trans ?_
      set kA : ℝ := gridWindowSum kappa (p + 1) rr j with hkA_def
      set kB : ℝ := gridWindowSum kappa p (rr + 1) j with hkB_def
      set sA : ℝ := ∑ q ∈ Finset.range ((p + 1) + j + 1),
        riemannianFiberNormSq (I := I) (M := M) g r (rr + q) x
          ((iteratedCovGrad g r rr q W).toSection x) with hsA_def
      set sB : ℝ := ∑ q ∈ Finset.range (p + j + 1),
        riemannianFiberNormSq (I := I) (M := M) g r (rr + (q + 1)) x
          ((iteratedCovGrad g r rr (q + 1) W).toSection x) with hsB_def
      have hA : riemannianFiberNormSq (I := I) (M := M) g r ((rr + 1 + (p + 1)) + j) x
            ((iteratedCovGrad g r (rr + 1 + (p + 1)) j
              (diffCurvGenuineDiffOpRS (I := I) (M := M) g r (p + 1) rr W)).toSection x) ≤
          (4 : ℝ) ^ j * (kA * sA) := by
        refine (ih (p + 1) rr W x).trans_eq ?_
        rw [hkA_def, hsA_def, mul_assoc]
      have hB0 := ih p (rr + 1) (covGrad g r rr W) x
      have hBshift : gridWindowSum kappa p (rr + 1) j *
            ∑ q ∈ Finset.range (p + j + 1),
              riemannianFiberNormSq (I := I) (M := M) g r ((rr + 1) + q) x
                ((iteratedCovGrad g r (rr + 1) q (covGrad g r rr W)).toSection x) =
          kB * sB := by
        rw [hkB_def, hsB_def]
        congr 1
        exact Finset.sum_congr rfl fun q _ =>
          rfns_iteratedCovGrad_covGrad_comm_raiseRS g r rr q W x
      have hB : riemannianFiberNormSq (I := I) (M := M) g r (((rr + 1) + 1 + p) + j) x
            ((iteratedCovGrad g r ((rr + 1) + 1 + p) j
              (diffCurvGenuineDiffOpRS (I := I) (M := M) g r p (rr + 1)
                (covGrad g r rr W))).toSection x) ≤
          (4 : ℝ) ^ j * (kB * sB) := by
        refine hB0.trans_eq ?_
        rw [mul_assoc, ← hBshift]
      have hkA_le : kA ≤ K := by
        rw [hkA_def, hK_def]
        exact gridWindowSum_shift_le kappa_nonneg p rr j 1 0 le_rfl (Nat.zero_le _)
      have hkB_le : kB ≤ K := by
        rw [hkB_def, hK_def]
        exact gridWindowSum_shift_le kappa_nonneg p rr j 0 1 (Nat.zero_le _) le_rfl
      have hsA_le : sA ≤ Sm := by
        rw [hsA_def, hSm_def]
        exact le_of_eq (Finset.sum_congr (by rw [show (p + 1) + j + 1 = p + (j + 1) + 1 from by omega])
          (fun _ _ => rfl))
      have hsB_le : sB ≤ Sm := by
        rw [hsB_def, hSm_def]
        refine le_trans (sum_range_shift_le_raiseRS (p + j + 1)
          (fun q => riemannianFiberNormSq (I := I) (M := M) g r (rr + q) x
            ((iteratedCovGrad g r rr q W).toSection x))
          (fun q => riemannianFiberNormSq_nonneg (I := I) (M := M) g r (rr + q) x _)) ?_
        exact le_of_eq (Finset.sum_congr (by rw [show (p + j + 1) + 1 = p + (j + 1) + 1 from by omega])
          (fun _ _ => rfl))
      have hkA_nn : 0 ≤ kA := gridWindowSum_nonneg kappa_nonneg (p + 1) rr j
      have hkB_nn : 0 ≤ kB := gridWindowSum_nonneg kappa_nonneg p (rr + 1) j
      have hsA_nn : 0 ≤ sA :=
        Finset.sum_nonneg fun q _ => riemannianFiberNormSq_nonneg (I := I) (M := M) g r (rr + q) x _
      have hsB_nn : 0 ≤ sB :=
        Finset.sum_nonneg fun q _ =>
          riemannianFiberNormSq_nonneg (I := I) (M := M) g r (rr + (q + 1)) x _
      have hprodA : kA * sA ≤ K * Sm := mul_le_mul hkA_le hsA_le hsA_nn hK_nn
      have hprodB : kB * sB ≤ K * Sm := mul_le_mul hkB_le hsB_le hsB_nn hK_nn
      have hgoal : (2 : ℝ) * ((4 : ℝ) ^ j * (kA * sA)) +
            (2 : ℝ) * ((4 : ℝ) ^ j * (kB * sB)) ≤
          (4 : ℝ) ^ (j + 1) * (K * Sm) := by
        have h4 : (4 : ℝ) ^ (j + 1) = 4 * (4 : ℝ) ^ j := by rw [pow_succ]; ring
        rw [h4]
        nlinarith [hprodA, hprodB, hpow_nn,
          mul_le_mul_of_nonneg_left hprodA hpow_nn,
          mul_le_mul_of_nonneg_left hprodB hpow_nn]
      have htarget : (4 : ℝ) ^ (j + 1) * (K * Sm) =
          (4 : ℝ) ^ (j + 1) * gridWindowSum kappa p rr (j + 1) *
            ∑ q ∈ Finset.range (p + (j + 1) + 1),
              riemannianFiberNormSq (I := I) (M := M) g r (rr + q) x
                ((iteratedCovGrad g r rr q W).toSection x) := by
        rw [hK_def, hSm_def, mul_assoc]
      rw [htarget] at hgoal
      refine le_trans ?_ hgoal
      have hb_eq : riemannianFiberNormSq (I := I) (M := M) g r (((rr + 1 + p) + 1) + j) x
            ((iteratedCovGrad g r ((rr + 1 + p) + 1) j
              (castRankCc_db g r (by omega : (rr + 1) + 1 + p = rr + 1 + (p + 1))
                (diffCurvGenuineDiffOpRS (I := I) (M := M) g r p (rr + 1)
                  (covGrad g r rr W)))).toSection x) =
          riemannianFiberNormSq (I := I) (M := M) g r (((rr + 1) + 1 + p) + j) x
            ((iteratedCovGrad g r ((rr + 1) + 1 + p) j
              (diffCurvGenuineDiffOpRS (I := I) (M := M) g r p (rr + 1)
                (covGrad g r rr W))).toSection x) :=
        rfns_iteratedCovGrad_castRankCc_db g r (by omega : (rr + 1) + 1 + p = rr + 1 + (p + 1))
          (diffCurvGenuineDiffOpRS (I := I) (M := M) g r p (rr + 1) (covGrad g r rr W)) j x
      rw [hb_eq]
      exact add_le_add (mul_le_mul_of_nonneg_left hA (by norm_num))
        (mul_le_mul_of_nonneg_left hB (by norm_num))

/-! ## The `(∇R) S` carrier section and its graded curvature jet at valence `r` -/

/-- **The frame-free differentiated-curvature `(∇R) S` carrier section at valence `r`.** The order-`0`
base of the differentiated `(∇R)·` tower: the genuine differentiated curvature `(∇R) S` of the smooth
compactly-supported `(r, s)`-tensor `S`, a smooth compactly-supported `(r, s + 1)`-tensor.  The valence-`r`
mirror of `genuineDiffCurvSection`. -/
noncomputable def diffCurvSectionRS (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) : SmoothCcTensor g r (s + 1) :=
  diffCurvGenuineDiffOpRS (I := I) (M := M) g r 0 s S

/-- **The `(∇R) S` carrier is the order-`0` base of the differentiated `(∇R)·` tower.** By definition. -/
theorem diffCurvSectionRS_eq_diffCurvGenuineDiffOpRS_zero (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) :
    diffCurvSectionRS (I := I) (M := M) g r s S =
      diffCurvGenuineDiffOpRS (I := I) (M := M) g r 0 s S := rfl

set_option linter.unusedSectionVars false in
/-- **The differentiated-curvature `(∇R) S` carrier iterated-gradient grid at valence `r`.** For a closed
smooth Riemannian manifold `(M, g)` and a fixed contravariant valence `r` there is a valence/order-
dependent nonnegative constant family `c : ℕ → ℕ → ℝ` such that, at every covariant rank `s`, every
smooth compactly-supported `(r, s)`-tensor `S`, every gradient order `k` and every point `x`, the
`k`-fold iterated covariant gradient of the gauge-glued tensorial differentiated-curvature carrier
`diffCurvSectionRS g r s S` (the `(∇R) S` contraction) is fibre-bounded by the truncated contracted-order
window `0 … k` of the iterated gradients of `S`:
```
rfns(∇^k (diffCurvSectionRS g r s S))(x) ≤ (c s k)² · ∑_{i < 1 + k} rfns(∇^{i + 0} S)(x).
```
This is the contravariant-valence-`r` mirror of the rank-`0`
`genuineDiffCurvSection_gradedCurvJet` (the `(∇R) S` graded jet of lowest order `0` and width `1`), in
the *raw fibre-inequality* form (it does not reference the downstream predicate `IsGradedCurvJetRS`, which
lives in the consumer `OrderSeparatedCurvatureJetRS` that imports this file).

**Proof.** `diffCurvSectionRS g r s S = diffCurvGenuineDiffOpRS g r 0 s S` is the order-`0` base of the
differentiated `(∇R)·` tower. The at-point covariant-Leibniz double grid
`rfns_iteratedCovGrad_diffCurvGenuineDiffOpRS_grid` at differentiation order `p = 0` (whose per-order jet
envelope `exists_proportional_diffCurvGenuineDiffOpRS` comes from the posited genuine differentiated
curvature tower) bounds `∇^k` of that base by `4^k · gridWindowSum kappa 0 s k · ∑_{q < k + 1} rfns(∇^q S)`;
the contracted-order range `q < k + 1 = 1 + k` is the differentiation entering entirely on the curvature
factor, so the section enters at order `0` (width `1`). The constant family is the engine's single-sum
constant `c s k := √(4^k · gridWindowSum kappa 0 s k)`. Consumers transitively depend on `sorryAx`
through the single posited node `exists_diffCurvGenuineTowerRS`. -/
theorem exists_diffCurvSectionRS_iteratedCovGrad_grid_bound (g : SmoothRiemannianMetric I M) (r : ℕ) :
    ∃ c : ℕ → ℕ → ℝ, (∀ s k, 0 ≤ c s k) ∧
      ∀ (s : ℕ) (S : SmoothCcTensor g r s) (k : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g r ((s + 1) + k) x
            ((iteratedCovGrad g r (s + 1) k
              (diffCurvSectionRS (I := I) (M := M) g r s S)).toSection x) ≤
          (c s k) ^ 2 * ∑ i ∈ Finset.range (1 + k),
            riemannianFiberNormSq (I := I) (M := M) g r (s + (i + 0)) x
              ((iteratedCovGrad g r s (i + 0) S).toSection x) := by
  classical
  obtain ⟨kappa, hkappa_nn, hkappa⟩ := exists_proportional_diffCurvGenuineDiffOpRS (I := I) (M := M) g r
  refine ⟨fun s' k => Real.sqrt ((4 : ℝ) ^ k * gridWindowSum kappa 0 s' k),
    fun _ k => Real.sqrt_nonneg _, fun s S k x => ?_⟩
  have hcsq : (Real.sqrt ((4 : ℝ) ^ k * gridWindowSum kappa 0 s k)) ^ 2 =
      (4 : ℝ) ^ k * gridWindowSum kappa 0 s k := by
    rw [Real.sq_sqrt]
    exact mul_nonneg (by positivity) (gridWindowSum_nonneg hkappa_nn 0 s k)
  rw [hcsq]
  -- The at-point grid for the differentiated `(∇R)·` tower, differentiation order `p = 0`, section `S`.
  have hgrid := rfns_iteratedCovGrad_diffCurvGenuineDiffOpRS_grid (I := I) (M := M) g r
    kappa hkappa_nn hkappa k 0 s S x
  -- The order-`0` base is `diffCurvSectionRS g r s S`; the windows collapse to `range (k + 1)`.
  rw [show (diffCurvGenuineDiffOpRS (I := I) (M := M) g r 0 s S) =
      diffCurvSectionRS (I := I) (M := M) g r s S from rfl] at hgrid
  -- Normalize the contracted-order window in `hgrid`: `range (0 + k + 1) = range (k + 1)`.
  rw [Nat.zero_add] at hgrid
  refine le_trans (le_of_eq ?_) (hgrid.trans (le_of_eq ?_))
  · -- LHS rank reassociation `(s + 1 + 0) + k = (s + 1) + k`.
    norm_num
  · -- RHS: re-index the target window `range (1 + k) = range (k + 1)`, `i + 0 = i`.
    have hsum : ∑ i ∈ Finset.range (1 + k),
          riemannianFiberNormSq (I := I) (M := M) g r (s + (i + 0)) x
            ((iteratedCovGrad g r s (i + 0) S).toSection x) =
        ∑ q ∈ Finset.range (k + 1),
          riemannianFiberNormSq (I := I) (M := M) g r (s + q) x
            ((iteratedCovGrad g r s q S).toSection x) := by
      rw [Nat.add_comm 1 k]
      refine Finset.sum_congr rfl (fun q _ => ?_)
      rw [Nat.add_zero]
    rw [hsum, mul_assoc]

end Connection
end Integral
end DifferentialGeometry

end
