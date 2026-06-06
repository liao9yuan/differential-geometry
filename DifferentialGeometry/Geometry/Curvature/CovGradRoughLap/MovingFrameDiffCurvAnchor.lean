import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.FrozenFramePureRCurvatureTower
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.MovingFrameRemainderDivergenceForm
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.MovingFrameDiffCurvTraceSection
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.MovingFrameIntegratedNullity

/-!
# The coupled differentiated-curvature section `(∇R) S` with its order-`2` remainder and integrated
nullity

For a closed (compact, boundaryless) smooth Riemannian manifold `(M, g)` this file isolates the single
genuinely-irreducible coupled moving-frame curvature-endomorphism content of the rank-generic order-`2`
rough-Laplacian / covariant-gradient commutator defect

```
Curv S := Δ_∇(∇S) − ∇(Δ_∇ S)
```

(`pointwiseTensorCurv g s S`, a `(0, s + 1)`-tensor field; `∇S = covGrad g 0 s S`), over the concrete
pure-Riemann genuine section `Gcurv := GcurvSection g s S` (`MovingFrameCurvatureTraceSmooth`, the
slot-`0` assembly of the *tensorial* trace `∑ᵢ R(Bᵢ, ·)(∇_{Bᵢ} S)`, whose frame-free curvature-jet grid
is already discharged by `exists_GcurvSection_iteratedCovGrad_grid_bound`,
`FrozenFramePureRCurvatureTower`).

## The deepest atom: the genuine `(∇R) S` field with its integrated nullity

The genuine third-order Weitzenböck field split
`pointwiseTensorCurv_toSection_eq_genuine_add_bracket_field`
(`Geometry/Curvature/Bochner/PointwiseTensorBochnerFieldSplit`) reads, in the slot-`0` witness frame,
`Curv` as the sum of the genuine third-order curvature field `genuineThirdCurvFieldFib` and the bracket
field `bracketThirdCurvFieldFib`; the genuine field itself splits
(`genuineThirdCurvFieldFib_eq_pureR_add_covDeriv`) into the pure-Riemann part
`genuineThirdCurvFieldFibPureR` (the tensorial `R(∇S)` trace, frame-free, reconstructing the concrete
`GcurvSection`) and the differentiated-curvature part `genuineThirdCurvFieldFibCovDeriv` (the
`(∇R) S = ∑ᵢ ∇_{Bᵢ}(R(Bᵢ, ·) S)` trace). The differentiated-curvature trace is **non-tensorial** in the
direction — its on-disk fibre realisation `genuineThirdCurvFieldFibCovDeriv` reads the
`smoothExtensionTangent` jet of the frame direction, so it is frame- and chart-selection-dependent, has
**no** clean slot-`0` uncurry (a per-direction packaging is the unsound object documented at
`Order2Defect/SlotSplitBound`). The smooth moving-centre `(0, s + 1)`-tensor `Gcd` that carries the
`(∇R) S` content must therefore be assembled *tensorially* and *existentially* — never extension-curried
— and the precise normalisation that makes the companion remainder `Curv − Gcurv − Gcd` genuinely
**second-order** is the one for which the subtraction leaves exactly the bracket field plus a frame-summed
total covariant divergence (the `∇³S` top-order terms cancelled by the iterated Ricci identity
`secondCovDeriv_covGrad_antisymm_eq_riemannOp_gen`, `IntegratedOrder2WeitzenbockCurvature`).

This coupling — the existential tensorial section `Gcd`, its `rfns(∇S) + rfns(S)`-order (sum) fibre
bound, the companion remainder's `rfns(∇²S)`-sum fibre bound, **and** the **integrated moving-frame
nullity** `⟨Grem, ∇S⟩_{L²} = 0` — cannot be factored into independent standalone lemmas: the nullity is
a property of *the specific* `Gcd` (the frame-summed bracket field is a total covariant divergence
against `∇S` only for the genuine curvature fields, *false* term-by-term through `smoothExtensionTangent`
and *false* for an arbitrary bounded field; only its *integral* vanishes — the pointwise pairing carries
genuine non-divergence content). It is therefore the single irreducible coupled differentiated-curvature
node, isolated here, and is the covariant-derivative analogue of the on-disk pure-Riemann `GcurvSection`:
where the pure-Riemann trace is tensorial and hence concretely constructible, the differentiated-curvature
trace is non-tensorial and hence carried as this coupled existential. Its shape mirrors the order-`m`
sibling `exists_pointwiseTensorCurv_diffCurvAndRemainder_gradedCurvJet` (`OrderSeparatedCurvatureJet`,
the graded-in-`k` version) at gradient order `k = 0`, and matches the *sound integrated form* of the
sibling tri-split node `exists_pointwiseTensorCurv_genuineTriSplit_divergence`
(`MovingFrameGenuineSectionOrderDivergence`).

## Main result

* `exists_movingCentreDiffCurvSection_divergenceDatum` — the coupled differentiated-curvature primitive:
  a *valence-dependent* nonnegative constant `K : ℕ → ℝ` and, at every rank `s` and smooth
  compactly-supported `(0, s)`-tensor `S`, a smooth compactly-supported `(0, s + 1)`-tensor `Gcd` for
  which the **sum** fibre bound on `Gcd`, the **sum** fibre bound on the companion remainder
  `Curv − Gcurv − Gcd`, and the **integrated moving-frame nullity** `⟨Curv − Gcurv − Gcd, ∇S⟩_{L²} = 0`
  all hold. It is proved from the explicit-remainder split form
  `exists_movingCentreDiffCurvSection_splitDivergenceDatum`, and feeds the integrated nullity `(2)` of
  `exists_movingCentreDiffCurvSection_fiberNormSq_bound`
  (`MovingFrameDifferentiatedCurvatureSection`) directly — the integrated form transports verbatim, no
  divergence-theorem step. (An earlier *pointwise* divergence-current form of this atom was over-strong:
  producing a tangent field `X` with `⟨Grem, ∇S⟩ =ᵐ divᵍ X` requires a Poisson / Hodge solve absent in
  the library, and the moving-frame remainder's pointwise pairing is genuinely *not* a total covariant
  divergence; only its integral vanishes. The integrated nullity is the honest primitive.)
-/

noncomputable section

set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1600000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.PDE.RicciFlow

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

/-- **Posited deepest coupled moving-frame differentiated-curvature atom: the explicit named-remainder
split of the order-`2` commutator defect with its integrated moving-frame nullity.** This is the
canonical (more-informative) primitive form of `exists_movingCentreDiffCurvSection_divergenceDatum`: it
surfaces the moving-frame remainder as an *explicit named field* `Grem` together with the section split
`Curv S = GcurvSection g s S + Gcd + Grem` (rather than hiding it as the literal subtraction
`Curv S − GcurvSection − Gcd`). For a closed smooth Riemannian manifold `(M, g)` there is a
*valence-dependent* nonnegative constant `K : ℕ → ℝ` such that, at every covariant rank `s` and for
every smooth compactly-supported `(0, s)`-tensor `S`, there are smooth compactly-supported
`(0, s + 1)`-tensors `Gcd` — the **tensorial, existentially-carried** (never extension-curried)
gauge-glued moving-centre section of the differentiated-curvature contraction `∑ᵢ ∇_{Bᵢ}(R(Bᵢ, ·) S)`
(the `(∇R) S` field) — and `Grem` — the moving-frame / frame-bracket remainder — for which, writing
`Curv := pointwiseTensorCurv g s S`, `Gcurv := GcurvSection g s S`, `∇S := covGrad g 0 s S` and
`∇²S := covGrad g 0 (s + 1) (covGrad g 0 s S)`, the **four coupled facts** hold:
* the **section split** `Curv = Gcurv + Gcd + Grem`;
* `(3')` the **sum** fibre bound on the constructed section
  `rfns(Gcd)(x) ≤ (K s)² · ( rfns(∇S)(x) + rfns(S)(x) )`;
* `(4')` the **sum** fibre bound on the explicit remainder
  `rfns(Grem)(x) ≤ (K s)² · ( rfns(∇²S)(x) + rfns(∇S)(x) + rfns(S)(x) )`; and
* `(2)` the **integrated moving-frame nullity** of that explicit remainder: the global metric `L²`
  pairing of `Grem` against `∇S` vanishes, `⟨Grem, ∇S⟩_{L²} = 0`.

**Why the integrated nullity is the true primitive (the pointwise-current upgrade was over-strong).**
An earlier form of this atom carried a *pointwise* divergence current `X` with
`⟨Grem, ∇S⟩ =ᵐ divᵍ X`. That pointwise form is over-strong: producing such an `X` requires solving
`⟨Grem, ∇S⟩ − c = divᵍ X` (a Poisson / Hodge solve onto the mean-zero subspace), absent in the library,
and the moving-frame remainder's pointwise pairing is genuinely *not* a total covariant divergence — by
the pointwise Bochner divergence identity `divergence_dirichletVFGen_eq`
(`TensorConnLapGreenDivergenceIdentityAnySection`) it carries the pointwise-nonzero non-divergence
content `‖∇²S‖² − ⟨Δ_∇²(∇S), S⟩`, so only its *integral* vanishes. The sole consumer chain
(`exists_movingCentreDiffCurvSection_divergenceDatum` → `exists_movingCentreDiffCurvSection_fiberNormSq_bound`
→ `exists_pointwiseTensorCurv_genuineTriSplit_divergence`) reduces the pointwise datum to its integrated
half immediately, so the integrated nullity `⟨Grem, ∇S⟩_{L²} = 0` is the honest primitive — exactly the
*sound integrated form* the sibling tri-split node
`exists_pointwiseTensorCurv_genuineTriSplit_divergence` (`MovingFrameGenuineSectionOrderDivergence`)
already carries.

**Why this is TRUE — the gauge-glued tensorial `(∇R) S` section and its integrated nullity.** The genuine
third-order Weitzenböck field split `pointwiseTensorCurv_toSection_eq_genuine_add_bracket_field`
(`PointwiseTensorBochnerFieldSplit`) reads `Curv` (in the slot-`0` witness frame) as
`genuineThirdCurvFieldFib + bracketThirdCurvFieldFib`; the genuine field splits
(`genuineThirdCurvFieldFib_eq_pureR_add_covDeriv`) into the pure-Riemann `R(∇S)` trace (the concrete
`Gcurv = GcurvSection`, frame-free) and the differentiated-curvature `(∇R) S` trace
`genuineThirdCurvFieldFibCovDeriv`. The latter is non-tensorial (its on-disk fibre realisation reads the
`smoothExtensionTangent` jet, frame-dependent) and so has no clean slot-`0` uncurry; the smooth section
`Gcd` carrying its content is assembled *tensorially* from the frame-traced curvature-contraction
building block `covGradCurvatureContraction` (`Analysis/.../UniformCurvatureSup`, the smooth
`∇(R(X, Y) Z)` for fixed smooth tangent fields `X, Y`) summed over a frozen orthonormal frame and
partition-of-unity-glued across a finite chart cover (the frozen-frame fibre value agreeing on overlaps
because the contraction reads only the *values* of the frame, exactly as for the pure-Riemann section
`GcurvSection_toSection_eventuallyEq_fixedFramePureRSection`, `MovingFrameCurvatureTraceSmooth`).
`Grem := Curv − Gcurv − Gcd` is the surviving moving-frame / frame-bracket remainder (the explicit
`bracketThirdCurvFieldFib` of the field split). `(3')` is the frame-summed `∇R` sup
(`exists_uniform_riemannianFiberNormSq_covGrad_riemannOp_bound`), the **sum** envelope absorbing the
Leibniz defect between this gauge-glued tensorial section and the genuine non-tensorial `(∇R) S` trace
(the strict `rfns(S)` bound is *unachievable* — the genuine trace's extension jet is non-tensorial, so
the defect cannot be made to vanish). `(4')` is the explicit remainder's fibre order: its unit fibre
value is the bracket field, `rfns(∇²S)`-order in its leading term after the iterated Ricci identity
`secondCovDeriv_covGrad_antisymm_eq_riemannOp_gen` (`IntegratedOrder2WeitzenbockCurvature`) cancels the
top-order `∇³S` terms, the lower terms in the **sum**. `(2)` is the frame-summed covariant
integration by parts: the moving-frame remainder, paired against `∇S` and summed over the
`g_x`-orthonormal frame `Bᵢ := smoothOrthoFrame g x i`, telescopes into a total covariant divergence
(`integral_tensorInner_tangentAction_add_smul_divergence_eq_zero`, `CovariantIntegrationByParts`) of an
honest smooth `∇S`-order tangent field whose integral over the closed manifold vanishes
(`integral_divergence_eq_zero_of_hasCompactSupport`) — the gauge-glued `Gcd`'s defect is itself a total
covariant divergence against `∇S`. The `∇³S`-cancellation and the divergence form are *false
term-by-term* through `smoothExtensionTangent`; only the tensorial frame-summed remainder is `∇²S`-order
and a total divergence — the irreducible coupled moving-frame content.

**Non-vacuity (the coupling rejects `Gcd = Grem = 0`).** The bound `(3')` alone does not reject the zero
witness, but the COUPLING does. With `Gcd = 0`, the split forces `Grem = Curv − Gcurv`, so `(2)` reads
`⟨Curv − Gcurv, ∇S⟩_{L²} = 0`, i.e. `⟨Curv, ∇S⟩_{L²} = ⟨Gcurv, ∇S⟩_{L²}`; but the genuine Weitzenböck
value `⟨Curv, ∇S⟩_{L²} = ‖Δ_∇S‖²_{L²} − ‖∇²S‖²_{L²}` (`weitzenbock_integrated_covGrad_l2_normSq`) is
*not* carried by the pure-Riemann pairing `⟨Gcurv, ∇S⟩_{L²}` alone on a non-flat manifold (the
differentiated-curvature `(∇R) S` content is genuinely missing), a contradiction; and `(4')` with
`Grem = Curv − Gcurv` would read `rfns(Curv − Gcurv) ≤ (K s)² · (rfns(∇²S) + rfns(∇S) + rfns(S))`,
*false* since the `(∇R) S` content is genuinely `rfns(S)`-order and would not be carried. So the
existential `Gcd` and the remainder `Grem` must carry the actual third-order Weitzenböck content; the
constant family is genuinely positive.

This is the rank-`0` analogue of the on-disk general-rank deepest moving-frame atom
`exists_pointwiseTensorCurvRS_genuineTriSplit_divergence` (`MovingFrameGenuineFieldPairingRS`, posited
`sorry`) and the order-`m`/`k = 0` specialisation of the graded sibling
`exists_pointwiseTensorCurv_diffCurvAndRemainder_gradedCurvJet` (`OrderSeparatedCurvatureJet`,
downstream, posited `sorry`); `exists_movingCentreDiffCurvSection_divergenceDatum` (the
literal-subtraction consumer form) reads off by collapsing `Grem` to `Curv − Gcurv − Gcd`.

**Proof (composition glue over the gauge-glued section, two upstream posits).** The gauge-glued
tensorial differentiated-curvature section is the *concrete* `Gcd := genuineDiffCurvSection g s S`
(`MovingFrameDiffCurvTraceSection`, the operator-field action of `covGrad (Φ₀ s)` on `S`), and
`Grem := Curv − Gcurv − Gcd` is the literal moving-frame remainder (the section split
`Curv = Gcurv + Gcd + Grem` then holds by `abel`). The `(3')` Gcd fibre bound is
`exists_genuineDiffCurvSection_fiberNormSq_bound` verbatim. The `(4')` remainder fibre bound is the
two-step fibre subadditivity triangle `riemannianFiberNormSq_sub_le` over the three pieces — the
order-`2` commutator-defect fibre order `exists_pointwiseTensorCurv_fiberNormSq_bound_upstream`
(posited curvature input), the pure-Riemann section grid bound
`exists_GcurvSection_iteratedCovGrad_grid_bound` at gradient order `k = 0` (whose contracted range
collapses to `rfns(∇S)`), and `(3')` — with the constants merged into a single
`K s := √((Kgcd s)² + 4(Ccurv s)² + 4(cg s 0)² + 2(Kgcd s)²)`. The `(2)` integrated moving-frame
nullity is `movingFrameNullity_of_genuineCrossPairingValue` (`MovingFrameIntegratedNullity`) fed its
hypothesis by the genuine differentiated-curvature cross-pairing value
`genuineDiffCurv_crossPairing_value` (`MovingFrameDiffCurvTraceSection`, the posited third-order
Weitzenböck IBP-telescoping content) with `Gcd := genuineDiffCurvSection g s S`. The body is thus
*proved by composition*, transiting only the two upstream posited leaves
(`exists_pointwiseTensorCurv_fiberNormSq_bound_upstream` and `genuineDiffCurv_crossPairing_value`);
consumers transitively depend on their `sorryAx`. -/
theorem exists_movingCentreDiffCurvSection_splitDivergenceDatum
    (g : SmoothRiemannianMetric I M) :
    ∃ K : ℕ → ℝ, (∀ s, 0 ≤ K s) ∧
      ∀ (s : ℕ) (S : SmoothCcTensor g 0 s),
        ∃ Gcd Grem : SmoothCcTensor g 0 (s + 1),
          pointwiseTensorCurv (I := I) (M := M) g s S =
              GcurvSection (I := I) (M := M) g s S + Gcd + Grem ∧
          (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x (Gcd.toSection x) ≤
            K s ^ 2 *
              (riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
                  ((covGrad (I := I) (M := M) g 0 s S).toSection x) +
                riemannianFiberNormSq (I := I) (M := M) g 0 s x (S.toSection x))) ∧
          (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x (Grem.toSection x) ≤
            K s ^ 2 *
              (riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1 + 1) x
                  ((covGrad (I := I) (M := M) g 0 (s + 1)
                    (covGrad (I := I) (M := M) g 0 s S)).toSection x) +
                riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
                    ((covGrad (I := I) (M := M) g 0 s S).toSection x) +
                riemannianFiberNormSq (I := I) (M := M) g 0 s x (S.toSection x))) ∧
          tensorL2Inner (I := I) (M := M) g 0 (s + 1) Grem.toFun
              (covGrad (I := I) (M := M) g 0 s S).toFun = 0 := by
  classical
  obtain ⟨Kgcd, hKgcd_nn, hKgcd⟩ :=
    exists_genuineDiffCurvSection_fiberNormSq_bound (I := I) (M := M) g
  obtain ⟨Ccurv, hCcurv_nn, hCcurv⟩ :=
    exists_pointwiseTensorCurv_fiberNormSq_bound_upstream (I := I) (M := M) g
  obtain ⟨cg, hcg_nn, hcg⟩ :=
    exists_GcurvSection_iteratedCovGrad_grid_bound (I := I) (M := M) g
  refine ⟨fun s => Real.sqrt ((Kgcd s) ^ 2 + 4 * (Ccurv s) ^ 2 + 4 * (cg s 0) ^ 2
      + 2 * (Kgcd s) ^ 2), fun s => Real.sqrt_nonneg _, fun s S => ?_⟩
  set Curv : SmoothCcTensor g 0 (s + 1) := pointwiseTensorCurv (I := I) (M := M) g s S with hCurv
  set Gcurv : SmoothCcTensor g 0 (s + 1) := GcurvSection (I := I) (M := M) g s S with hGcurv
  set Gcd : SmoothCcTensor g 0 (s + 1) := genuineDiffCurvSection (I := I) (M := M) g s S with hGcd
  refine ⟨Gcd, Curv - Gcurv - Gcd, ?_, ?_, ?_, ?_⟩
  · abel
  · intro x
    have hKsq : Real.sqrt ((Kgcd s) ^ 2 + 4 * (Ccurv s) ^ 2 + 4 * (cg s 0) ^ 2
        + 2 * (Kgcd s) ^ 2) ^ 2 =
        (Kgcd s) ^ 2 + 4 * (Ccurv s) ^ 2 + 4 * (cg s 0) ^ 2 + 2 * (Kgcd s) ^ 2 := by
      rw [Real.sq_sqrt]; positivity
    rw [hKsq]
    have h3 := hKgcd s S x
    have hfgS_nn : 0 ≤ riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
        ((covGrad (I := I) (M := M) g 0 s S).toSection x) :=
      riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 (s + 1) x _
    have hfS_nn : 0 ≤ riemannianFiberNormSq (I := I) (M := M) g 0 s x (S.toSection x) :=
      riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 s x _
    nlinarith [h3, hfgS_nn, hfS_nn, sq_nonneg (Ccurv s), sq_nonneg (cg s 0), sq_nonneg (Kgcd s),
      mul_nonneg (add_nonneg hfgS_nn hfS_nn) (sq_nonneg (Ccurv s)),
      mul_nonneg (add_nonneg hfgS_nn hfS_nn) (sq_nonneg (cg s 0)),
      mul_nonneg (add_nonneg hfgS_nn hfS_nn) (sq_nonneg (Kgcd s))]
  · intro x
    have hKsq : Real.sqrt ((Kgcd s) ^ 2 + 4 * (Ccurv s) ^ 2 + 4 * (cg s 0) ^ 2
        + 2 * (Kgcd s) ^ 2) ^ 2 =
        (Kgcd s) ^ 2 + 4 * (Ccurv s) ^ 2 + 4 * (cg s 0) ^ 2 + 2 * (Kgcd s) ^ 2 := by
      rw [Real.sq_sqrt]; positivity
    rw [hKsq]
    simp only [SmoothCcTensor.toSection_sub, ContMDiffSection.coe_sub, Pi.sub_apply]
    set fS : ℝ := riemannianFiberNormSq (I := I) (M := M) g 0 s x (S.toSection x) with hfS
    set fgS : ℝ := riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
        ((covGrad (I := I) (M := M) g 0 s S).toSection x) with hfgS
    set fg2S : ℝ := riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1 + 1) x
        ((covGrad (I := I) (M := M) g 0 (s + 1) (covGrad (I := I) (M := M) g 0 s S)).toSection x)
      with hfg2S
    have hfS_nn : 0 ≤ fS := riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 s x _
    have hfgS_nn : 0 ≤ fgS := riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 (s + 1) x _
    have hfg2S_nn : 0 ≤ fg2S := riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 (s + 1 + 1) x _
    have hsub1 := riemannianFiberNormSq_sub_le (I := I) (M := M) g 0 (s + 1) x
      (Curv.toSection x - Gcurv.toSection x) (Gcd.toSection x)
    have hsub2 := riemannianFiberNormSq_sub_le (I := I) (M := M) g 0 (s + 1) x
      (Curv.toSection x) (Gcurv.toSection x)
    have hCurvB := hCcurv s S x
    rw [← hCurv] at hCurvB
    have hgc0 := hcg s S 0 x
    simp only [iteratedCovGrad_zero, Nat.add_zero, Finset.range_one, Finset.sum_singleton,
      iteratedCovGrad_succ] at hgc0
    rw [← hGcurv] at hgc0
    have hgc : riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x (Gcurv.toSection x) ≤
        cg s 0 ^ 2 * fgS := hgc0
    have hGcdB := hKgcd s S x
    rw [← hGcd] at hGcdB
    nlinarith [hsub1, hsub2, hCurvB, hgc, hGcdB, hfS_nn, hfgS_nn, hfg2S_nn,
      sq_nonneg (Ccurv s), sq_nonneg (cg s 0), sq_nonneg (Kgcd s),
      riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 (s + 1) x (Curv.toSection x),
      riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 (s + 1) x (Gcurv.toSection x),
      riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 (s + 1) x (Gcd.toSection x),
      riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 (s + 1) x
        (Curv.toSection x - Gcurv.toSection x),
      mul_nonneg hfg2S_nn (sq_nonneg (Ccurv s)), mul_nonneg hfgS_nn (sq_nonneg (cg s 0)),
      mul_nonneg hfgS_nn (sq_nonneg (Kgcd s)), mul_nonneg hfS_nn (sq_nonneg (Kgcd s))]
  · rw [show (Curv - Gcurv - Gcd).toFun = (pointwiseTensorCurv (I := I) (M := M) g s S
        - GcurvSection (I := I) (M := M) g s S -
          genuineDiffCurvSection (I := I) (M := M) g s S).toFun
      from by rw [hCurv, hGcurv, hGcd]]
    exact movingFrameNullity_of_genuineCrossPairingValue (I := I) (M := M) g s S
      (genuineDiffCurvSection (I := I) (M := M) g s S)
      (genuineDiffCurv_crossPairing_value (I := I) (M := M) g s S)

/-- **Coupled differentiated-curvature section `(∇R) S` with its order-`2` remainder fibre bound and
its integrated moving-frame nullity (literal-subtraction consumer form).** For a closed smooth
Riemannian manifold `(M, g)` there is a *valence-dependent* nonnegative constant `K : ℕ → ℝ` such that,
at every covariant rank `s` and for every smooth compactly-supported `(0, s)`-tensor `S`, there is a
smooth compactly-supported `(0, s + 1)`-tensor `Gcd` — the **tensorial, existentially-carried** (never
extension-curried) smooth moving-centre section of the differentiated-curvature contraction
`∑ᵢ ∇_{Bᵢ}(R(Bᵢ, ·) S)` (the `(∇R) S` field) — for which, writing `Curv := pointwiseTensorCurv g s S`,
`Gcurv := GcurvSection g s S` (the concrete pure-Riemann section), `∇S := covGrad g 0 s S` and
`∇²S := covGrad g 0 (s + 1) (covGrad g 0 s S)`, the **three coupled facts** hold:
* `(3')` the **sum** fibre bound on the constructed section
  `rfns(Gcd)(x) ≤ (K s)² · ( rfns(∇S)(x) + rfns(S)(x) )`;
* `(4')` the **sum** fibre bound on the companion moving-frame remainder `Curv − Gcurv − Gcd`,
  `rfns(Curv − Gcurv − Gcd)(x) ≤ (K s)² · ( rfns(∇²S)(x) + rfns(∇S)(x) + rfns(S)(x) )`; and
* `(2)` the **integrated moving-frame nullity** for that same companion remainder: the global metric
  `L²` pairing of `Curv − Gcurv − Gcd` against `∇S` vanishes,
  `⟨Curv − Gcurv − Gcd, ∇S⟩_{L²} = 0`.

This is **proved** from the explicit-remainder split form
`exists_movingCentreDiffCurvSection_splitDivergenceDatum` (which carries the section split
`Curv = Gcurv + Gcd + Grem`, the two sum fibre bounds, and the integrated nullity
`⟨Grem, ∇S⟩_{L²} = 0`): identifying the explicit remainder `Grem` with the literal subtraction
`Curv − Gcurv − Gcd` (from the split, `abel`), the `(4')` fibre bound and the integrated nullity carried
about `Grem` transport verbatim — the integrated nullity transfers directly, no divergence-theorem step
needed (the parent already carries the integrated form). The integrated nullity is the *sound* form:
the moving-frame remainder pairs to zero against `∇S` only *under the integral* — its pointwise pairing
carries the genuine non-divergence content `‖∇²S‖² − ⟨Δ_∇²(∇S), S⟩` (`divergence_dirichletVFGen_eq`),
vanishing only in the integral by the closed-manifold divergence theorem.

**Non-vacuity (the coupling rejects `Gcd = 0`).** The bound `(3')` alone does not reject `Gcd = 0`, but
the COUPLING does. With `Gcd = 0`, `(2)` reads `⟨Curv − Gcurv, ∇S⟩_{L²} = 0`, i.e.
`⟨Curv, ∇S⟩_{L²} = ⟨Gcurv, ∇S⟩_{L²}`; but the genuine Weitzenböck value
`⟨Curv, ∇S⟩_{L²} = ‖Δ_∇S‖²_{L²} − ‖∇²S‖²_{L²}` (`weitzenbock_integrated_covGrad_l2_normSq`) is *not*
carried by the pure-Riemann pairing `⟨Gcurv, ∇S⟩_{L²}` alone on a non-flat manifold (the
differentiated-curvature `(∇R) S` content is genuinely missing), a contradiction; and `(4')` with
`Gcd = 0` would read `rfns(Curv − Gcurv) ≤ (K s)² · (rfns(∇²S) + rfns(∇S) + rfns(S))`, *false* since the
`(∇R) S` content is genuinely `rfns(S)`-order and would not be carried. So the existential `Gcd` must
carry the actual third-order Weitzenböck content; the constant family is genuinely positive. It is the
covariant-derivative analogue of the on-disk pure-Riemann `GcurvSection`, gauge-glued, coupled to its
companion remainder's order bound and integrated nullity; consumers transitively depend on `sorryAx`. -/
theorem exists_movingCentreDiffCurvSection_divergenceDatum
    (g : SmoothRiemannianMetric I M) :
    ∃ K : ℕ → ℝ, (∀ s, 0 ≤ K s) ∧
      ∀ (s : ℕ) (S : SmoothCcTensor g 0 s),
        ∃ Gcd : SmoothCcTensor g 0 (s + 1),
          (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x (Gcd.toSection x) ≤
            K s ^ 2 *
              (riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
                  ((covGrad (I := I) (M := M) g 0 s S).toSection x) +
                riemannianFiberNormSq (I := I) (M := M) g 0 s x (S.toSection x))) ∧
          (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
              ((pointwiseTensorCurv (I := I) (M := M) g s S -
                  GcurvSection (I := I) (M := M) g s S - Gcd).toSection x) ≤
            K s ^ 2 *
              (riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1 + 1) x
                  ((covGrad (I := I) (M := M) g 0 (s + 1)
                    (covGrad (I := I) (M := M) g 0 s S)).toSection x) +
                riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
                    ((covGrad (I := I) (M := M) g 0 s S).toSection x) +
                riemannianFiberNormSq (I := I) (M := M) g 0 s x (S.toSection x))) ∧
          tensorL2Inner (I := I) (M := M) g 0 (s + 1)
              (pointwiseTensorCurv (I := I) (M := M) g s S -
                GcurvSection (I := I) (M := M) g s S - Gcd).toFun
              (covGrad (I := I) (M := M) g 0 s S).toFun = 0 := by
  obtain ⟨K, hK_nn, h⟩ :=
    exists_movingCentreDiffCurvSection_splitDivergenceDatum (I := I) (M := M) g
  refine ⟨K, hK_nn, fun s S => ?_⟩
  obtain ⟨Gcd, Grem, hsplit, hGcd, hGrem, hnull⟩ := h s S
  -- The genuine moving-frame remainder of the explicit split is the literal subtraction
  -- `Curv − GcurvSection − Gcd`: from `Curv = GcurvSection + Gcd + Grem`, `abel` gives
  -- `Grem = Curv − GcurvSection − Gcd`, so the `(4')` fibre bound and the integrated nullity carried
  -- about `Grem` transport verbatim to the literal-subtraction remainder the consumer reads.
  have hGrem_eq : Grem = pointwiseTensorCurv (I := I) (M := M) g s S -
      GcurvSection (I := I) (M := M) g s S - Gcd := by
    rw [hsplit]; abel
  refine ⟨Gcd, hGcd, fun x => ?_, ?_⟩
  · rw [← hGrem_eq]; exact hGrem x
  · rw [← hGrem_eq]; exact hnull

end Connection
end Integral
end DifferentialGeometry

end
