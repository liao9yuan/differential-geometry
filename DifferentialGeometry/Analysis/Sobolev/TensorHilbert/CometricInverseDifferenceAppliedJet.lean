import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.CometricInverseDifferenceMultiplier
import DifferentialGeometry.Geometry.Connection.TensorNabla.HomFieldActionIteratedCovGradWindow
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.PointwiseToL2Packaging
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.IteratedCovGradLinear
import DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricRealization.TensorHsRealize

/-! # The cometric inverse-difference applied section and its covariant-gradient jet tower

Building on `CometricInverseDifferenceMultiplier.lean` (which constructs the cometric
inverse-difference fibre endomorphism `gInvDiffFibreEndo g₀ g₁` and proves its order-`0`
Neumann fibre bound `exists_gInvDiffFibreEndo_neumannFibreBound`), this file constructs the
**applied section**

  `gInvDiffAppliedSection g₀ g₁ X := appFullRS g₀ 0 2 2 (gInvDiffFibreEndo g₀ g₁) … X`,

the `(0, 2)`-tensor section obtained by applying the cometric inverse-difference fibre multiplier
to a fixed `(0, 2)`-tensor section `X`, and develops the **covariant-gradient jet bound** of this
applied section — the inverse-Gram analog of the connection-difference jet terminus
`exists_riemannianFiberNormSq_iteratedCovGrad_loweredConnDiff_le_jetSum`
(`CrossCorrectionParallelContraction.lean`).

## The order-`0` family-uniform fibre bound

The pointwise value of the applied section is `(gInvDiffFibreEndo g₀ g₁ x) (X.toSection x)`
(`appFullRS_toSection`), so the order-`0` Neumann fibre bound of the multiplier
(`exists_gInvDiffFibreEndo_neumannFibreBound`, with `Cnorm = 2 · dim M`) immediately gives, under the
realize-tie `g₁ = g₀ + ccTensorBilinSymm g₀ T₁` with the fibre gate `gFibreOpBound … δ` and
`δ < 1/2`, the family-uniform fibre bound

  `rfns(gInvDiffAppliedSection g₀ g₁ X .toSection x) ≤ (Cnorm · δ)² · rfns(X .toSection x)`.

This is the **base case** of the covariant-Leibniz jet tower (the `p = 0` order): the cometric
inverse-difference weight is fibre-small (`≤ Cnorm · δ`) uniformly over the perturbation family.

## Non-vacuity

At `g₁ = g₀` the multiplier vanishes (`gInvDiffRaisedEndo_self`), so the applied section is the zero
section and the order-`0` bound is `0 ≤ 0`; the `δ`-arm genuinely carries the inverse-Gram smallness.
-/

noncomputable section

set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry.Analysis.Sobolev.TensorHilbert

open DifferentialGeometry
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
open DifferentialGeometry.Integral.Connection

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [BoundarylessManifold I M]
      [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

/-! ## The applied section -/

/-- **The cometric inverse-difference applied section.**  The `(0, 2)`-tensor section obtained by
applying the cometric inverse-difference fibre multiplier `gInvDiffFibreEndo g₀ g₁` (an endomorphism
of `(0, 2)`-tensor fibres, `CometricInverseDifferenceMultiplier.lean`) to a fixed `(0, 2)`-tensor
section `X`, through the smooth full Hom-bundle action `appFullRS`.  Its pointwise value is
`(gInvDiffFibreEndo g₀ g₁ x) (X.toSection x)` (`gInvDiffAppliedSection_toSection`). -/
def gInvDiffAppliedSection (g₀ g₁ : SmoothRiemannianMetric I M)
    (X : Integral.L2.SmoothCcTensor g₀ 0 2) : Integral.L2.SmoothCcTensor g₀ 0 2 :=
  appFullRS (I := I) (M := M) g₀ 0 2 2 (fun x => gInvDiffFibreEndo (I := I) g₀ g₁ x)
    (gInvDiffFibreEndo_contMDiff (I := I) g₀ g₁) X

/-- **The pointwise value of the applied section.**  At every point `x`, the applied section reads
the fibre value `(gInvDiffFibreEndo g₀ g₁ x) (X.toSection x)` of the cometric inverse-difference
multiplier on `X`. -/
lemma gInvDiffAppliedSection_toSection (g₀ g₁ : SmoothRiemannianMetric I M)
    (X : Integral.L2.SmoothCcTensor g₀ 0 2) (x : M) :
    (gInvDiffAppliedSection (I := I) g₀ g₁ X).toSection x =
      gInvDiffFibreEndo (I := I) g₀ g₁ x (X.toSection x) := by
  rw [gInvDiffAppliedSection,
    appFullRS_toSection (I := I) (M := M) g₀ 0 2 2 (fun x => gInvDiffFibreEndo (I := I) g₀ g₁ x)
      (gInvDiffFibreEndo_contMDiff (I := I) g₀ g₁) X x]

/-- **Self-vanishing of the applied section at `g₁ = g₀`** (non-vacuity litmus).  When the two
metrics coincide, the cometric inverse-difference multiplier vanishes (`gInvDiffRaisedEndo_self`
through the slot insertion and post-composition), so the applied section is the zero section. -/
lemma gInvDiffAppliedSection_self (g₀ : SmoothRiemannianMetric I M)
    (X : Integral.L2.SmoothCcTensor g₀ 0 2) (x : M) :
    (gInvDiffAppliedSection (I := I) g₀ g₀ X).toSection x = 0 := by
  rw [gInvDiffAppliedSection_toSection]
  rw [gInvDiffFibreEndo_apply]
  -- The slot insertion of the raised representative at `g₁ = g₀` is the zero endomorphism.
  have hslot : gInvDiffSlotEndo (I := I) g₀ g₀ x = 0 := by
    rw [gInvDiffSlotEndo]
    rw [show gInvDiffRaisedEndo (I := I) g₀ g₀ x
          = (0 : ℝ) • gInvDiffRaisedEndo (I := I) g₀ g₀ x from by
      rw [zero_smul]
      ext v; rw [gInvDiffRaisedEndo_self, ContinuousLinearMap.zero_apply]]
    rw [slotInsertEndoFib_smul_left (I := I) (M := M) 2 0 x (0 : ℝ)
      (gInvDiffRaisedEndo (I := I) g₀ g₀ x), zero_smul]
  rw [hslot, ContinuousLinearMap.zero_comp]
  rfl

/-! ## The order-`0` family-uniform fibre bound (the base case of the jet tower) -/

set_option linter.unusedSectionVars false in
/-- **The order-`0` family-uniform `g₀`-fibre bound of the cometric inverse-difference applied
section.**  For a closed Riemannian manifold `(M, g₀)` there is a single nonnegative constant
`Cnorm = 2 · dim M` such that, under the realize-tie `g₁ = g₀ + ccTensorBilinSymm g₀ T₁` with the
fibre gate `gFibreOpBound g₀ (ccTensorBilinSymm g₀ T₁) δ` and `δ < 1/2`, for every fixed `(0, 2)`
section `X`, every point `x`,

  `rfns(gInvDiffAppliedSection g₀ g₁ X .toSection x) ≤ (Cnorm · δ)² · rfns(X .toSection x)`.

This is the **base case** (order `0`) of the covariant-Leibniz jet tower: the pointwise value of the
applied section is the cometric multiplier on `X` (`gInvDiffAppliedSection_toSection`), and the
multiplier's order-`0` Neumann fibre bound (`exists_gInvDiffFibreEndo_neumannFibreBound`) supplies the
`(Cnorm · δ)²` factor uniformly over the perturbation family.

**Non-vacuity.**  At `g₁ = g₀` (`T₁ = 0` realized, `δ = 0`) the applied section vanishes
(`gInvDiffAppliedSection_self`), so the bound is `0 ≤ 0`. -/
theorem exists_gInvDiffAppliedSection_order0_fibreBound
    (g₀ : SmoothRiemannianMetric I M) :
    ∃ Cnorm : ℝ, 0 ≤ Cnorm ∧
      ∀ (g₁ : SmoothRiemannianMetric I M)
        (T₁ : Integral.L2.SmoothCcTensor g₀ 0 2),
        (∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm g₀ T₁ y v w) →
        ∀ {δ : ℝ}, δ < 1 / 2 → 0 ≤ δ →
        gFibreOpBound g₀ (fun y => ccTensorBilinSymm g₀ T₁ y) δ →
        ∀ (X : Integral.L2.SmoothCcTensor g₀ 0 2) (x : M),
          riemannianFiberNormSq g₀ 0 2 x
              ((gInvDiffAppliedSection (I := I) g₀ g₁ X).toSection x) ≤
            (Cnorm * δ) ^ 2 *
              riemannianFiberNormSq g₀ 0 2 x (X.toSection x) := by
  obtain ⟨Cnorm, hCnorm0, hbound⟩ := exists_gInvDiffFibreEndo_neumannFibreBound (I := I) g₀
  refine ⟨Cnorm, hCnorm0, ?_⟩
  intro g₁ T₁ htie δ hδ_half hδ_nn hδ X x
  rw [gInvDiffAppliedSection_toSection]
  exact hbound g₁ (fun y => ccTensorBilinSymm g₀ T₁ y) htie hδ_half hδ_nn hδ x
    (X.toSection x)

/-! ## The cometric inverse-difference Hom-bundle field and the all-order jet window bound -/

/-- **The cometric inverse-difference Hom-bundle field.**  The smooth full Hom-bundle field section
packaging the cometric inverse-difference fibre multiplier `gInvDiffFibreEndo g₀ g₁` (a fibre
endomorphism of `(0, 2)`-tensors) together with its smoothness witness `gInvDiffFibreEndo_contMDiff`.
This is the `HomTensorRSField`-section form of the multiplier, the coefficient feeding the all-order
covariant-Leibniz jet window engine `appFullSec`. -/
def gInvDiffHomField (g₀ g₁ : SmoothRiemannianMetric I M) :
    HomTensorRSField (E := E) (M := M) 0 2 2 I :=
  ContMDiffSection.mk (fun x => gInvDiffFibreEndo (I := I) g₀ g₁ x)
    (gInvDiffFibreEndo_contMDiff (I := I) g₀ g₁)

/-- **The applied section is the Hom-field action of the cometric inverse-difference field.**  The
`appFullRS`-defined applied section coincides with the `appFullSec` action of the packaged Hom-bundle
field `gInvDiffHomField g₀ g₁`, since `appFullSec Q W = appFullRS (⇑Q) Q.contMDiff W` and the field /
smoothness witness of `gInvDiffHomField` are exactly those of `gInvDiffAppliedSection`. -/
lemma gInvDiffAppliedSection_eq_appFullSec (g₀ g₁ : SmoothRiemannianMetric I M)
    (X : Integral.L2.SmoothCcTensor g₀ 0 2) :
    gInvDiffAppliedSection (I := I) g₀ g₁ X =
      appFullSec (I := I) (M := M) g₀ 0 2 2 (gInvDiffHomField (I := I) g₀ g₁) X :=
  rfl

set_option linter.unusedSectionVars false in
/-- **The all-order covariant-gradient jet window bound of the cometric inverse-difference applied
section, at a fixed perturbed metric.**  For a closed Riemannian manifold `(M, g₀)` and a fixed second
metric `g₁`, there is a single nonnegative constant family `cc : ℕ → ℝ` such that, for every fixed
`(0, 2)` section `X`, every order `k`, every point `x`, the order-`k` covariant gradient of the
cometric inverse-difference applied section is dominated by the `≤ k`-jet window of `X`:

  `rfns(∇^k (gInvDiffAppliedSection g₀ g₁ X) .toSection x) ≤ cc k · ∑_{i ≤ k} rfns(∇^i X .toSection x)`.

This is the genuine covariant-Leibniz jet grid of the smooth Hom-bundle multiplier: the binomial
covariant Leibniz expansion of `∇^k (A · X)` (`homFieldAction_iteratedCovGrad_expansion`) places the
top derivative on either factor, the iterated covariant jets of the cometric coefficient
`gInvDiffHomField g₀ g₁` entering the base-point-uniform constant family `cc k` (its `C^k`-sup over the
compact manifold) and only the gradient order of `X` surviving as a fibre-norm jet window
(`exists_appFullSec_iteratedCovGrad_window_bound`, applied to the packaged coefficient field).

For the *fixed* coefficient `g₁` this is the complete proved jet tower; the family-uniform refinement —
the constant `cc k` controlled by the `≤ (k+1)`-jet of the realization generator `T₁` uniformly over
the fibre-small perturbation family — layers the Neumann-resolvent covariant-jet control of the
coefficient (`g₁⁻¹ − g₀⁻¹ = −g₁⁻¹(g₁ − g₀)g₀⁻¹`) on top of this window. -/
theorem exists_riemannianFiberNormSq_iteratedCovGrad_gInvDiffAppliedSection_window_le
    (g₀ g₁ : SmoothRiemannianMetric I M) :
    ∃ cc : ℕ → ℝ, (∀ k : ℕ, 0 ≤ cc k) ∧
      ∀ (X : Integral.L2.SmoothCcTensor g₀ 0 2) (k : ℕ) (x : M),
        riemannianFiberNormSq g₀ 0 (2 + k) x
            ((iteratedCovGrad (I := I) g₀ 0 2 k
                (gInvDiffAppliedSection (I := I) g₀ g₁ X)).toSection x) ≤
          cc k * ∑ i ∈ Finset.range (k + 1),
            riemannianFiberNormSq g₀ 0 (2 + i) x
              ((iteratedCovGrad (I := I) g₀ 0 2 i X).toSection x) := by
  obtain ⟨cc, hcc0, hcc⟩ :=
    exists_appFullSec_iteratedCovGrad_window_bound (I := I) (M := M) g₀ 0 2 2
      (gInvDiffHomField (I := I) g₀ g₁)
  refine ⟨cc, hcc0, ?_⟩
  intro X k x
  rw [gInvDiffAppliedSection_eq_appFullSec]
  exact hcc X k x

end DifferentialGeometry.Analysis.Sobolev.TensorHilbert

end
