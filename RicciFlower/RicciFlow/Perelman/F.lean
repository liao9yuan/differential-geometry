/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RicciFlower contributors
-/

import RicciFlower.Analysis.Green
import RicciFlower.LeviCivita.Variation
import RicciFlower.RicciFlow.Perelman.Variation
import RicciFlower.Tensor.RSTensor.MetricTrace

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.longLine false

/-!
# Perelman's `F` functional and formula 5.10 interfaces

This file starts the RicciFlower-native route to MSM135 formula 5.10.  It
contains the concrete measure-theoretic `F` functional, the low-risk
`e^{-f} dmu` variation producer, and explicit predicate handles for the
remaining Ricci/Hessian/divergence steps.
-/

namespace RicciFlower
namespace RicciFlow
namespace Perelman

noncomputable section

open Filter MeasureTheory
open RicciFlower.Analysis.Volume
open RicciFlower.Analysis.VolumeVariation
open RicciFlower.Coordinates
open Tensor0SBundle
open scoped Manifold ContDiff

variable {M : Type*}

/-! ## Concrete `F` functional -/

/-- The density `e^{-f}` used in Perelman's `F` functional. -/
def expNegPotentialDensity (potential : M -> Real) : M -> Real :=
  fun x => Real.exp (-(potential x))

/-- The weighted measure `e^{-f} dmu`. -/
def expNegPotentialWeightedMeasure [MeasurableSpace M] (mu : Measure M)
    (potential : M -> Real) : Measure M :=
  mu.withDensity fun x => ENNReal.ofReal (expNegPotentialDensity potential x)

/-- Rewrite integrals against `e^{-f} dmu` as base-measure integrals with the
explicit density factor.  This is the measure-theoretic bridge used by the
closed Green/IBP identity in Perelman's formula 5.10 route. -/
theorem expNegPotentialWeightedMeasure_integral_eq_base
    [MeasurableSpace M] (mu : Measure M) (potential integrand : M -> Real)
    (hmeas :
      AEMeasurable
        (fun x : M => ENNReal.ofReal (expNegPotentialDensity potential x))
        mu) :
    (∫ x, integrand x ∂(expNegPotentialWeightedMeasure mu potential)) =
      ∫ x, expNegPotentialDensity potential x * integrand x ∂mu := by
  rw [expNegPotentialWeightedMeasure]
  rw [integral_withDensity_eq_integral_toReal_smul₀
    (μ := mu)
    (f := fun x : M => ENNReal.ofReal (expNegPotentialDensity potential x))
    hmeas
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)
    integrand]
  apply integral_congr_ae
  refine Filter.Eventually.of_forall ?_
  intro x
  have hnonneg : 0 ≤ expNegPotentialDensity potential x :=
    le_of_lt (Real.exp_pos _)
  simp [ENNReal.toReal_ofReal hnonneg, smul_eq_mul]

/-- Perelman-facing weighted exponential IBP bridge.  Once Green's identity and
the chain rule prove the base-density identity, this transports it to the
weighted measure `e^{-f}dmu`. -/
theorem expWeightedIBP_of_baseIntegral_zero [MeasurableSpace M]
    (mu : Measure M) (potential lapPotential gradPotentialNormSq : M -> Real)
    (hmeas :
      AEMeasurable
        (fun x : M => ENNReal.ofReal (expNegPotentialDensity potential x))
        mu)
    (hbase :
      ∫ x,
        expNegPotentialDensity potential x *
          (lapPotential x - gradPotentialNormSq x)
        ∂mu = 0) :
    ∫ x, (lapPotential x - gradPotentialNormSq x)
      ∂(expNegPotentialWeightedMeasure mu potential) = 0 := by
  rw [expNegPotentialWeightedMeasure_integral_eq_base
    (mu := mu) (potential := potential)
    (integrand := fun x : M => lapPotential x - gradPotentialNormSq x)
    hmeas]
  exact hbase

/-- The pointwise bracket `R + |grad f|^2` in Perelman's `F`. -/
def fFunctionalBracket (scalarCurvature gradPotentialNormSq : M -> Real) :
    M -> Real :=
  fun x => scalarCurvature x + gradPotentialNormSq x

/-- The alternate closed-manifold bracket `R + Delta f` used in the proof of
formula 5.10. -/
def fFunctionalClosedBracket (scalarCurvature lapPotential : M -> Real) :
    M -> Real :=
  fun x => scalarCurvature x + lapPotential x

/-- Concrete measure-theoretic version of Perelman's `F` functional. -/
def fFunctional [MeasurableSpace M] (mu : Measure M)
    (scalarCurvature gradPotentialNormSq potential : M -> Real) : Real :=
  ∫ x, fFunctionalBracket scalarCurvature gradPotentialNormSq x
    ∂(expNegPotentialWeightedMeasure mu potential)

/-- Unfolding form of the concrete `F` functional. -/
theorem fFunctional_eq_integral [MeasurableSpace M] (mu : Measure M)
    (scalarCurvature gradPotentialNormSq potential : M -> Real) :
    fFunctional mu scalarCurvature gradPotentialNormSq potential =
      ∫ x, fFunctionalBracket scalarCurvature gradPotentialNormSq x
        ∂(expNegPotentialWeightedMeasure mu potential) := rfl

/-- `F` along a one-parameter scalar/measure path. -/
def fFunctionalAlong [MeasurableSpace M] (mu : Real -> Measure M)
    (scalarCurvature gradPotentialNormSq potential : Real -> M -> Real) :
    Real -> Real :=
  fun s => fFunctional (mu s) (scalarCurvature s) (gradPotentialNormSq s)
    (potential s)

/-- `F` has first variation `firstVariation` at `s0` along the supplied path. -/
def FFunctionalHasFirstVariationAt [MeasurableSpace M]
    (mu : Real -> Measure M)
    (scalarCurvature gradPotentialNormSq potential : Real -> M -> Real)
    (s0 firstVariation : Real) : Prop :=
  HasDerivAt (fFunctionalAlong mu scalarCurvature gradPotentialNormSq potential)
    firstVariation s0

/-- The actual first variation of `F` along a path, defined as `deriv`. -/
def fFunctionalFirstVariation [MeasurableSpace M]
    (mu : Real -> Measure M)
    (scalarCurvature gradPotentialNormSq potential : Real -> M -> Real)
    (s0 : Real) : Real :=
  deriv (fFunctionalAlong mu scalarCurvature gradPotentialNormSq potential) s0

theorem fFunctionalFirstVariation_eq_of_hasFirstVariationAt [MeasurableSpace M]
    {mu : Real -> Measure M}
    {scalarCurvature gradPotentialNormSq potential : Real -> M -> Real}
    {s0 firstVariation : Real}
    (h :
      FFunctionalHasFirstVariationAt mu scalarCurvature gradPotentialNormSq
        potential s0 firstVariation) :
    fFunctionalFirstVariation mu scalarCurvature gradPotentialNormSq potential s0 =
      firstVariation := by
  unfold fFunctionalFirstVariation FFunctionalHasFirstVariationAt at *
  exact h.deriv

/-! ## `e^{-f} dmu` variation producer -/

theorem expNegPotentialDensity_hasDerivAt
    {potentialPath : Real -> M -> Real} {s0 : Real}
    {potentialVariation : M -> Real}
    (hpotential_deriv :
      ∀ x : M,
        HasDerivAt (fun s : Real => potentialPath s x)
          (potentialVariation x) s0)
    (x : M) :
    HasDerivAt
      (fun s : Real => expNegPotentialDensity (potentialPath s) x)
      (-(potentialVariation x) *
        expNegPotentialDensity (potentialPath s0) x)
      s0 := by
  have h := (hpotential_deriv x).neg.exp
  simpa [expNegPotentialDensity, mul_comm, mul_left_comm, mul_assoc] using h

/-- The scalar factor in
`delta(e^{-f} dmu) = (V/2 - h) e^{-f} dmu`. -/
def expWeightedMeasureVariationFactor
    (potentialVariation metricVariationTrace : M -> Real) : M -> Real :=
  fun x => metricVariationTrace x / 2 - potentialVariation x

/-- The base-measure integrand produced by differentiating
`e^{-f_s} * phi_s dmu_s`. -/
def expWeightedIntegralVariationIntegrand
    (potential potentialVariation metricVariationTrace phi phiVariation :
      M -> Real) :
    M -> Real :=
  fun x =>
    expNegPotentialDensity potential x *
      (phiVariation x +
        phi x *
          expWeightedMeasureVariationFactor potentialVariation
            metricVariationTrace x)

section Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [InnerProductSpace Real E]
variable [Module.Finite Real E] [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

/-- Perelman-facing weighted identity
`∫ (Delta f - |grad f|^2) e^{-f} dmu_g = 0`, obtained from the closed
Green identity and the pointwise chain rule for `grad(exp(-f))`. -/
theorem weightedIBP
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M)
    {potential : M -> Real}
    (hpotential : ContMDiff I 𝓘(Real, Real) ∞ potential)
    (hmeas :
      AEMeasurable
        (fun x : M => ENNReal.ofReal (expNegPotentialDensity potential x))
        (riemannianVolumeMeasure (I := I) (M := M) g))
    (hlap :
      Integrable (fun x : M =>
        expNegPotentialDensity potential x *
          RicciFlower.Analysis.DivergenceTheorem.Δ_g
            (I := I) g hpotential x)
        (riemannianVolumeMeasure (I := I) (M := M) g))
    (hgrad :
      Integrable (fun x : M =>
        expNegPotentialDensity potential x *
          g.inner x
            ((RicciFlower.Analysis.DivergenceTheorem.grad_g
              (I := I) g hpotential :
              Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
            ((RicciFlower.Analysis.DivergenceTheorem.grad_g
              (I := I) g hpotential :
              Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x))
        (riemannianVolumeMeasure (I := I) (M := M) g)) :
    ∫ x,
      (RicciFlower.Analysis.DivergenceTheorem.Δ_g
          (I := I) g hpotential x -
        g.inner x
          ((RicciFlower.Analysis.DivergenceTheorem.grad_g
            (I := I) g hpotential :
            Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
          ((RicciFlower.Analysis.DivergenceTheorem.grad_g
            (I := I) g hpotential :
            Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x))
      ∂(expNegPotentialWeightedMeasure
          (riemannianVolumeMeasure (I := I) (M := M) g) potential) = 0 := by
  apply expWeightedIBP_of_baseIntegral_zero
    (mu := riemannianVolumeMeasure (I := I) (M := M) g)
    (potential := potential)
    (lapPotential :=
      RicciFlower.Analysis.DivergenceTheorem.Δ_g
        (I := I) g hpotential)
    (gradPotentialNormSq := fun x : M =>
      g.inner x
        ((RicciFlower.Analysis.DivergenceTheorem.grad_g
          (I := I) g hpotential :
          Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
        ((RicciFlower.Analysis.DivergenceTheorem.grad_g
          (I := I) g hpotential :
          Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x))
  · exact hmeas
  · simpa [expNegPotentialDensity] using
      RicciFlower.Analysis.DivergenceTheorem.expNegIBP
        (I := I) g hpotential hlap hgrad

/-- Arbitrary-test weighted Green identity transported to the weighted measure
`e^{-f} dmu_g`. -/
theorem weightedGreen
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M)
    {potential q : M -> Real}
    (hpotential : ContMDiff I 𝓘(Real, Real) ∞ potential)
    (hq : ContMDiff I 𝓘(Real, Real) ∞ q)
    (hmeas :
      AEMeasurable
        (fun x : M => ENNReal.ofReal (expNegPotentialDensity potential x))
        (riemannianVolumeMeasure (I := I) (M := M) g)) :
    ∫ x,
        RicciFlower.Analysis.DivergenceTheorem.Δ_g
          (I := I) g hq x
      ∂(expNegPotentialWeightedMeasure
          (riemannianVolumeMeasure (I := I) (M := M) g) potential) =
      ∫ x,
        q x *
          (-RicciFlower.Analysis.DivergenceTheorem.Δ_g
              (I := I) g hpotential x +
            g.inner x
              ((RicciFlower.Analysis.DivergenceTheorem.grad_g
                (I := I) g hpotential :
                Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
              ((RicciFlower.Analysis.DivergenceTheorem.grad_g
                (I := I) g hpotential :
                Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x))
      ∂(expNegPotentialWeightedMeasure
          (riemannianVolumeMeasure (I := I) (M := M) g) potential) := by
  classical
  let μ := riemannianVolumeMeasure (I := I) (M := M) g
  let gradSq : M -> Real := fun x =>
    g.inner x
      ((RicciFlower.Analysis.DivergenceTheorem.grad_g
        (I := I) g hpotential :
        Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
      ((RicciFlower.Analysis.DivergenceTheorem.grad_g
        (I := I) g hpotential :
        Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
  rw [expNegPotentialWeightedMeasure_integral_eq_base
    (mu := μ) (potential := potential)
    (integrand := fun x : M =>
      RicciFlower.Analysis.DivergenceTheorem.Δ_g (I := I) g hq x)
    hmeas]
  rw [expNegPotentialWeightedMeasure_integral_eq_base
    (mu := μ) (potential := potential)
    (integrand := fun x : M =>
      q x *
        (-RicciFlower.Analysis.DivergenceTheorem.Δ_g
            (I := I) g hpotential x + gradSq x))
    hmeas]
  calc
    ∫ x,
        expNegPotentialDensity potential x *
          RicciFlower.Analysis.DivergenceTheorem.Δ_g (I := I) g hq x ∂μ =
      ∫ x,
        q x *
          (expNegPotentialDensity potential x *
            (-RicciFlower.Analysis.DivergenceTheorem.Δ_g
                (I := I) g hpotential x + gradSq x)) ∂μ := by
      simpa [μ, expNegPotentialDensity, gradSq] using
        RicciFlower.Analysis.DivergenceTheorem.expNegGreen
          (I := I) g hpotential hq
    _ =
      ∫ x,
        expNegPotentialDensity potential x *
          (q x *
            (-RicciFlower.Analysis.DivergenceTheorem.Δ_g
                (I := I) g hpotential x + gradSq x)) ∂μ := by
      apply integral_congr_ae
      refine Filter.Eventually.of_forall ?_
      intro x
      ring

/-- Closed weighted-divergence cancellation.  If a scalar term becomes the
ordinary divergence after multiplying by `e^{-f}`, then its weighted integral
vanishes. -/
theorem weightedDivZero
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M)
    {potential weightedDivergenceTrace : M -> Real}
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (hmeas :
      AEMeasurable
        (fun x : M => ENNReal.ofReal (expNegPotentialDensity potential x))
        (riemannianVolumeMeasure (I := I) (M := M) g))
    (hdiv :
      ∀ x : M,
        RicciFlower.Analysis.DivergenceTheorem.divergence_g
            (I := I) g X x =
          expNegPotentialDensity potential x * weightedDivergenceTrace x) :
    ∫ x, weightedDivergenceTrace x
      ∂(expNegPotentialWeightedMeasure
          (riemannianVolumeMeasure (I := I) (M := M) g) potential) = 0 := by
  classical
  let μ := riemannianVolumeMeasure (I := I) (M := M) g
  rw [expNegPotentialWeightedMeasure_integral_eq_base
    (mu := μ) (potential := potential)
    (integrand := weightedDivergenceTrace) hmeas]
  calc
    ∫ x, expNegPotentialDensity potential x * weightedDivergenceTrace x ∂μ =
        ∫ x, RicciFlower.Analysis.DivergenceTheorem.divergence_g
          (I := I) g X x ∂μ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => (hdiv x).symm
    _ = 0 := by
      simpa [μ] using
        RicciFlower.Analysis.DivergenceTheorem.integral_divergence_eq_zero_of_compact
          (I := I) g X

/-- Smoothness of Perelman's density `e^{-f}`. -/
theorem expNegPotentialDensity_contMDiff
    {potential : M -> Real}
    (hpotential : ContMDiff I 𝓘(Real, Real) ∞ potential) :
    ContMDiff I 𝓘(Real, Real) ∞ (expNegPotentialDensity potential) := by
  simpa [expNegPotentialDensity] using
    Real.contDiff_exp.contMDiff.comp hpotential.neg

/-- Tangent-action chain rule for `e^{-f}`. -/
theorem tangentSectionAction_expNeg
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M -> Type _)⟯)
    {potential : M -> Real}
    (hpotential : ContMDiff I 𝓘(Real, Real) ∞ potential) (x : M) :
    RicciFlower.Analysis.DivergenceTheorem.tangentSectionAction
        (I := I) X (expNegPotentialDensity potential) x =
      -expNegPotentialDensity potential x *
        RicciFlower.Analysis.DivergenceTheorem.tangentSectionAction
          (I := I) X potential x := by
  have hmf :=
    RicciFlower.Analysis.DivergenceTheorem.mfderiv_exp_neg_toLinearMap
      (I := I) (f := potential) (x := x)
      (hpotential.mdifferentiableAt (by simp))
  unfold RicciFlower.Analysis.DivergenceTheorem.tangentSectionAction
    expNegPotentialDensity
  change
    extDerivFun (I := I) (fun y : M => Real.exp (-(potential y))) x (X x) =
      -Real.exp (-(potential x)) *
        extDerivFun (I := I) potential x (X x)
  rw [extDerivFun, extDerivFun]
  simp only [NormedSpace.fromTangentSpace, ContinuousLinearMap.comp_apply]
  have happly := congrArg (fun L => L (X x)) hmf
  simpa [smul_eq_mul] using happly

/-- The global divergence field used to cancel the connection-variation term in
formula 5.10, once the metric trace of the connection variation has already
been constructed as a smooth tangent section.  If `traceVec = tr_g A`, then
this is the book's vector field `X = e^{-f} tr_g A`. -/
def connTraceVec
    {potential : M -> Real}
    (hpotential : ContMDiff I 𝓘(Real, Real) ∞ potential)
    (traceVec : Cₛ^∞⟮I; E, (TangentSpace I : M -> Type _)⟯) :
    Cₛ^∞⟮I; E, (TangentSpace I : M -> Type _)⟯ :=
  RicciFlower.Analysis.DivergenceTheorem.smoothSmul
    (I := I) (expNegPotentialDensity potential)
    (expNegPotentialDensity_contMDiff (I := I) hpotential) traceVec

/-- Divergence of `connTraceVec`.  This is the global smooth-section version of
`div(e^{-f} tr_g A) = e^{-f}(div(tr_g A) - tr_g A(f))`. -/
theorem connTraceDivEq
    [I.Boundaryless] [T2Space M]
    (g : SmoothRiemannianMetric I M)
    {potential weightedDivergenceTrace rawTrace actionTrace : M -> Real}
    (hpotential : ContMDiff I 𝓘(Real, Real) ∞ potential)
    (traceVec : Cₛ^∞⟮I; E, (TangentSpace I : M -> Type _)⟯)
    (hdivTrace :
      ∀ x : M,
        RicciFlower.Analysis.DivergenceTheorem.divergence_g
            (I := I) g traceVec x =
          rawTrace x)
    (hactionTrace :
      ∀ x : M,
        RicciFlower.Analysis.DivergenceTheorem.tangentSectionAction
            (I := I) traceVec potential x =
          actionTrace x)
    (hweighted :
      ∀ x : M,
        weightedDivergenceTrace x = rawTrace x - actionTrace x) :
    ∀ x : M,
      RicciFlower.Analysis.DivergenceTheorem.divergence_g
          (I := I) g
          (connTraceVec (I := I) hpotential traceVec) x =
        expNegPotentialDensity potential x * weightedDivergenceTrace x := by
  intro x
  rw [connTraceVec]
  rw [RicciFlower.Analysis.DivergenceTheorem.divergence_g_smoothSmul
    (I := I) g (expNegPotentialDensity potential)
    (expNegPotentialDensity_contMDiff (I := I) hpotential) traceVec x]
  rw [hdivTrace x]
  rw [tangentSectionAction_expNeg (I := I) traceVec hpotential x]
  rw [hactionTrace x, hweighted x]
  ring

/-- Closed weighted-divergence cancellation when the divergence field is the
actual section `connTraceVec = e^{-f} tr_g A`. -/
theorem weightedDivZero_of_connTrace
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M)
    {potential weightedDivergenceTrace rawTrace actionTrace : M -> Real}
    (hpotential : ContMDiff I 𝓘(Real, Real) ∞ potential)
    (traceVec : Cₛ^∞⟮I; E, (TangentSpace I : M -> Type _)⟯)
    (hmeas :
      AEMeasurable
        (fun x : M => ENNReal.ofReal (expNegPotentialDensity potential x))
        (riemannianVolumeMeasure (I := I) (M := M) g))
    (hdivTrace :
      ∀ x : M,
        RicciFlower.Analysis.DivergenceTheorem.divergence_g
            (I := I) g traceVec x =
          rawTrace x)
    (hactionTrace :
      ∀ x : M,
        RicciFlower.Analysis.DivergenceTheorem.tangentSectionAction
            (I := I) traceVec potential x =
          actionTrace x)
    (hweighted :
      ∀ x : M,
        weightedDivergenceTrace x = rawTrace x - actionTrace x) :
    ∫ x, weightedDivergenceTrace x
      ∂(expNegPotentialWeightedMeasure
          (riemannianVolumeMeasure (I := I) (M := M) g) potential) = 0 := by
  exact weightedDivZero (I := I) g
    (connTraceVec (I := I) hpotential traceVec) hmeas
    (connTraceDivEq (I := I) g hpotential traceVec hdivTrace
      hactionTrace hweighted)

/-- Weighted Green in the exact scalar form used by formula 5.10 for the
shifted Hessian trace `Delta(h - V/2)`. -/
theorem shiftIntEq
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M)
    {potential q shiftedTrace potentialVariation metricVariationTrace :
      M -> Real}
    (hpotential : ContMDiff I 𝓘(Real, Real) ∞ potential)
    (hq : ContMDiff I 𝓘(Real, Real) ∞ q)
    (hmeas :
      AEMeasurable
        (fun x : M => ENNReal.ofReal (expNegPotentialDensity potential x))
        (riemannianVolumeMeasure (I := I) (M := M) g))
    (hshift :
      ∀ x : M,
        shiftedTrace x =
          RicciFlower.Analysis.DivergenceTheorem.Δ_g
            (I := I) g hq x)
    (hqeq :
      ∀ x : M,
        q x = potentialVariation x - metricVariationTrace x / 2) :
    ∫ x, shiftedTrace x
      ∂(expNegPotentialWeightedMeasure
          (riemannianVolumeMeasure (I := I) (M := M) g) potential) =
      ∫ x,
        expWeightedMeasureVariationFactor potentialVariation
          metricVariationTrace x *
          (RicciFlower.Analysis.DivergenceTheorem.Δ_g
              (I := I) g hpotential x -
            g.inner x
              ((RicciFlower.Analysis.DivergenceTheorem.grad_g
                (I := I) g hpotential :
                Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
              ((RicciFlower.Analysis.DivergenceTheorem.grad_g
                (I := I) g hpotential :
                Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x))
      ∂(expNegPotentialWeightedMeasure
          (riemannianVolumeMeasure (I := I) (M := M) g) potential) := by
  calc
    ∫ x, shiftedTrace x
      ∂(expNegPotentialWeightedMeasure
          (riemannianVolumeMeasure (I := I) (M := M) g) potential) =
        ∫ x,
          RicciFlower.Analysis.DivergenceTheorem.Δ_g (I := I) g hq x
        ∂(expNegPotentialWeightedMeasure
            (riemannianVolumeMeasure (I := I) (M := M) g) potential) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall hshift
    _ = ∫ x,
        q x *
          (-RicciFlower.Analysis.DivergenceTheorem.Δ_g
              (I := I) g hpotential x +
            g.inner x
              ((RicciFlower.Analysis.DivergenceTheorem.grad_g
                (I := I) g hpotential :
                Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
              ((RicciFlower.Analysis.DivergenceTheorem.grad_g
                (I := I) g hpotential :
                Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x))
        ∂(expNegPotentialWeightedMeasure
            (riemannianVolumeMeasure (I := I) (M := M) g) potential) := by
      exact weightedGreen (I := I) g hpotential hq hmeas
    _ = ∫ x,
        expWeightedMeasureVariationFactor potentialVariation
          metricVariationTrace x *
          (RicciFlower.Analysis.DivergenceTheorem.Δ_g
              (I := I) g hpotential x -
            g.inner x
              ((RicciFlower.Analysis.DivergenceTheorem.grad_g
                (I := I) g hpotential :
                Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
              ((RicciFlower.Analysis.DivergenceTheorem.grad_g
                (I := I) g hpotential :
                Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x))
        ∂(expNegPotentialWeightedMeasure
            (riemannianVolumeMeasure (I := I) (M := M) g) potential) := by
      apply integral_congr_ae
      refine Filter.Eventually.of_forall ?_
      intro x
      dsimp
      rw [hqeq x]
      unfold expWeightedMeasureVariationFactor
      ring

/-- Moving-volume derivative for integrals against `e^{-f_s} dmu_s`. -/
theorem expWeightedMeasureIntegral_hasDerivAt_at
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (G : Realized.RealizedMetricFamily (I := I) (M := M) Real)
    {potentialPath phiPath : Real -> M -> Real}
    {s0 : Real}
    {potentialVariation metricVariationTrace phiVariation : M -> Real}
    (hpotential_deriv :
      ∀ x : M,
        HasDerivAt (fun s : Real => potentialPath s x)
          (potentialVariation x) s0)
    (hphi_deriv :
      ∀ x : M,
        HasDerivAt (fun s : Real => phiPath s x)
          (phiVariation x) s0)
    (htrace :
      ∀ x : M,
        traceTimeDerivMetricAt (I := I) G s0 x = metricVariationTrace x)
    (hmetric_reg :
      MetricFamilyRegularAt (I := I)
        (metricFamilyForMeasure (I := I) (M := M) G) s0)
    (hintegrand_reg :
      FunctionRegularAt
        (fun s : Real => fun x : M =>
          expNegPotentialDensity (potentialPath s) x * phiPath s x)
        s0) :
    HasDerivAt
      (fun s : Real =>
        ∫ x,
          expNegPotentialDensity (potentialPath s) x * phiPath s x
          ∂(volumeMeasureFamily (I := I) (M := M) G s))
      (∫ x,
        expWeightedIntegralVariationIntegrand
          (potentialPath s0) potentialVariation metricVariationTrace
          (phiPath s0) phiVariation x
        ∂(volumeMeasureFamily (I := I) (M := M) G s0))
      s0 := by
  have hvol :=
    volume_variation_formula_clean_at
      (I := I) (M := M) G
      (f := fun s : Real => fun x : M =>
        expNegPotentialDensity (potentialPath s) x * phiPath s x)
      (t₀ := s0) hmetric_reg hintegrand_reg
  refine hvol.congr_deriv ?_
  apply integral_congr_ae
  refine Filter.Eventually.of_forall ?_
  intro x
  have hdens :=
    expNegPotentialDensity_hasDerivAt
      (M := M) (potentialPath := potentialPath)
      (potentialVariation := potentialVariation)
      hpotential_deriv x
  have hprod :
      HasDerivAt
        (fun s : Real =>
          expNegPotentialDensity (potentialPath s) x * phiPath s x)
        (-(potentialVariation x) *
            expNegPotentialDensity (potentialPath s0) x * phiPath s0 x +
          expNegPotentialDensity (potentialPath s0) x * phiVariation x)
        s0 :=
    hdens.mul (hphi_deriv x)
  have hderiv := hprod.deriv
  change
    deriv
        (fun s : Real =>
          expNegPotentialDensity (potentialPath s) x * phiPath s x)
        s0 +
      1 / 2 * traceTimeDerivMetricAt (I := I) G s0 x *
        (expNegPotentialDensity (potentialPath s0) x * phiPath s0 x) =
    expWeightedIntegralVariationIntegrand
      (potentialPath s0) potentialVariation metricVariationTrace
      (phiPath s0) phiVariation x
  rw [hderiv, htrace x]
  unfold expWeightedIntegralVariationIntegrand
    expWeightedMeasureVariationFactor
  ring

/-- Scalar derivative of the bracket `R + |grad f|^2`. -/
def fFunctionalBracketVariation
    (scalarCurvatureVariation gradPotentialNormSqVariation : M -> Real) :
    M -> Real :=
  fun x => scalarCurvatureVariation x + gradPotentialNormSqVariation x

theorem fFunctionalBracket_hasDerivAt
    {scalarCurvaturePath gradPotentialNormSqPath : Real -> M -> Real}
    {s0 : Real}
    {scalarCurvatureVariation gradPotentialNormSqVariation : M -> Real}
    (hscalar_deriv :
      ∀ x : M,
        HasDerivAt (fun s : Real => scalarCurvaturePath s x)
          (scalarCurvatureVariation x) s0)
    (hgrad_deriv :
      ∀ x : M,
        HasDerivAt (fun s : Real => gradPotentialNormSqPath s x)
          (gradPotentialNormSqVariation x) s0)
    (x : M) :
    HasDerivAt
      (fun s : Real =>
        fFunctionalBracket (scalarCurvaturePath s)
          (gradPotentialNormSqPath s) x)
      (fFunctionalBracketVariation scalarCurvatureVariation
        gradPotentialNormSqVariation x)
      s0 := by
  have h := (hscalar_deriv x).add (hgrad_deriv x)
  simpa [fFunctionalBracket, fFunctionalBracketVariation] using h

/-- Formula specialized to Perelman's `F` bracket.  The derivatives of scalar
curvature and `|grad f|^2` are scalar inputs; formula 5.10 later identifies
their integrated geometric expression. -/
theorem fFunctionalBaseIntegral_hasDerivAt_at
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (G : Realized.RealizedMetricFamily (I := I) (M := M) Real)
    {scalarCurvaturePath gradPotentialNormSqPath potentialPath :
      Real -> M -> Real}
    {s0 : Real}
    {scalarCurvatureVariation gradPotentialNormSqVariation potentialVariation
      metricVariationTrace : M -> Real}
    (hscalar_deriv :
      ∀ x : M,
        HasDerivAt (fun s : Real => scalarCurvaturePath s x)
          (scalarCurvatureVariation x) s0)
    (hgrad_deriv :
      ∀ x : M,
        HasDerivAt (fun s : Real => gradPotentialNormSqPath s x)
          (gradPotentialNormSqVariation x) s0)
    (hpotential_deriv :
      ∀ x : M,
        HasDerivAt (fun s : Real => potentialPath s x)
          (potentialVariation x) s0)
    (htrace :
      ∀ x : M,
        traceTimeDerivMetricAt (I := I) G s0 x = metricVariationTrace x)
    (hmetric_reg :
      MetricFamilyRegularAt (I := I)
        (metricFamilyForMeasure (I := I) (M := M) G) s0)
    (hintegrand_reg :
      FunctionRegularAt
        (fun s : Real => fun x : M =>
          expNegPotentialDensity (potentialPath s) x *
            fFunctionalBracket (scalarCurvaturePath s)
              (gradPotentialNormSqPath s) x)
        s0) :
    HasDerivAt
      (fun s : Real =>
        ∫ x,
          expNegPotentialDensity (potentialPath s) x *
            fFunctionalBracket (scalarCurvaturePath s)
              (gradPotentialNormSqPath s) x
          ∂(volumeMeasureFamily (I := I) (M := M) G s))
      (∫ x,
        expWeightedIntegralVariationIntegrand
          (potentialPath s0) potentialVariation metricVariationTrace
          (fFunctionalBracket (scalarCurvaturePath s0)
            (gradPotentialNormSqPath s0))
          (fFunctionalBracketVariation scalarCurvatureVariation
            gradPotentialNormSqVariation) x
        ∂(volumeMeasureFamily (I := I) (M := M) G s0))
      s0 :=
  expWeightedMeasureIntegral_hasDerivAt_at
    (I := I) (M := M) G
    (potentialPath := potentialPath)
    (phiPath := fun s : Real => fun x : M =>
      fFunctionalBracket (scalarCurvaturePath s)
        (gradPotentialNormSqPath s) x)
    (s0 := s0)
    (potentialVariation := potentialVariation)
    (metricVariationTrace := metricVariationTrace)
    (phiVariation :=
      fFunctionalBracketVariation scalarCurvatureVariation
        gradPotentialNormSqVariation)
    hpotential_deriv
    (fFunctionalBracket_hasDerivAt
      (M := M) (scalarCurvaturePath := scalarCurvaturePath)
      (gradPotentialNormSqPath := gradPotentialNormSqPath)
      (s0 := s0)
      (scalarCurvatureVariation := scalarCurvatureVariation)
      (gradPotentialNormSqVariation := gradPotentialNormSqVariation)
      hscalar_deriv hgrad_deriv)
    htrace hmetric_reg hintegrand_reg

/-- Convert a base-integral derivative into the path-level first-variation
predicate for `F`. -/
theorem FFunctionalHasFirstVariationAt_of_baseIntegral_hasDerivAt
    [MeasurableSpace M]
    {muPath : Real -> Measure M}
    {scalarCurvaturePath gradPotentialNormSqPath potentialPath :
      Real -> M -> Real}
    {s0 firstVariation : Real}
    (hbase_eq :
      (fun s : Real =>
        fFunctional (muPath s) (scalarCurvaturePath s)
          (gradPotentialNormSqPath s) (potentialPath s))
        =ᶠ[nhds s0]
      fun s : Real =>
        ∫ x,
          expNegPotentialDensity (potentialPath s) x *
            fFunctionalBracket (scalarCurvaturePath s)
              (gradPotentialNormSqPath s) x
          ∂(muPath s))
    (hbase :
      HasDerivAt
        (fun s : Real =>
          ∫ x,
            expNegPotentialDensity (potentialPath s) x *
              fFunctionalBracket (scalarCurvaturePath s)
                (gradPotentialNormSqPath s) x
            ∂(muPath s))
        firstVariation s0) :
    FFunctionalHasFirstVariationAt muPath scalarCurvaturePath
      gradPotentialNormSqPath potentialPath s0 firstVariation := by
  unfold FFunctionalHasFirstVariationAt fFunctionalAlong
  exact hbase.congr_of_eventuallyEq hbase_eq

/-- First-variation producer for `F` from moving-volume differentiation. -/
theorem FFunctionalHasFirstVariationAt_of_volumeVariation
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (G : Realized.RealizedMetricFamily (I := I) (M := M) Real)
    {scalarCurvaturePath gradPotentialNormSqPath potentialPath :
      Real -> M -> Real}
    {s0 : Real}
    {scalarCurvatureVariation gradPotentialNormSqVariation potentialVariation
      metricVariationTrace : M -> Real}
    (hbase_eq :
      (fun s : Real =>
        fFunctional (volumeMeasureFamily (I := I) (M := M) G s)
          (scalarCurvaturePath s) (gradPotentialNormSqPath s)
          (potentialPath s))
        =ᶠ[nhds s0]
      fun s : Real =>
        ∫ x,
          expNegPotentialDensity (potentialPath s) x *
            fFunctionalBracket (scalarCurvaturePath s)
              (gradPotentialNormSqPath s) x
          ∂(volumeMeasureFamily (I := I) (M := M) G s))
    (hscalar_deriv :
      ∀ x : M,
        HasDerivAt (fun s : Real => scalarCurvaturePath s x)
          (scalarCurvatureVariation x) s0)
    (hgrad_deriv :
      ∀ x : M,
        HasDerivAt (fun s : Real => gradPotentialNormSqPath s x)
          (gradPotentialNormSqVariation x) s0)
    (hpotential_deriv :
      ∀ x : M,
        HasDerivAt (fun s : Real => potentialPath s x)
          (potentialVariation x) s0)
    (htrace :
      ∀ x : M,
        traceTimeDerivMetricAt (I := I) G s0 x = metricVariationTrace x)
    (hmetric_reg :
      MetricFamilyRegularAt (I := I)
        (metricFamilyForMeasure (I := I) (M := M) G) s0)
    (hintegrand_reg :
      FunctionRegularAt
        (fun s : Real => fun x : M =>
          expNegPotentialDensity (potentialPath s) x *
            fFunctionalBracket (scalarCurvaturePath s)
              (gradPotentialNormSqPath s) x)
        s0) :
    FFunctionalHasFirstVariationAt
      (volumeMeasureFamily (I := I) (M := M) G)
      scalarCurvaturePath gradPotentialNormSqPath potentialPath s0
      (∫ x,
        expWeightedIntegralVariationIntegrand
          (potentialPath s0) potentialVariation metricVariationTrace
          (fFunctionalBracket (scalarCurvaturePath s0)
            (gradPotentialNormSqPath s0))
          (fFunctionalBracketVariation scalarCurvatureVariation
            gradPotentialNormSqVariation) x
        ∂(volumeMeasureFamily (I := I) (M := M) G s0)) := by
  exact FFunctionalHasFirstVariationAt_of_baseIntegral_hasDerivAt
    (M := M)
    (muPath := volumeMeasureFamily (I := I) (M := M) G)
    hbase_eq
    (fFunctionalBaseIntegral_hasDerivAt_at
      (I := I) (M := M) G
      hscalar_deriv hgrad_deriv hpotential_deriv htrace hmetric_reg
      hintegrand_reg)

end Geometry

/-! ## Formula 5.10 proof-step interfaces -/

section Formula510

variable {Idx : Type*} [Fintype Idx]

/-- Arbitrary metric-variation Christoffel formula in a fixed frame:
`delta Gamma^k_ij = 1/2 g^{kl}(nabla_i v_jl + nabla_j v_il - nabla_l v_ij)`. -/
def MetricVariationChristoffelInFrame
    (gInv : M -> Idx -> Idx -> Real)
    (nablaMetricVariation christoffelVariation :
      M -> Idx -> Idx -> Idx -> Real) : Prop :=
  ∀ x : M, ∀ i j k : Idx,
    christoffelVariation x k i j =
      (1 / 2 : Real) *
        ∑ l : Idx, gInv x k l *
          (nablaMetricVariation x i j l +
            nablaMetricVariation x j i l -
              nablaMetricVariation x l i j)

/-- Trace of the arbitrary metric-variation Christoffel formula:
`delta Gamma^p_pj = 1/2 nabla_j V`. -/
def MetricVariationChristoffelTraceInFrame
    (christoffelTraceVariation metricVariationTraceGradient :
      M -> Idx -> Real) : Prop :=
  ∀ x : M, ∀ j : Idx,
    christoffelTraceVariation x j =
      (1 / 2 : Real) * metricVariationTraceGradient x j

/-- Ricci variation by differentiating the Christoffel variation:
`delta Ric_ij = nabla_p(delta Gamma^p_ij) - nabla_i(delta Gamma^p_pj)`. -/
def RicciVariationByChristoffelInFrame
    (ricciVariation : M -> Idx -> Idx -> Real)
    (nablaChristoffelVariation : M -> Idx -> Idx -> Idx -> Idx -> Real)
    (nablaChristoffelTraceVariation : M -> Idx -> Idx -> Real) : Prop :=
  ∀ x : M, ∀ i j : Idx,
    ricciVariation x i j =
      (∑ p : Idx, nablaChristoffelVariation x p p i j) -
        nablaChristoffelTraceVariation x i j

/-- Hessian variation for a scalar potential:
`delta Hess_ij f = Hess_ij h - (delta Gamma^p_ij) nabla_p f`. -/
def HessianPotentialVariationByChristoffelInFrame
    (hessianPotentialVariation hessianPotentialVariationDirection :
      M -> Idx -> Idx -> Real)
    (christoffelVariation : M -> Idx -> Idx -> Idx -> Real)
    (gradPotential : M -> Idx -> Real) : Prop :=
  ∀ x : M, ∀ i j : Idx,
    hessianPotentialVariation x i j =
      hessianPotentialVariationDirection x i j -
        ∑ p : Idx, christoffelVariation x p i j * gradPotential x p

/-- Combined variation of `Ric_ij + Hess_ij f` in the weighted-divergence
form used in the book proof. -/
def RicciHessianVariationWeightedDivergenceInFrame
    (ricciHessianVariation weightedDivergenceTerm shiftedHessianTerm :
      M -> Idx -> Idx -> Real) : Prop :=
  ∀ x : M, ∀ i j : Idx,
    ricciHessianVariation x i j =
      weightedDivergenceTerm x i j + shiftedHessianTerm x i j

/-- Sum of Ricci and Hessian variations in a fixed frame. -/
def ricciHessianVariationInFrame
    (ricciVariation hessianVariation : M -> Idx -> Idx -> Real) :
    M -> Idx -> Idx -> Real :=
  fun x i j => ricciVariation x i j + hessianVariation x i j

/-- Coordinate expression for
`e^f nabla_p(e^{-f} A^p_ij) = nabla_p A^p_ij - A^p_ij partial_p f`. -/
def christoffelWeightedDivergenceInFrame
    (nablaChristoffelVariation : M -> Idx -> Idx -> Idx -> Idx -> Real)
    (christoffelVariation : M -> Idx -> Idx -> Idx -> Real)
    (gradPotential : M -> Idx -> Real) :
    M -> Idx -> Idx -> Real :=
  fun x i j =>
    (∑ p : Idx, nablaChristoffelVariation x p p i j) -
      ∑ p : Idx, christoffelVariation x p i j * gradPotential x p

/-- Shifted Hessian term `Hess h - Hess(V/2)` in formula 5.10. -/
def shiftedHessianInFrame
    (hessianPotentialVariationDirection metricTraceHessianHalf :
      M -> Idx -> Idx -> Real) :
    M -> Idx -> Idx -> Real :=
  fun x i j =>
    hessianPotentialVariationDirection x i j -
      metricTraceHessianHalf x i j

/-- Pointwise assembly of the already separated Ricci and Hessian variation
formulas into the weighted-divergence form used before contraction. -/
theorem ricciHessianWeightedDivergence_of_ricci_hessian
    (ricciVariation hessianVariation hessianPotentialVariationDirection :
      M -> Idx -> Idx -> Real)
    (christoffelVariation : M -> Idx -> Idx -> Idx -> Real)
    (nablaChristoffelVariation : M -> Idx -> Idx -> Idx -> Idx -> Real)
    (nablaChristoffelTraceVariation metricTraceHessianHalf :
      M -> Idx -> Idx -> Real)
    (gradPotential : M -> Idx -> Real)
    (hRic :
      RicciVariationByChristoffelInFrame ricciVariation
        nablaChristoffelVariation nablaChristoffelTraceVariation)
    (hHess :
      HessianPotentialVariationByChristoffelInFrame hessianVariation
        hessianPotentialVariationDirection christoffelVariation gradPotential)
    (hTrace :
      ∀ x : M, ∀ i j : Idx,
        nablaChristoffelTraceVariation x i j =
          metricTraceHessianHalf x i j) :
    RicciHessianVariationWeightedDivergenceInFrame
      (ricciHessianVariationInFrame ricciVariation hessianVariation)
      (christoffelWeightedDivergenceInFrame nablaChristoffelVariation
        christoffelVariation gradPotential)
      (shiftedHessianInFrame hessianPotentialVariationDirection
        metricTraceHessianHalf) := by
  intro x i j
  rw [ricciHessianVariationInFrame, hRic x i j, hHess x i j, hTrace x i j]
  simp [christoffelWeightedDivergenceInFrame, shiftedHessianInFrame,
    sub_eq_add_neg, add_comm, add_left_comm, add_assoc]

/-- Variation of `(Ric_ij + Hess_ij f)e^{-f}dmu` before contraction. -/
def RicciHessianWeightedDensityVariationInFrame
    (weightedVariation weightedDivergenceTerm shiftedHessianTerm
      ricciHessian : M -> Idx -> Idx -> Real)
    (potentialVariation metricVariationTrace density : M -> Real) : Prop :=
  ∀ x : M, ∀ i j : Idx,
    weightedVariation x i j =
      weightedDivergenceTerm x i j +
        density x * shiftedHessianTerm x i j +
          ricciHessian x i j * density x *
            expWeightedMeasureVariationFactor potentialVariation
              metricVariationTrace x

/-- The density-weighted divergence term
`nabla_p(e^{-f} A^p_ij)` when
`weightedDivergenceTerm = e^f nabla_p(e^{-f} A^p_ij)`. -/
def densityWeightedDivergenceInFrame
    (density : M -> Real) (weightedDivergenceTerm : M -> Idx -> Idx -> Real) :
    M -> Idx -> Idx -> Real :=
  fun x i j => density x * weightedDivergenceTerm x i j

omit [Fintype Idx] in
/-- Pointwise density variation bridge for
`(Ric_ij + Hess_ij f)e^{-f} dmu`. -/
theorem ricciHessianWeightedDensity_of_divergence
    (weightedDivergenceTerm shiftedHessianTerm ricciHessian :
      M -> Idx -> Idx -> Real)
    (density potentialVariation metricVariationTrace : M -> Real) :
    RicciHessianWeightedDensityVariationInFrame
      (fun x i j =>
        densityWeightedDivergenceInFrame density weightedDivergenceTerm x i j +
          density x * shiftedHessianTerm x i j +
            ricciHessian x i j * density x *
              expWeightedMeasureVariationFactor potentialVariation
                metricVariationTrace x)
      (densityWeightedDivergenceInFrame density weightedDivergenceTerm)
      shiftedHessianTerm ricciHessian potentialVariation metricVariationTrace
      density := by
  intro x i j
  rfl

/-- Frame contraction of a metric variation against `Ric + Hess f`. -/
def metricVariationRicciHessContractInFrame
    (metricVariation ricciHessian : M -> Idx -> Idx -> Real) : M -> Real :=
  fun x =>
    ∑ i : Idx, ∑ j : Idx,
      metricVariation x i j * ricciHessian x i j

/-- Inverse-metric variation contribution in formula 5.10:
`delta g^{ij}(Ric_ij + Hess_ij f) = -v_ij(Ric_ij + Hess_ij f)`. -/
def inverseMetricVariationContractionTermInFrame
    (metricVariation ricciHessian : M -> Idx -> Idx -> Real) : M -> Real :=
  fun x => -metricVariationRicciHessContractInFrame metricVariation ricciHessian x

/-- Public bridge naming the inverse-metric contraction contribution. -/
theorem inverseMetricVariationContractionTerm_eq_neg
    (metricVariation ricciHessian : M -> Idx -> Idx -> Real) :
    inverseMetricVariationContractionTermInFrame metricVariation ricciHessian =
      fun x => -metricVariationRicciHessContractInFrame metricVariation
        ricciHessian x := rfl

end Formula510

/-- Final weighted-measure integrand in MSM135 formula 5.10. -/
def fFunctionalFormula510Integrand
    (scalarCurvature lapPotential gradPotentialNormSq
      potentialVariation metricVariationTrace metricVariationRicciHess :
      M -> Real) :
    M -> Real :=
  fun x =>
    -metricVariationRicciHess x +
      (metricVariationTrace x / 2 - potentialVariation x) *
        (2 * lapPotential x - gradPotentialNormSq x + scalarCurvature x)

/-- Formula 5.10 as a final integral identity. -/
def FFunctionalFormula510 [MeasurableSpace M] (weightedMeasure : Measure M)
    (firstVariation : Real)
    (scalarCurvature lapPotential gradPotentialNormSq potentialVariation
      metricVariationTrace metricVariationRicciHess : M -> Real) : Prop :=
  firstVariation =
    ∫ x,
      fFunctionalFormula510Integrand scalarCurvature lapPotential
        gradPotentialNormSq potentialVariation metricVariationTrace
        metricVariationRicciHess x
      ∂weightedMeasure

/-- Pre-cancellation scalar integrand for the closed-manifold formula 5.10
assembly.  It is the contracted first-variation integrand before the closed
weighted-divergence term and weighted Green term are canceled. -/
def fFunctionalPre510Integrand
    (scalarCurvature lapPotential _gradPotentialNormSq
      potentialVariation metricVariationTrace metricVariationRicciHess
      weightedDivergenceTrace shiftedTrace : M -> Real) :
    M -> Real :=
  fun x =>
    -metricVariationRicciHess x +
      weightedDivergenceTrace x + shiftedTrace x +
        (scalarCurvature x + lapPotential x) *
          expWeightedMeasureVariationFactor potentialVariation
            metricVariationTrace x

/-- The remainder canceled by closed divergence plus weighted Green in formula
5.10. -/
def fFunctional510Remainder
    (lapPotential gradPotentialNormSq potentialVariation metricVariationTrace
      weightedDivergenceTrace shiftedTrace : M -> Real) :
    M -> Real :=
  fun x =>
    weightedDivergenceTrace x +
      (shiftedTrace x -
        expWeightedMeasureVariationFactor potentialVariation
          metricVariationTrace x *
          (lapPotential x - gradPotentialNormSq x))

/-- Pointwise scalar algebra behind formula 5.10 after the geometric producers
have produced the pre-cancellation integrand. -/
theorem pre510_eq_final_add_rem
    (scalarCurvature lapPotential gradPotentialNormSq
      potentialVariation metricVariationTrace metricVariationRicciHess
      weightedDivergenceTrace shiftedTrace : M -> Real) :
    fFunctionalPre510Integrand scalarCurvature lapPotential
        gradPotentialNormSq potentialVariation metricVariationTrace
        metricVariationRicciHess weightedDivergenceTrace shiftedTrace =
      fun x : M =>
        fFunctionalFormula510Integrand scalarCurvature lapPotential
          gradPotentialNormSq potentialVariation metricVariationTrace
          metricVariationRicciHess x +
        fFunctional510Remainder lapPotential gradPotentialNormSq
          potentialVariation metricVariationTrace weightedDivergenceTrace
          shiftedTrace x := by
  funext x
  unfold fFunctionalPre510Integrand fFunctionalFormula510Integrand
    fFunctional510Remainder expWeightedMeasureVariationFactor
  ring

/-- The formula 5.10 remainder has zero integral once the closed divergence
term vanishes and weighted Green identifies the shifted Hessian trace. -/
theorem rem510_integral_zero [MeasurableSpace M]
    {weightedMeasure : Measure M}
    {lapPotential gradPotentialNormSq potentialVariation metricVariationTrace
      weightedDivergenceTrace shiftedTrace : M -> Real}
    (hdiv_int : Integrable weightedDivergenceTrace weightedMeasure)
    (hshift_int : Integrable shiftedTrace weightedMeasure)
    (hcorr_int :
      Integrable
        (fun x : M =>
          expWeightedMeasureVariationFactor potentialVariation
            metricVariationTrace x *
            (lapPotential x - gradPotentialNormSq x))
        weightedMeasure)
    (hdiv_zero :
      ∫ x, weightedDivergenceTrace x ∂weightedMeasure = 0)
    (hshift :
      ∫ x, shiftedTrace x ∂weightedMeasure =
        ∫ x,
          expWeightedMeasureVariationFactor potentialVariation
            metricVariationTrace x *
            (lapPotential x - gradPotentialNormSq x)
          ∂weightedMeasure) :
    ∫ x,
      fFunctional510Remainder lapPotential gradPotentialNormSq
        potentialVariation metricVariationTrace weightedDivergenceTrace
        shiftedTrace x
      ∂weightedMeasure = 0 := by
  let corr : M -> Real := fun x =>
    expWeightedMeasureVariationFactor potentialVariation
      metricVariationTrace x *
      (lapPotential x - gradPotentialNormSq x)
  have hcorr_int' : Integrable corr weightedMeasure := by
    simpa [corr] using hcorr_int
  have hshift' :
      ∫ x, shiftedTrace x ∂weightedMeasure =
        ∫ x, corr x ∂weightedMeasure := by
    simpa [corr] using hshift
  unfold fFunctional510Remainder
  change
    ∫ x, weightedDivergenceTrace x + (shiftedTrace - corr) x
      ∂weightedMeasure = 0
  rw [integral_add hdiv_int (hshift_int.sub hcorr_int')]
  change
    ∫ x, weightedDivergenceTrace x ∂weightedMeasure +
      ∫ x, shiftedTrace x - corr x ∂weightedMeasure = 0
  rw [integral_sub hshift_int hcorr_int']
  rw [hdiv_zero, hshift']
  ring

/-- Formula 5.10 from the pre-cancellation scalar integrand and a zero
remainder. -/
theorem formula510_of_rem_zero [MeasurableSpace M]
    {weightedMeasure : Measure M}
    {firstVariation : Real}
    {scalarCurvature lapPotential gradPotentialNormSq potentialVariation
      metricVariationTrace metricVariationRicciHess weightedDivergenceTrace
      shiftedTrace : M -> Real}
    (hfirst :
      firstVariation =
        ∫ x,
          fFunctionalPre510Integrand scalarCurvature lapPotential
            gradPotentialNormSq potentialVariation metricVariationTrace
            metricVariationRicciHess weightedDivergenceTrace shiftedTrace x
          ∂weightedMeasure)
    (hfinal_int :
      Integrable
        (fFunctionalFormula510Integrand scalarCurvature lapPotential
          gradPotentialNormSq potentialVariation metricVariationTrace
          metricVariationRicciHess)
        weightedMeasure)
    (hrem_int :
      Integrable
        (fFunctional510Remainder lapPotential gradPotentialNormSq
          potentialVariation metricVariationTrace weightedDivergenceTrace
          shiftedTrace)
        weightedMeasure)
    (hrem_zero :
      ∫ x,
        fFunctional510Remainder lapPotential gradPotentialNormSq
          potentialVariation metricVariationTrace weightedDivergenceTrace
          shiftedTrace x
        ∂weightedMeasure = 0) :
    FFunctionalFormula510 weightedMeasure firstVariation scalarCurvature
      lapPotential gradPotentialNormSq potentialVariation metricVariationTrace
      metricVariationRicciHess := by
  unfold FFunctionalFormula510
  rw [hfirst]
  calc
    ∫ x,
        fFunctionalPre510Integrand scalarCurvature lapPotential
          gradPotentialNormSq potentialVariation metricVariationTrace
          metricVariationRicciHess weightedDivergenceTrace shiftedTrace x
        ∂weightedMeasure =
      ∫ x,
        (fFunctionalFormula510Integrand scalarCurvature lapPotential
            gradPotentialNormSq potentialVariation metricVariationTrace
            metricVariationRicciHess x +
          fFunctional510Remainder lapPotential gradPotentialNormSq
            potentialVariation metricVariationTrace weightedDivergenceTrace
            shiftedTrace x)
        ∂weightedMeasure := by
      apply integral_congr_ae
      refine Filter.Eventually.of_forall ?_
      intro x
      rw [pre510_eq_final_add_rem]
    _ =
      ∫ x,
        fFunctionalFormula510Integrand scalarCurvature lapPotential
          gradPotentialNormSq potentialVariation metricVariationTrace
          metricVariationRicciHess x
        ∂weightedMeasure +
      ∫ x,
        fFunctional510Remainder lapPotential gradPotentialNormSq
          potentialVariation metricVariationTrace weightedDivergenceTrace
          shiftedTrace x
        ∂weightedMeasure := by
      rw [integral_add hfinal_int hrem_int]
    _ =
      ∫ x,
        fFunctionalFormula510Integrand scalarCurvature lapPotential
          gradPotentialNormSq potentialVariation metricVariationTrace
          metricVariationRicciHess x
        ∂weightedMeasure := by
      rw [hrem_zero, add_zero]

/-- Formula 5.10 from the closed divergence cancellation and weighted Green
identification of the shifted Hessian trace. -/
theorem formula510_of_ints [MeasurableSpace M]
    {weightedMeasure : Measure M}
    {firstVariation : Real}
    {scalarCurvature lapPotential gradPotentialNormSq potentialVariation
      metricVariationTrace metricVariationRicciHess weightedDivergenceTrace
      shiftedTrace : M -> Real}
    (hfirst :
      firstVariation =
        ∫ x,
          fFunctionalPre510Integrand scalarCurvature lapPotential
            gradPotentialNormSq potentialVariation metricVariationTrace
            metricVariationRicciHess weightedDivergenceTrace shiftedTrace x
          ∂weightedMeasure)
    (hfinal_int :
      Integrable
        (fFunctionalFormula510Integrand scalarCurvature lapPotential
          gradPotentialNormSq potentialVariation metricVariationTrace
          metricVariationRicciHess)
        weightedMeasure)
    (hdiv_int : Integrable weightedDivergenceTrace weightedMeasure)
    (hshift_int : Integrable shiftedTrace weightedMeasure)
    (hcorr_int :
      Integrable
        (fun x : M =>
          expWeightedMeasureVariationFactor potentialVariation
            metricVariationTrace x *
            (lapPotential x - gradPotentialNormSq x))
        weightedMeasure)
    (hdiv_zero :
      ∫ x, weightedDivergenceTrace x ∂weightedMeasure = 0)
    (hshift :
      ∫ x, shiftedTrace x ∂weightedMeasure =
        ∫ x,
          expWeightedMeasureVariationFactor potentialVariation
            metricVariationTrace x *
            (lapPotential x - gradPotentialNormSq x)
          ∂weightedMeasure) :
    FFunctionalFormula510 weightedMeasure firstVariation scalarCurvature
      lapPotential gradPotentialNormSq potentialVariation metricVariationTrace
      metricVariationRicciHess := by
  apply formula510_of_rem_zero
    (weightedDivergenceTrace := weightedDivergenceTrace)
    (shiftedTrace := shiftedTrace)
    hfirst hfinal_int
  · unfold fFunctional510Remainder
    exact hdiv_int.add (hshift_int.sub hcorr_int)
  · exact rem510_integral_zero hdiv_int hshift_int hcorr_int
      hdiv_zero hshift

section GeometryFormula510

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [InnerProductSpace Real E]
variable [Module.Finite Real E] [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

/-- Formula 5.10 from the geometric connection-trace divergence field and the
weighted Green shift identity.  This is the assembly form matching the book's
step where `∇_p(e^{-f} g^{ij} A^p_{ij})` integrates to zero. -/
theorem formula510_of_connTrace
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M)
    {firstVariation : Real}
    {scalarCurvature lapPotential gradPotentialNormSq potential
      potentialVariation metricVariationTrace metricVariationRicciHess
      weightedDivergenceTrace shiftedTrace rawTrace actionTrace q : M -> Real}
    (hpotential : ContMDiff I 𝓘(Real, Real) ∞ potential)
    (hq : ContMDiff I 𝓘(Real, Real) ∞ q)
    (traceVec : Cₛ^∞⟮I; E, (TangentSpace I : M -> Type _)⟯)
    (hmeas :
      AEMeasurable
        (fun x : M => ENNReal.ofReal (expNegPotentialDensity potential x))
        (riemannianVolumeMeasure (I := I) (M := M) g))
    (hfirst :
      firstVariation =
        ∫ x,
          fFunctionalPre510Integrand scalarCurvature lapPotential
            gradPotentialNormSq potentialVariation metricVariationTrace
            metricVariationRicciHess weightedDivergenceTrace shiftedTrace x
          ∂(expNegPotentialWeightedMeasure
              (riemannianVolumeMeasure (I := I) (M := M) g) potential))
    (hfinal_int :
      Integrable
        (fFunctionalFormula510Integrand scalarCurvature lapPotential
          gradPotentialNormSq potentialVariation metricVariationTrace
          metricVariationRicciHess)
        (expNegPotentialWeightedMeasure
          (riemannianVolumeMeasure (I := I) (M := M) g) potential))
    (hdiv_int :
      Integrable weightedDivergenceTrace
        (expNegPotentialWeightedMeasure
          (riemannianVolumeMeasure (I := I) (M := M) g) potential))
    (hshift_int :
      Integrable shiftedTrace
        (expNegPotentialWeightedMeasure
          (riemannianVolumeMeasure (I := I) (M := M) g) potential))
    (hcorr_int :
      Integrable
        (fun x : M =>
          expWeightedMeasureVariationFactor potentialVariation
            metricVariationTrace x *
            (lapPotential x - gradPotentialNormSq x))
        (expNegPotentialWeightedMeasure
          (riemannianVolumeMeasure (I := I) (M := M) g) potential))
    (hdivTrace :
      ∀ x : M,
        RicciFlower.Analysis.DivergenceTheorem.divergence_g
            (I := I) g traceVec x =
          rawTrace x)
    (hactionTrace :
      ∀ x : M,
        RicciFlower.Analysis.DivergenceTheorem.tangentSectionAction
            (I := I) traceVec potential x =
          actionTrace x)
    (hweighted :
      ∀ x : M,
        weightedDivergenceTrace x = rawTrace x - actionTrace x)
    (hlap :
      ∀ x : M,
        lapPotential x =
          RicciFlower.Analysis.DivergenceTheorem.Δ_g
            (I := I) g hpotential x)
    (hgradSq :
      ∀ x : M,
        gradPotentialNormSq x =
          g.inner x
            ((RicciFlower.Analysis.DivergenceTheorem.grad_g
              (I := I) g hpotential :
              Cₛ^∞⟮I; E, (TangentSpace I : M -> Type _)⟯) x)
            ((RicciFlower.Analysis.DivergenceTheorem.grad_g
              (I := I) g hpotential :
              Cₛ^∞⟮I; E, (TangentSpace I : M -> Type _)⟯) x))
    (hshift :
      ∀ x : M,
        shiftedTrace x =
          RicciFlower.Analysis.DivergenceTheorem.Δ_g
            (I := I) g hq x)
    (hqeq :
      ∀ x : M,
        q x = potentialVariation x - metricVariationTrace x / 2) :
    FFunctionalFormula510
      (expNegPotentialWeightedMeasure
        (riemannianVolumeMeasure (I := I) (M := M) g) potential)
      firstVariation scalarCurvature lapPotential gradPotentialNormSq
      potentialVariation metricVariationTrace metricVariationRicciHess := by
  have hdiv_zero :
      ∫ x, weightedDivergenceTrace x
        ∂(expNegPotentialWeightedMeasure
            (riemannianVolumeMeasure (I := I) (M := M) g) potential) = 0 :=
    weightedDivZero_of_connTrace (I := I) g hpotential traceVec hmeas
      hdivTrace hactionTrace hweighted
  have hshift_eq :
      ∫ x, shiftedTrace x
        ∂(expNegPotentialWeightedMeasure
            (riemannianVolumeMeasure (I := I) (M := M) g) potential) =
        ∫ x,
          expWeightedMeasureVariationFactor potentialVariation
            metricVariationTrace x *
            (RicciFlower.Analysis.DivergenceTheorem.Δ_g
                (I := I) g hpotential x -
              g.inner x
                ((RicciFlower.Analysis.DivergenceTheorem.grad_g
                  (I := I) g hpotential :
                  Cₛ^∞⟮I; E, (TangentSpace I : M -> Type _)⟯) x)
                ((RicciFlower.Analysis.DivergenceTheorem.grad_g
                  (I := I) g hpotential :
                  Cₛ^∞⟮I; E, (TangentSpace I : M -> Type _)⟯) x))
        ∂(expNegPotentialWeightedMeasure
            (riemannianVolumeMeasure (I := I) (M := M) g) potential) :=
    shiftIntEq (I := I) g hpotential hq hmeas hshift hqeq
  have hshift_final :
      ∫ x, shiftedTrace x
        ∂(expNegPotentialWeightedMeasure
            (riemannianVolumeMeasure (I := I) (M := M) g) potential) =
        ∫ x,
          expWeightedMeasureVariationFactor potentialVariation
            metricVariationTrace x *
            (lapPotential x - gradPotentialNormSq x)
        ∂(expNegPotentialWeightedMeasure
            (riemannianVolumeMeasure (I := I) (M := M) g) potential) := by
    calc
      ∫ x, shiftedTrace x
        ∂(expNegPotentialWeightedMeasure
            (riemannianVolumeMeasure (I := I) (M := M) g) potential) =
        ∫ x,
          expWeightedMeasureVariationFactor potentialVariation
            metricVariationTrace x *
            (RicciFlower.Analysis.DivergenceTheorem.Δ_g
                (I := I) g hpotential x -
              g.inner x
                ((RicciFlower.Analysis.DivergenceTheorem.grad_g
                  (I := I) g hpotential :
                  Cₛ^∞⟮I; E, (TangentSpace I : M -> Type _)⟯) x)
                ((RicciFlower.Analysis.DivergenceTheorem.grad_g
                  (I := I) g hpotential :
                  Cₛ^∞⟮I; E, (TangentSpace I : M -> Type _)⟯) x))
        ∂(expNegPotentialWeightedMeasure
            (riemannianVolumeMeasure (I := I) (M := M) g) potential) := hshift_eq
      _ = ∫ x,
          expWeightedMeasureVariationFactor potentialVariation
            metricVariationTrace x *
            (lapPotential x - gradPotentialNormSq x)
        ∂(expNegPotentialWeightedMeasure
            (riemannianVolumeMeasure (I := I) (M := M) g) potential) := by
        apply integral_congr_ae
        refine Filter.Eventually.of_forall ?_
        intro x
        simp [hlap x, hgradSq x]
  exact formula510_of_ints
    (weightedMeasure :=
      expNegPotentialWeightedMeasure
        (riemannianVolumeMeasure (I := I) (M := M) g) potential)
    hfirst hfinal_int hdiv_int hshift_int hcorr_int hdiv_zero hshift_final

/-- Coordinate-frame action formula for the constructed connection-trace field.
This is the first local realization needed to identify the book's
`g^{ij} A^p_{ij} ∂_p f` term with the intrinsic tangent-section action. -/
theorem connTraceAction_coord
    (g : SmoothRiemannianMetric I M)
    (A : Tensor0SBundle.TensorRSField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 1 2)
    (potential : M -> Real)
    (x₀ : M) {x : M} (hx : x ∈ coordinateFrameSet (I := I) x₀) :
    RicciFlower.Analysis.DivergenceTheorem.tangentSectionAction
        (I := I) (RicciFlower.Realized.connTraceField (I := I) g A)
        potential x =
      ∑ p : CoordinateIdx (𝕜 := Real) E,
        (∑ i : CoordinateIdx (𝕜 := Real) E,
          ∑ j : CoordinateIdx (𝕜 := Real) E,
            inverseMetricFlatModelInChart_component (I := I) g x₀ i j
                (extChartAt I x₀ x) *
              componentRS (I := I) (coordinateFrameAt_basis (I := I) x₀ hx)
                (A x) (fun _ : Fin 1 => p)
                (fun q : Fin 2 => if q = 0 then i else j)) *
          extDerivFun (I := I) potential x
            (coordinateFrameAt (I := I) x₀ p x) := by
  classical
  let X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _) :=
    RicciFlower.Realized.connTraceField (I := I) g A
  let frame := coordinateFrameAt (I := I) x₀
  let hframe := coordinateFrameAt_isLocalFrame (I := I) x₀
  have hX :
      X x = ∑ p : CoordinateIdx (𝕜 := Real) E,
        hframe.coeff p x (X x) • frame p x := by
    simpa [X, frame, hframe] using hframe.coeff_sum_eq (fun y : M => X y) hx
  rw [RicciFlower.Analysis.DivergenceTheorem.tangentSectionAction_def]
  rw [← RicciFlower.extDerivFun_real_eq_mfderiv I potential x (X x)]
  change extDerivFun (I := I) potential x (X x) = _
  rw [hX, map_sum]
  refine Finset.sum_congr rfl ?_
  intro p _
  rw [map_smul]
  have hcoeff :=
    RicciFlower.Realized.connTraceField_coord (I := I) g A x₀ hx p
  rw [hcoeff]
  exact smul_eq_mul ..

/-- Intrinsic raw divergence trace of the constructed field `tr_g A`. -/
def connTraceRawDiv
    (g : SmoothRiemannianMetric I M)
    (A : Tensor0SBundle.TensorRSField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 1 2) : M -> Real :=
  fun x =>
    RicciFlower.Analysis.DivergenceTheorem.divergence_g
      (I := I) g (RicciFlower.Realized.connTraceField (I := I) g A) x

/-- Pointwise coordinate-centered action trace of `tr_g A` on a scalar
potential.  The chart is centered at the point being evaluated, so this is a
global scalar function without choosing a fixed chart. -/
def connTraceAction
    (g : SmoothRiemannianMetric I M)
    (A : Tensor0SBundle.TensorRSField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 1 2)
    (potential : M -> Real) : M -> Real :=
  fun x =>
    ∑ p : CoordinateIdx (𝕜 := Real) E,
      (∑ i : CoordinateIdx (𝕜 := Real) E,
        ∑ j : CoordinateIdx (𝕜 := Real) E,
          inverseMetricFlatModelInChart_component (I := I) g x i j
              (extChartAt I x x) *
            componentRS (I := I)
              (coordinateFrameAt_basis (I := I) x (coordinateFrameAt_mem (I := I) x))
              (A x) (fun _ : Fin 1 => p)
              (fun q : Fin 2 => if q = 0 then i else j)) *
        extDerivFun (I := I) potential x
          (coordinateFrameAt (I := I) x p x)

/-- The coordinate-centered `connTraceAction` is the intrinsic tangent action
of the constructed field. -/
theorem connTraceAction_eq
    (g : SmoothRiemannianMetric I M)
    (A : Tensor0SBundle.TensorRSField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 1 2)
    (potential : M -> Real) (x : M) :
    RicciFlower.Analysis.DivergenceTheorem.tangentSectionAction
        (I := I) (RicciFlower.Realized.connTraceField (I := I) g A)
        potential x =
      connTraceAction (I := I) g A potential x := by
  simpa [connTraceAction] using
    connTraceAction_coord (I := I) g A potential x
      (coordinateFrameAt_mem (I := I) x)

/-- Formula 5.10 using the intrinsic metric trace field `tr_g A` of a smooth
connection-variation tensor.  This specializes `formula510_of_connTrace` with
the smooth section constructed in `Tensor.RSTensor.MetricTrace`. -/
theorem formula510_of_connTraceField
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M)
    (A : Tensor0SBundle.TensorRSField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 1 2)
    {firstVariation : Real}
    {scalarCurvature lapPotential gradPotentialNormSq potential
      potentialVariation metricVariationTrace metricVariationRicciHess
      weightedDivergenceTrace shiftedTrace rawTrace actionTrace q : M -> Real}
    (hpotential : ContMDiff I 𝓘(Real, Real) ∞ potential)
    (hq : ContMDiff I 𝓘(Real, Real) ∞ q)
    (hmeas :
      AEMeasurable
        (fun x : M => ENNReal.ofReal (expNegPotentialDensity potential x))
        (riemannianVolumeMeasure (I := I) (M := M) g))
    (hfirst :
      firstVariation =
        ∫ x,
          fFunctionalPre510Integrand scalarCurvature lapPotential
            gradPotentialNormSq potentialVariation metricVariationTrace
            metricVariationRicciHess weightedDivergenceTrace shiftedTrace x
          ∂(expNegPotentialWeightedMeasure
              (riemannianVolumeMeasure (I := I) (M := M) g) potential))
    (hfinal_int :
      Integrable
        (fFunctionalFormula510Integrand scalarCurvature lapPotential
          gradPotentialNormSq potentialVariation metricVariationTrace
          metricVariationRicciHess)
        (expNegPotentialWeightedMeasure
          (riemannianVolumeMeasure (I := I) (M := M) g) potential))
    (hdiv_int :
      Integrable weightedDivergenceTrace
        (expNegPotentialWeightedMeasure
          (riemannianVolumeMeasure (I := I) (M := M) g) potential))
    (hshift_int :
      Integrable shiftedTrace
        (expNegPotentialWeightedMeasure
          (riemannianVolumeMeasure (I := I) (M := M) g) potential))
    (hcorr_int :
      Integrable
        (fun x : M =>
          expWeightedMeasureVariationFactor potentialVariation
            metricVariationTrace x *
            (lapPotential x - gradPotentialNormSq x))
        (expNegPotentialWeightedMeasure
          (riemannianVolumeMeasure (I := I) (M := M) g) potential))
    (hdivTrace :
      ∀ x : M,
        RicciFlower.Analysis.DivergenceTheorem.divergence_g
            (I := I) g (RicciFlower.Realized.connTraceField (I := I) g A) x =
          rawTrace x)
    (hactionTrace :
      ∀ x : M,
        RicciFlower.Analysis.DivergenceTheorem.tangentSectionAction
            (I := I) (RicciFlower.Realized.connTraceField (I := I) g A) potential x =
          actionTrace x)
    (hweighted :
      ∀ x : M,
        weightedDivergenceTrace x = rawTrace x - actionTrace x)
    (hlap :
      ∀ x : M,
        lapPotential x =
          RicciFlower.Analysis.DivergenceTheorem.Δ_g
            (I := I) g hpotential x)
    (hgradSq :
      ∀ x : M,
        gradPotentialNormSq x =
          g.inner x
            ((RicciFlower.Analysis.DivergenceTheorem.grad_g
              (I := I) g hpotential :
              Cₛ^∞⟮I; E, (TangentSpace I : M -> Type _)⟯) x)
            ((RicciFlower.Analysis.DivergenceTheorem.grad_g
              (I := I) g hpotential :
              Cₛ^∞⟮I; E, (TangentSpace I : M -> Type _)⟯) x))
    (hshift :
      ∀ x : M,
        shiftedTrace x =
          RicciFlower.Analysis.DivergenceTheorem.Δ_g
            (I := I) g hq x)
    (hqeq :
      ∀ x : M,
        q x = potentialVariation x - metricVariationTrace x / 2) :
    FFunctionalFormula510
      (expNegPotentialWeightedMeasure
        (riemannianVolumeMeasure (I := I) (M := M) g) potential)
      firstVariation scalarCurvature lapPotential gradPotentialNormSq
      potentialVariation metricVariationTrace metricVariationRicciHess :=
  formula510_of_connTrace (I := I) g hpotential hq
    (RicciFlower.Realized.connTraceField (I := I) g A)
    hmeas hfirst hfinal_int hdiv_int hshift_int hcorr_int
    hdivTrace hactionTrace hweighted hlap hgradSq hshift hqeq

/-- Formula 5.10 assembly with the raw divergence and action trace supplied by
the constructed field `tr_g A` itself.  The remaining geometric bridge is the
single pointwise identity saying the weighted-divergence component produced by
the `δ(Ric + Hess f)` calculation is `div(tr_g A) - (tr_g A)(f)`. -/
theorem formula510_of_trace
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M)
    (A : Tensor0SBundle.TensorRSField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 1 2)
    {firstVariation : Real}
    {scalarCurvature lapPotential gradPotentialNormSq potential
      potentialVariation metricVariationTrace metricVariationRicciHess
      weightedDivergenceTrace shiftedTrace q : M -> Real}
    (hpotential : ContMDiff I 𝓘(Real, Real) ∞ potential)
    (hq : ContMDiff I 𝓘(Real, Real) ∞ q)
    (hmeas :
      AEMeasurable
        (fun x : M => ENNReal.ofReal (expNegPotentialDensity potential x))
        (riemannianVolumeMeasure (I := I) (M := M) g))
    (hfirst :
      firstVariation =
        ∫ x,
          fFunctionalPre510Integrand scalarCurvature lapPotential
            gradPotentialNormSq potentialVariation metricVariationTrace
            metricVariationRicciHess weightedDivergenceTrace shiftedTrace x
          ∂(expNegPotentialWeightedMeasure
              (riemannianVolumeMeasure (I := I) (M := M) g) potential))
    (hfinal_int :
      Integrable
        (fFunctionalFormula510Integrand scalarCurvature lapPotential
          gradPotentialNormSq potentialVariation metricVariationTrace
          metricVariationRicciHess)
        (expNegPotentialWeightedMeasure
          (riemannianVolumeMeasure (I := I) (M := M) g) potential))
    (hdiv_int :
      Integrable weightedDivergenceTrace
        (expNegPotentialWeightedMeasure
          (riemannianVolumeMeasure (I := I) (M := M) g) potential))
    (hshift_int :
      Integrable shiftedTrace
        (expNegPotentialWeightedMeasure
          (riemannianVolumeMeasure (I := I) (M := M) g) potential))
    (hcorr_int :
      Integrable
        (fun x : M =>
          expWeightedMeasureVariationFactor potentialVariation
            metricVariationTrace x *
            (lapPotential x - gradPotentialNormSq x))
        (expNegPotentialWeightedMeasure
          (riemannianVolumeMeasure (I := I) (M := M) g) potential))
    (hweighted :
      ∀ x : M,
        weightedDivergenceTrace x =
          connTraceRawDiv (I := I) g A x -
            connTraceAction (I := I) g A potential x)
    (hlap :
      ∀ x : M,
        lapPotential x =
          RicciFlower.Analysis.DivergenceTheorem.Δ_g
            (I := I) g hpotential x)
    (hgradSq :
      ∀ x : M,
        gradPotentialNormSq x =
          g.inner x
            ((RicciFlower.Analysis.DivergenceTheorem.grad_g
              (I := I) g hpotential :
              Cₛ^∞⟮I; E, (TangentSpace I : M -> Type _)⟯) x)
            ((RicciFlower.Analysis.DivergenceTheorem.grad_g
              (I := I) g hpotential :
              Cₛ^∞⟮I; E, (TangentSpace I : M -> Type _)⟯) x))
    (hshift :
      ∀ x : M,
        shiftedTrace x =
          RicciFlower.Analysis.DivergenceTheorem.Δ_g
            (I := I) g hq x)
    (hqeq :
      ∀ x : M,
        q x = potentialVariation x - metricVariationTrace x / 2) :
    FFunctionalFormula510
      (expNegPotentialWeightedMeasure
        (riemannianVolumeMeasure (I := I) (M := M) g) potential)
      firstVariation scalarCurvature lapPotential gradPotentialNormSq
      potentialVariation metricVariationTrace metricVariationRicciHess := by
  exact formula510_of_connTraceField (I := I) g A hpotential hq hmeas
    hfirst hfinal_int hdiv_int hshift_int hcorr_int
    (rawTrace := connTraceRawDiv (I := I) g A)
    (actionTrace := connTraceAction (I := I) g A potential)
    (fun x => rfl)
    (connTraceAction_eq (I := I) g A potential)
    hweighted hlap hgradSq hshift hqeq

end GeometryFormula510

/-- Final assembly adapter for formula 5.10 once the previous producer chain has
identified the first-variation integrand pointwise. -/
theorem formula510_of_steps [MeasurableSpace M]
    {weightedMeasure : Measure M}
    {firstVariation : Real}
    {preIntegrand scalarCurvature lapPotential gradPotentialNormSq
      potentialVariation metricVariationTrace metricVariationRicciHess :
      M -> Real}
    (hfirst :
      firstVariation = ∫ x, preIntegrand x ∂weightedMeasure)
    (hpoint :
      ∀ x : M,
        preIntegrand x =
          fFunctionalFormula510Integrand scalarCurvature lapPotential
            gradPotentialNormSq potentialVariation metricVariationTrace
            metricVariationRicciHess x) :
    FFunctionalFormula510 weightedMeasure firstVariation scalarCurvature
      lapPotential gradPotentialNormSq potentialVariation metricVariationTrace
      metricVariationRicciHess := by
  unfold FFunctionalFormula510
  rw [hfirst]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall hpoint

/-- If formula 5.10 has been proved for the first variation value, then the
`deriv`-based first variation agrees with the formula 5.10 integral. -/
theorem fFunctionalFirstVariation_eq_formula510_of_hasFirstVariationAt
    [MeasurableSpace M]
    {muPath : Real -> Measure M}
    {scalarCurvaturePath gradPotentialNormSqPath potentialPath :
      Real -> M -> Real}
    {weightedMeasure : Measure M} {s0 firstVariation : Real}
    {scalarCurvature lapPotential gradPotentialNormSq potentialVariation
      metricVariationTrace metricVariationRicciHess : M -> Real}
    (hderiv :
      FFunctionalHasFirstVariationAt muPath scalarCurvaturePath
        gradPotentialNormSqPath potentialPath s0 firstVariation)
    (hformula :
      FFunctionalFormula510 weightedMeasure firstVariation scalarCurvature
        lapPotential gradPotentialNormSq potentialVariation
        metricVariationTrace metricVariationRicciHess) :
    fFunctionalFirstVariation muPath scalarCurvaturePath
        gradPotentialNormSqPath potentialPath s0 =
      ∫ x,
        fFunctionalFormula510Integrand scalarCurvature lapPotential
          gradPotentialNormSq potentialVariation metricVariationTrace
          metricVariationRicciHess x
        ∂weightedMeasure := by
  rw [fFunctionalFirstVariation_eq_of_hasFirstVariationAt hderiv]
  exact hformula

end

end Perelman
end RicciFlow
end RicciFlower
