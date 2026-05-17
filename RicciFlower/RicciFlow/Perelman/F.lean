/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RicciFlower contributors
-/

import RicciFlower.Analysis.Green
import RicciFlower.LeviCivita.Variation
import RicciFlower.RicciFlow.Perelman.Variation

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
