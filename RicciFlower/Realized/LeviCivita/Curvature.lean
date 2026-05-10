import RicciFlower.Realized.CurvatureComponents
import RicciFlower.Realized.LeviCivita.Torsion
import RicciFlower.Tensor.RSTensor.NablaOnTensors.Connection

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# Levi-Civita curvature endpoints

This file localizes the geometric Levi-Civita curvature facts needed by scalar
Bochner.  Generic curvature realization predicates remain in
`RicciFlower.Realized.CurvatureComponents`; this file only specializes them to
`leviCivitaConnectionOfMetric`.
-/

noncomputable section

namespace RicciFlower
namespace Realized
namespace LeviCivita

open Bundle Tensor0SBundle
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [IsManifold I 1 M] [IsManifold I 2 M] [IsManifold I 3 M]
variable [IsManifold I ((⊤ : WithTop ℕ∞) + 1) M]
variable [SigmaCompactSpace M] [T2Space M]

/-- The scalar Lie bracket acts as the commutator of directional derivatives.

This is the local scalar-calculus identity used by the metric-compatibility
curvature skew calculation.  The eventual proof should come from the same
chart-pullback theorem as `VectorField.fderiv_apply_lieBracket`, specialized to
`extDerivFun`. -/
theorem directionalDeriv_directionalDeriv_sub_commutator
    (X Y : (p : M) -> TangentSpace I p) (f : M -> Real) (x : M)
    (hX : ContMDiffAt I (I.prod 𝓘(Real, E)) (minSmoothness Real 2) (T% X) x)
    (hY : ContMDiffAt I (I.prod 𝓘(Real, E)) (minSmoothness Real 2) (T% Y) x)
    (hf : ContMDiffAt I 𝓘(Real, Real) (minSmoothness Real 2) f x) :
    directionalDeriv (I := I) X (fun y : M => directionalDeriv (I := I) Y f y) x -
        directionalDeriv (I := I) Y (fun y : M => directionalDeriv (I := I) X f y) x -
          directionalDeriv (I := I) (VectorField.mlieBracket I X Y) f x = 0 := by
  -- Frontier: pull back to the extended chart and apply
  -- `VectorField.fderiv_apply_lieBracket`.
  sorry

/-- Metric-compatible curvature endomorphisms are skew-adjoint in the metric.

The proof uses only metric compatibility.  The tangent-constant covariant
derivative smoothness facts are supplied by
`CovariantDerivative.tangentConst_cov_mdiffAt`; the remaining local scalar
commutator expansion is isolated in
`directionalDeriv_directionalDeriv_sub_commutator`. -/
private theorem connectionRiemannCurvatureField_metric_skew_at_of_metricCompatible
    (g : SmoothRiemannianMetric I M)
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov
      (1 : WithTop ℕ∞))
    (hmc : IsMetricCompatible (I := I) cov g)
    {x : M} (W X Y Z : TangentSpace I x) :
    g.inner x W
        ((connectionRiemannCurvatureField (I := I) cov
          (tangentConstAt (I := I) x X)
          (tangentConstAt (I := I) x Y)
          (tangentConstAt (I := I) x Z)) x) =
      -g.inner x Z
        ((connectionRiemannCurvatureField (I := I) cov
          (tangentConstAt (I := I) x X)
          (tangentConstAt (I := I) x Y)
          (tangentConstAt (I := I) x W)) x) := by
  have hX : MDiffAt
      (T% (tangentConstAt (I := I) x X : (p : M) -> TangentSpace I p)) x :=
    mdifferentiableAt_tangentConstAt_self (I := I) x X
  have hY : MDiffAt
      (T% (tangentConstAt (I := I) x Y : (p : M) -> TangentSpace I p)) x :=
    mdifferentiableAt_tangentConstAt_self (I := I) x Y
  have hZ : MDiffAt
      (T% (tangentConstAt (I := I) x Z : (p : M) -> TangentSpace I p)) x :=
    mdifferentiableAt_tangentConstAt_self (I := I) x Z
  have hW : MDiffAt
      (T% (tangentConstAt (I := I) x W : (p : M) -> TangentSpace I p)) x :=
    mdifferentiableAt_tangentConstAt_self (I := I) x W
  have hYZ : MDiffAt
      (T% (fun p : M =>
        (cov (tangentConstAt (I := I) x Z) p)
          ((tangentConstAt (I := I) x Y) p))) x := by
    simpa [tangentConstAt] using
      CovariantDerivative.tangentConst_cov_mdiffAt
        (𝕜 := Real) (I := I) cov hcov (x := x) (v := Y) (w := Z)
  have hYW : MDiffAt
      (T% (fun p : M =>
        (cov (tangentConstAt (I := I) x W) p)
          ((tangentConstAt (I := I) x Y) p))) x := by
    simpa [tangentConstAt] using
      CovariantDerivative.tangentConst_cov_mdiffAt
        (𝕜 := Real) (I := I) cov hcov (x := x) (v := Y) (w := W)
  have hXZ : MDiffAt
      (T% (fun p : M =>
        (cov (tangentConstAt (I := I) x Z) p)
          ((tangentConstAt (I := I) x X) p))) x := by
    simpa [tangentConstAt] using
      CovariantDerivative.tangentConst_cov_mdiffAt
        (𝕜 := Real) (I := I) cov hcov (x := x) (v := X) (w := Z)
  have hXW : MDiffAt
      (T% (fun p : M =>
        (cov (tangentConstAt (I := I) x W) p)
          ((tangentConstAt (I := I) x X) p))) x := by
    simpa [tangentConstAt] using
      CovariantDerivative.tangentConst_cov_mdiffAt
        (𝕜 := Real) (I := I) cov hcov (x := x) (v := X) (w := W)
  have hmetric_ZW :=
    RicciFlower.Realized.metric_compatible_apply (I := I) hmc
      (tangentConstAt (I := I) x X)
      (tangentConstAt (I := I) x Z)
      (tangentConstAt (I := I) x W) hX hZ hW
  have hmetric_YZ_W :=
    RicciFlower.Realized.metric_compatible_apply (I := I) hmc
      (tangentConstAt (I := I) x X)
      (fun p : M =>
        (cov (tangentConstAt (I := I) x Z) p)
          ((tangentConstAt (I := I) x Y) p))
      (tangentConstAt (I := I) x W) hX hYZ hW
  have hmetric_YW_Z :=
    RicciFlower.Realized.metric_compatible_apply (I := I) hmc
      (tangentConstAt (I := I) x X)
      (tangentConstAt (I := I) x Z)
      (fun p : M =>
        (cov (tangentConstAt (I := I) x W) p)
          ((tangentConstAt (I := I) x Y) p)) hX hZ hYW
  -- Frontier: combine the metric-compatibility expansions above with the
  -- corresponding `Y`-derivative expansions and the scalar Lie-bracket
  -- commutator identity, then cancel the mixed terms exactly as in the
  -- textbook proof.
  sorry

/-- The lowered Levi-Civita curvature tensor is skew-adjoint in the output
slot. -/
theorem rm04OutputSkewAt_of_leviCivita_realizes
    (g : SmoothRiemannianMetric I M)
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally
      (leviCivitaConnectionOfMetric (I := I) g) (1 : WithTop ℕ∞))
    (Rm04 : Tensor04Section (I := I) (M := M))
    (hRm04 : Rm04RealizesConnection (I := I) g
      (leviCivitaConnectionOfMetric (I := I) g) Rm04)
    {x : M} :
    Rm04OutputSkewAt (I := I) (Rm04 x) := by
  intro W X Y Z
  let Wsec : (p : M) -> TangentSpace I p := tangentConstAt (I := I) x W
  let Xsec : (p : M) -> TangentSpace I p := tangentConstAt (I := I) x X
  let Ysec : (p : M) -> TangentSpace I p := tangentConstAt (I := I) x Y
  let Zsec : (p : M) -> TangentSpace I p := tangentConstAt (I := I) x Z
  have hleft := hRm04 Wsec Xsec Ysec Zsec x
  have hright := hRm04 Zsec Xsec Ysec Wsec x
  have hskew :=
    connectionRiemannCurvatureField_metric_skew_at_of_metricCompatible
      (I := I) g (leviCivitaConnectionOfMetric (I := I) g) hcov
      (leviCivitaConnectionOfMetric_isMetricCompatible (I := I) g) W X Y Z
  dsimp [Wsec, Xsec, Ysec, Zsec] at hleft hright
  rw [tangentConstAt_self] at hleft
  rw [tangentConstAt_self] at hleft
  rw [tangentConstAt_self] at hleft
  rw [tangentConstAt_self] at hleft
  rw [tangentConstAt_self] at hright
  rw [tangentConstAt_self] at hright
  rw [tangentConstAt_self] at hright
  rw [tangentConstAt_self] at hright
  exact hleft.trans (hskew.trans (congrArg (fun r : Real => -r) hright.symm))

/-- The `(1,3)` Levi-Civita curvature tensor is metric-skew in the output
slot. -/
theorem rm13MetricSkewAt_of_leviCivita_realizes
    (g : SmoothRiemannianMetric I M)
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally
      (leviCivitaConnectionOfMetric (I := I) g) (1 : WithTop ℕ∞))
    (Rm13 : Tensor13Section (I := I) (M := M))
    (Rm04 : Tensor04Section (I := I) (M := M))
    (hRm13 : Rm13RealizesConnection (I := I)
      (leviCivitaConnectionOfMetric (I := I) g) Rm13)
    (hRm04 : Rm04RealizesConnection (I := I) g
      (leviCivitaConnectionOfMetric (I := I) g) Rm04)
    {x : M} :
    Rm13MetricSkewAt (I := I) g x (Rm13 x) :=
  rm13MetricSkewAt_of_realizes_outputSkew (I := I) g
    (leviCivitaConnectionOfMetric (I := I) g) Rm13 Rm04 hRm13 hRm04
    (rm04OutputSkewAt_of_leviCivita_realizes (I := I) g hcov Rm04 hRm04)

/-- Levi-Civita Ricci identity for the third covariant derivative of a
one-form. -/
theorem oneFormThirdCovDerivCommAt_of_leviCivita
    (g : SmoothRiemannianMetric I M)
    (Rm13 : Tensor13Section (I := I) (M := M))
    (alphaSec : OneFormSection (I := I) (M := M))
    (nablaAlphaSec : TwoTensorSection (I := I) (M := M))
    {x : M}
    (alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x)
    (nabla2Alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (hRm13 : Rm13RealizesConnection (I := I)
      (leviCivitaConnectionOfMetric (I := I) g) Rm13)
    (halpha : alphaSec x = alpha)
    (hnabla2 : Nabla2OneFormRealizesAt (I := I)
      (leviCivitaConnectionOfMetric (I := I) g) alphaSec nablaAlphaSec x
      nabla2Alpha) :
    OneFormThirdCovDerivCommAt (I := I) Rm13 alpha nabla2Alpha := by
  -- Frontier: use coordinate-frame expansion of `nabla0SFun` on one-forms,
  -- commute scalar second derivatives, identify the remaining Christoffel
  -- terms with `Rm13` using `connection_curvature_coord_of_christoffel`, and
  -- promote from coordinate components with `one_form_third_comm_of_coord_ijk`.
  sorry

end LeviCivita
end Realized
end RicciFlower
