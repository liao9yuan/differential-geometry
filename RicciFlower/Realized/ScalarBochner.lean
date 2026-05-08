import RicciFlower.Realized.Operators
import RicciFlower.Realized.CurvatureComponents
import RicciFlower.Realized.LeviCivita.MetricCompatibility
import RicciFlower.Realized.LeviCivita.Torsion
import RicciFlower.Tensor.RSTensor.Tensor0SRiemannian

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# Scalar Bochner Formula

This file contains the RicciFlower-facing scalar Bochner endpoint.  The fully
geometric work is split into named realized frontier hypotheses:

* the one-form norm product rule;
* the Weitzenbock/commutator identity for `du`.

The endpoint theorem below composes those two facts with the concrete realized
gradient/cotangent bridges.  No synthetic imports are used.
-/

noncomputable section

namespace RicciFlower
namespace Realized

open Bundle Tensor0SBundle
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [Module.Finite Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- The realized one-form `du`, represented as a `(0,1)` tensor. -/
def differential1FormFun (u : M -> Real) (x : M) :
    Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x :=
  dualToCotangent (I := I) (mfderiv I 𝓘(Real, Real) u x).toLinearMap

/-- Squared norm of the realized gradient of a scalar function. -/
def gradNormSq (g : SmoothRiemannianMetric I M) (u : M -> Real) : M -> Real :=
  fun x => g.inner x (gradientFun (I := I) g u x) (gradientFun (I := I) g u x)

/-- Squared norm of a supplied Hessian two-tensor. -/
def hessianNormSq
    (g : SmoothRiemannianMetric I M)
    (Hess : (x : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x) :
    M -> Real :=
  fun x => normSq0S (I := I) g x 2 (Hess x)

/-- The Ricci term in the scalar Bochner formula. -/
def ricciGradGrad
    (Ric : Tensor02Section (I := I) (M := M))
    (g : SmoothRiemannianMetric I M) (u : M -> Real) : M -> Real :=
  fun x => Ric x (vec2 (gradientFun (I := I) g u x) (gradientFun (I := I) g u x))

/-- Raising `du` by the metric recovers the realized gradient. -/
theorem cotangentSharp_differential1FormFun_eq_gradientFun
    (g : SmoothRiemannianMetric I M) (u : M -> Real) (x : M) :
    cotangentSharp (I := I) g x (differential1FormFun (I := I) u x) =
      gradientFun (I := I) g u x := by
  apply (metricFlatEquiv (I := I) g x).injective
  ext X
  change
    g.inner x (cotangentSharp (I := I) g x (differential1FormFun (I := I) u x)) X =
      g.inner x (gradientFun (I := I) g u x) X
  rw [cotangentSharp_inner, inner_gradientFun]
  rfl

/-- Inner product of `du` with `dv` is the metric inner product of gradients. -/
theorem inner0S_differential1FormFun_pair_eq_grad_inner
    (g : SmoothRiemannianMetric I M) (u v : M -> Real) (x : M) :
    inner0S (I := I) g x 1
        (differential1FormFun (I := I) u x)
        (differential1FormFun (I := I) v x) =
      g.inner x (gradientFun (I := I) g u x) (gradientFun (I := I) g v x) := by
  rw [Tensor0SBundle.inner0S_one_eq_cotangent, cotangentInner_eq_sharp]
  rw [cotangentSharp_differential1FormFun_eq_gradientFun,
    cotangentSharp_differential1FormFun_eq_gradientFun]

/-- The norm of `du` agrees with the squared norm of `grad u`. -/
theorem inner0S_differential1FormFun_eq_gradNormSq
    (g : SmoothRiemannianMetric I M) (u : M -> Real) (x : M) :
    inner0S (I := I) g x 1
        (differential1FormFun (I := I) u x)
        (differential1FormFun (I := I) u x) =
      gradNormSq (I := I) g u x := by
  rw [inner0S_differential1FormFun_pair_eq_grad_inner]
  rfl

/-! ## Named Bochner frontier hypotheses -/

/-- The one-form norm product rule at a point.

Mathematically this is
`1/2 Δ |α|² = <roughΔ α, α> + |∇α|²`.  The rough Laplacian one-form and
the covariant-derivative two-tensor are supplied explicitly until the tensor
rough-Laplacian API is bundled. -/
def OneFormNormBochnerAt
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (g : SmoothRiemannianMetric I M)
    (α roughAlpha : (x : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x)
    (nablaAlpha : (x : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    (x : M) : Prop :=
  (1 / 2 : Real) *
      laplacian (I := I) cov g
        (fun y : M => inner0S (I := I) g y 1 (α y) (α y)) x =
    inner0S (I := I) g x 1 (roughAlpha x) (α x) +
      normSq0S (I := I) g x 2 (nablaAlpha x)

/-- The commutator/Weitzenbock identity for the differential one-form `du`,
paired with `du`.

Mathematically this packages
`roughΔ(du) = d(Δu) + Ric(du)` after pairing with `du`. -/
def DifferentialOneFormCommutatorAt
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (g : SmoothRiemannianMetric I M)
    (Ric : Tensor02Section (I := I) (M := M))
    (u : M -> Real)
    (roughDu : (x : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x)
    (x : M) : Prop :=
  inner0S (I := I) g x 1 (roughDu x) (differential1FormFun (I := I) u x) =
    inner0S (I := I) g x 1
        (differential1FormFun (I := I) (laplacian (I := I) cov g u) x)
        (differential1FormFun (I := I) u x) +
      ricciGradGrad (I := I) Ric g u x

/-- The covariant derivative of `du` realizes the Hessian norm used in the
scalar Bochner formula. -/
def HessianNormRealizesNablaDifferentialAt
    (g : SmoothRiemannianMetric I M)
    (Hess nablaDu : (x : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    (x : M) : Prop :=
  normSq0S (I := I) g x 2 (nablaDu x) =
    hessianNormSq (I := I) g Hess x

/-- Scalar Bochner formula, assembled from the realized one-form product rule
and the realized commutator identity for `du`.

The Levi-Civita and Ricci-trace hypotheses are explicit in the statement
because those are the geometric sources of the two frontier identities. -/
theorem half_laplacian_gradNormSq_eq
    {Idx : Type*} [Fintype Idx]
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (g : SmoothRiemannianMetric I M)
    (Ric : Tensor02Section (I := I) (M := M))
    (Rm04 : Tensor04Section (I := I) (M := M))
    (gInv : InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (_hlc : LeviCivita.IsLeviCivita (I := I) cov g)
    (_hRic : RicciTensorRealizesRm04TraceInFrame (I := I) Ric Rm04 gInv frame)
    (u : M -> Real)
    (Hess nablaDu : (x : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    (roughDu : (x : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x)
    (x : M)
    (h_norm : OneFormNormBochnerAt (I := I) cov g
      (differential1FormFun (I := I) u) roughDu nablaDu x)
    (h_comm : DifferentialOneFormCommutatorAt (I := I) cov g Ric u roughDu x)
    (h_hess : HessianNormRealizesNablaDifferentialAt (I := I) g Hess nablaDu x) :
    (1 / 2 : Real) * laplacian (I := I) cov g (gradNormSq (I := I) g u) x =
      g.inner x
          (gradientFun (I := I) g (laplacian (I := I) cov g u) x)
          (gradientFun (I := I) g u x) +
        hessianNormSq (I := I) g Hess x +
          ricciGradGrad (I := I) Ric g u x := by
  have h_norm_fun :
      (fun y : M =>
          inner0S (I := I) g y 1
            (differential1FormFun (I := I) u y)
            (differential1FormFun (I := I) u y)) =
        gradNormSq (I := I) g u := by
    funext y
    exact inner0S_differential1FormFun_eq_gradNormSq (I := I) g u y
  rw [← h_norm_fun]
  rw [h_norm, h_comm, h_hess]
  rw [inner0S_differential1FormFun_pair_eq_grad_inner]
  ring

end Realized
end RicciFlower
