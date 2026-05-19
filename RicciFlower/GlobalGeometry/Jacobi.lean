import RicciFlower.GlobalGeometry.Lecture07.PullbackConnection
import RicciFlower.Riemann.Basic

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# Pullback Jacobi fields

This file is the canonical global-geometry layer for Jacobi fields.  It uses
the pullback covariant-derivative relation from Lecture 7.3 rather than the
older global-extension predicate.

The curvature term is stated in the pointwise `(1,3)` tensor API:
`riemannCurvatureAt cov hcov x`.  Since RicciFlower does not yet expose a
general vector-valued public action `R(X,Y)Z`, the Jacobi equation is tested
against all cotangent vectors.  This keeps the statement intrinsic and avoids
returning to ambient vector-field representatives.
-/

noncomputable section

namespace RicciFlower
namespace GlobalGeometry

open Bundle Filter Tensor0SBundle RicciFlower.Curvature
open scoped Manifold ContDiff Topology

open Lecture07

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

variable [VectorBundle Real E (TangentSpace I : M -> Type _)]

/-! ## Two-parameter variations -/

/-- A two-parameter surface used for geodesic variations.  The first parameter
is the variation parameter and the second is the curve time. -/
abbrev Surface (M : Type*) := Real × Real -> M

/-- The time curve `t ↦ F (s,t)` in a variation. -/
def timeCurve (F : Surface M) (s : Real) : Curve M :=
  fun t => F (s, t)

/-- The parameter curve `s ↦ F (s,t)` through a fixed time. -/
def paramCurve (F : Surface M) (t : Real) : Curve M :=
  fun s => F (s, t)

/-- Velocity in the time direction of a two-parameter surface. -/
def timeField (I : ModelWithCorners Real E H) (F : Surface M) :
    (p : Real × Real) -> TangentSpace I (F p) :=
  fun p => curveVelocity I (timeCurve F p.1) p.2

/-- Velocity in the variation-parameter direction of a two-parameter surface. -/
def paramField (I : ModelWithCorners Real E H) (F : Surface M) :
    (p : Real × Real) -> TangentSpace I (F p) :=
  fun p => curveVelocity I (paramCurve F p.2) p.1

/-- The variation field along the base curve `t ↦ F (s0,t)`. -/
def variationField (I : ModelWithCorners Real E H) (F : Surface M)
    (s0 : Real) : VectorFieldAlong I (timeCurve F s0) :=
  fun t => curveVelocity I (paramCurve F t) s0

/-- Smoothness of a two-parameter variation as a map from the product model. -/
def SmoothSurface (I : ModelWithCorners Real E H) (F : Surface M) : Prop :=
  ContMDiff (𝓘(Real, Real).prod 𝓘(Real, Real)) I ∞ F

/-! ## Surface fields and curve restrictions -/

/-- A tangent field along a two-parameter surface. -/
abbrev SurfaceField (I : ModelWithCorners Real E H) (F : Surface M) :=
  (p : Real × Real) -> TangentSpace I (F p)

/-- Restrict a surface field to the time curve `t ↦ F (s,t)`. -/
def timeRestrictField (I : ModelWithCorners Real E H) (F : Surface M)
    (V : SurfaceField I F) (s : Real) :
    VectorFieldAlong I (timeCurve F s) :=
  fun t => V (s, t)

/-- Restrict a surface field to the parameter curve `s ↦ F (s,t)`. -/
def paramRestrictField (I : ModelWithCorners Real E H) (F : Surface M)
    (V : SurfaceField I F) (t : Real) :
    VectorFieldAlong I (paramCurve F t) :=
  fun s => V (s, t)

/-- An ambient field realizes a surface field near a parameter point. -/
def SurfaceFieldRealizedByAt (F : Surface M) (V : SurfaceField I F)
    (X : GlobalVectorField I M) (p : Real × Real) : Prop :=
  ∀ᶠ q in 𝓝 p, V q = X (F q)

/-- A surface-field representative restricts to a pullback derivative along a
time curve. -/
theorem surfTime_rep
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    {F : Surface M} {V : SurfaceField I F} {X : GlobalVectorField I M}
    {s0 t : Real}
    (hγ : MDifferentiableAt 𝓘(Real, Real) I (timeCurve F s0) t)
    (hX : MDiffSectionAt (I := I) (F := E) (V := TangentSpace I) X (F (s0, t)))
    (hVX : SurfaceFieldRealizedByAt (I := I) F V X (s0, t)) :
    HasPullbackCovariantDerivativeAlongCurveAt (I := I) cov (timeCurve F s0)
      (timeRestrictField I F V s0) t
      ((cov X (F (s0, t))) (curveVelocity I (timeCurve F s0) t)) := by
  have hmap :
      Tendsto (fun τ : Real => (s0, τ)) (𝓝 t) (𝓝 (s0, t)) :=
    (ContinuousAt.prodMk continuousAt_const continuousAt_id).tendsto
  refine ⟨hγ, X, ⟨hX, ?_⟩, rfl⟩
  filter_upwards [hmap.eventually hVX] with τ hτ
  simpa [timeRestrictField, timeCurve] using hτ

/-- A surface-field representative restricts to a pullback derivative along a
parameter curve. -/
theorem surfParam_rep
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    {F : Surface M} {V : SurfaceField I F} {X : GlobalVectorField I M}
    {s t0 : Real}
    (hγ : MDifferentiableAt 𝓘(Real, Real) I (paramCurve F t0) s)
    (hX : MDiffSectionAt (I := I) (F := E) (V := TangentSpace I) X (F (s, t0)))
    (hVX : SurfaceFieldRealizedByAt (I := I) F V X (s, t0)) :
    HasPullbackCovariantDerivativeAlongCurveAt (I := I) cov (paramCurve F t0)
      (paramRestrictField I F V t0) s
      ((cov X (F (s, t0))) (curveVelocity I (paramCurve F t0) s)) := by
  have hmap :
      Tendsto (fun σ : Real => (σ, t0)) (𝓝 s) (𝓝 (s, t0)) :=
    (ContinuousAt.prodMk continuousAt_id continuousAt_const).tendsto
  refine ⟨hγ, X, ⟨hX, ?_⟩, rfl⟩
  filter_upwards [hmap.eventually hVX] with σ hσ
  simpa [paramRestrictField, paramCurve] using hσ

/-- A surface-field representative restricts to the canonical frame-defined
pullback derivative along a time curve. -/
theorem surfTime_frame
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    {F : Surface M} {V : SurfaceField I F} {X : GlobalVectorField I M}
    {s0 t : Real}
    (hγ : MDifferentiableAt 𝓘(Real, Real) I (timeCurve F s0) t)
    (hX : MDiffSectionAt (I := I) (F := E) (V := TangentSpace I) X (F (s0, t)))
    (hVX : SurfaceFieldRealizedByAt (I := I) F V X (s0, t)) :
    HasPBCovAlongAt (I := I) cov (timeCurve F s0)
      (timeRestrictField I F V s0) t
      ((cov X (F (s0, t))) (curveVelocity I (timeCurve F s0) t)) := by
  exact (surfTime_rep (I := I) (cov := cov) hγ hX hVX).toPBCov

/-- A surface-field representative restricts to the canonical frame-defined
pullback derivative along a parameter curve. -/
theorem surfParam_frame
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    {F : Surface M} {V : SurfaceField I F} {X : GlobalVectorField I M}
    {s t0 : Real}
    (hγ : MDifferentiableAt 𝓘(Real, Real) I (paramCurve F t0) s)
    (hX : MDiffSectionAt (I := I) (F := E) (V := TangentSpace I) X (F (s, t0)))
    (hVX : SurfaceFieldRealizedByAt (I := I) F V X (s, t0)) :
    HasPBCovAlongAt (I := I) cov (paramCurve F t0)
      (paramRestrictField I F V t0) s
      ((cov X (F (s, t0))) (curveVelocity I (paramCurve F t0) s)) := by
  exact (surfParam_rep (I := I) (cov := cov) hγ hX hVX).toPBCov

/-! ## Pullback Jacobi equation -/

/-- A second covariant derivative along a curve, using the canonical
frame-defined pullback derivative relation. -/
def HasSecondPullbackDerivAt
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (gamma : Curve M) (J : VectorFieldAlong I gamma) (t : Real)
    (A : TangentSpace I (gamma t)) : Prop :=
  ∃ W : VectorFieldAlong I gamma,
    HasPBCovAlongAt (I := I) cov gamma J t (W t) ∧
      HasPBCovAlongAt (I := I) cov gamma W t A

/-- The pointwise curvature scalar `α (R(J,γ')γ')`.

This is the public curvature term for the current Jacobi API.  It is
cotangent-tested because the available pointwise curvature object is the
RicciFlower `(1,3)` tensor `riemannCurvatureAt`. -/
def curvatureAlongScalarAt
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov ∞)
    (gamma : Curve M) (J : VectorFieldAlong I gamma) (t : Real)
    (α : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      1 (gamma t)) : Real :=
  Riemann.CovariantDerivative.riemannCurvatureAt (I := I) cov hcov (gamma t) α
    (vec3 (I := I) (J t) (curveVelocity I gamma t) (curveVelocity I gamma t))

/-- Pointwise Jacobi equation along a curve.

The equation is
`D_t^2 J + R(J,γ')γ' = 0`, tested against every cotangent vector at the point. -/
def IsJacobiFieldAt
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov ∞)
    (gamma : Curve M) (J : VectorFieldAlong I gamma) (t : Real) : Prop :=
  ∃ A : TangentSpace I (gamma t),
    HasSecondPullbackDerivAt (I := I) cov gamma J t A ∧
      ∀ α : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
          1 (gamma t),
        cotangentToDual (I := I) α A +
            curvatureAlongScalarAt (I := I) cov hcov gamma J t α = 0

/-- Jacobi equation on a set of parameter values. -/
def IsJacobiFieldOn
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov ∞)
    (gamma : Curve M) (J : VectorFieldAlong I gamma) (T : Set Real) : Prop :=
  ∀ t ∈ T, IsJacobiFieldAt (I := I) cov hcov gamma J t

/-! ## Formal geodesic-variation identities -/

/-- A geodesic variation on a rectangle of parameter values. -/
def IsGeodesicVariationOn
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (F : Surface M) (S T : Set Real) : Prop :=
  ∀ s ∈ S, ∀ t ∈ T,
    HasPBCovAccelAt (I := I) cov (timeCurve F s) t 0

/-- Torsion/mixed-derivative swap data at one point of a variation.

`W` is both the time covariant derivative of the variation field and the
parameter covariant derivative of the time field.  This is the canonical
pullback version of `D_t S = D_s T`. -/
def VariationTorsionSwapAt
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (F : Surface M) (s0 t : Real)
    (W : VectorFieldAlong I (timeCurve F s0)) : Prop :=
  HasPBCovAlongAt (I := I) cov (timeCurve F s0)
      (variationField I F s0) t (W t) ∧
    HasPBCovAlongAt (I := I) cov (paramCurve F t)
      (paramRestrictField I F (timeField I F) t) s0 (W t)

/-- Curvature commutator data after differentiating the geodesic equation.

Together with `VariationTorsionSwapAt`, this supplies the second derivative of
the variation field and the curvature term in the Jacobi equation. -/
def VariationCurvCommAt
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov ∞)
    (F : Surface M) (s0 t : Real)
    (W : VectorFieldAlong I (timeCurve F s0)) : Prop :=
  ∃ A : TangentSpace I (timeCurve F s0 t),
    HasPBCovAlongAt (I := I) cov (timeCurve F s0) W t A ∧
      ∀ α : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
          1 (timeCurve F s0 t),
        cotangentToDual (I := I) α A +
            curvatureAlongScalarAt (I := I) cov hcov
              (timeCurve F s0) (variationField I F s0) t α = 0

/-! ## Representative-level identities -/

/-- Representative-level torsion swap.

For a torsion-free pair with zero Lie bracket at the point, the two first
covariant derivatives agree.  This is the algebraic core of
`D_t S = D_s T`. -/
theorem torsionSwap_rep
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    {X Y : GlobalVectorField I M} {x : M}
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x)
    (htor : cov.torsion x (X x) (Y x) = 0)
    (hbracket : VectorField.mlieBracket I X Y x = 0) :
    (cov Y x) (X x) = (cov X x) (Y x) := by
  have htor_apply := cov.torsion_apply (I := I) (x := x) hX hY
  rw [htor_apply] at htor
  have hsub : (cov Y x) (X x) - (cov X x) (Y x) = 0 := by
    simpa [hbracket, sub_eq_add_neg] using htor
  exact sub_eq_zero.mp hsub

/-- Representative-level producer for the canonical pullback torsion swap.

If ambient fields realize the time and parameter velocity fields near the
surface point, and the torsion and bracket terms vanish there, then
`D_t S = D_s T` in the frame-defined pullback derivative API. -/
theorem torsionSwap_frame
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    {F : Surface M} {s0 t : Real} {X Y : GlobalVectorField I M}
    (hγt : MDifferentiableAt 𝓘(Real, Real) I (timeCurve F s0) t)
    (hγs : MDifferentiableAt 𝓘(Real, Real) I (paramCurve F t) s0)
    (hX : MDiffSectionAt (I := I) (F := E) (V := TangentSpace I) X (F (s0, t)))
    (hY : MDiffSectionAt (I := I) (F := E) (V := TangentSpace I) Y (F (s0, t)))
    (hTX : SurfaceFieldRealizedByAt (I := I) F (timeField I F) X (s0, t))
    (hSY : SurfaceFieldRealizedByAt (I := I) F (paramField I F) Y (s0, t))
    (htor : cov.torsion (F (s0, t)) (X (F (s0, t))) (Y (F (s0, t))) = 0)
    (hbracket : VectorField.mlieBracket I X Y (F (s0, t)) = 0) :
    VariationTorsionSwapAt (I := I) cov F s0 t
      (fun τ => (cov X (F (s0, τ))) (curveVelocity I (paramCurve F τ) s0)) := by
  let W : VectorFieldAlong I (timeCurve F s0) :=
    fun τ => (cov X (F (s0, τ))) (curveVelocity I (paramCurve F τ) s0)
  have hTX₀ : timeField I F (s0, t) = X (F (s0, t)) :=
    hTX.self_of_nhds
  have hSY₀ : paramField I F (s0, t) = Y (F (s0, t)) :=
    hSY.self_of_nhds
  have hswap_raw :
      (cov Y (F (s0, t))) (X (F (s0, t))) =
        (cov X (F (s0, t))) (Y (F (s0, t))) :=
    torsionSwap_rep (I := I) (cov := cov)
      (X := X) (Y := Y) (x := F (s0, t))
      (mdiffSectionAt_tPercent (I := I) (F := E) (V := TangentSpace I) hX)
      (mdiffSectionAt_tPercent (I := I) (F := E) (V := TangentSpace I) hY)
      htor hbracket
  have hswap :
      (cov Y (F (s0, t))) (curveVelocity I (timeCurve F s0) t) = W t := by
    have h := hswap_raw
    rw [← hTX₀, ← hSY₀] at h
    simpa [W, timeField, paramField, timeCurve, paramCurve] using h
  have htime :
      HasPBCovAlongAt (I := I) cov (timeCurve F s0)
        (variationField I F s0) t (W t) := by
    have hrep :=
      surfTime_frame (I := I) (cov := cov)
        (F := F) (V := paramField I F) (X := Y)
        (s0 := s0) (t := t) hγt hY hSY
    rw [← hswap]
    simpa [timeRestrictField, variationField, paramField] using hrep
  have hparam :
      HasPBCovAlongAt (I := I) cov (paramCurve F t)
        (paramRestrictField I F (timeField I F) t) s0 (W t) := by
    have hrep :=
      surfParam_frame (I := I) (cov := cov)
        (F := F) (V := timeField I F) (X := X)
        (s := s0) (t0 := t) hγs hX hTX
    simpa [W, paramRestrictField, timeField, paramCurve] using hrep
  exact ⟨htime, hparam⟩

/-- Curvature along a curve computed by smooth ambient representatives. -/
theorem curvScalar_rep
    [T2Space M]
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    {hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov ∞}
    {gamma : Curve M} {J : VectorFieldAlong I gamma} {t : Real}
    (X Y : ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _))
    (hX : X (gamma t) = J t)
    (hY : Y (gamma t) = curveVelocity I gamma t)
    (α : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      1 (gamma t)) :
    curvatureAlongScalarAt (I := I) cov hcov gamma J t α =
      cotangentToDual (I := I) α
        (connectionRiemannCurvatureField (I := I) cov
          (fun p : M => X p) (fun p : M => Y p) (fun p : M => Y p)
          (gamma t)) := by
  simpa [curvatureAlongScalarAt, hX, hY] using
    (Riemann.CovariantDerivative.riemannCurvatureAt_apply_smooth
      (I := I) cov hcov X Y Y α)

/-- The cotangent-tested Jacobi scalar equation for the negative curvature
representative. -/
theorem jacobiScalar_rep
    [T2Space M]
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    {hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov ∞}
    {gamma : Curve M} {J : VectorFieldAlong I gamma} {t : Real}
    (X Y : ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _))
    (hX : X (gamma t) = J t)
    (hY : Y (gamma t) = curveVelocity I gamma t)
    (α : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      1 (gamma t)) :
    cotangentToDual (I := I) α
        (-(connectionRiemannCurvatureField (I := I) cov
          (fun p : M => X p) (fun p : M => Y p) (fun p : M => Y p)
          (gamma t))) +
      curvatureAlongScalarAt (I := I) cov hcov gamma J t α = 0 := by
  let R : TangentSpace I (gamma t) :=
    connectionRiemannCurvatureField (I := I) cov
      (fun p : M => X p) (fun p : M => Y p) (fun p : M => Y p)
      (gamma t)
  change cotangentToDual (I := I) α (-R) +
      curvatureAlongScalarAt (I := I) cov hcov gamma J t α = 0
  rw [curvScalar_rep (I := I) (cov := cov) (hcov := hcov)
    (gamma := gamma) (J := J) (t := t) X Y hX hY α]
  have hdual :
      cotangentToDual (I := I) α (-R) + cotangentToDual (I := I) α R = 0 := by
    rw [map_neg]
    exact neg_add_cancel _
  simpa [cotangentToDual_apply] using hdual

/-- A frame-defined curvature commutator value supplies
`VariationCurvCommAt`.

The derivative witness is already in the canonical pullback API; smooth ambient
representatives are used only to identify the pointwise curvature scalar with
RicciFlower's current `riemannCurvatureAt` tensor API. -/
theorem curvComm_frame
    [T2Space M]
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    {hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov ∞}
    {F : Surface M} {s0 t : Real}
    {W : VectorFieldAlong I (timeCurve F s0)}
    {A : TangentSpace I (timeCurve F s0 t)}
    (X Y : ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _))
    (hWA : HasPBCovAlongAt (I := I) cov (timeCurve F s0) W t A)
    (hA : A =
      -(connectionRiemannCurvatureField (I := I) cov
        (fun p : M => X p) (fun p : M => Y p) (fun p : M => Y p)
        (timeCurve F s0 t)))
    (hX : X (timeCurve F s0 t) = variationField I F s0 t)
    (hY : Y (timeCurve F s0 t) = curveVelocity I (timeCurve F s0) t) :
    VariationCurvCommAt (I := I) cov hcov F s0 t W := by
  refine ⟨A, hWA, ?_⟩
  intro α
  rw [hA]
  exact jacobiScalar_rep (I := I) (cov := cov) (hcov := hcov)
    (gamma := timeCurve F s0) (J := variationField I F s0) (t := t)
    X Y hX hY α

/-- A representative-level curvature commutator value supplies
`VariationCurvCommAt`. -/
theorem curvComm_rep
    [T2Space M]
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    {hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov ∞}
    {F : Surface M} {s0 t : Real}
    {W : VectorFieldAlong I (timeCurve F s0)}
    {A : TangentSpace I (timeCurve F s0 t)}
    (X Y : ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _))
    (hWA : HasPullbackCovariantDerivativeAlongCurveAt (I := I) cov
      (timeCurve F s0) W t A)
    (hA : A =
      -(connectionRiemannCurvatureField (I := I) cov
        (fun p : M => X p) (fun p : M => Y p) (fun p : M => Y p)
        (timeCurve F s0 t)))
    (hX : X (timeCurve F s0 t) = variationField I F s0 t)
    (hY : Y (timeCurve F s0 t) = curveVelocity I (timeCurve F s0) t) :
    VariationCurvCommAt (I := I) cov hcov F s0 t W :=
  curvComm_frame (I := I) (cov := cov) (hcov := hcov)
    (F := F) (s0 := s0) (t := t) (W := W) (A := A)
    X Y hWA.toPBCov hA hX hY

/-- The formal Jacobi-field theorem for a geodesic variation.

The geometric producer of `hswap` and `hcomm` is intentionally kept separate.
For the current representative-based pullback derivative, smooth surface data
alone is not enough; see the note below. -/
theorem jacobi_of_variation
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    {hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov ∞}
    {F : Surface M} {S T : Set Real} {s0 : Real}
    {W : VectorFieldAlong I (timeCurve F s0)}
    (_hgeo : IsGeodesicVariationOn (I := I) cov F S T)
    (hswap : ∀ t ∈ T, VariationTorsionSwapAt (I := I) cov F s0 t W)
    (hcomm : ∀ t ∈ T, VariationCurvCommAt (I := I) cov hcov F s0 t W) :
    IsJacobiFieldOn (I := I) cov hcov (timeCurve F s0)
      (variationField I F s0) T := by
  intro t ht
  rcases hcomm t ht with ⟨A, hWA, hscalar⟩
  refine ⟨A, ?_, hscalar⟩
  exact ⟨W, (hswap t ht).1, hWA⟩

/-!
The tempting producer

```
SmoothSurface F →
cov.torsion = 0 →
IsGeodesicVariationOn cov F S T →
∃ W, (∀ t ∈ T, VariationTorsionSwapAt cov F s0 t W) ∧
  ∀ t ∈ T, VariationCurvCommAt cov hcov F s0 t W
```

is not true for the current representative-based pullback derivative.

In flat `Real`, the variation `F (s,t) = s * t` has geodesic time-curves.
At `s0 = 0`, the base curve is constant, while the variation field is
`J(t) = t` in the same tangent fiber.  The present
`HasPullbackCovariantDerivativeAlongCurveAt` requires a single ambient
representative to realize `J` near a time, hence would force `J` to be locally
constant along that constant base curve.

The correct next producer must therefore either:

* use a genuine pullback connection on arbitrary sections of `F^* TM`, or
* assume explicit local ambient representatives/descent data and then apply
  the checked `surfTime_rep`, `surfParam_rep`, `torsionSwap_rep`, and
  `curvComm_rep` lemmas above.
-/

end GlobalGeometry
end RicciFlower
