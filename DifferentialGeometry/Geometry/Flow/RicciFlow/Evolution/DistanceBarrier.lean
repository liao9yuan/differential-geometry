import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.DistanceBarrierCore

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Calabi upper supports for evolving Riemannian distance

This endpoint module assembles the curvature and completeness inputs with the
precompiled fixed-time support core.
-/

noncomputable section

universe u uE uH

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle Filter Set
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Geometry.Riemannian
open scoped Manifold ContDiff Topology Bundle

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [CompleteSpace E]
  [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [IsManifold I 1 M] [IsManifold I 2 M]
  [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
  [SigmaCompactSpace M] [T2Space M]

/-- The curvature-derived inputs needed by the fixed-time support core. -/
private structure CurvPrep
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (T K t : Real) : Prop where
  lambda_nonneg :
    0 ≤ (Module.finrank Real E : Real) ^ 2 * Real.sqrt K
  ricci_quad :
    ∀ s ∈ Set.Icc 0 T, ∀ y : M, ∀ v : TangentSpace I y,
      |ricciTensor (I := I) (S.base.metric s) y v v| ≤
        ((Module.finrank Real E : Real) ^ 2 * Real.sqrt K) *
          (S.base.metric s).inner y v v
  complete_t :
    RiemannianMetricComplete (I := I) (S.base.metric t)

/-- Prepare the curvature coefficient and selected-slice completeness. -/
private theorem curv_prep
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    {T K t : Real}
    (hslab : Set.Icc 0 T ⊆ D.carrier)
    (hreg : Set.Ioc 0 T ⊆ D.regular)
    (hcomplete :
      RiemannianMetricComplete (I := I) (S.base.metric 0))
    (hK : 0 ≤ K)
    (hcurv : ∀ s ∈ Set.Icc 0 T, ∀ y : M,
      nablaKRm04NormSqIntrinsic (I := I) S 0 s y ≤ K)
    (ht : t ∈ Set.Icc 0 T) :
    CurvPrep (I := I) S T K t := by
  rcases
      DistanceBarrierCore.ricci_quad_of_curv
        (I := I) S hK hcurv
    with ⟨hΛ, hricQuad⟩
  have hcomplete_t :
      RiemannianMetricComplete (I := I) (S.base.metric t) :=
    complete_of_ricBound
      (I := I) (D := D) (a := 0) (b := T)
      (K := (Module.finrank Real E : Real) ^ 2 * Real.sqrt K)
      (s := t)
      S hS hslab hreg hΛ hricQuad hcomplete ht
  exact CurvPrep.mk hΛ hricQuad hcomplete_t

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- Assemble the scaled support from the original curvature and
anchor-completeness inputs. -/
private theorem scaled_of_curv
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (O : M)
    {T K t : Real}
    (hT : 0 < T)
    (hslab : Set.Icc 0 T ⊆ D.carrier)
    (hreg : Set.Ioc 0 T ⊆ D.regular)
    (hcomplete :
      RiemannianMetricComplete (I := I) (S.base.metric 0))
    (hK : 0 ≤ K)
    (hcurv : ∀ s ∈ Set.Icc 0 T, ∀ y : M,
      nablaKRm04NormSqIntrinsic (I := I) S 0 s y ≤ K)
    (ht : t ∈ Set.Icc 0 T)
    (htpos : 0 < t)
    (x : M)
    (hfinite :
      riemannianEDistOf (I := I) (S.base.metric t) O x ≠ ⊤)
    (hOx : O ≠ x) :
    Nonempty
      (DistanceBarrierCore.ScaledDistSupport
        (I := I) S O T t x (Module.finrank Real E : Real)
        ((Module.finrank Real E : Real) ^ 2 * Real.sqrt K)
        (riemannianEDistOf
      (I := I) (S.base.metric t) O x).toReal) := by
  have hp :=
    curv_prep
      (I := I) (D := D) (T := T) (K := K) (t := t)
      S hS hslab hreg hcomplete hK hcurv ht
  exact
    DistanceBarrierCore.scaled_of_quad
      (I := I) (D := D) (T := T) (t := t)
      (Λ := (Module.finrank Real E : Real) ^ 2 * Real.sqrt K)
      S hS O hT hreg hp.lambda_nonneg hp.ricci_quad hp.complete_t
        ht htpos x hfinite hOx

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- A positively rescaled evolving distance admits a quantitative smooth
Calabi upper support at every positive-time point of finite nonzero distance.

This is the unique new geometric-analysis frontier in the Route B-prime
complete-Shi producer.  The proof joins a point-pair minimizing geodesic, a
fixed-first Calabi tail, fixed-metric Laplacian comparison, and the Ricci-flow
variation of the length of the selected broken path. -/
theorem scaledDist_calabiUpperSupport_of_sol
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (O : M)
    {T K t : Real}
    (hT : 0 < T)
    (hslab : Set.Icc 0 T ⊆ D.carrier)
    (hreg : Set.Ioc 0 T ⊆ D.regular)
    (hcomplete :
      RiemannianMetricComplete (I := I) (S.base.metric 0))
    (hK : 0 ≤ K)
    (hcurv : ∀ s ∈ Set.Icc 0 T, ∀ y : M,
      nablaKRm04NormSqIntrinsic (I := I) S 0 s y ≤ K)
    (ht : t ∈ Set.Icc 0 T)
    (htpos : 0 < t)
    (x : M)
    (hfinite :
      riemannianEDistOf (I := I) (S.base.metric t) O x ≠ ⊤)
    (hOx : O ≠ x) :
    let d : Real := Module.finrank Real E
    let Λ : Real := d ^ 2 * Real.sqrt K
    let r : Real :=
      (riemannianEDistOf (I := I) (S.base.metric t) O x).toReal
    ∃ ρ : Real → M → Real,
      ρ t x = Real.exp (Λ * t) * r ∧
      (∀ᶠ p in 𝓝[spacetimeSlab (M := M) T] (t, x),
        Real.exp (Λ * p.1) *
            (riemannianEDistOf (I := I)
              (S.base.metric p.1) O p.2).toReal ≤
          ρ p.1 p.2) ∧
      DifferentiableWithinAt Real
        (fun s => ρ s x) (Set.Icc 0 T) t ∧
      (∀ᶠ y in 𝓝 x,
        MDifferentiableAt I 𝓘(Real, Real) (ρ t) y) ∧
      MDifferentiableAt I (I.prod 𝓘(Real, E))
        (T% fun y : M =>
          gradientFun (I := I) (S.base.metric t) (ρ t) y) x ∧
      (S.base.metric t).inner x
          (gradientFun (I := I) (S.base.metric t) (ρ t) x)
          (gradientFun (I := I) (S.base.metric t) (ρ t) x) ≤
        Real.exp (2 * Λ * t) ∧
      -Real.exp (Λ * t) *
          (2 * (d - 1) / r + Real.sqrt ((d - 1) * Λ)) ≤
        parabolicOperatorWithDrift
          (I := I) (flowG (I := I) S) T
          (fun _ y => (0 : TangentSpace I y)) ρ t x := by
  dsimp only
  obtain ⟨h⟩ :=
    scaled_of_curv
      (I := I) (D := D) (T := T) (K := K) (t := t)
      S hS O hT hslab hreg hcomplete hK hcurv
        ht htpos x hfinite hOx
  exact h.toResult

end DifferentialGeometry.PDE.RicciFlow

end
