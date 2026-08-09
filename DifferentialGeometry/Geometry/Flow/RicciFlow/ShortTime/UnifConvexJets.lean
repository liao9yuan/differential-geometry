import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RicciDifferenceMeanValue
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.UnifBochnerGap
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.AllTimesBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.UnifCurvActionZero

/-!
# Class-uniform convex-path jet package

This module separates the finite Sobolev conversion from the geometric production of
curvature-action constants.  A single class-first rank-two/rank-three curvature-action package
produces simultaneous class-first `H²` and `H³` covariant-jet bounds along every convex tensor
segment.
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold MeasureTheory Set Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow

open DifferentialGeometry.HCGCompactness
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.PDE.DeTurck.RicciLinearization
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]

variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

/-- The two curvature-action constants needed by the finite `H²`/`H³` comparison. -/
structure CurvActionData where
  rankTwo : ℝ
  rankThree : ℝ

/-- The closed curvature-action constants determined by the class parameter and fixed-background
curvature caps. -/
noncomputable def classCurvActions (d : ℕ) (Λ Kb₀ Kb₁ : ℝ) : CurvActionData where
  rankTwo := unifPtCurvZeroC d Λ Kb₀ Kb₁
  rankThree := unifPtCurvThreeC d Λ Kb₀ Kb₁

/-- `K` bounds the order-zero curvature action at tensor ranks two and three, uniformly over
the entire metric class.  The constants are data fixed before the class metric varies. -/
structure IsCurvActionUnif
    (gBase : SmoothRiemannianMetric I M) (Λ : ℝ) (K : CurvActionData) : Prop where
  bounds : ∀ (g : SmoothRiemannianMetric I M),
    MetricUniformEquivalentOn (I := I) Set.univ gBase g Λ →
    (∀ a : ℕ, a ≤ 3 →
      MetricCovDerivOrderBoundOn (I := I) Set.univ a g gBase Λ) →
    IsCurvAction0 (I := I) (M := M) g 2 K.rankTwo ∧
      IsCurvAction0 (I := I) (M := M) g 3 K.rankThree

/-- Supplied fixed-background curvature caps produce the explicit rank-two/rank-three
curvature-action package uniformly over the order-three metric class. -/
theorem class_curv_actions
    (gBase : SmoothRiemannianMetric I M) {Λ Kb₀ Kb₁ : ℝ}
    (hΛ : 1 ≤ Λ)
    (hKb₀_nonneg : 0 ≤ Kb₀)
    (hKb₀ : ∀ (x : M) (v w u : TangentSpace I x),
      gBase.inner x (riemannOp (LeviCivita (I := I) gBase) x v w u)
          (riemannOp (LeviCivita (I := I) gBase) x v w u) ≤
        Kb₀ * gBase.inner x v v * gBase.inner x w w * gBase.inner x u u)
    (hKb₁_nonneg : 0 ≤ Kb₁)
    (hKb₁ : ∀ x : M,
      Real.sqrt (normSq0S (I := I) gBase x 5
        (iterCov (I := I) gBase 4
          (metricRm04 (I := I) (M := M) gBase) 1 x)) ≤ Kb₁) :
    IsCurvActionUnif (I := I) (M := M) gBase Λ
      (classCurvActions (Module.finrank ℝ E) Λ Kb₀ Kb₁) := by
  refine ⟨?_⟩
  intro g hEq hjet
  have hcomp : ∀ (x : M) (v : TangentSpace I x),
      Λ⁻¹ * gBase.inner x v v ≤ g.inner x v v ∧
        g.inner x v v ≤ Λ * gBase.inner x v v :=
    fun x v => hEq.2 x (Set.mem_univ x) v
  have hjet1 := hjet 1 (by norm_num)
  have hjet2 := hjet 2 (by norm_num)
  have hjet3 := hjet 3 (by norm_num)
  constructor
  · simpa only [classCurvActions] using
      (unifCurvAction0_of (I := I) (M := M) gBase g hΛ
        hKb₀_nonneg hKb₀ hKb₁_nonneg hKb₁ hcomp hjet1 hjet2 hjet3)
  · simpa only [classCurvActions] using
      (unifCurvAction3_of (I := I) (M := M) gBase g hΛ
        hKb₀_nonneg hKb₀ hKb₁_nonneg hKb₁ hcomp hjet1 hjet2 hjet3)

/-- Every fixed background and class parameter at least one admit one explicit uniform
curvature-action packet. -/
theorem exists_curv_actions
    (gBase : SmoothRiemannianMetric I M) {Λ : ℝ} (hΛ : 1 ≤ Λ) :
    ∃ K : CurvActionData, IsCurvActionUnif (I := I) (M := M) gBase Λ K := by
  obtain ⟨Kb₀, hKb₀_nonneg, hKb₀⟩ :=
    exists_uniform_riemannOp_LeviCivita_gNorm_bound (I := I) (M := M) gBase
  obtain ⟨Kb₁, hKb₁_nonneg, hKb₁⟩ :=
    exists_curvJet_sup (I := I) (M := M) gBase 1
  have hKb₁' : ∀ x : M,
      Real.sqrt (normSq0S (I := I) gBase x 5
        (iterCov (I := I) gBase 4
          (metricRm04 (I := I) (M := M) gBase) 1 x)) ≤ Kb₁ := by
    intro x
    simpa using hKb₁ x
  exact ⟨classCurvActions (Module.finrank ℝ E) Λ Kb₀ Kb₁,
    class_curv_actions (I := I) (M := M) gBase hΛ
      hKb₀_nonneg hKb₀ hKb₁_nonneg hKb₁'⟩

/-- The explicit finite `H²` coefficient associated with a curvature-action package. -/
noncomputable def convexH2C (K : CurvActionData) : ℝ :=
  h2CovsumC K.rankTwo

/-- The explicit finite `H³` coefficient associated with a curvature-action package. -/
noncomputable def convexH3C (K : CurvActionData) : ℝ :=
  h3CovsumC K.rankTwo K.rankThree

/-- The two class-first convex-path jet coefficients. -/
structure ConvexJetData where
  h2C : ℝ
  h3C : ℝ

/-- The closed convex-path coefficient packet attached to `K`. -/
noncomputable def convexJetData (K : CurvActionData) : ConvexJetData where
  h2C := convexH2C K
  h3C := convexH3C K

/-- `C` gives simultaneous class-uniform `H²` and `H³` intrinsic jet bounds along every
convex tensor segment. -/
structure IsConvexJetUnif
    (gBase : SmoothRiemannianMetric I M) (Λ : ℝ) (C : ConvexJetData) : Prop where
  h2_nonneg : 0 ≤ C.h2C
  h3_nonneg : 0 ≤ C.h3C
  bounds : ∀ (g : SmoothRiemannianMetric I M),
    MetricUniformEquivalentOn (I := I) Set.univ gBase g Λ →
    (∀ a : ℕ, a ≤ 3 →
      MetricCovDerivOrderBoundOn (I := I) Set.univ a g gBase Λ) →
    (∀ (T T' : SmoothCcTensor g 0 2) (R : ℝ), 0 ≤ R →
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ R →
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T'‖ ≤ R →
      ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 →
        (∑ j ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g 0 2 j
            (convexPerturbation (I := I) g T T' s)‖ ^ 2) ≤
          (C.h2C * R) ^ 2) ∧
    (∀ (T T' : SmoothCcTensor g 0 2) (R : ℝ), 0 ≤ R →
      ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T‖ ≤ R →
      ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T'‖ ≤ R →
      ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 →
        (∑ j ∈ Finset.range 4,
          ‖iteratedCovGrad (I := I) g 0 2 j
            (convexPerturbation (I := I) g T T' s)‖ ^ 2) ≤
          (C.h3C * R) ^ 2)

private theorem convex_hs_norm_le
    (g : SmoothRiemannianMetric I M) (q : ℝ)
    (T T' : SmoothCcTensor g 0 2) {R s : ℝ} (_hR : 0 ≤ R)
    (hT : ‖ccTensorToHs (I := I) (M := M) g 2 q T‖ ≤ R)
    (hT' : ‖ccTensorToHs (I := I) (M := M) g 2 q T'‖ ≤ R)
    (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    ‖ccTensorToHs (I := I) (M := M) g 2 q
      (convexPerturbation (I := I) g T T' s)‖ ≤ R := by
  have hs0 : (0 : ℝ) ≤ s := hs.1
  have h1ms : (0 : ℝ) ≤ 1 - s := by linarith [hs.2]
  rw [show convexPerturbation (I := I) g T T' s =
      (1 - s) • T' + s • T from rfl,
    ccTensorToHs_add, ccTensorToHs_smul, ccTensorToHs_smul]
  calc
    ‖(1 - s) • ccTensorToHs (I := I) (M := M) g 2 q T' +
        s • ccTensorToHs (I := I) (M := M) g 2 q T‖
        ≤ ‖(1 - s) • ccTensorToHs (I := I) (M := M) g 2 q T'‖ +
          ‖s • ccTensorToHs (I := I) (M := M) g 2 q T‖ := norm_add_le _ _
    _ = (1 - s) * ‖ccTensorToHs (I := I) (M := M) g 2 q T'‖ +
          s * ‖ccTensorToHs (I := I) (M := M) g 2 q T‖ := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
          abs_of_nonneg h1ms, abs_of_nonneg hs0]
    _ ≤ (1 - s) * R + s * R :=
      add_le_add (mul_le_mul_of_nonneg_left hT' h1ms)
        (mul_le_mul_of_nonneg_left hT hs0)
    _ = R := by ring

/-- A class-first rank-two/rank-three curvature-action package produces one explicit,
simultaneous class-first convex-path `H²`/`H³` jet package. -/
theorem convex_h23_of_act
    (gBase : SmoothRiemannianMetric I M) (Λ : ℝ) (K : CurvActionData)
    (hK : IsCurvActionUnif (I := I) (M := M) gBase Λ K) :
    IsConvexJetUnif (I := I) (M := M) gBase Λ (convexJetData K) := by
  refine ⟨h2CovsumC_nonneg K.rankTwo,
    h3CovsumC_nonneg K.rankTwo K.rankThree, ?_⟩
  intro g hEq hjet
  obtain ⟨hact₂, hact₃⟩ := hK.bounds g hEq hjet
  constructor
  · intro T T' R hR hT hT' s hs
    have hpath := convex_hs_norm_le (I := I) (M := M) g 2 T T' hR hT hT' hs
    have hsum := covsum_hs_two (I := I) (M := M) g 2 hact₂
      (convexPerturbation (I := I) g T T' s)
    have hsum' : (∑ j ∈ Finset.range 3,
        ‖iteratedCovGrad (I := I) g 0 2 j
          (convexPerturbation (I := I) g T T' s)‖) ≤
        h2CovsumC K.rankTwo * R := by
      exact hsum.trans
        (mul_le_mul_of_nonneg_left hpath (h2CovsumC_nonneg K.rankTwo))
    exact (Finset.sum_sq_le_sq_sum_of_nonneg
      (fun j _ => norm_nonneg
        (iteratedCovGrad (I := I) g 0 2 j
          (convexPerturbation (I := I) g T T' s)))).trans
      (pow_le_pow_left₀
        (Finset.sum_nonneg fun j _ => norm_nonneg
          (iteratedCovGrad (I := I) g 0 2 j
            (convexPerturbation (I := I) g T T' s))) hsum' 2)
  · intro T T' R hR hT hT' s hs
    have hpath := convex_hs_norm_le (I := I) (M := M) g 3 T T' hR hT hT' hs
    have hsum := covsum_hs_three (I := I) (M := M) g 2 hact₂ hact₃
      (convexPerturbation (I := I) g T T' s)
    have hsum' : (∑ j ∈ Finset.range 4,
        ‖iteratedCovGrad (I := I) g 0 2 j
          (convexPerturbation (I := I) g T T' s)‖) ≤
        h3CovsumC K.rankTwo K.rankThree * R := by
      exact hsum.trans
        (mul_le_mul_of_nonneg_left hpath
          (h3CovsumC_nonneg K.rankTwo K.rankThree))
    exact (Finset.sum_sq_le_sq_sum_of_nonneg
      (fun j _ => norm_nonneg
        (iteratedCovGrad (I := I) g 0 2 j
          (convexPerturbation (I := I) g T T' s)))).trans
      (pow_le_pow_left₀
        (Finset.sum_nonneg fun j _ => norm_nonneg
          (iteratedCovGrad (I := I) g 0 2 j
            (convexPerturbation (I := I) g T T' s))) hsum' 2)

/-- Existential wrapper for consumers that do not need the closed coefficient formula. -/
theorem convex_jets_of_act
    (gBase : SmoothRiemannianMetric I M) (Λ : ℝ) (K : CurvActionData)
    (hK : IsCurvActionUnif (I := I) (M := M) gBase Λ K) :
    ∃ C : ConvexJetData, IsConvexJetUnif (I := I) (M := M) gBase Λ C :=
  ⟨convexJetData K, convex_h23_of_act (I := I) (M := M) gBase Λ K hK⟩

/-- Supplied fixed-background curvature caps produce the explicit simultaneous class-first
convex-path `H²`/`H³` jet package. -/
theorem convex_h23_unif
    (gBase : SmoothRiemannianMetric I M) {Λ Kb₀ Kb₁ : ℝ}
    (hΛ : 1 ≤ Λ)
    (hKb₀_nonneg : 0 ≤ Kb₀)
    (hKb₀ : ∀ (x : M) (v w u : TangentSpace I x),
      gBase.inner x (riemannOp (LeviCivita (I := I) gBase) x v w u)
          (riemannOp (LeviCivita (I := I) gBase) x v w u) ≤
        Kb₀ * gBase.inner x v v * gBase.inner x w w * gBase.inner x u u)
    (hKb₁_nonneg : 0 ≤ Kb₁)
    (hKb₁ : ∀ x : M,
      Real.sqrt (normSq0S (I := I) gBase x 5
        (iterCov (I := I) gBase 4
          (metricRm04 (I := I) (M := M) gBase) 1 x)) ≤ Kb₁) :
    IsConvexJetUnif (I := I) (M := M) gBase Λ
      (convexJetData
        (classCurvActions (Module.finrank ℝ E) Λ Kb₀ Kb₁)) := by
  exact convex_h23_of_act (I := I) (M := M) gBase Λ
    (classCurvActions (Module.finrank ℝ E) Λ Kb₀ Kb₁)
    (class_curv_actions (I := I) (M := M) gBase hΛ
      hKb₀_nonneg hKb₀ hKb₁_nonneg hKb₁)

/-- Every fixed background and class parameter at least one admit one explicit simultaneous
convex-path `H²`/`H³` jet packet. -/
theorem exists_convex_jets
    (gBase : SmoothRiemannianMetric I M) {Λ : ℝ} (hΛ : 1 ≤ Λ) :
    ∃ C : ConvexJetData, IsConvexJetUnif (I := I) (M := M) gBase Λ C := by
  obtain ⟨K, hK⟩ := exists_curv_actions (I := I) (M := M) gBase hΛ
  exact convex_jets_of_act (I := I) (M := M) gBase Λ K hK

end RicciFlow
end PDE
end DifferentialGeometry

end
