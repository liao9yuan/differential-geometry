import DifferentialGeometry.Geometry.Geodesic.MaximalInterval
import DifferentialGeometry.Geometry.Exponential.DiagExpDerivative
import DifferentialGeometry.Geometry.Exponential.IntrinsicVelocity
import DifferentialGeometry.Geometry.Metric.DistanceScaling

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Explicit-metric distance bounds for Calabi broken paths

This file exposes the standard distance-bounded-by-length inequality with the
smooth Riemannian metric supplied explicitly.  It also packages the two-arc
broken-path estimate used by point-centered Calabi upper supports.
-/

noncomputable section

open Bundle Filter Manifold Set Topology
open scoped Manifold ContDiff ENNReal

namespace DifferentialGeometry

open Geometry.Riemannian
open Geometry.Riemannian.Exponential
open Geometry.Riemannian.HopfRinow

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [InnerProductSpace Real E] [Module.Finite Real E] [FiniteDimensional Real E]
  [NeZero (Module.finrank Real E)]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]

private theorem continuousAt_fiber_smul
    {X B F : Type*} [TopologicalSpace X] [TopologicalSpace B]
    [NormedAddCommGroup F] [NormedSpace Real F]
    {V : B → Type*} [∀ b, AddCommGroup (V b)] [∀ b, Module Real (V b)]
    [∀ b, TopologicalSpace (V b)]
    [TopologicalSpace (TotalSpace F V)] [FiberBundle F V] [VectorBundle Real F V]
    {b : X → B} {v : ∀ x, V (b x)} {a : X → Real} {x₀ : X}
    (hv : ContinuousAt (fun x => TotalSpace.mk' F (b x) (v x)) x₀)
    (ha : ContinuousAt a x₀) :
    ContinuousAt (fun x => TotalSpace.mk' F (b x) (a x • v x)) x₀ := by
  rw [FiberBundle.continuousAt_totalSpace] at hv ⊢
  refine ⟨hv.1, ?_⟩
  let e := trivializationAt F V (b x₀)
  have hb : ∀ᶠ x in 𝓝 x₀, b x ∈ e.baseSet :=
    hv.1 (e.open_baseSet.mem_nhds (FiberBundle.mem_baseSet_trivializationAt' (b x₀)))
  have heq :
      (fun x => (e (TotalSpace.mk' F (b x) (a x • v x))).2) =ᶠ[𝓝 x₀]
        fun x => a x • (e (TotalSpace.mk' F (b x) (v x))).2 := by
    filter_upwards [hb] with x hx
    exact (e.linear Real hx).map_smul (a x) (v x)
  exact (ha.smul hv.2).congr_of_eventuallyEq heq

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- The extended distance of an explicitly supplied Riemannian metric is at
most the arc length of any `C¹` curve joining the endpoints. -/
theorem edistOf_le_arcLength
    (g : SmoothRiemannianMetric I M) {γ : Real → M} {a b : Real}
    (hab : a ≤ b)
    (hγ : ContMDiffOn 𝓘(Real, Real) I 1 γ (Set.Icc a b)) :
    riemannianEDistOf (I := I) g (γ a) (γ b) ≤
      ENNReal.ofReal
        (Geometry.Riemannian.Variation.arcLength (I := I) g γ a b) := by
  letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
    ⟨g.toRiemannianMetric⟩
  change riemannianEDist I (γ a) (γ b) ≤ _
  apply Geometry.Riemannian.Geodesic.riemannianEDist_le_arcLength
    (I := I) g hab hγ
  intro t ht
  rw [← ofReal_norm_eq_enorm, norm_eq_sqrt_real_inner]
  congr 2

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- A broken path made of two `C¹` arcs bounds the explicit Riemannian
extended distance by the sum of their arc lengths. -/
theorem edistOf_le_two_arcs
    (g : SmoothRiemannianMetric I M)
    {γ δ : Real → M} {a b c d : Real}
    (hab : a ≤ b) (hcd : c ≤ d)
    (hγ : ContMDiffOn 𝓘(Real, Real) I 1 γ (Set.Icc a b))
    (hδ : ContMDiffOn 𝓘(Real, Real) I 1 δ (Set.Icc c d))
    (hjoin : γ b = δ c) :
    riemannianEDistOf (I := I) g (γ a) (δ d) ≤
      ENNReal.ofReal
          (Geometry.Riemannian.Variation.arcLength (I := I) g γ a b) +
        ENNReal.ofReal
          (Geometry.Riemannian.Variation.arcLength (I := I) g δ c d) := by
  letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
    ⟨g.toRiemannianMetric⟩
  change riemannianEDist I (γ a) (δ d) ≤ _
  calc
    riemannianEDist I (γ a) (δ d) ≤
        riemannianEDist I (γ a) (γ b) +
          riemannianEDist I (γ b) (δ d) :=
      Manifold.riemannianEDist_triangle
    _ = riemannianEDist I (γ a) (γ b) +
          riemannianEDist I (δ c) (δ d) := by rw [hjoin]
    _ ≤ ENNReal.ofReal
          (Geometry.Riemannian.Variation.arcLength (I := I) g γ a b) +
        ENNReal.ofReal
          (Geometry.Riemannian.Variation.arcLength (I := I) g δ c d) :=
      add_le_add
        (edistOf_le_arcLength (I := I) g hab hγ)
        (edistOf_le_arcLength (I := I) g hcd hδ)

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- A minimizing intrinsic geodesic from `O` to `x` admits a terminal point
strictly before `x` whose remaining velocity lies in a prescribed inverse
branch centered at `x`. -/
theorem calabi_tail_of
    [RiemannianBundle (fun y : M => TangentSpace I y)]
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun y : M => TangentSpace I y)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (y : M) (w : TangentSpace I y),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner y w w)))
    (O x : M) (hOx : riemannianEDist I O x ≠ ⊤)
    (B : DiagInvBranch (I := I) g hEnorm x) :
    ∃ (v : TangentSpace I O) (s₀ : Real),
      expMapIntrinsic (I := I) g hEnorm O v = x ∧
      Real.sqrt (g.inner O v v) = (riemannianEDist I O x).toReal ∧
      0 < s₀ ∧ s₀ < 1 ∧
      let velocity : Real → TangentBundle I M :=
        intrinsicVelocityLift (I := I) g hEnorm O v
      let tail : Real → TangentBundle I M := fun s =>
        ⟨(velocity s).proj, (1 - s) • (velocity s).snd⟩
      tail s₀ ∈ B.hom.source ∧
        ((tail s₀).proj, x) ∈ B.dom ∧
        expMapIntrinsic (I := I) g hEnorm (tail s₀).proj (tail s₀).snd = x ∧
        B.inv ((tail s₀).proj, x) = tail s₀ := by
  obtain ⟨v, hvx, hvmin⟩ :=
    hopf_rinow_expMapIntrinsic_surjective_minimizing_of_ne_top
      (I := I) g hEnorm O x hOx
  let velocity : Real → TangentBundle I M :=
    intrinsicVelocityLift (I := I) g hEnorm O v
  let tail : Real → TangentBundle I M := fun s =>
    ⟨(velocity s).proj, (1 - s) • (velocity s).snd⟩
  have hvelocity : Continuous velocity :=
    (lift_isIntegral (I := I) g hEnorm O v).continuous
  have htail : ContinuousAt tail 1 := by
    apply continuousAt_fiber_smul hvelocity.continuousAt
    fun_prop
  have hvelocity_one : (velocity 1).proj = x := by
    change intrinsicGeodesic (I := I) g hEnorm O v 1 = x
    simpa only [expMapIntrinsic_def] using hvx
  have htail_one :
      tail 1 = (⟨x, (0 : TangentSpace I x)⟩ : TangentBundle I M) := by
    apply TotalSpace.ext hvelocity_one
    apply heq_of_eq
    simp only [tail, sub_self, zero_smul]
    rfl
  have htail_mem : tail 1 ∈ B.hom.source := by
    rw [htail_one]
    exact B.zero_mem
  have hsource_nhds : {s : Real | tail s ∈ B.hom.source} ∈ 𝓝 (1 : Real) :=
    htail.preimage_mem_nhds (B.hom.open_source.mem_nhds htail_mem)
  obtain ⟨ε, hε, hε_sub⟩ := Metric.mem_nhds_iff.mp hsource_nhds
  let d : Real := min ε 1 / 2
  let s₀ : Real := 1 - d
  have hd_pos : 0 < d := by
    dsimp [d]
    exact half_pos (lt_min hε zero_lt_one)
  have hd_lt_one : d < 1 := by
    dsimp [d]
    nlinarith [min_le_right ε (1 : Real)]
  have hd_lt_ε : d < ε := by
    dsimp [d]
    nlinarith [min_le_left ε (1 : Real), lt_min hε zero_lt_one]
  have hs₀_pos : 0 < s₀ := by
    dsimp [s₀]
    linarith
  have hs₀_lt : s₀ < 1 := by
    dsimp [s₀]
    linarith
  have hs₀_ball : s₀ ∈ Metric.ball (1 : Real) ε := by
    rw [Metric.mem_ball, Real.dist_eq]
    have : |s₀ - 1| = d := by
      dsimp [s₀]
      rw [abs_of_nonpos]
      · ring
      · linarith
    rw [this]
    exact hd_lt_ε
  have hs₀_source : tail s₀ ∈ B.hom.source := hε_sub hs₀_ball
  have hs₀_exp :
      expMapIntrinsic (I := I) g hEnorm (tail s₀).proj (tail s₀).snd = x := by
    have hcontinue :=
      congrFun (intrinsicGeodesic_continuation (I := I) g hEnorm O v s₀) (1 - s₀)
    have hend :
        intrinsicGeodesic (I := I) g hEnorm O v 1 = x := by
      simpa only [expMapIntrinsic_def] using hvx
    change intrinsicGeodesic (I := I) g hEnorm (velocity s₀).proj
      ((1 - s₀) • (velocity s₀).snd) 1 = x
    rw [intrinsicGeodesic_smul (I := I) g hEnorm]
    rw [show (velocity s₀).proj =
        intrinsicGeodesic (I := I) g hEnorm O v s₀ by
          exact velocityLift_proj (I := I) g hEnorm O v s₀]
    rw [show (velocity s₀).snd =
        (mfderiv 𝓘(Real, Real) I
          (intrinsicGeodesic (I := I) g hEnorm O v) s₀ :
            Real →L[Real] TangentSpace I
              (intrinsicGeodesic (I := I) g hEnorm O v s₀)) 1 by rfl]
    calc
      intrinsicGeodesic (I := I) g hEnorm
          (intrinsicGeodesic (I := I) g hEnorm O v s₀)
          (mfderiv 𝓘(Real, Real) I
            (intrinsicGeodesic (I := I) g hEnorm O v) s₀ 1)
          (1 - s₀) =
          intrinsicGeodesic (I := I) g hEnorm O v (1 - s₀ + s₀) :=
        hcontinue.symm
      _ = intrinsicGeodesic (I := I) g hEnorm O v 1 := by
        congr 1
        ring
      _ = x := hend
  have hs₀_dom : ((tail s₀).proj, x) ∈ B.dom := by
    have hmap : B.hom (tail s₀) ∈ B.hom.target :=
      B.hom.map_source hs₀_source
    have hhom : B.hom (tail s₀) = ((tail s₀).proj, x) := by
      have hdiag :
          diagExp (I := I) g hEnorm (tail s₀) = ((tail s₀).proj, x) := by
        change ((tail s₀).proj,
          expMapIntrinsic (I := I) g hEnorm (tail s₀).proj (tail s₀).snd) =
            ((tail s₀).proj, x)
        rw [hs₀_exp]
      change (fun u ↦ B.hom u) (tail s₀) = ((tail s₀).proj, x)
      exact (B.hom_eq hs₀_source).trans hdiag
    change ((tail s₀).proj, x) ∈ B.hom.target
    rwa [← hhom]
  refine ⟨v, s₀, hvx, hvmin, hs₀_pos, hs₀_lt, ?_⟩
  dsimp only
  refine ⟨hs₀_source, hs₀_dom, hs₀_exp, ?_⟩
  exact B.inv_eq_of_exp hs₀_source hs₀_exp

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- The generic diagonal-exponential branch supplies the terminal inverse
segment needed in the Calabi broken-path construction. -/
theorem exists_calabi_tail
    [RiemannianBundle (fun y : M => TangentSpace I y)]
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [T2Space (TangentBundle I M)]
    [IsContinuousRiemannianBundle E (fun y : M => TangentSpace I y)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (y : M) (w : TangentSpace I y),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner y w w)))
    (O x : M) (hOx : riemannianEDist I O x ≠ ⊤) :
    ∃ (v : TangentSpace I O) (s₀ : Real),
      expMapIntrinsic (I := I) g hEnorm O v = x ∧
      Real.sqrt (g.inner O v v) = (riemannianEDist I O x).toReal ∧
      0 < s₀ ∧ s₀ < 1 ∧
      let velocity : Real → TangentBundle I M :=
        intrinsicVelocityLift (I := I) g hEnorm O v
      let tail : Real → TangentBundle I M := fun s =>
        ⟨(velocity s).proj, (1 - s) • (velocity s).snd⟩
      tail s₀ ∈
          (Geometry.Riemannian.Exponential.stdBranch (I := I) g hEnorm x).hom.source ∧
        ((tail s₀).proj, x) ∈
          (Geometry.Riemannian.Exponential.stdBranch (I := I) g hEnorm x).dom ∧
        expMapIntrinsic (I := I) g hEnorm (tail s₀).proj (tail s₀).snd = x ∧
        (Geometry.Riemannian.Exponential.stdBranch (I := I) g hEnorm x).inv
          ((tail s₀).proj, x) = tail s₀ := by
  exact calabi_tail_of (I := I) g hEnorm O x hOx
    (Geometry.Riemannian.Exponential.stdBranch (I := I) g hEnorm x)

end DifferentialGeometry
