import DifferentialGeometry.Geometry.Metric.LocalPullback

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry

open Bundle
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace Real F]
  [FiniteDimensional Real F]
variable {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners Real E H}
variable {G : Type*} [TopologicalSpace G]
  {J : ModelWithCorners Real F G}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]
variable {N : Type*} [TopologicalSpace N] [ChartedSpace G N]
  [IsManifold J ∞ N]

omit [FiniteDimensional Real E] [FiniteDimensional Real F] in
private theorem prodInner_symm
    (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric J N)
    (x : M × N) (v w : TangentSpace (I.prod J) x) :
    (localPullInner (I := I.prod J) (J := I) g Prod.fst x +
        localPullInner (I := I.prod J) (J := J) h Prod.snd x) v w =
      (localPullInner (I := I.prod J) (J := I) g Prod.fst x +
        localPullInner (I := I.prod J) (J := J) h Prod.snd x) w v := by
  simp only [ContinuousLinearMap.add_apply, localPullInner_apply, mfderiv_fst,
    mfderiv_snd]
  change g.inner x.1 v.1 w.1 + h.inner x.2 v.2 w.2 =
    g.inner x.1 w.1 v.1 + h.inner x.2 w.2 v.2
  rw [g.symm, h.symm]

omit [FiniteDimensional Real E] [FiniteDimensional Real F] in
private theorem prodInner_pos
    (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric J N)
    (x : M × N) (v : TangentSpace (I.prod J) x) (hv : v ≠ 0) :
    0 < (localPullInner (I := I.prod J) (J := I) g Prod.fst x +
      localPullInner (I := I.prod J) (J := J) h Prod.snd x) v v := by
  simp only [ContinuousLinearMap.add_apply, localPullInner_apply, mfderiv_fst,
    mfderiv_snd]
  change 0 < g.inner x.1 v.1 v.1 + h.inner x.2 v.2 v.2
  by_cases hv₁ : v.1 = 0
  · have hv₂ : v.2 ≠ 0 := by
      intro hv₂
      apply hv
      exact Prod.ext hv₁ hv₂
    have hgzero :
        g.inner x.1 (0 : TangentSpace I x.1) 0 = 0 := by
      rw [(g.inner x.1).map_zero, ContinuousLinearMap.zero_apply]
    have hgzero_v : g.inner x.1 v.1 v.1 = 0 := by
      rw [hv₁]
      exact hgzero
    rw [hgzero_v, zero_add]
    exact h.pos x.2 v.2 hv₂
  · have hh : 0 ≤ h.inner x.2 v.2 v.2 := by
      by_cases hv₂ : v.2 = 0
      · have hhzero :
            h.inner x.2 (0 : TangentSpace J x.2) 0 = 0 := by
          rw [(h.inner x.2).map_zero, ContinuousLinearMap.zero_apply]
        have hhzero_v : h.inner x.2 v.2 v.2 = 0 := by
          rw [hv₂]
          exact hhzero
        rw [hhzero_v]
      · exact (h.pos x.2 v.2 hv₂).le
    exact add_pos_of_pos_of_nonneg (g.pos x.1 v.1 hv₁) hh

/-- The product of two smooth Riemannian metrics. -/
noncomputable def prodMetric
    [SigmaCompactSpace M] [T2Space M]
    [SigmaCompactSpace N] [T2Space N]
    (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric J N) :
    SmoothRiemannianMetric (I.prod J) (M × N) where
  inner x :=
    localPullInner (I := I.prod J) (J := I) g Prod.fst x +
      localPullInner (I := I.prod J) (J := J) h Prod.snd x
  symm x := prodInner_symm (I := I) (J := J) g h x
  pos x := prodInner_pos (I := I) (J := J) g h x
  isVonNBounded x :=
    Geometry.posDef_isVonNBounded (E := E × F)
      (localPullInner (I := I.prod J) (J := I) g Prod.fst x +
        localPullInner (I := I.prod J) (J := J) h Prod.snd x)
      (prodInner_pos (I := I) (J := J) g h x)
  contMDiff :=
    (localPull_smooth (I := I.prod J) (J := I) g Prod.fst contMDiff_fst).add_section
      (localPull_smooth (I := I.prod J) (J := J) h Prod.snd contMDiff_snd)

/-- Evaluation of the product metric on product tangent vectors. -/
theorem prodMetric_inner
    [SigmaCompactSpace M] [T2Space M]
    [SigmaCompactSpace N] [T2Space N]
    (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric J N)
    (x : M × N) (v w : TangentSpace (I.prod J) x) :
    (prodMetric (I := I) (J := J) g h).inner x v w =
      g.inner x.1 v.1 w.1 + h.inner x.2 v.2 w.2 := by
  simp only [prodMetric, localPullInner_apply, mfderiv_fst, mfderiv_snd,
    ContinuousLinearMap.add_apply]
  change g.inner x.1 v.1 w.1 + h.inner x.2 v.2 w.2 =
    g.inner x.1 v.1 w.1 + h.inner x.2 v.2 w.2
  rfl

end DifferentialGeometry
