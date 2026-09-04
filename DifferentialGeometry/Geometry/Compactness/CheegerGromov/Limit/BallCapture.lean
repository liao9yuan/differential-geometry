import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Limit.Distances
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Limit.Limit

set_option autoImplicit false

noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace HCGCompactness

open Bundle Manifold
open scoped Manifold ContDiff ENNReal

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace

/-- A controlled partial Riemannian almost-isometry maps a sufficiently buffered
closed ball onto a set containing the prescribed ball about every inner point. -/
theorem ball_subset_image
    {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
    [FiniteDimensional Real E] [CompleteSpace E]
    {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners Real E H}
    {M N : Type u}
    [PseudoMetricSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
    [SigmaCompactSpace M] [ProperSpace M]
    [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M]
    [PseudoMetricSpace N] [ChartedSpace H N] [T2Space N] [IsManifold I ∞ N]
    [SigmaCompactSpace N]
    [RiemannianBundle (fun y : N => TangentSpace I y)] [IsRiemannianManifold I N]
    (Φ : PartialDiffeomorph I I M N (∞ : WithTop ℕ∞))
    {O x : M} {r R A eps : Real} {p : Nat}
    {g : SmoothRiemannianMetric I M} {h : SmoothRiemannianMetric I N}
    (hgnorm : ∀ (z : M) (v : TangentSpace I z),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner z v v)))
    (hhnorm : ∀ (z : N) (v : TangentSpace I z),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (h.inner z v v)))
    (hA : 0 < A) (hx : x ∈ Metric.ball O r)
    (hmargin : Real.sqrt (1 + eps) * A + r < R)
    (D : BookApproxIsoPartialData (I := I) (Metric.closedBall O R) eps p Φ g h) :
    Metric.ball ((Φ : M → N) x) A ⊆
      (Φ : M → N) '' Metric.closedBall O R := by
  have hrR : r < R := by
    have hsqrtA : 0 ≤ Real.sqrt (1 + eps) * A :=
      mul_nonneg (Real.sqrt_nonneg _) hA.le
    linarith
  have hxR : x ∈ Metric.ball O R := Metric.ball_subset_ball hrR.le hx
  have hballSrc : Metric.ball O R ⊆ Φ.source :=
    (Metric.ball_subset_closedBall.trans D.source_sub)
  have hKcompact : IsCompact ((Φ : M → N) '' Metric.closedBall O R) :=
    (isCompact_closedBall O R).image_of_continuousOn D.forward.smoothOn.continuousOn
  have hKclosed : IsClosed ((Φ : M → N) '' Metric.closedBall O R) :=
    hKcompact.isClosed
  have hOpen : IsOpen ((Φ : M → N) '' Metric.ball O R) :=
    Φ.toOpenPartialHomeomorph.isOpen_image_of_subset_source Metric.isOpen_ball hballSrc
  have hOpenSub : (Φ : M → N) '' Metric.ball O R ⊆
      (Φ : M → N) '' Metric.closedBall O R :=
    Set.image_mono Metric.ball_subset_closedBall
  have hstart : (Φ : M → N) x ∈
      interior ((Φ : M → N) '' Metric.closedBall O R) := by
    rw [mem_interior_iff_mem_nhds]
    exact Filter.mem_of_superset (hOpen.mem_nhds ⟨x, hxR, rfl⟩) hOpenSub
  intro y hy
  by_cases hyK : y ∈ (Φ : M → N) '' Metric.closedBall O R
  · exact hyK
  have hyEdist : Manifold.riemannianEDist I ((Φ : M → N) x) y <
      ENNReal.ofReal A := by
    rw [← IsRiemannianManifold.out (I := I), edist_dist,
      ENNReal.ofReal_lt_ofReal_iff hA]
    simpa only [Metric.mem_ball, dist_comm] using hy
  obtain ⟨η, hη0, hη1, hηC, hηlen⟩ :=
    Manifold.exists_lt_of_riemannianEDist_lt (I := I) hyEdist
  obtain ⟨t, ht, hstay, hfront⟩ :=
    exists_first_exit hKclosed hηC.continuousOn (hη0 ▸ hstart) (hη1 ▸ hyK)
  have hηtK : η t ∈ (Φ : M → N) '' Metric.closedBall O R := by
    rw [← hKclosed.closure_eq]
    exact frontier_subset_closure hfront
  obtain ⟨x', hx'R, hx'eq⟩ := hηtK
  have hx'not : x' ∉ Metric.ball O R := by
    intro hx'ball
    have hInt' : (Φ : M → N) x' ∈
        interior ((Φ : M → N) '' Metric.closedBall O R) := by
      rw [mem_interior_iff_mem_nhds]
      exact Filter.mem_of_superset (hOpen.mem_nhds ⟨x', hx'ball, rfl⟩) hOpenSub
    have hηtK' : η t ∈ (Φ : M → N) '' Metric.closedBall O R :=
      ⟨x', hx'R, hx'eq⟩
    exact (mem_frontier_iff_notMem_interior hηtK').mp hfront (hx'eq ▸ hInt')
  have hx'rad : dist O x' = R := by
    apply le_antisymm
    · simpa only [Metric.mem_closedBall, dist_comm] using hx'R
    · exact le_of_not_gt (fun hlt => hx'not (by
        simpa only [Metric.mem_ball, dist_comm] using hlt))
  let δ : Real → M := (Φ.symm : N → M) ∘ η
  have hδC : ContMDiffOn 𝓘(Real, Real) I 1 δ (Set.Icc 0 t) := by
    apply (Φ.symm.contMDiffOn_toFun.of_le
      (by decide : (1 : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞))).comp
        (hηC.mono (Set.Icc_subset_Icc le_rfl ht.2))
    intro s hs
    obtain ⟨z, hzR, hzEq⟩ := hstay s hs
    change η s ∈ Φ.symm.source
    rw [← hzEq]
    exact Φ.map_source' (D.source_sub hzR)
  have hxSrc : x ∈ Φ.source := D.source_sub (Metric.ball_subset_closedBall hxR)
  have hx'Src : x' ∈ Φ.source := D.source_sub hx'R
  have hδ0 : δ 0 = x := by
    simp only [δ, Function.comp_apply, hη0]
    exact Φ.left_inv hxSrc
  have hδt : δ t = x' := by
    change (Φ.symm : N → M) (η t) = x'
    rw [← hx'eq]
    exact Φ.left_inv hx'Src
  have hlen : Manifold.pathELength (I := I) δ 0 t ≤
      ENNReal.ofReal (Real.sqrt (1 + eps)) *
        Manifold.pathELength (I := I) η 0 t := by
    rw [Manifold.pathELength_eq_lintegral_mfderiv_Ioo,
      Manifold.pathELength_eq_lintegral_mfderiv_Ioo,
      ← MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine MeasureTheory.lintegral_mono_ae
      (Filter.eventually_of_mem
        (MeasureTheory.self_mem_ae_restrict measurableSet_Ioo) ?_)
    intro s hs
    have hsIcc : s ∈ Set.Icc (0 : Real) t := Set.mem_Icc_of_Ioo hs
    have hηsK := hstay s hsIcc
    obtain ⟨z, hzR, hzEq⟩ := hηsK
    have hηd : MDifferentiableAt 𝓘(Real, Real) I η s := by
      refine ((hηC.contMDiffAt ?_).mdifferentiableAt (by norm_num))
      exact Icc_mem_nhds hs.1 (hs.2.trans_le ht.2)
    have hΦd : MDifferentiableAt I I (Φ.symm : N → M) (η s) :=
      by
        rw [← hzEq]
        exact (Φ.symm.contMDiffOn_toFun.contMDiffAt
          (Φ.symm.open_source.mem_nhds (Φ.map_source' (D.source_sub hzR)))).mdifferentiableAt
          (by decide : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0)
    have hchain := mfderiv_comp s hΦd hηd
    have happ : mfderiv 𝓘(Real, Real) I δ s 1 =
        mfderiv I I (Φ.symm : N → M) (η s)
          (mfderiv 𝓘(Real, Real) I η s 1) := by
      simpa only [δ] using congrArg (fun f => f 1) hchain
    rw [happ]
    set w := mfderiv 𝓘(Real, Real) I η s 1
    have hPval : g.inner ((Φ.symm : N → M) (η s))
        (mfderiv I I (Φ.symm : N → M) (η s) w)
        (mfderiv I I (Φ.symm : N → M) (η s) w) =
          D.reverse.pullback (η s) (fun _ => w) := by
      rw [D.reverse.pullback_apply (η s) ⟨z, hzR, hzEq⟩ (fun _ => w)]
    have hquad : D.reverse.pullback (η s) (fun _ => w) ≤
        (1 + eps) * h.inner (η s) w w :=
      speed_le_of_c0 (I := I) D.reverse.pullback h
        (D.reverse.c0_small (η s) ⟨z, hzR, hzEq⟩) w
    calc
      ‖mfderiv I I (Φ.symm : N → M) (η s) w‖ₑ =
          ENNReal.ofReal (Real.sqrt (g.inner ((Φ.symm : N → M) (η s))
            (mfderiv I I (Φ.symm : N → M) (η s) w)
            (mfderiv I I (Φ.symm : N → M) (η s) w))) := hgnorm _ _
      _ ≤ ENNReal.ofReal (Real.sqrt ((1 + eps) * h.inner (η s) w w)) := by
        refine ENNReal.ofReal_le_ofReal (Real.sqrt_le_sqrt ?_)
        rw [hPval]
        exact hquad
      _ = ENNReal.ofReal (Real.sqrt (1 + eps)) *
          ENNReal.ofReal (Real.sqrt (h.inner (η s) w w)) := by
        rw [Real.sqrt_mul (by linarith [D.forward.eps_pos] : 0 ≤ 1 + eps),
          ENNReal.ofReal_mul (Real.sqrt_nonneg _)]
      _ = ENNReal.ofReal (Real.sqrt (1 + eps)) * ‖w‖ₑ := by
        rw [hhnorm (η s) w]
  have hlenPrefix : Manifold.pathELength (I := I) η 0 t ≤
      Manifold.pathELength (I := I) η 0 1 :=
    Manifold.pathELength_mono le_rfl ht.2
  have hcoefPos : 0 < ENNReal.ofReal (Real.sqrt (1 + eps)) :=
    ENNReal.ofReal_pos.mpr (Real.sqrt_pos.2 (by linarith [D.forward.eps_pos]))
  have hδlt : Manifold.pathELength (I := I) δ 0 t <
      ENNReal.ofReal (Real.sqrt (1 + eps) * A) := by
    calc
      Manifold.pathELength (I := I) δ 0 t ≤
          ENNReal.ofReal (Real.sqrt (1 + eps)) *
            Manifold.pathELength (I := I) η 0 t := hlen
      _ ≤ ENNReal.ofReal (Real.sqrt (1 + eps)) *
            Manifold.pathELength (I := I) η 0 1 :=
        by gcongr
      _ < ENNReal.ofReal (Real.sqrt (1 + eps)) * ENNReal.ofReal A :=
        by
          simpa only [mul_comm] using
            (ENNReal.mul_lt_mul_left hcoefPos.ne' ENNReal.ofReal_ne_top hηlen)
      _ = ENNReal.ofReal (Real.sqrt (1 + eps) * A) := by
        rw [ENNReal.ofReal_mul (Real.sqrt_nonneg _)]
  have hxx' : dist x x' < Real.sqrt (1 + eps) * A := by
    have hedLe : Manifold.riemannianEDist I x x' ≤
        Manifold.pathELength (I := I) δ 0 t :=
      Manifold.riemannianEDist_le_pathELength hδC hδ0 hδt ht.1.le
    have hedLt := hedLe.trans_lt hδlt
    rw [← IsRiemannianManifold.out (I := I), edist_dist,
      ENNReal.ofReal_lt_ofReal_iff
        (mul_pos (Real.sqrt_pos.2 (by linarith [D.forward.eps_pos])) hA)] at hedLt
    exact hedLt
  have hxDist : dist O x < r := by
    simpa only [Metric.mem_ball, dist_comm] using hx
  have hcontra : dist O x' < R := by
    calc
      dist O x' ≤ dist O x + dist x x' := dist_triangle _ _ _
      _ < r + Real.sqrt (1 + eps) * A := add_lt_add hxDist hxx'
      _ = Real.sqrt (1 + eps) * A + r := add_comm _ _
      _ < R := hmargin
  linarith

end HCGCompactness
end DifferentialGeometry
