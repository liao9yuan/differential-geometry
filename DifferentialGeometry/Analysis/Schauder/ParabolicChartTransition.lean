import DifferentialGeometry.Analysis.Schauder.ParabolicChart
import DifferentialGeometry.Analysis.Schauder.ParabolicComposition
import DifferentialGeometry.Analysis.Schauder.Interpolation
import DifferentialGeometry.Analysis.Sobolev.Chart.ChartTransition.ChartPullbackSmooth

noncomputable section

open Set
open scoped ContDiff ENNReal NNReal Manifold

namespace DifferentialGeometry.Analysis.Schauder

open DifferentialGeometry.Analysis.Sobolev.Chart

variable {E F H M : Type*}
  [NormedAddCommGroup E] [NormedSpace Real E]
  [NormedAddCommGroup F] [NormedSpace Real F]
  [TopologicalSpace H] {I : ModelWithCorners Real E H}
  [TopologicalSpace M] [ChartedSpace H M]

omit [NormedAddCommGroup F] [NormedSpace Real F] in
theorem parabolicEuclideanChartRepresentation_eq_parabolicSpatialPullback_chartTransitionEuclid
    [FiniteDimensional Real E] [I.Boundaryless]
    (gamma delta : M) (u : Real → M → F) (J : Set Real) :
    Set.EqOn (fun p ↦
        parabolicEuclideanChartRepresentation I gamma u p.time p.space)
      (fun p ↦ parabolicSpatialPullback
        (chartTransitionEuclid (I := I) (M := M) gamma delta)
        (parabolicEuclideanChartRepresentation I delta u) p.time p.space)
      (parabolicCylinder J
        (chartOverlapEuclid (I := I) (M := M) gamma delta)) := by
  intro p hp
  rcases hp.2 with ⟨z, ⟨x, hx, hxz⟩, hzy⟩
  have hxGamma : x ∈ (extChartAt I gamma).source := by
    rw [extChartAt_source (I := I)]
    exact hx.1
  have hxDelta : x ∈ (extChartAt I delta).source := by
    rw [extChartAt_source (I := I)]
    exact hx.2
  have hgamma :
      (extChartAt I gamma).symm
          ((toEuclidean (E := E)).symm p.space) = x := by
    rw [← hzy, ← hxz, (toEuclidean (E := E)).symm_apply_apply]
    exact (extChartAt I gamma).left_inv hxGamma
  have htransition :
      chartTransitionEuclid (I := I) (M := M) gamma delta p.space =
        (toEuclidean (E := E)) (extChartAt I delta x) := by
    rw [← hzy, ← hxz]
    exact chartTransitionEuclid_eq_chartα_image
      (I := I) (M := M) gamma delta hx.1
  have hdelta :
      (extChartAt I delta).symm
          ((toEuclidean (E := E)).symm
            (chartTransitionEuclid (I := I) (M := M)
              gamma delta p.space)) = x := by
    rw [htransition, (toEuclidean (E := E)).symm_apply_apply]
    exact (extChartAt I delta).left_inv hxDelta
  change parabolicEuclideanChartRepresentation I gamma u p.time p.space =
    parabolicSpatialPullback
      (chartTransitionEuclid (I := I) (M := M) gamma delta)
      (parabolicEuclideanChartRepresentation I delta u) p.time p.space
  rw [parabolicEuclideanChartRepresentation_apply,
    parabolicSpatialPullback_apply,
    parabolicEuclideanChartRepresentation_apply, hgamma, hdelta]

private theorem exists_chart_transition_lower_jet_gauge_bound
    [FiniteDimensional Real E] [I.Boundaryless] [IsManifold I ∞ M]
    (gamma delta : M) {s : Set (EuclideanSpace Real
      (Fin (Module.finrank Real E)))}
    (hs : IsCompact s) (hsconv : Convex Real s)
    (hsOverlap : s ⊆
      chartOverlapEuclid (I := I) (M := M) gamma delta)
    {beta : NNReal} (hbeta : beta ≤ 1) (J : Set Real) :
    ∃ Kgamma : NNReal,
      ∀ {R : Set (ParabolicPoint
          (EuclideanSpace Real (Fin (Module.finrank Real E))))}
        {u : Real → M → F},
        MapsTo
          (parabolicMap
            (chartTransitionEuclid (I := I) (M := M) gamma delta))
          (parabolicCylinder J s) R →
        IsParabolicC2On R
          (parabolicEuclideanChartRepresentation I delta u) →
        eParabolicC2HolderGaugeWithLowerJetsInEuclideanChartOn
            beta I gamma (parabolicCylinder J s) u ≤
          Kgamma *
            eParabolicC2HolderGaugeWithLowerJetsInEuclideanChartOn
              beta I delta R u := by
  have hOverlapOpen : IsOpen
      (chartOverlapEuclid (I := I) (M := M) gamma delta) :=
    chartOverlapEuclid_isOpen (I := I) (M := M) gamma delta
  have htransition : ContDiffOn Real 3
      (chartTransitionEuclid (I := I) (M := M) gamma delta)
      (chartOverlapEuclid (I := I) (M := M) gamma delta) :=
    (chartTransitionEuclid_contDiffOn_overlap
      (I := I) (M := M) gamma delta).of_le
        (WithTop.coe_le_coe.mpr
          (le_top : ((3 : Nat) : ℕ∞) ≤ ⊤))
  obtain ⟨Kpull, hpull⟩ :=
    exists_eParabolicC2HolderGaugeWithLowerJetsOn_parabolicSpatialPullback_le_mul_of_contDiffOn
      (F := F) hs hsconv hOverlapOpen hsOverlap htransition hbeta J
  refine ⟨Kpull, ?_⟩
  intro R u hmap hu
  change eParabolicC2HolderGaugeWithLowerJetsOn beta
      (parabolicCylinder J s)
        (parabolicEuclideanChartRepresentation I gamma u) ≤
    (Kpull : ENNReal) *
      eParabolicC2HolderGaugeWithLowerJetsOn beta R
        (parabolicEuclideanChartRepresentation I delta u)
  rw [eParabolicC2HolderGaugeWithLowerJetsOn_congr_of_eqOn_open
    (isOpen_parabolicCylinder isOpen_univ hOverlapOpen)
    (fun p hp ↦ ⟨Set.mem_univ p.time, hsOverlap hp.2⟩)
    (parabolicEuclideanChartRepresentation_eq_parabolicSpatialPullback_chartTransitionEuclid
      gamma delta u Set.univ) beta]
  exact hpull hmap hu

theorem exists_eParabolicC2HolderGaugeInEuclideanChartOn_le_mul_of_chartTransition_of_nested_source_balls
    [FiniteDimensional Real E] [I.Boundaryless] [IsManifold I ∞ M]
    (gamma delta : M) {s : Set (EuclideanSpace Real
      (Fin (Module.finrank Real E)))}
    (hs : IsCompact s) (hsconv : Convex Real s)
    (hsOverlap : s ⊆
      chartOverlapEuclid (I := I) (M := M) gamma delta)
    {beta : NNReal} (hbeta : beta ≤ 1)
    (J : Set Real) (hJ : Convex Real J)
    (sourceCenter : EuclideanSpace Real (Fin (Module.finrank Real E)))
    {r R : Real} (hrR : r < R) :
    ∃ Kgamma : NNReal,
      ∀ {u : Real → M → F},
        MapsTo
          (parabolicMap
            (chartTransitionEuclid (I := I) (M := M) gamma delta))
          (parabolicCylinder J s)
          (parabolicCylinder J (Metric.closedBall sourceCenter r)) →
        IsParabolicC2On
          (parabolicCylinder J (Metric.ball sourceCenter R))
          (parabolicEuclideanChartRepresentation I delta u) →
        eParabolicC2HolderGaugeInEuclideanChartOn
            beta I gamma (parabolicCylinder J s) u ≤
          Kgamma *
            eParabolicC2HolderGaugeInEuclideanChartOn
              beta I delta
                (parabolicCylinder J (Metric.ball sourceCenter R)) u := by
  obtain ⟨Kpull, hpull⟩ :=
    exists_chart_transition_lower_jet_gauge_bound
      (F := F) gamma delta hs hsconv hsOverlap hbeta J
  let gap := Real.toNNReal (R - r)
  let Klower := bufferedParabolicC2HolderGaugeWithLowerJetsFactor gap
  refine ⟨Kpull * Klower, ?_⟩
  intro u hmap hu
  have hrRsubset : Metric.closedBall sourceCenter r ⊆
      Metric.ball sourceCenter R := by
    intro x hx
    rw [Metric.mem_ball]
    exact (Metric.mem_closedBall.mp hx).trans_lt hrR
  have huInner : IsParabolicC2On
      (parabolicCylinder J (Metric.closedBall sourceCenter r))
      (parabolicEuclideanChartRepresentation I delta u) := by
    exact ⟨
      fun p hp ↦ hu.1 p ⟨hp.1, hrRsubset hp.2⟩,
      fun p hp ↦ hu.2 p ⟨hp.1, hrRsubset hp.2⟩⟩
  have hsource :=
    eParabolicC2HolderGaugeWithLowerJetsOn_le_mul_of_nested_balls
      hJ sourceCenter hrR hbeta hu
  calc
    eParabolicC2HolderGaugeInEuclideanChartOn
        beta I gamma (parabolicCylinder J s) u ≤
      eParabolicC2HolderGaugeWithLowerJetsInEuclideanChartOn
        beta I gamma (parabolicCylinder J s) u :=
      eParabolicC2HolderGaugeInEuclideanChartOn_le_with_lower_jets
        beta I gamma (parabolicCylinder J s) u
    _ ≤ (Kpull : ENNReal) *
        eParabolicC2HolderGaugeWithLowerJetsInEuclideanChartOn
          beta I delta
            (parabolicCylinder J (Metric.closedBall sourceCenter r)) u :=
      hpull hmap huInner
    _ ≤ (Kpull : ENNReal) * (Klower : ENNReal) *
        eParabolicC2HolderGaugeInEuclideanChartOn
          beta I delta
            (parabolicCylinder J (Metric.ball sourceCenter R)) u := by
      calc
        (Kpull : ENNReal) *
            eParabolicC2HolderGaugeWithLowerJetsInEuclideanChartOn
              beta I delta
                (parabolicCylinder J
                  (Metric.closedBall sourceCenter r)) u ≤
          (Kpull : ENNReal) *
            ((Klower : ENNReal) *
              eParabolicC2HolderGaugeInEuclideanChartOn
                beta I delta
                  (parabolicCylinder J
                    (Metric.ball sourceCenter R)) u) := by
          have hsource' : eParabolicC2HolderGaugeWithLowerJetsInEuclideanChartOn
              beta I delta
                (parabolicCylinder J (Metric.closedBall sourceCenter r)) u ≤
            (Klower : ENNReal) *
              eParabolicC2HolderGaugeInEuclideanChartOn beta I delta
                (parabolicCylinder J (Metric.ball sourceCenter R)) u := by
            change eParabolicC2HolderGaugeWithLowerJetsOn beta
              (parabolicCylinder J (Metric.closedBall sourceCenter r))
                (parabolicEuclideanChartRepresentation I delta u) ≤
              (Klower : ENNReal) *
                eParabolicC2HolderGaugeOn beta
                  (parabolicCylinder J (Metric.ball sourceCenter R))
                    (parabolicEuclideanChartRepresentation I delta u)
            simpa only [Klower, gap] using hsource
          simpa only [mul_comm] using
            mul_le_mul_right hsource' (Kpull : ENNReal)
        _ = (Kpull : ENNReal) * (Klower : ENNReal) *
            eParabolicC2HolderGaugeInEuclideanChartOn
              beta I delta
                (parabolicCylinder J (Metric.ball sourceCenter R)) u := by
          rw [mul_assoc]
    _ = ((Kpull * Klower : NNReal) : ENNReal) *
        eParabolicC2HolderGaugeInEuclideanChartOn
          beta I delta
            (parabolicCylinder J (Metric.ball sourceCenter R)) u := by
      push_cast
      rfl

theorem exists_eParabolicC2HolderGaugeInEuclideanChartOn_le_of_chartTransition_of_nested_source_balls
    [FiniteDimensional Real E] [I.Boundaryless] [IsManifold I ∞ M]
    (gamma delta : M) {s : Set (EuclideanSpace Real
      (Fin (Module.finrank Real E)))}
    (hs : IsCompact s) (hsconv : Convex Real s)
    (hsOverlap : s ⊆
      chartOverlapEuclid (I := I) (M := M) gamma delta)
    {beta : NNReal} (hbeta : beta ≤ 1)
    (J : Set Real) (hJ : Convex Real J)
    (sourceCenter : EuclideanSpace Real (Fin (Module.finrank Real E)))
    {r R : Real} (hrR : r < R)
    {u : Real → M → F}
    (hmap : MapsTo
      (parabolicMap
        (chartTransitionEuclid (I := I) (M := M) gamma delta))
      (parabolicCylinder J s)
      (parabolicCylinder J (Metric.closedBall sourceCenter r)))
    (hu : IsParabolicC2On
      (parabolicCylinder J (Metric.ball sourceCenter R))
      (parabolicEuclideanChartRepresentation I delta u))
    {C : NNReal}
    (hsource : eParabolicC2HolderGaugeInEuclideanChartOn
      beta I delta (parabolicCylinder J (Metric.ball sourceCenter R)) u ≤
        C) :
    ∃ Kgamma : NNReal,
      eParabolicC2HolderGaugeInEuclideanChartOn
          beta I gamma (parabolicCylinder J s) u ≤ Kgamma * C := by
  obtain ⟨Kgamma, hgamma⟩ :=
    exists_eParabolicC2HolderGaugeInEuclideanChartOn_le_mul_of_chartTransition_of_nested_source_balls
      (F := F) gamma delta hs hsconv hsOverlap hbeta J hJ sourceCenter hrR
  refine ⟨Kgamma, (hgamma hmap hu).trans ?_⟩
  exact mul_le_mul_right hsource Kgamma

theorem exists_eParabolicC2HolderGaugeWithLowerJetsInEuclideanChartOn_le_mul_of_chartTransition
    [FiniteDimensional Real E] [I.Boundaryless] [IsManifold I ∞ M]
    (gamma delta : M) {s : Set (EuclideanSpace Real
      (Fin (Module.finrank Real E)))}
    (hs : IsCompact s) (hsconv : Convex Real s)
    (hsOverlap : s ⊆
      chartOverlapEuclid (I := I) (M := M) gamma delta)
    {beta : NNReal} (hbeta : beta ≤ 1) (J : Set Real) :
    ∃ Kgamma : NNReal,
      ∀ {R : Set (ParabolicPoint
          (EuclideanSpace Real (Fin (Module.finrank Real E))))}
        {u : Real → M → F},
        MapsTo
          (parabolicMap
            (chartTransitionEuclid (I := I) (M := M) gamma delta))
          (parabolicCylinder J s) R →
        IsParabolicC2On R
          (parabolicEuclideanChartRepresentation I delta u) →
        eParabolicC2HolderGaugeWithLowerJetsInEuclideanChartOn
            beta I gamma (parabolicCylinder J s) u ≤
          Kgamma *
            eParabolicC2HolderGaugeWithLowerJetsInEuclideanChartOn
              beta I delta R u := by
  exact exists_chart_transition_lower_jet_gauge_bound
    (F := F) gamma delta hs hsconv hsOverlap hbeta J

theorem exists_eParabolicC2HolderGaugeWithLowerJetsInEuclideanChartOn_le_of_chartTransition
    [FiniteDimensional Real E] [I.Boundaryless] [IsManifold I ∞ M]
    (gamma delta : M) {s : Set (EuclideanSpace Real
      (Fin (Module.finrank Real E)))}
    (hs : IsCompact s) (hsconv : Convex Real s)
    (hsOverlap : s ⊆
      chartOverlapEuclid (I := I) (M := M) gamma delta)
    {beta : NNReal} (hbeta : beta ≤ 1) (J : Set Real)
    {R : Set (ParabolicPoint
      (EuclideanSpace Real (Fin (Module.finrank Real E))))}
    {u : Real → M → F}
    (hmap : MapsTo
      (parabolicMap
        (chartTransitionEuclid (I := I) (M := M) gamma delta))
      (parabolicCylinder J s) R)
    (hu : IsParabolicC2On R
      (parabolicEuclideanChartRepresentation I delta u))
    {C : NNReal}
    (hsource : eParabolicC2HolderGaugeWithLowerJetsInEuclideanChartOn
      beta I delta R u ≤ C) :
    ∃ Kgamma : NNReal,
      eParabolicC2HolderGaugeWithLowerJetsInEuclideanChartOn
          beta I gamma (parabolicCylinder J s) u ≤ Kgamma * C := by
  obtain ⟨Kgamma, hgamma⟩ :=
    exists_eParabolicC2HolderGaugeWithLowerJetsInEuclideanChartOn_le_mul_of_chartTransition
      (F := F) gamma delta hs hsconv hsOverlap hbeta J
  refine ⟨Kgamma, (hgamma hmap hu).trans ?_⟩
  exact mul_le_mul_right hsource Kgamma

theorem exists_eParabolicC2HolderGaugeWithLowerJetsInEuclideanChartOn_le_of_chartTransition_image
    [FiniteDimensional Real E] [I.Boundaryless] [IsManifold I ∞ M]
    (gamma delta : M) {s : Set (EuclideanSpace Real
      (Fin (Module.finrank Real E)))}
    (hs : IsCompact s) (hsconv : Convex Real s)
    (hsOverlap : s ⊆
      chartOverlapEuclid (I := I) (M := M) gamma delta)
    {beta : NNReal} (hbeta : beta ≤ 1) (J : Set Real)
    {u : Real → M → F}
    (hu : IsParabolicC2On
      (parabolicMap
          (chartTransitionEuclid (I := I) (M := M) gamma delta) ''
        parabolicCylinder J s)
      (parabolicEuclideanChartRepresentation I delta u))
    {C : NNReal}
    (hsource : eParabolicC2HolderGaugeWithLowerJetsInEuclideanChartOn
      beta I delta
        (parabolicMap
            (chartTransitionEuclid (I := I) (M := M) gamma delta) ''
          parabolicCylinder J s) u ≤ C) :
    ∃ Kgamma : NNReal,
      eParabolicC2HolderGaugeWithLowerJetsInEuclideanChartOn
          beta I gamma (parabolicCylinder J s) u ≤ Kgamma * C := by
  exact
    exists_eParabolicC2HolderGaugeWithLowerJetsInEuclideanChartOn_le_of_chartTransition
      (R := parabolicMap
          (chartTransitionEuclid (I := I) (M := M) gamma delta) ''
        parabolicCylinder J s)
      (u := u) (C := C) gamma delta hs hsconv hsOverlap hbeta J
      (fun p hp ↦ ⟨p, hp, rfl⟩) hu hsource

theorem exists_eParabolicC2HolderGaugeInEuclideanChartsOn_le_mul_of_chartTransitions_of_nested_source_balls
    [FiniteDimensional Real E] [I.Boundaryless] [IsManifold I ∞ M]
    {A : Type*} [Finite A] (center source : A → M)
    (s : A → Set (EuclideanSpace Real
      (Fin (Module.finrank Real E))))
    (hs : ∀ i, IsCompact (s i)) (hsconv : ∀ i, Convex Real (s i))
    (hsOverlap : ∀ i, s i ⊆
      chartOverlapEuclid (I := I) (M := M) (center i) (source i))
    {beta : NNReal} (hbeta : beta ≤ 1)
    (J : Set Real) (hJ : Convex Real J)
    (sourceBallCenter : A →
      EuclideanSpace Real (Fin (Module.finrank Real E)))
    (r R : A → Real) (hrR : ∀ i, r i < R i) :
    ∃ Katlas : NNReal,
      ∀ {u : Real → M → F},
        (∀ i, MapsTo
          (parabolicMap
            (chartTransitionEuclid
              (I := I) (M := M) (center i) (source i)))
          (parabolicCylinder J (s i))
          (parabolicCylinder J
            (Metric.closedBall (sourceBallCenter i) (r i)))) →
        (∀ i, IsParabolicC2On
          (parabolicCylinder J
            (Metric.ball (sourceBallCenter i) (R i)))
          (parabolicEuclideanChartRepresentation I (source i) u)) →
        eParabolicC2HolderGaugeInEuclideanChartsOn
            beta I center (fun i ↦ parabolicCylinder J (s i)) u ≤
          Katlas *
            eParabolicC2HolderGaugeInEuclideanChartsOn
              beta I source
                (fun i ↦ parabolicCylinder J
                  (Metric.ball (sourceBallCenter i) (R i))) u := by
  classical
  letI := Fintype.ofFinite A
  have hlocal : ∀ i, ∃ Ktarget : NNReal,
      ∀ {utarget : Real → M → F},
        MapsTo
          (parabolicMap
            (chartTransitionEuclid
              (I := I) (M := M) (center i) (source i)))
          (parabolicCylinder J (s i))
          (parabolicCylinder J
            (Metric.closedBall (sourceBallCenter i) (r i))) →
        IsParabolicC2On
          (parabolicCylinder J
            (Metric.ball (sourceBallCenter i) (R i)))
          (parabolicEuclideanChartRepresentation I (source i) utarget) →
        eParabolicC2HolderGaugeInEuclideanChartOn
            beta I (center i) (parabolicCylinder J (s i)) utarget ≤
          Ktarget *
            eParabolicC2HolderGaugeInEuclideanChartOn
              beta I (source i)
                (parabolicCylinder J
                  (Metric.ball (sourceBallCenter i) (R i))) utarget := by
    intro i
    exact
      exists_eParabolicC2HolderGaugeInEuclideanChartOn_le_mul_of_chartTransition_of_nested_source_balls
        (F := F) (center i) (source i) (hs i) (hsconv i) (hsOverlap i)
        hbeta J hJ (sourceBallCenter i) (hrR i)
  choose Ktarget htarget using hlocal
  refine ⟨∑ i, Ktarget i, ?_⟩
  intro u hmap hu
  apply
    (eParabolicC2HolderGaugeInEuclideanChartsOn_le_iff
      beta I center (fun i ↦ parabolicCylinder J (s i)) u _).2
  intro i
  calc
    eParabolicC2HolderGaugeInEuclideanChartOn
        beta I (center i) (parabolicCylinder J (s i)) u ≤
      (Ktarget i : ENNReal) *
        eParabolicC2HolderGaugeInEuclideanChartOn
          beta I (source i)
            (parabolicCylinder J
              (Metric.ball (sourceBallCenter i) (R i))) u :=
      htarget i (hmap i) (hu i)
    _ ≤ (Ktarget i : ENNReal) *
        eParabolicC2HolderGaugeInEuclideanChartsOn
          beta I source
            (fun j ↦ parabolicCylinder J
              (Metric.ball (sourceBallCenter j) (R j))) u := by
      exact mul_le_mul_right
        (eParabolicC2HolderGaugeInEuclideanChartOn_le_euclideanCharts
          beta I source
            (fun j ↦ parabolicCylinder J
              (Metric.ball (sourceBallCenter j) (R j))) u i)
        (Ktarget i)
    _ ≤ ((∑ j, Ktarget j : NNReal) : ENNReal) *
        eParabolicC2HolderGaugeInEuclideanChartsOn
          beta I source
            (fun j ↦ parabolicCylinder J
              (Metric.ball (sourceBallCenter j) (R j))) u := by
      have hcoefficient : (Ktarget i : ENNReal) ≤
          ((∑ j, Ktarget j : NNReal) : ENNReal) := by
        exact_mod_cast
          (Finset.single_le_sum (fun j _ ↦ zero_le (Ktarget j))
            (Finset.mem_univ i))
      calc
        (Ktarget i : ENNReal) *
            eParabolicC2HolderGaugeInEuclideanChartsOn
              beta I source
                (fun j ↦ parabolicCylinder J
                  (Metric.ball (sourceBallCenter j) (R j))) u =
          eParabolicC2HolderGaugeInEuclideanChartsOn
              beta I source
                (fun j ↦ parabolicCylinder J
                  (Metric.ball (sourceBallCenter j) (R j))) u *
            Ktarget i := mul_comm _ _
        _ ≤ eParabolicC2HolderGaugeInEuclideanChartsOn
              beta I source
                (fun j ↦ parabolicCylinder J
                  (Metric.ball (sourceBallCenter j) (R j))) u *
            ((∑ j, Ktarget j : NNReal) : ENNReal) :=
          mul_le_mul_right hcoefficient _
        _ = ((∑ j, Ktarget j : NNReal) : ENNReal) *
            eParabolicC2HolderGaugeInEuclideanChartsOn
              beta I source
                (fun j ↦ parabolicCylinder J
                  (Metric.ball (sourceBallCenter j) (R j))) u :=
          mul_comm _ _

theorem exists_eParabolicC2HolderGaugeInEuclideanChartsOn_le_of_chartTransitions_of_nested_source_balls
    [FiniteDimensional Real E] [I.Boundaryless] [IsManifold I ∞ M]
    {A : Type*} [Finite A] (center source : A → M)
    (s : A → Set (EuclideanSpace Real
      (Fin (Module.finrank Real E))))
    (hs : ∀ i, IsCompact (s i)) (hsconv : ∀ i, Convex Real (s i))
    (hsOverlap : ∀ i, s i ⊆
      chartOverlapEuclid (I := I) (M := M) (center i) (source i))
    {beta : NNReal} (hbeta : beta ≤ 1)
    (J : Set Real) (hJ : Convex Real J)
    (sourceBallCenter : A →
      EuclideanSpace Real (Fin (Module.finrank Real E)))
    (r R : A → Real) (hrR : ∀ i, r i < R i)
    {u : Real → M → F}
    (hmap : ∀ i, MapsTo
      (parabolicMap
        (chartTransitionEuclid
          (I := I) (M := M) (center i) (source i)))
      (parabolicCylinder J (s i))
      (parabolicCylinder J
        (Metric.closedBall (sourceBallCenter i) (r i))))
    (hu : ∀ i, IsParabolicC2On
      (parabolicCylinder J
        (Metric.ball (sourceBallCenter i) (R i)))
      (parabolicEuclideanChartRepresentation I (source i) u))
    {C : NNReal}
    (hsource : eParabolicC2HolderGaugeInEuclideanChartsOn
      beta I source
        (fun i ↦ parabolicCylinder J
          (Metric.ball (sourceBallCenter i) (R i))) u ≤ C) :
    ∃ Katlas : NNReal,
      eParabolicC2HolderGaugeInEuclideanChartsOn
          beta I center (fun i ↦ parabolicCylinder J (s i)) u ≤
        Katlas * C := by
  obtain ⟨Katlas, hatlas⟩ :=
    exists_eParabolicC2HolderGaugeInEuclideanChartsOn_le_mul_of_chartTransitions_of_nested_source_balls
      (F := F) center source s hs hsconv hsOverlap hbeta J hJ
      sourceBallCenter r R hrR
  refine ⟨Katlas, (hatlas hmap hu).trans ?_⟩
  exact mul_le_mul_right hsource Katlas

theorem exists_eParabolicC2HolderGaugeWithLowerJetsInEuclideanChartsOn_le_of_chartwise_chartTransitions
    [FiniteDimensional Real E] [I.Boundaryless] [IsManifold I ∞ M]
    {A : Type*} [Finite A] (center source : A → M)
    (s : A → Set (EuclideanSpace Real
      (Fin (Module.finrank Real E))))
    (hs : ∀ i, IsCompact (s i)) (hsconv : ∀ i, Convex Real (s i))
    (hsOverlap : ∀ i, s i ⊆
      chartOverlapEuclid (I := I) (M := M) (center i) (source i))
    {beta : NNReal} (hbeta : beta ≤ 1) (J : Set Real)
    {R : A → Set (ParabolicPoint
      (EuclideanSpace Real (Fin (Module.finrank Real E))))}
    {u : Real → M → F}
    (hmap : ∀ i, MapsTo
      (parabolicMap
        (chartTransitionEuclid (I := I) (M := M) (center i) (source i)))
      (parabolicCylinder J (s i)) (R i))
    (hu : ∀ i, IsParabolicC2On (R i)
      (parabolicEuclideanChartRepresentation I (source i) u))
    (Csource : A → NNReal)
    (hsource : ∀ i,
      eParabolicC2HolderGaugeWithLowerJetsInEuclideanChartOn
        beta I (source i) (R i) u ≤ Csource i) :
    ∃ Catlas : NNReal,
      eParabolicC2HolderGaugeWithLowerJetsInEuclideanChartsOn
          beta I center (fun i ↦ parabolicCylinder J (s i)) u ≤ Catlas := by
  classical
  letI := Fintype.ofFinite A
  have hlocal : ∀ i, ∃ Ctarget : NNReal,
      eParabolicC2HolderGaugeWithLowerJetsInEuclideanChartOn
          beta I (center i) (parabolicCylinder J (s i)) u ≤ Ctarget := by
    intro i
    obtain ⟨Ktarget, htarget⟩ :=
      exists_eParabolicC2HolderGaugeWithLowerJetsInEuclideanChartOn_le_of_chartTransition
        (center i) (source i) (hs i) (hsconv i) (hsOverlap i)
        hbeta J (hmap i) (hu i) (hsource i)
    exact ⟨Ktarget * Csource i, htarget⟩
  choose Ctarget htarget using hlocal
  refine ⟨∑ i, Ctarget i, ?_⟩
  exact
    eParabolicC2HolderGaugeWithLowerJetsInEuclideanChartsOn_le_sum_of_finite
      beta I center (fun i ↦ parabolicCylinder J (s i)) u Ctarget htarget

theorem exists_eParabolicC2HolderGaugeWithLowerJetsInEuclideanChartsOn_le_mul_of_chartTransitions
    [FiniteDimensional Real E] [I.Boundaryless] [IsManifold I ∞ M]
    {A : Type*} [Finite A] (center source : A → M)
    (s : A → Set (EuclideanSpace Real
      (Fin (Module.finrank Real E))))
    (hs : ∀ i, IsCompact (s i)) (hsconv : ∀ i, Convex Real (s i))
    (hsOverlap : ∀ i, s i ⊆
      chartOverlapEuclid (I := I) (M := M) (center i) (source i))
    {beta : NNReal} (hbeta : beta ≤ 1) (J : Set Real) :
    ∃ Katlas : NNReal,
      ∀ {R : A → Set (ParabolicPoint
          (EuclideanSpace Real (Fin (Module.finrank Real E))))}
        {u : Real → M → F},
        (∀ i, MapsTo
          (parabolicMap
            (chartTransitionEuclid (I := I) (M := M) (center i) (source i)))
          (parabolicCylinder J (s i)) (R i)) →
        (∀ i, IsParabolicC2On (R i)
          (parabolicEuclideanChartRepresentation I (source i) u)) →
        eParabolicC2HolderGaugeWithLowerJetsInEuclideanChartsOn
            beta I center (fun i ↦ parabolicCylinder J (s i)) u ≤
          Katlas *
            eParabolicC2HolderGaugeWithLowerJetsInEuclideanChartsOn
              beta I source R u := by
  classical
  letI := Fintype.ofFinite A
  have hlocal : ∀ i, ∃ Ktarget : NNReal,
      ∀ {Rtarget : Set (ParabolicPoint
          (EuclideanSpace Real (Fin (Module.finrank Real E))))}
        {utarget : Real → M → F},
        MapsTo
          (parabolicMap
            (chartTransitionEuclid (I := I) (M := M) (center i) (source i)))
          (parabolicCylinder J (s i)) Rtarget →
        IsParabolicC2On Rtarget
          (parabolicEuclideanChartRepresentation I (source i) utarget) →
        eParabolicC2HolderGaugeWithLowerJetsInEuclideanChartOn
            beta I (center i) (parabolicCylinder J (s i)) utarget ≤
          Ktarget *
            eParabolicC2HolderGaugeWithLowerJetsInEuclideanChartOn
              beta I (source i) Rtarget utarget := by
    intro i
    exact
      exists_eParabolicC2HolderGaugeWithLowerJetsInEuclideanChartOn_le_mul_of_chartTransition
        (F := F) (center i) (source i) (hs i) (hsconv i) (hsOverlap i)
        hbeta J
  choose Ktarget htarget using hlocal
  refine ⟨∑ i, Ktarget i, ?_⟩
  intro R u hmap hu
  apply
    (eParabolicC2HolderGaugeWithLowerJetsInEuclideanChartsOn_le_iff
      beta I center (fun i ↦ parabolicCylinder J (s i)) u _).2
  intro i
  calc
    eParabolicC2HolderGaugeWithLowerJetsInEuclideanChartOn
        beta I (center i) (parabolicCylinder J (s i)) u ≤
        (Ktarget i : ENNReal) *
          eParabolicC2HolderGaugeWithLowerJetsInEuclideanChartOn
            beta I (source i) (R i) u := htarget i (hmap i) (hu i)
    _ ≤ (Ktarget i : ENNReal) *
        eParabolicC2HolderGaugeWithLowerJetsInEuclideanChartsOn
          beta I source R u := by
      exact mul_le_mul_right
        (eParabolicC2HolderGaugeWithLowerJetsInEuclideanChartOn_le_euclideanCharts
          beta I source R u i) (Ktarget i)
    _ ≤ ((∑ j, Ktarget j : NNReal) : ENNReal) *
        eParabolicC2HolderGaugeWithLowerJetsInEuclideanChartsOn
          beta I source R u := by
      have hcoefficient : (Ktarget i : ENNReal) ≤
          ((∑ j, Ktarget j : NNReal) : ENNReal) := by
        exact_mod_cast
          (Finset.single_le_sum (fun j _ ↦ zero_le (Ktarget j))
            (Finset.mem_univ i))
      calc
        (Ktarget i : ENNReal) *
            eParabolicC2HolderGaugeWithLowerJetsInEuclideanChartsOn
              beta I source R u =
            eParabolicC2HolderGaugeWithLowerJetsInEuclideanChartsOn
              beta I source R u * Ktarget i := mul_comm _ _
        _ ≤ eParabolicC2HolderGaugeWithLowerJetsInEuclideanChartsOn
              beta I source R u *
            ((∑ j, Ktarget j : NNReal) : ENNReal) :=
          mul_le_mul_right hcoefficient _
        _ = ((∑ j, Ktarget j : NNReal) : ENNReal) *
            eParabolicC2HolderGaugeWithLowerJetsInEuclideanChartsOn
              beta I source R u := mul_comm _ _

theorem exists_eParabolicC2HolderGaugeWithLowerJetsInEuclideanChartsOn_le_of_chartTransitions
    [FiniteDimensional Real E] [I.Boundaryless] [IsManifold I ∞ M]
    {A : Type*} [Finite A] (center source : A → M)
    (s : A → Set (EuclideanSpace Real
      (Fin (Module.finrank Real E))))
    (hs : ∀ i, IsCompact (s i)) (hsconv : ∀ i, Convex Real (s i))
    (hsOverlap : ∀ i, s i ⊆
      chartOverlapEuclid (I := I) (M := M) (center i) (source i))
    {beta : NNReal} (hbeta : beta ≤ 1) (J : Set Real)
    {R : A → Set (ParabolicPoint
      (EuclideanSpace Real (Fin (Module.finrank Real E))))}
    {u : Real → M → F}
    (hmap : ∀ i, MapsTo
      (parabolicMap
        (chartTransitionEuclid (I := I) (M := M) (center i) (source i)))
      (parabolicCylinder J (s i)) (R i))
    (hu : ∀ i, IsParabolicC2On (R i)
      (parabolicEuclideanChartRepresentation I (source i) u))
    {C : NNReal}
    (hsource : eParabolicC2HolderGaugeWithLowerJetsInEuclideanChartsOn
      beta I source R u ≤ C) :
    ∃ Katlas : NNReal,
      eParabolicC2HolderGaugeWithLowerJetsInEuclideanChartsOn
          beta I center (fun i ↦ parabolicCylinder J (s i)) u ≤
        Katlas * C := by
  obtain ⟨Katlas, hatlas⟩ :=
    exists_eParabolicC2HolderGaugeWithLowerJetsInEuclideanChartsOn_le_mul_of_chartTransitions
      (F := F) center source s hs hsconv hsOverlap hbeta J
  refine ⟨Katlas, (hatlas hmap hu).trans ?_⟩
  exact mul_le_mul_right hsource Katlas

end DifferentialGeometry.Analysis.Schauder

end
