import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.StepCAveraging
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.StepCSmoothness

set_option autoImplicit false
set_option linter.style.longLine false

/-!
# Admissible configurations and ambient Step-C center extensions

The full configuration space contains negative and identically-zero weight
vectors, so it cannot carry `CenterInput` at every point.  The actual selected
center is therefore defined only on an admissible set (and harmlessly filled
outside it).  Smoothness on an ambient open set belongs instead to an implicit
solution extension, which later must be proved to agree with the actual center
along the finite-hat configuration image.
-/

noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace HCGCompactness

open Set Bundle Manifold
open scoped Topology Manifold ContDiff
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
variable [InnerProductSpace Real E] [FiniteDimensional Real E]
variable [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [T2Space (TangentBundle I M)] [SigmaCompactSpace M]
  [ConnectedSpace M] [T3Space M]

/-- The selected center of mass on an admissible configuration region, filled
by the chart base outside that region. -/
noncomputable def centerCfgOn
    (g : SmoothRiemannianMetric I M) (p : M) {ι : Type} [Fintype ι]
    (join : M -> M -> Real -> M) (r : Real)
    (V : Set ((ι -> Real) × (ι -> E)))
    (h : forall params, params ∈ V ->
      CenterInput (I := I) g params.1
        (fun i => (NormalCoordinates.normalChartAt (I := I) g p).symm (params.2 i))
        join p r) :
    ((ι -> Real) × (ι -> E)) -> M :=
  centerAverageOn (I := I) g V (fun params => params.1)
    (fun params i => (NormalCoordinates.normalChartAt (I := I) g p).symm (params.2 i))
    join (fun _ => p) (fun _ => r) (fun _ => p) h

/-- The chart readout of `centerCfgOn`. -/
noncomputable def chartCenterOn
    (g : SmoothRiemannianMetric I M) (p : M) {ι : Type} [Fintype ι]
    (join : M -> M -> Real -> M) (r : Real)
    (V : Set ((ι -> Real) × (ι -> E)))
    (h : forall params, params ∈ V ->
      CenterInput (I := I) g params.1
        (fun i => (NormalCoordinates.normalChartAt (I := I) g p).symm (params.2 i))
        join p r)
    (params : (ι -> Real) × (ι -> E)) : E :=
  NormalCoordinates.normalChartAt (I := I) g p (centerCfgOn (I := I) g p join r V h params)

/-- On the admissible region, `centerCfgOn` is the genuine selected center of
mass rather than its outside-domain filler. -/
theorem centerCfgOn_eq
    (g : SmoothRiemannianMetric I M) (p : M) {ι : Type} [Fintype ι]
    (join : M -> M -> Real -> M) (r : Real)
    {V : Set ((ι -> Real) × (ι -> E))}
    (h : forall params, params ∈ V ->
      CenterInput (I := I) g params.1
        (fun i => (NormalCoordinates.normalChartAt (I := I) g p).symm (params.2 i))
        join p r)
    {params : (ι -> Real) × (ι -> E)} (hparams : params ∈ V) :
    centerCfgOn (I := I) g p join r V h params =
      centerOfMass (I := I) g params.1
        (fun i => (NormalCoordinates.normalChartAt (I := I) g p).symm (params.2 i))
        join p r (h params hparams) := by
  exact centerAverage.on_eq (I := I) (g := g)
    (μ := fun q : (ι -> Real) × (ι -> E) => q.1)
    (pts := fun q i => (NormalCoordinates.normalChartAt (I := I) g p).symm (q.2 i))
    (join := join) (p := fun _ => p) (r := fun _ => r) (qstar := fun _ => p)
    h hparams

section RootExtension

variable {P₀ : Type*} [TopologicalSpace P₀] [T2Space P₀]

omit [NormedSpace Real E] [InnerProductSpace Real E] [FiniteDimensional Real E]
  [NeZero (Module.finrank Real E)] in
/-- Local pinned inverses along a compact graph glue to one continuous ambient
root extension.  The common injectivity neighborhood is returned explicitly;
agreement with the original root on `B` follows from injectivity, not merely
from the fact that both functions solve the same equation. -/
theorem existsRootExtension
    (G : E -> P₀ -> E) {A B : Set P₀} (hA : IsCompact A) (hAB : A ⊆ B)
    (c : P₀ -> E) (hc : ContinuousOn c B)
    (hc0 : ∀ p ∈ B, G (c p) p = 0)
    (hlocal : ∀ p ∈ A,
      ∃ e : OpenPartialHomeomorph (E × P₀) (E × P₀),
        (c p, p) ∈ e.source ∧
          (e : (E × P₀) -> (E × P₀)) = fun w => (G w.1 w.2, w.2)) :
    ∃ (T : Set (E × P₀)) (V : Set P₀) (z : P₀ -> E),
      IsOpen T ∧ IsOpen V ∧
      (∀ p ∈ A, (c p, p) ∈ T) ∧
      Set.InjOn (fun w : E × P₀ => (G w.1 w.2, w.2)) T ∧
      A ⊆ V ∧ ContinuousOn z V ∧
      (∀ p ∈ V, G (z p) p = 0) ∧ Set.EqOn z c (B ∩ V) := by
  classical
  by_cases hAne : A.Nonempty
  · let F : E × P₀ -> E × P₀ := fun w => (G w.1 w.2, w.2)
    let graph : P₀ -> E × P₀ := fun p => (c p, p)
    let S : Set (E × P₀) := graph '' A
    let eA : ∀ p : A, OpenPartialHomeomorph (E × P₀) (E × P₀) := fun p =>
      Classical.choose (hlocal p p.2)
    have he_mem (p : A) : graph p ∈ (eA p).source :=
      (Classical.choose_spec (hlocal p p.2)).1
    have he_eq (p : A) :
        ((eA p : OpenPartialHomeomorph (E × P₀) (E × P₀)) :
          (E × P₀) -> (E × P₀)) = F :=
      (Classical.choose_spec (hlocal p p.2)).2
    let R : Set (E × P₀) := ⋃ p : A, (eA p).source
    have hRopen : IsOpen R := isOpen_iUnion fun p => (eA p).open_source
    have hSR : S ⊆ R := by
      rintro _ ⟨p, hp, rfl⟩
      exact Set.mem_iUnion.mpr ⟨⟨p, hp⟩, he_mem ⟨p, hp⟩⟩
    have hlocalR : IsLocalHomeomorphOn F R := by
      intro x hx
      obtain ⟨p, hxp⟩ := Set.mem_iUnion.mp hx
      exact ⟨eA p, hxp, (he_eq p).symm⟩
    have hScompact : IsCompact S := by
      exact hA.image_of_continuousOn ((hc.mono hAB).prodMk continuousOn_id)
    have hSinj : Set.InjOn F S := by
      rintro _ ⟨p, hp, rfl⟩ _ ⟨q, hq, rfl⟩ heq
      have hpq : p = q := congrArg Prod.snd heq
      subst q
      rfl
    have hFcont : ∀ x ∈ S, ContinuousAt F x := fun x hx =>
      hlocalR.continuousAt (hSR hx)
    have hFloc : ∀ x ∈ S, ∃ u ∈ 𝓝 x, Set.InjOn F u := by
      intro x hx
      obtain ⟨e, hxe, he⟩ := hlocalR x (hSR hx)
      refine ⟨e.source, e.open_source.mem_nhds hxe, ?_⟩
      simpa only [he] using e.injOn
    obtain ⟨T₀, hT₀open, hST₀, hT₀inj⟩ :=
      Set.InjOn.exists_isOpen_superset hSinj hScompact hFcont hFloc
    let T : Set (E × P₀) := T₀ ∩ R
    have hTopen : IsOpen T := hT₀open.inter hRopen
    have hST : S ⊆ T := fun x hx => ⟨hST₀ hx, hSR hx⟩
    have hTinj : Set.InjOn F T := hT₀inj.mono inter_subset_left
    have hlocalT : IsLocalHomeomorphOn F T := hlocalR.mono inter_subset_right
    have hFopen : IsOpenMap (T.restrict F) := by
      intro W hW
      rw [Set.restrict_eq, Set.image_comp]
      let W₀ : Set (E × P₀) := ((↑) : T -> E × P₀) '' W
      have hW₀open : IsOpen W₀ := hTopen.isOpenMap_subtype_val W hW
      have hW₀T : W₀ ⊆ T := by
        rintro _ ⟨x, hx, rfl⟩
        exact x.2
      change IsOpen (F '' W₀)
      rw [isOpen_iff_forall_mem_open]
      intro y hy
      obtain ⟨x, hxW, rfl⟩ := hy
      obtain ⟨e, hxe, he⟩ := hlocalT x (hW₀T hxW)
      refine ⟨e '' (W₀ ∩ e.source), ?_, ?_, ?_⟩
      · rintro _ ⟨w, hw, rfl⟩
        exact ⟨w, hw.1, congrFun he w⟩
      · exact e.isOpen_image_of_subset_source
          (hW₀open.inter e.open_source) inter_subset_right
      · exact ⟨x, ⟨hxW, hxe⟩, (congrFun he x).symm⟩
    have hFembed : Topology.IsOpenEmbedding (T.restrict F) :=
      .of_continuous_injective_isOpenMap hlocalT.continuousOn.restrict
        hTinj.injective hFopen
    obtain ⟨p₀, hp₀⟩ := hAne
    have hx₀ : graph p₀ ∈ T := hST ⟨p₀, hp₀, rfl⟩
    letI : Nonempty T := ⟨⟨graph p₀, hx₀⟩⟩
    let eT : OpenPartialHomeomorph T (E × P₀) :=
      hFembed.toOpenPartialHomeomorph (T.restrict F)
    have heT_coe : (eT : T -> E × P₀) = T.restrict F := by rfl
    let pair : P₀ -> E × P₀ := fun p => (0, p)
    let V₀ : Set P₀ := pair ⁻¹' eT.target
    have hpair : Continuous pair := continuous_const.prodMk continuous_id
    have hV₀open : IsOpen V₀ := eT.open_target.preimage hpair
    have hAV₀ : A ⊆ V₀ := by
      intro p hp
      change pair p ∈ (hFembed.toOpenPartialHomeomorph (T.restrict F)).target
      rw [Topology.IsOpenEmbedding.toOpenPartialHomeomorph_target]
      refine ⟨⟨graph p, hST ⟨p, hp, rfl⟩⟩, ?_⟩
      change F (graph p) = pair p
      simp only [F, graph, pair, hc0 p (hAB hp)]
    have hgraphB : ContinuousOn graph B := hc.prodMk continuousOn_id
    obtain ⟨O, hOopen, hOeq⟩ := (continuousOn_iff'.mp hgraphB) T hTopen
    let V : Set P₀ := V₀ ∩ O
    have hVopen : IsOpen V := hV₀open.inter hOopen
    have hAV : A ⊆ V := by
      intro p hp
      refine ⟨hAV₀ hp, ?_⟩
      have hp' : p ∈ graph ⁻¹' T ∩ B := ⟨hST ⟨p, hp, rfl⟩, hAB hp⟩
      rw [hOeq] at hp'
      exact hp'.1
    let z : P₀ -> E := fun p => ((eT.symm (pair p) : T) : E × P₀).1
    have hinvVal : ContinuousOn
        (fun y : E × P₀ => ((eT.symm y : T) : E × P₀)) eT.target :=
      continuous_subtype_val.comp_continuousOn eT.continuousOn_symm
    have hinvFst : ContinuousOn
        (fun y : E × P₀ => ((eT.symm y : T) : E × P₀).1) eT.target :=
      continuous_fst.comp_continuousOn hinvVal
    have hzcont₀ : ContinuousOn z V₀ :=
      hinvFst.comp hpair.continuousOn fun p hp => hp
    have hzcont : ContinuousOn z V := hzcont₀.mono inter_subset_left
    have hroot : ∀ p ∈ V, G (z p) p = 0 := by
      intro p hp
      have hri := eT.right_inv hp.1
      rw [heT_coe] at hri
      change F ((eT.symm (pair p) : T) : E × P₀) = pair p at hri
      have hsnd := congrArg Prod.snd hri
      have hfst := congrArg Prod.fst hri
      change G (z p) p = 0
      change (((eT.symm (pair p) : T) : E × P₀).2) = p at hsnd
      change G (z p) (((eT.symm (pair p) : T) : E × P₀).2) = 0 at hfst
      rwa [hsnd] at hfst
    have hagree : Set.EqOn z c (B ∩ V) := by
      intro p hp
      have hpOB : p ∈ O ∩ B := ⟨hp.2.2, hp.1⟩
      rw [← hOeq] at hpOB
      have hcT : graph p ∈ T := hpOB.1
      have hri := eT.right_inv hp.2.1
      rw [heT_coe] at hri
      change F ((eT.symm (pair p) : T) : E × P₀) = pair p at hri
      have hcg : F (graph p) = pair p := by
        simp only [F, graph, pair, hc0 p hp.1]
      have hxg : ((eT.symm (pair p) : T) : E × P₀) = graph p :=
        hTinj (eT.symm (pair p)).2 hcT (hri.trans hcg.symm)
      exact congrArg Prod.fst hxg
    exact ⟨T, V, z, hTopen, hVopen, fun p hp => hST ⟨p, hp, rfl⟩,
      hTinj, hAV, hzcont, hroot, hagree⟩
  · have hAe : A = ∅ := by
      exact Set.not_nonempty_iff_eq_empty.mp hAne
    subst A
    refine ⟨∅, ∅, fun _ => 0, isOpen_empty, isOpen_empty, ?_⟩
    simp

end RootExtension

section SmoothDomain

variable [RiemannianBundle (fun x : M => TangentSpace I x)]
variable [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- The actual selected center satisfies the readout equation on an explicit
branch readout domain once its inverse vectors lie in the named realized-exp
radius. -/
theorem centerReadoutB_zero
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) (B : DiagInvBranch (I := I) g hEnorm p)
    {ι : Type} [Fintype ι] (mu : ι -> Real) (xi : ι -> E)
    (join : M -> M -> Real -> M) (r : Real)
    (h : CenterInput (I := I) g mu
      (fun i => (NormalCoordinates.normalChartAt (I := I) g p).symm (xi i))
      join p r)
    (hcenter : centerOfMass (I := I) g mu
      (fun i => (NormalCoordinates.normalChartAt (I := I) g p).symm (xi i))
      join p r h ∈ (NormalCoordinates.normalChartAt (I := I) g p).source)
    (hdiff :
      letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
        ⟨g.toRiemannianMetric⟩
      letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
        ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
      letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
      ∀ i : ι, MDifferentiableAt I 𝓘(Real, Real)
        (CenterOfMass.halfSqDist
          ((NormalCoordinates.normalChartAt (I := I) g p).symm (xi i)))
        (centerOfMass (I := I) g mu
          (fun j => (NormalCoordinates.normalChartAt (I := I) g p).symm (xi j))
          join p r h))
    (hsrc :
      letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
        ⟨g.toRiemannianMetric⟩
      letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
        ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
      letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
      ∀ i : ι, (NormalCoordinates.normalChartAt (I := I) g p).symm (xi i) ∈
        (NormalCoordinates.normalChartAt (I := I) g
          (centerOfMass (I := I) g mu
            (fun j => (NormalCoordinates.normalChartAt (I := I) g p).symm (xi j))
            join p r h)).source)
    (hsmall :
      letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
        ⟨g.toRiemannianMetric⟩
      letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
        ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
      letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
      ∀ i : ι,
        (NormalCoordinates.normalChartAt (I := I) g p).symm (xi i) ≠
          centerOfMass (I := I) g mu
            (fun j => (NormalCoordinates.normalChartAt (I := I) g p).symm (xi j))
            join p r h ->
        Real.sqrt
          (g.inner
            (centerOfMass (I := I) g mu
              (fun j => (NormalCoordinates.normalChartAt (I := I) g p).symm (xi j))
              join p r h)
            (NormalCoordinates.normalChartAt (I := I) g
              (centerOfMass (I := I) g mu
                (fun j => (NormalCoordinates.normalChartAt (I := I) g p).symm (xi j))
                join p r h)
              ((NormalCoordinates.normalChartAt (I := I) g p).symm (xi i)) : E)
            (NormalCoordinates.normalChartAt (I := I) g
              (centerOfMass (I := I) g mu
                (fun j => (NormalCoordinates.normalChartAt (I := I) g p).symm (xi j))
                join p r h)
              ((NormalCoordinates.normalChartAt (I := I) g p).symm (xi i)) : E)) <
          centerOfMass.eqnRadius (I := I) h)
    (hread : ∀ i,
      (centerOfMass (I := I) g mu
          (fun j => (NormalCoordinates.normalChartAt (I := I) g p).symm (xi j))
          join p r h,
        (NormalCoordinates.normalChartAt (I := I) g p).symm (xi i)) ∈ B.readDom)
    (hreal : ∀ i,
      Real.sqrt
        (g.inner
          (centerOfMass (I := I) g mu
            (fun j => (NormalCoordinates.normalChartAt (I := I) g p).symm (xi j))
            join p r h)
          (B.inv
            (centerOfMass (I := I) g mu
                (fun j => (NormalCoordinates.normalChartAt (I := I) g p).symm (xi j))
                join p r h,
              (NormalCoordinates.normalChartAt (I := I) g p).symm (xi i))).snd
          (B.inv
            (centerOfMass (I := I) g mu
                (fun j => (NormalCoordinates.normalChartAt (I := I) g p).symm (xi j))
                join p r h,
              (NormalCoordinates.normalChartAt (I := I) g p).symm (xi i))).snd) <
        expDiffeoRadius (I := I) g hEnorm
          (centerOfMass (I := I) g mu
            (fun j => (NormalCoordinates.normalChartAt (I := I) g p).symm (xi j))
            join p r h)) :
    chartCmEqnB (I := I) g hEnorm p B
      (NormalCoordinates.normalChartAt (I := I) g p
        (centerOfMass (I := I) g mu
          (fun i => (NormalCoordinates.normalChartAt (I := I) g p).symm (xi i))
          join p r h))
      (mu, xi) = 0 := by
  let c := centerOfMass (I := I) g mu
    (fun i => (NormalCoordinates.normalChartAt (I := I) g p).symm (xi i))
    join p r h
  obtain ⟨i₀, _⟩ := h.μ_pos
  have hbase : c ∈ (trivializationAt E (TangentSpace I) p).baseSet := by
    simpa only [c] using (hread i₀).2
  have hpt (i : ι) :
      B.inv (c, (NormalCoordinates.normalChartAt (I := I) g p).symm (xi i)) =
        (⟨c, (show TangentSpace I c from
          (NormalCoordinates.normalChartAt (I := I) g c
            ((NormalCoordinates.normalChartAt (I := I) g p).symm (xi i)) : E))⟩ :
          TangentBundle I M) := by
    exact B.inv_eq_normal_lt (hread i).1 (hreal i)
  have hbook := centerOfMass.expInv_eqn_of_lt (I := I) h hdiff hsrc hsmall
  have hreadout := (readoutB_zero_iff (I := I) g hEnorm p B mu c
    (fun i => (NormalCoordinates.normalChartAt (I := I) g p).symm (xi i))
    hbase hpt).2 hbook
  have hdecode : (NormalCoordinates.normalChartAt (I := I) g p).symm
      (NormalCoordinates.normalChartAt (I := I) g p c) = c :=
    (NormalCoordinates.normalChartAt (I := I) g p).left_inv hcenter
  unfold chartCmEqnB
  rw [hdecode]
  exact hreadout

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- The actual selected center satisfies the chart readout equation under the
named geometric small-domain conditions.  The equation is produced by
`centerOfMass.expInv_eqn_of_lt` and transported to the fixed trivialization by
`readout_sum_eq_zero_iff`; it is not assumed as an abstract root predicate. -/
theorem centerReadout_zero
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) {ι : Type} [Fintype ι] (mu : ι -> Real) (xi : ι -> E)
    (join : M -> M -> Real -> M) (r : Real)
    (h : CenterInput (I := I) g mu
      (fun i => (NormalCoordinates.normalChartAt (I := I) g p).symm (xi i))
      join p r)
    (hcenter : centerOfMass (I := I) g mu
      (fun i => (NormalCoordinates.normalChartAt (I := I) g p).symm (xi i))
      join p r h ∈ (NormalCoordinates.normalChartAt (I := I) g p).source)
    (hdiff :
      letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
        ⟨g.toRiemannianMetric⟩
      letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
        ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
      letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
      ∀ i : ι, MDifferentiableAt I 𝓘(Real, Real)
        (CenterOfMass.halfSqDist
          ((NormalCoordinates.normalChartAt (I := I) g p).symm (xi i)))
        (centerOfMass (I := I) g mu
          (fun j => (NormalCoordinates.normalChartAt (I := I) g p).symm (xi j))
          join p r h))
    (hsrc :
      letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
        ⟨g.toRiemannianMetric⟩
      letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
        ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
      letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
      ∀ i : ι, (NormalCoordinates.normalChartAt (I := I) g p).symm (xi i) ∈
        (NormalCoordinates.normalChartAt (I := I) g
          (centerOfMass (I := I) g mu
            (fun j => (NormalCoordinates.normalChartAt (I := I) g p).symm (xi j))
            join p r h)).source)
    (hsmall :
      letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
        ⟨g.toRiemannianMetric⟩
      letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
        ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
      letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
      ∀ i : ι,
        (NormalCoordinates.normalChartAt (I := I) g p).symm (xi i) ≠
          centerOfMass (I := I) g mu
            (fun j => (NormalCoordinates.normalChartAt (I := I) g p).symm (xi j))
            join p r h ->
        Real.sqrt
          (g.inner
            (centerOfMass (I := I) g mu
              (fun j => (NormalCoordinates.normalChartAt (I := I) g p).symm (xi j))
              join p r h)
            (NormalCoordinates.normalChartAt (I := I) g
              (centerOfMass (I := I) g mu
                (fun j => (NormalCoordinates.normalChartAt (I := I) g p).symm (xi j))
                join p r h)
              ((NormalCoordinates.normalChartAt (I := I) g p).symm (xi i)) : E)
            (NormalCoordinates.normalChartAt (I := I) g
              (centerOfMass (I := I) g mu
                (fun j => (NormalCoordinates.normalChartAt (I := I) g p).symm (xi j))
                join p r h)
              ((NormalCoordinates.normalChartAt (I := I) g p).symm (xi i)) : E)) <
          centerOfMass.eqnRadius (I := I) h)
    (hbase : centerOfMass (I := I) g mu
      (fun i => (NormalCoordinates.normalChartAt (I := I) g p).symm (xi i))
      join p r h ∈ (trivializationAt E (TangentSpace I) p).baseSet)
    (hproj : ∀ i,
      (diagExpInv (I := I) g hEnorm p
        (centerOfMass (I := I) g mu
            (fun j => (NormalCoordinates.normalChartAt (I := I) g p).symm (xi j))
            join p r h,
          (NormalCoordinates.normalChartAt (I := I) g p).symm (xi i))).proj =
        centerOfMass (I := I) g mu
          (fun j => (NormalCoordinates.normalChartAt (I := I) g p).symm (xi j))
          join p r h)
    (hintr : ∀ i,
      expMapIntrinsic (I := I) g hEnorm
        (centerOfMass (I := I) g mu
          (fun j => (NormalCoordinates.normalChartAt (I := I) g p).symm (xi j))
          join p r h)
        (diagExpInv (I := I) g hEnorm p
          (centerOfMass (I := I) g mu
              (fun j => (NormalCoordinates.normalChartAt (I := I) g p).symm (xi j))
              join p r h,
            (NormalCoordinates.normalChartAt (I := I) g p).symm (xi i))).snd =
          (NormalCoordinates.normalChartAt (I := I) g p).symm (xi i))
    (hreal : ∀ i,
      Real.sqrt
        (g.inner
          (centerOfMass (I := I) g mu
            (fun j => (NormalCoordinates.normalChartAt (I := I) g p).symm (xi j))
            join p r h)
          (diagExpInv (I := I) g hEnorm p
            (centerOfMass (I := I) g mu
                (fun j => (NormalCoordinates.normalChartAt (I := I) g p).symm (xi j))
                join p r h,
              (NormalCoordinates.normalChartAt (I := I) g p).symm (xi i))).snd
          (diagExpInv (I := I) g hEnorm p
            (centerOfMass (I := I) g mu
                (fun j => (NormalCoordinates.normalChartAt (I := I) g p).symm (xi j))
                join p r h,
              (NormalCoordinates.normalChartAt (I := I) g p).symm (xi i))).snd) <
        expDiffeoRadius (I := I) g hEnorm
          (centerOfMass (I := I) g mu
            (fun j => (NormalCoordinates.normalChartAt (I := I) g p).symm (xi j))
            join p r h)) :
    chartCmEqn' (I := I) g hEnorm p
      (NormalCoordinates.normalChartAt (I := I) g p
        (centerOfMass (I := I) g mu
          (fun i => (NormalCoordinates.normalChartAt (I := I) g p).symm (xi i))
          join p r h))
      (mu, xi) = 0 := by
  let c := centerOfMass (I := I) g mu
    (fun i => (NormalCoordinates.normalChartAt (I := I) g p).symm (xi i))
    join p r h
  have hbook := centerOfMass.expInv_eqn_of_lt (I := I) h hdiff hsrc hsmall
  have hpt (i : ι) := diagInv_eq_normal_lt (I := I) g hEnorm p c
    ((NormalCoordinates.normalChartAt (I := I) g p).symm (xi i))
    (hproj i) (hintr i) (hreal i)
  have hreadout := (readout_sum_eq_zero_iff (I := I) g hEnorm p mu c
    (fun i => (NormalCoordinates.normalChartAt (I := I) g p).symm (xi i))
    hbase hpt).2 hbook
  have hdecode : (NormalCoordinates.normalChartAt (I := I) g p).symm
      (NormalCoordinates.normalChartAt (I := I) g p c) = c :=
    (NormalCoordinates.normalChartAt (I := I) g p).left_inv hcenter
  unfold chartCmEqn'
  rw [hdecode]
  exact hreadout

omit [T3Space M] in
attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- Specialize compact pinned-root gluing to the center equation associated to
an explicit selected inverse branch. -/
theorem existsCmExtensionB
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) (D : DiagInvBranch (I := I) g hEnorm p)
    {ι : Type} [Fintype ι]
    {A B : Set ((ι -> Real) × (ι -> E))} (hA : IsCompact A) (hAB : A ⊆ B)
    (c : ((ι -> Real) × (ι -> E)) -> E) (hc : ContinuousOn c B)
    (hzero : ∀ params ∈ B,
      chartCmEqnB (I := I) g hEnorm p D (c params) params = 0)
    (hjoint : ∀ params ∈ A, ContDiffAt Real 1
      (fun w : E × ((ι -> Real) × (ι -> E)) =>
        chartCmEqnB (I := I) g hEnorm p D w.1 w.2) (c params, params))
    (hinv : ∀ params ∈ A, ∃ L : E ≃L[Real] E,
      HasFDerivAt
        (fun z : E => chartCmEqnB (I := I) g hEnorm p D z params)
        (L : E →L[Real] E) (c params)) :
    ∃ (T : Set (E × ((ι -> Real) × (ι -> E))))
        (V : Set ((ι -> Real) × (ι -> E)))
        (z : ((ι -> Real) × (ι -> E)) -> E),
      IsOpen T ∧ IsOpen V ∧
      (∀ params ∈ A, (c params, params) ∈ T) ∧
      Set.InjOn
        (fun w : E × ((ι -> Real) × (ι -> E)) =>
          (chartCmEqnB (I := I) g hEnorm p D w.1 w.2, w.2)) T ∧
      A ⊆ V ∧ ContinuousOn z V ∧
      (∀ params ∈ V, chartCmEqnB (I := I) g hEnorm p D (z params) params = 0) ∧
      Set.EqOn z c (B ∩ V) := by
  apply existsRootExtension
    (G := fun z params => chartCmEqnB (I := I) g hEnorm p D z params)
    hA hAB c hc hzero
  intro params hparams
  exact existsPinnedLocal
    (fun z params => chartCmEqnB (I := I) g hEnorm p D z params)
    (c params) params one_ne_zero (hjoint params hparams) (hinv params hparams)

omit [T3Space M] in
attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- Specialize the compact pinned-root gluing theorem to the readout
center-of-mass equation.  Joint `C¹` regularity and Hessian invertibility are
needed only along the compact actual-configuration set `A`; the resulting root
extends continuously to an ambient open neighborhood and agrees with `c` on
the admissible locus. -/
theorem existsCmExtension
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) {ι : Type} [Fintype ι]
    {A B : Set ((ι -> Real) × (ι -> E))} (hA : IsCompact A) (hAB : A ⊆ B)
    (c : ((ι -> Real) × (ι -> E)) -> E) (hc : ContinuousOn c B)
    (hzero : ∀ params ∈ B,
      chartCmEqn' (I := I) g hEnorm p (c params) params = 0)
    (hjoint : ∀ params ∈ A, ContDiffAt Real 1
      (fun w : E × ((ι -> Real) × (ι -> E)) =>
        chartCmEqn' (I := I) g hEnorm p w.1 w.2) (c params, params))
    (hinv : ∀ params ∈ A, ∃ L : E ≃L[Real] E,
      HasFDerivAt
        (fun z : E => chartCmEqn' (I := I) g hEnorm p z params)
        (L : E →L[Real] E) (c params)) :
    ∃ (T : Set (E × ((ι -> Real) × (ι -> E))))
        (V : Set ((ι -> Real) × (ι -> E)))
        (z : ((ι -> Real) × (ι -> E)) -> E),
      IsOpen T ∧ IsOpen V ∧
      (∀ params ∈ A, (c params, params) ∈ T) ∧
      Set.InjOn
        (fun w : E × ((ι -> Real) × (ι -> E)) =>
          (chartCmEqn' (I := I) g hEnorm p w.1 w.2, w.2)) T ∧
      A ⊆ V ∧ ContinuousOn z V ∧
      (∀ params ∈ V, chartCmEqn' (I := I) g hEnorm p (z params) params = 0) ∧
      Set.EqOn z c (B ∩ V) := by
  apply existsRootExtension
    (G := fun z params => chartCmEqn' (I := I) g hEnorm p z params)
    hA hAB c hc hzero
  intro params hparams
  exact existsPinnedLocal
    (fun z params => chartCmEqn' (I := I) g hEnorm p z params)
    (c params) params one_ne_zero (hjoint params hparams) (hinv params hparams)

omit [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M] in
attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- The actual chart center is continuous on an admissible parameter set once
the chart-realized point tuple is continuous and every selected center stays in
the fixed readout chart.  The proof runs `centerOfMassChart_cont` on the
parameter subtype and then removes the outside-domain filler by
`centerCfgOn_eq`. -/
theorem chartCenterOn_cont
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M) (p : M) {ι : Type} [Fintype ι]
    (join : M -> M -> Real -> M) (r : Real)
    (V : Set ((ι -> Real) × (ι -> E)))
    (h : ∀ params, params ∈ V ->
      CenterInput (I := I) g params.1
        (fun i => (NormalCoordinates.normalChartAt (I := I) g p).symm (params.2 i))
        join p r)
    (hpts : Continuous (fun params : V => fun i =>
      (NormalCoordinates.normalChartAt (I := I) g p).symm (params.1.2 i)))
    (hsrc : ∀ params : V,
      centerOfMass (I := I) g params.1.1
        (fun i => (NormalCoordinates.normalChartAt (I := I) g p).symm (params.1.2 i))
        join p r (h params params.2) ∈
          (NormalCoordinates.normalChartAt (I := I) g p).source) :
    ContinuousOn (chartCenterOn (I := I) g p join r V h) V := by
  rw [continuousOn_iff_continuous_restrict]
  let H : ∀ params : V,
      CenterInput (I := I) g params.1.1
        (fun i => (NormalCoordinates.normalChartAt (I := I) g p).symm (params.1.2 i))
        join p r := fun params => h params params.2
  let f : V -> E := fun params =>
    NormalCoordinates.normalChartAt (I := I) g p
      (centerOfMass (I := I) g params.1.1
        (fun i => (NormalCoordinates.normalChartAt (I := I) g p).symm (params.1.2 i))
        join p r (H params))
  have hf : Continuous f := by
    rw [continuous_iff_continuousAt]
    intro params
    have hμ : Continuous (fun q : V => q.1.1) :=
      continuous_fst.comp continuous_subtype_val
    have hcm := centerOfMass_cont (I := I) g
      (fun q : V => q.1.1)
      (fun q : V => fun i =>
        (NormalCoordinates.normalChartAt (I := I) g p).symm (q.1.2 i))
      join p r params H hμ hpts
    have hchart : ContinuousAt
        (fun q : M => (NormalCoordinates.normalChartAt (I := I) g p q : E))
        (centerOfMass (I := I) g params.1.1
          (fun i => (NormalCoordinates.normalChartAt (I := I) g p).symm
            (params.1.2 i)) join p r (H params)) :=
      (NormalCoordinates.normalChartAt_contMDiffOn (I := I) g p).continuousOn.continuousAt
        ((NormalCoordinates.normalChartAt (I := I) g p).open_source.mem_nhds
          (hsrc params))
    exact hchart.tendsto.comp hcm
  have heq : V.restrict (chartCenterOn (I := I) g p join r V h) = f := by
    funext params
    change NormalCoordinates.normalChartAt (I := I) g p
      (centerCfgOn (I := I) g p join r V h params) = f params
    rw [centerCfgOn_eq (I := I) g p join r h params.2]
  rw [heq]
  exact hf

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- A continuous ambient solution extension of the selected-branch center
equation is smooth on its open parameter domain. -/
theorem cmExtB_contDiffOn
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : forall (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) (B : DiagInvBranch (I := I) g hEnorm p)
    {ι : Type} [Fintype ι]
    (z : ((ι -> Real) × (ι -> E)) -> E)
    {V : Set ((ι -> Real) × (ι -> E))} (hV : IsOpen V)
    (hchz : ∀ params0 ∈ V, forall n : Nat, ContMDiffAt 𝓘(ℝ, E) I (n : ℕ∞)
      (fun z : E => (NormalCoordinates.normalChartAt (I := I) g p).symm z)
      (z params0))
    (hchxi : ∀ params0 ∈ V, forall n : Nat, forall i, ContMDiffAt 𝓘(ℝ, E) I (n : ℕ∞)
      (fun xi : E => (NormalCoordinates.normalChartAt (I := I) g p).symm xi)
      (params0.2 i))
    (hsm : ∀ params0 ∈ V, forall n : Nat, forall i,
      ContMDiffAt (I.prod I) 𝓘(ℝ, E) (n : ℕ∞)
        (fun yq : M × M => B.diagReadout yq)
        ((NormalCoordinates.normalChartAt (I := I) g p).symm (z params0),
          (NormalCoordinates.normalChartAt (I := I) g p).symm (params0.2 i)))
    (hinv : ∀ params0 ∈ V, exists L : E ≃L[Real] E,
      HasFDerivAt (fun z : E => chartCmEqnB (I := I) g hEnorm p B z params0)
        (L : E →L[Real] E) (z params0))
    (hzero : ∀ params0 ∈ V,
      chartCmEqnB (I := I) g hEnorm p B (z params0) params0 = 0)
    (hzcont : ContinuousOn z V) :
    ContDiffOn Real (∞ : WithTop ℕ∞) z V := by
  rw [contDiffOn_infty]
  intro n params0 hparams
  have hsolves : ∀ᶠ eventuallyParams in nhds params0,
      chartCmEqnB (I := I) g hEnorm p B (z eventuallyParams) eventuallyParams = 0 := by
    filter_upwards [hV.mem_nhds hparams] with params hparamsV
    exact hzero params hparamsV
  have hcont : Filter.Tendsto z (nhds params0) (nhds (z params0)) :=
    (hzcont.continuousAt (hV.mem_nhds hparams)).tendsto
  obtain ⟨f, _hf0, hfcd, _hfsolves, huniq⟩ :=
    readoutSolB_cdAt (I := I) g hEnorm p B (z params0) params0
      (max 1 n) (le_max_left 1 n)
    (hchz params0 hparams (max 1 n))
    (hchxi params0 hparams (max 1 n))
    (hsm params0 hparams (max 1 n))
    (hinv params0 hparams) (hzero params0 hparams)
  have huniq' := (hcont.prodMk_nhds Filter.tendsto_id).eventually huniq
  have hid : z =ᶠ[nhds params0] f := by
    filter_upwards [huniq', hsolves] with params hu hs
    exact hu hs
  exact ((hfcd.congr_of_eventuallyEq hid).of_le
    (by exact_mod_cast le_max_right 1 n)).contDiffWithinAt

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- Local-to-global-on-an-open-set form of the finite-order implicit-center
regularity theorem for an ambient chart-valued solution extension.  A pointwise
readout equation automatically supplies the neighborhood equation because `V`
is open, and `ContinuousOn` supplies the pointwise `Tendsto` input.  The theorem
does not claim that `z` is the selected center of mass on signed weights. -/
theorem cmExt_contDiffOn
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : forall (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) {ι : Type} [Fintype ι]
    (z : ((ι -> Real) × (ι -> E)) -> E)
    {V : Set ((ι -> Real) × (ι -> E))} (hV : IsOpen V)
    (hchz : ∀ params0 ∈ V, forall n : Nat, ContMDiffAt 𝓘(ℝ, E) I (n : ℕ∞)
      (fun z : E => (NormalCoordinates.normalChartAt (I := I) g p).symm z)
      (z params0))
    (hchxi : ∀ params0 ∈ V, forall n : Nat, forall i, ContMDiffAt 𝓘(ℝ, E) I (n : ℕ∞)
      (fun xi : E => (NormalCoordinates.normalChartAt (I := I) g p).symm xi)
      (params0.2 i))
    (hsm : ∀ params0 ∈ V, forall n : Nat, forall i,
      ContMDiffAt (I.prod I) 𝓘(ℝ, E) (n : ℕ∞)
        (fun yq : M × M => (trivializationAt E (TangentSpace I) p
          (diagExpInv (I := I) g hEnorm p yq)).2)
        ((NormalCoordinates.normalChartAt (I := I) g p).symm (z params0),
          (NormalCoordinates.normalChartAt (I := I) g p).symm (params0.2 i)))
    (hinv : ∀ params0 ∈ V, exists L : E ≃L[Real] E,
      HasFDerivAt (fun z : E => chartCmEqn' (I := I) g hEnorm p z params0)
        (L : E →L[Real] E) (z params0))
    (hzero : ∀ params0 ∈ V,
      chartCmEqn' (I := I) g hEnorm p (z params0) params0 = 0)
    (hzcont : ContinuousOn z V) :
    ContDiffOn Real (∞ : WithTop ℕ∞) z V := by
  rw [contDiffOn_infty]
  intro n params0 hparams
  have hsolves : ∀ᶠ eventuallyParams in nhds params0,
      chartCmEqn' (I := I) g hEnorm p (z eventuallyParams) eventuallyParams = 0 := by
    filter_upwards [hV.mem_nhds hparams] with params hparamsV
    exact hzero params hparamsV
  have hcont : Filter.Tendsto z (nhds params0) (nhds (z params0)) :=
    (hzcont.continuousAt (hV.mem_nhds hparams)).tendsto
  obtain ⟨f, _hf0, hfcd, _hfsolves, huniq⟩ :=
    readoutSol_contDiffAt (I := I) g hEnorm p (z params0) params0
      (max 1 n) (le_max_left 1 n)
    (hchz params0 hparams (max 1 n))
    (hchxi params0 hparams (max 1 n))
    (hsm params0 hparams (max 1 n))
    (hinv params0 hparams) (hzero params0 hparams)
  have huniq' := (hcont.prodMk_nhds Filter.tendsto_id).eventually huniq
  have hid : z =ᶠ[nhds params0] f := by
    filter_upwards [huniq', hsolves] with params hu hs
    exact hu hs
  exact ((hfcd.congr_of_eventuallyEq hid).of_le
    (by exact_mod_cast le_max_right 1 n)).contDiffWithinAt

end SmoothDomain

end HCGCompactness
end DifferentialGeometry
