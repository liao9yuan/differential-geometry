import DifferentialGeometry.Geometry.Comparison.HopfRinowProper
import DifferentialGeometry.Geometry.Comparison.MinimizingBranch
import DifferentialGeometry.Geometry.Exponential.DiagExpDerivative
import DifferentialGeometry.Geometry.Topology.ConeSlice
import DifferentialGeometry.Geometry.Topology.NearestPoint
import DifferentialGeometry.Geometry.Topology.RelativeFrontier

set_option autoImplicit false

noncomputable section

open Bundle Filter Manifold Set Topology
open scoped ContDiff ENNReal Manifold Set.Notation Topology

namespace DifferentialGeometry
namespace RiemannianMetricComplete

open Geometry Geometry.Riemannian Geometry.Riemannian.Exponential

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [T2Space (TangentBundle I M)]
  [SigmaCompactSpace M] [ConnectedSpace M]

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace

theorem exists_slice_succ
    {g : SmoothRiemannianMetric I M}
    (hg : RiemannianMetricComplete (I := I) g)
    {C N : Set M} {d : ℕ}
    (hC : IsTotallyConvex (I := I) g C)
    (hN : IsEmbeddedSlice I d N) (hNC : N ⊆ C)
    {p : M} (hpN : p ∈ N) (hpfront : p ∈ closure (C \ N))
    {W : Set M} (hW : W ∈ 𝓝 p) :
    ∃ S : Set M, S.Nonempty ∧ S ⊆ W ∩ C ∧
      IsEmbeddedSlice I (d + 1) S := by
  classical
  letI : IsManifold I 1 M :=
    IsManifold.of_le (I := I) (M := M) (n := (∞ : WithTop ℕ∞))
      (by decide : (1 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞))
  letI : TopologicalSpace.MetrizableSpace M := Manifold.metrizableSpace I M
  letI : T3Space M := inferInstance
  letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
    ⟨g.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle E
      (fun x : M ↦ TangentSpace I x) :=
    ⟨⟨g.inner, g.contMDiff.continuous, by intro x v w; rfl⟩⟩
  letI : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
  letI : CompleteSpace M := by simpa only using hg.complete
  let hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)) :=
    fun x v => tensor0SBundle_enorm_eq_riemannianBundle_enorm
      (I := I) g x v
  letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
  haveI : ProperSpace M :=
    HopfRinow.properSpace_riemMetric (I := I) (M := M)
      (by simpa only using hg.complete) g hEnorm
  let B := stdBranch (I := I) g hEnorm p
  let D : M → PartialDiffeomorph 𝓘(ℝ, E) I E M ∞ := fun q =>
    ExpInvBranch.framed (E := E) (B.fixed q)
  let Good : Set (M × M) :=
    {yz |
      yz.2 ∈ (D yz.1).target ∧
      ‖(D yz.1).symm yz.2‖ = (riemannianEDist I yz.1 yz.2).toReal ∧
      (∀ t ∈ Set.Icc (0 : ℝ) 1,
        t • (D yz.1).symm yz.2 ∈ (D yz.1).source) ∧
      ∀ t ∈ Set.Icc (0 : ℝ) 1,
        D yz.1 (t • (D yz.1).symm yz.2) =
          minJoin (I := I) g hEnorm yz.1 yz.2 t}
  have hGood : Good ∈ 𝓝 (p, p) := by
    filter_upwards [B.framed_symm_norm (E := E),
      B.framed_smul_mem (E := E), B.framed_smul_eq_join (E := E)]
      with yz hnorm hmem hjoin
    exact ⟨hnorm.1, hnorm.2, hmem, hjoin⟩
  obtain ⟨P, Q, hPopen, hpP, hQopen, hpQ, hPQ⟩ :=
    mem_nhds_prod_iff'.mp hGood
  obtain ⟨O, hOW, hOopen, hpO⟩ := mem_nhds_iff.mp hW
  obtain ⟨ε, hε, hεsub⟩ :=
    Metric.isOpen_iff.mp (hQopen.inter hOopen) p ⟨hpQ, hpO⟩
  obtain ⟨rN, hrN, hnearest⟩ := hN.is_locally_closed.exists_dist_min hpN
  let ρ : ℝ := min rN (ε / 3)
  have hρ : 0 < ρ := lt_min hrN (by positivity)
  have hnhds : P ∩ Metric.ball p ρ ∈ 𝓝 p :=
    Filter.inter_mem (hPopen.mem_nhds hpP)
      (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hρ))
  obtain ⟨q, hqnear, hqdiff⟩ :=
    (mem_closure_iff_nhds.mp hpfront) _ hnhds
  have hqP : q ∈ P := hqnear.1
  have hqball : q ∈ Metric.ball p ρ := hqnear.2
  have hqballN : q ∈ Metric.ball p rN := by
    rw [Metric.mem_ball] at hqball ⊢
    exact hqball.trans_le (min_le_left _ _)
  obtain ⟨z, hzN, hzmin⟩ := hnearest hqballN
  have hqz : dist q z ≤ dist q p := hzmin hpN
  have hzε : z ∈ Metric.ball p ε := by
    rw [Metric.mem_ball]
    calc
      dist z p ≤ dist z q + dist q p := dist_triangle z q p
      _ = dist q z + dist q p := by rw [dist_comm z q]
      _ ≤ dist q p + dist q p := add_le_add hqz le_rfl
      _ < ρ + ρ := add_lt_add hqball hqball
      _ ≤ ε / 3 + ε / 3 := add_le_add
        (min_le_right _ _) (min_le_right _ _)
      _ < ε := by linarith
  have hzQO : z ∈ Q ∩ O := hεsub hzε
  have hqC : q ∈ C := hqdiff.1
  have hqN : q ∉ N := hqdiff.2
  let Dq : PartialDiffeomorph 𝓘(ℝ, E) I E M ∞ := D q
  have hqzGood : (q, z) ∈ Good := hPQ ⟨hqP, hzQO.1⟩
  have hzTarget : z ∈ Dq.target := hqzGood.1
  let R : Set M := Q ∩ O
  have hRopen : IsOpen R := hQopen.inter hOopen
  have hNRtarget : N ∩ R ⊆ Dq.symm.source := by
    rintro y ⟨hyN, hyR⟩
    change y ∈ (D q).target
    have hgood : (q, y) ∈ Good := hPQ ⟨hqP, hyR.1⟩
    exact hgood.1
  let Sco : Set E := Dq.symm '' (N ∩ R)
  have hSco : IsEmbeddedSlice 𝓘(ℝ, E) d Sco :=
    (hN.inter_open hRopen).image Dq.symm hNRtarget
  let a₀ : E := Dq.symm z
  have ha₀ : a₀ ∈ Sco := ⟨z, ⟨hzN, hzQO⟩, rfl⟩
  obtain ⟨L, U, f, W₀, hLfin, hdim, hUopen, h0U, hfsmooth,
      hfinj, hf0, hW₀open, haW₀, hfimage⟩ := hSco.exists_param ha₀
  letI : FiniteDimensional ℝ L := hLfin
  have hparam (x : L) (hx : x ∈ U) :
      ∃ y ∈ N ∩ R, Dq (f x) = y ∧ Dq.symm y = f x := by
    have hfxSco : f x ∈ Sco := by
      have hfxImage : f x ∈ f '' U := ⟨x, hx, rfl⟩
      rw [hfimage] at hfxImage
      exact hfxImage.2
    obtain ⟨y, hyNR, hyEq⟩ := hfxSco
    have hyTarget : y ∈ Dq.symm.source := hNRtarget hyNR
    refine ⟨y, hyNR, ?_, hyEq⟩
    rw [← hyEq]
    exact Dq.toPartialEquiv.right_inv hyTarget
  have hmaps : Set.MapsTo (fun x : L ↦ Dq (f x)) U N := by
    intro x hx
    obtain ⟨y, hyNR, hDxy, _⟩ := hparam x hx
    change Dq (f x) ∈ N
    rw [hDxy]
    exact hyNR.1
  have hradial : ∀ x ∈ U, dist q (Dq (f x)) = ‖f x‖ := by
    intro x hx
    obtain ⟨y, hyNR, hDxy, hsymm⟩ := hparam x hx
    have hyGood : (q, y) ∈ Good := hPQ ⟨hqP, hyNR.2.1⟩
    calc
      dist q (Dq (f x)) = (riemannianEDist I q (Dq (f x))).toReal :=
        HopfRinow.riemMetric_dist_eq (I := I) (M := M) _ _
      _ = (riemannianEDist I q y).toReal := by rw [hDxy]
      _ = ‖Dq.symm y‖ := hyGood.2.1.symm
      _ = ‖f x‖ := by rw [hsymm]
  have hDfa : Dq (f 0) = z := by
    rw [hf0]
    exact Dq.toPartialEquiv.right_inv hzTarget
  have hzmin' : IsMinOn (fun y ↦ dist q y) N (Dq (f 0)) := by
    simpa only [hDfa] using hzmin
  have hlocal : IsLocalMin (fun x : L ↦ ‖f x‖ ^ 2) 0 :=
    radial_local_min (hUopen.mem_nhds h0U) hmaps hzmin' hradial
  have hfDiff : DifferentiableAt ℝ f 0 :=
    (hfsmooth.contDiffAt (hUopen.mem_nhds h0U)).differentiableAt (by simp)
  have hfne : f 0 ≠ 0 := by
    intro hzero
    have hzeroSource : (0 : E) ∈ Dq.source := by
      have hmem := hqzGood.2.2.1 0 ⟨le_rfl, zero_le_one⟩
      simpa only [zero_smul] using hmem
    have hDzero : Dq 0 = q := by
      change ExpInvBranch.framed (E := E) (B.fixed q) 0 = q
      rw [← ExpInvBranch.framed_eq_intr (E := E) (B.fixed q) hzeroSource]
      exact NormalCoordinates.intrFrame_zero (I := I) g hEnorm q
    have hqzEq : q = z := by
      rw [← hDfa, hzero, hDzero]
    exact hqN (hqzEq ▸ hzN)
  have htrans : f 0 ∉ (fderiv ℝ f 0).range :=
    radial_not_range hfDiff hlocal hfne
  let ell : ℝ → E := fun t ↦ t • f 0
  have hell : Continuous ell := continuous_id.smul continuous_const
  have hfaSource : f 0 ∈ Dq.source := by
    rw [hf0]
    exact Dq.symm.toPartialEquiv.map_source hzTarget
  have hDcont : ContinuousAt Dq (f 0) :=
    Dq.contMDiffOn_toFun.continuousOn.continuousAt
      (Dq.open_source.mem_nhds hfaSource)
  have hDell : ContinuousAt (fun t : ℝ ↦ Dq (ell t)) 1 := by
    exact hDcont.comp_of_eq hell.continuousAt (by simp only [ell, one_smul])
  have hlineSource : ell ⁻¹' Dq.source ∈ 𝓝 (1 : ℝ) := by
    apply hell.continuousAt
    simpa only [ell, one_smul] using Dq.open_source.mem_nhds hfaSource
  have hlineO : (fun t : ℝ ↦ Dq (ell t)) ⁻¹' O ∈ 𝓝 (1 : ℝ) := by
    apply hDell
    have hDzO : Dq (f 0) ∈ O := by simpa only [hDfa] using hzQO.2
    simpa only [ell, one_smul] using hOopen.mem_nhds hDzO
  have hlineGood :
      ell ⁻¹' Dq.source ∩ (fun t : ℝ ↦ Dq (ell t)) ⁻¹' O ∈ 𝓝 (1 : ℝ) :=
    Filter.inter_mem hlineSource hlineO
  have honeClosure : (1 : ℝ) ∈ closure (Set.Ioo 0 1) := by
    rw [closure_Ioo (by norm_num : (0 : ℝ) ≠ 1)]
    exact ⟨zero_le_one, le_rfl⟩
  obtain ⟨t₀, ht₀line, ht₀Ioo⟩ :=
    (mem_closure_iff_nhds.mp honeClosure) _ hlineGood
  have ht₀ne : t₀ ≠ 0 := ne_of_gt ht₀Ioo.1
  have ht₀source : t₀ • f 0 ∈ Dq.source := ht₀line.1
  have ht₀O : Dq (t₀ • f 0) ∈ O := ht₀line.2
  let cone : L × ℝ → E := fun xt ↦ xt.2 • f xt.1
  obtain ⟨V, hVopen, hbaseV, hVsub, hVsource, hslice⟩ :=
    exists_cone_image (E := E) (F := L) Dq hUopen h0U isOpen_Ioo
      ht₀Ioo hfsmooth hfinj ht₀ne htrans ht₀source
  let Sraw : Set M := Dq '' (cone '' V)
  have hrawC : Sraw ⊆ C := by
    rintro y ⟨w, ⟨xt, hxtV, rfl⟩, rfl⟩
    have hxt := hVsub hxtV
    obtain ⟨z', hz'NR, hDfz', hsymm'⟩ := hparam xt.1 hxt.1
    have hz'Good : (q, z') ∈ Good := hPQ ⟨hqP, hz'NR.2.1⟩
    have htIcc : xt.2 ∈ Set.Icc (0 : ℝ) 1 :=
      ⟨le_of_lt hxt.2.1, le_of_lt hxt.2.2⟩
    have hjoin := hz'Good.2.2.2 xt.2 htIcc
    have heq : Dq (xt.2 • f xt.1) =
        minJoin (I := I) g hEnorm q z' xt.2 := by
      rw [← hsymm']
      exact hjoin
    rw [heq]
    exact hC.minJoin hEnorm hqC (hNC hz'NR.1) htIcc
  refine ⟨Sraw ∩ O, ?_, ?_, ?_⟩
  · refine ⟨Dq (t₀ • f 0), ?_, ht₀O⟩
    refine ⟨t₀ • f 0, ?_, rfl⟩
    refine ⟨(0, t₀), hbaseV, ?_⟩
    simp only [cone]
  · rintro y ⟨hyRaw, hyO⟩
    exact ⟨hOW hyO, hrawC hyRaw⟩
  · have hslice' : IsEmbeddedSlice I (d + 1) Sraw := by
      simpa only [Sraw, cone, hdim] using hslice
    exact hslice'.inter_open hOopen

theorem max_slice_eq
    {g : SmoothRiemannianMetric I M}
    (hg : RiemannianMetricComplete (I := I) g)
    {C N : Set M}
    (hC : IsTotallyConvex (I := I) g C)
    (hN : IsEmbeddedSlice I (maxSliceDim I C) N) (hNC : N ⊆ C)
    {p : M} (hpN : p ∈ N) :
    ∃ U : Set M, IsOpen U ∧ p ∈ U ∧ U ∩ C = U ∩ N := by
  have hpfront : p ∉ closure (C \ N) := by
    intro hpfront
    obtain ⟨S, hSne, hSC, hS⟩ :=
      exists_slice_succ hg hC hN hNC hpN hpfront
        (W := Set.univ) Filter.univ_mem
    have hdim : maxSliceDim I C + 1 ∈ sliceDims I C :=
      ⟨S, hSne, fun x hx ↦ (hSC hx).2, hS⟩
    exact (Nat.not_succ_le_self _) (le_max_slice_dim (I := I) hdim)
  let U : Set M := (closure (C \ N))ᶜ
  refine ⟨U, isClosed_closure.isOpen_compl, hpfront, ?_⟩
  apply Set.Subset.antisymm
  · rintro x ⟨hxU, hxC⟩
    refine ⟨hxU, ?_⟩
    by_contra hxN
    exact hxU (subset_closure ⟨hxC, hxN⟩)
  · rintro x ⟨hxU, hxN⟩
    exact ⟨hxU, hNC hxN⟩

theorem max_slice_locus_eq
    {g : SmoothRiemannianMetric I M}
    (hg : RiemannianMetricComplete (I := I) g)
    {C : Set M} (hC : IsTotallyConvex (I := I) g C)
    {p : M} (hp : p ∈ maxSliceLocus I C) :
    ∃ U : Set M, IsOpen U ∧ p ∈ U ∧
      U ∩ maxSliceLocus I C = U ∩ C := by
  obtain ⟨N, hpN, hNC, hN⟩ := hp
  obtain ⟨U, hU, hpU, hUCN⟩ := max_slice_eq hg hC hN hNC hpN
  refine ⟨U, hU, hpU, ?_⟩
  apply Set.Subset.antisymm
  · rintro x ⟨hxU, hxL⟩
    exact ⟨hxU, max_slice_subset hxL⟩
  · rintro x hxUC
    have hxUN : x ∈ U ∩ N := hUCN ▸ hxUC
    exact ⟨hxUN.1, N, hxUN.2, hNC, hN⟩

theorem max_slice_rel_open
    {g : SmoothRiemannianMetric I M}
    (hg : RiemannianMetricComplete (I := I) g)
    {C : Set M} (hC : IsTotallyConvex (I := I) g C) :
    IsOpen (C ↓∩ maxSliceLocus I C) := by
  rw [isOpen_iff_mem_nhds]
  rintro ⟨p, hpC⟩ hpL
  obtain ⟨U, hU, hpU, hEq⟩ := max_slice_locus_eq hg hC hpL
  refine Filter.mem_of_superset ((hU.preimage_val).mem_nhds hpU) ?_
  intro q hqU
  have hqUC : (q : M) ∈ U ∩ C := ⟨hqU, q.property⟩
  rw [← hEq] at hqUC
  exact hqUC.2

theorem max_slice_is_slice
    {g : SmoothRiemannianMetric I M}
    (hg : RiemannianMetricComplete (I := I) g)
    {C : Set M} (hC : IsTotallyConvex (I := I) g C) :
    IsEmbeddedSlice I (maxSliceDim I C) (maxSliceLocus I C) := by
  apply IsEmbeddedSlice.of_germ
  intro p hp
  obtain ⟨N, hpN, hNC, hN⟩ := hp
  obtain ⟨U, hU, hpU, hUCN⟩ := max_slice_eq hg hC hN hNC hpN
  refine ⟨N, U, hN, hU, hpU, hpN, ?_⟩
  apply Set.Subset.antisymm
  · rintro x ⟨hxU, hxL⟩
    exact hUCN ▸ ⟨hxU, max_slice_subset hxL⟩
  · rintro x ⟨hxU, hxN⟩
    exact ⟨hxU, N, hxN, hNC, hN⟩

end RiemannianMetricComplete

namespace Geometry.Riemannian

open Exponential

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [T2Space (TangentBundle I M)]
  [SigmaCompactSpace M] [ConnectedSpace M]

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace

variable [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
variable [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]

theorem Exponential.DiagInvBranch.max_slice_pair
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    {C : Set M} (hC : IsTotallyConvex (I := I) g C)
    {c : M} (B : DiagInvBranch (I := I) g hEnorm c) :
    ∀ᶠ pq : M × M in 𝓝 (c, c),
      pq.1 ∈ maxSliceLocus I C → pq.2 ∈ C →
        ∀ t ∈ Set.Ioc (0 : ℝ) 1,
          minJoin (I := I) g hEnorm pq.2 pq.1 t ∈ maxSliceLocus I C := by
  classical
  let D : M → PartialDiffeomorph 𝓘(ℝ, E) I E M ∞ := fun q ↦
    ExpInvBranch.framed (E := E) (B.fixed q)
  let Good : Set (M × M) :=
    {yz | yz.2 ∈ (D yz.1).target ∧
      ∀ t ∈ Set.Icc (0 : ℝ) 1,
        t • (D yz.1).symm yz.2 ∈ (D yz.1).source ∧
          D yz.1 (t • (D yz.1).symm yz.2) =
            minJoin (I := I) g hEnorm yz.1 yz.2 t}
  have hGood : Good ∈ 𝓝 (c, c) := by
    filter_upwards [B.framed_symm_norm (E := E),
      B.framed_smul_mem (E := E), B.framed_smul_eq_join (E := E)]
      with yz hnorm hmem hjoin
    exact ⟨hnorm.1, fun t ht ↦ ⟨hmem t ht, hjoin t ht⟩⟩
  obtain ⟨P, Q, hPopen, hpP, hQopen, hpQ, hPQ⟩ :=
    mem_nhds_prod_iff'.mp hGood
  filter_upwards [prod_mem_nhds (hQopen.mem_nhds hpQ)
    (hPopen.mem_nhds hpP)] with pq hpq
  rcases pq with ⟨p, q⟩
  change p ∈ maxSliceLocus I C → q ∈ C → ∀ t ∈ Set.Ioc (0 : ℝ) 1,
    minJoin (I := I) g hEnorm q p t ∈ maxSliceLocus I C
  intro hp hqC t ht
  obtain ⟨N, hpN, hNC, hN⟩ := hp
  have hpQ : p ∈ Q := hpq.1
  have hqP : q ∈ P := hpq.2
  have htIcc : t ∈ Set.Icc (0 : ℝ) 1 := ⟨ht.1.le, ht.2⟩
  let Dq : PartialDiffeomorph 𝓘(ℝ, E) I E M ∞ := D q
  let N0 : Set M := N ∩ Q
  have hN0 : IsEmbeddedSlice I (maxSliceDim I C) N0 := hN.inter_open hQopen
  have hN0target : N0 ⊆ Dq.symm.source := by
    rintro y ⟨hyN, hyQ⟩
    have hgood : (q, y) ∈ Good := hPQ ⟨hqP, hyQ⟩
    simpa only [Dq] using hgood.1
  let Sco : Set E := Dq.symm '' N0
  have hSco : IsEmbeddedSlice 𝓘(ℝ, E) (maxSliceDim I C) Sco :=
    hN0.image Dq.symm hN0target
  let St : Set E := (fun z : E ↦ t • z) '' Sco
  have hSt : IsEmbeddedSlice 𝓘(ℝ, E) (maxSliceDim I C) St := by
    simpa only [St] using hSco.image_smul ht.1.ne'
  have hStSource : St ⊆ Dq.source := by
    rintro _ ⟨z, ⟨y, hyN0, rfl⟩, rfl⟩
    have hgood : (q, y) ∈ Good := hPQ ⟨hqP, hyN0.2⟩
    simpa only [Dq] using (hgood.2 t htIcc).1
  let T : Set M := Dq '' St
  have hT : IsEmbeddedSlice I (maxSliceDim I C) T :=
    hSt.image Dq hStSource
  have hTC : T ⊆ C := by
    rintro _ ⟨_, ⟨_, ⟨y, hyN0, rfl⟩, rfl⟩, rfl⟩
    have hgood : (q, y) ∈ Good := hPQ ⟨hqP, hyN0.2⟩
    have hjoin := (hgood.2 t htIcc).2
    rw [show Dq (t • Dq.symm y) =
      minJoin (I := I) g hEnorm q y t by simpa only [Dq] using hjoin]
    exact hC.minJoin hEnorm hqC (hNC hyN0.1) htIcc
  have hpN0 : p ∈ N0 := ⟨hpN, hpQ⟩
  have hpSco : Dq.symm p ∈ Sco := ⟨p, hpN0, rfl⟩
  have hpSt : t • Dq.symm p ∈ St := ⟨Dq.symm p, hpSco, rfl⟩
  have hpT : minJoin (I := I) g hEnorm q p t ∈ T := by
    refine ⟨t • Dq.symm p, hpSt, ?_⟩
    have hgood : (q, p) ∈ Good := hPQ ⟨hqP, hpQ⟩
    simpa only [Dq] using (hgood.2 t htIcc).2
  exact ⟨T, hpT, hTC, hT⟩

theorem max_slice_near
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    {C : Set M} (hC : IsTotallyConvex (I := I) g C)
    {p : M} (hp : p ∈ maxSliceLocus I C) :
    ∀ᶠ q in 𝓝 p, q ∈ C → ∀ t ∈ Set.Ioc (0 : ℝ) 1,
      minJoin (I := I) g hEnorm q p t ∈ maxSliceLocus I C := by
  let B := stdBranch (I := I) g hEnorm p
  have hmap : Tendsto (fun q : M ↦ (p, q)) (𝓝 p) (𝓝 (p, p)) :=
    continuousAt_const.prodMk continuousAt_id
  have hev := hmap.eventually (B.max_slice_pair g hEnorm hC)
  filter_upwards [hev] with q hq
  exact hq hp

theorem max_slice_intrinsic
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (hg : RiemannianMetricComplete (I := I) g)
    {C : Set M} (hC : IsTotallyConvex (I := I) g C)
    {O : M} (v : TangentSpace I O) {a b : ℝ} (hab : a ≤ b)
    (hmapC : Set.MapsTo (intrinsicGeodesic (I := I) g hEnorm O v)
      (Set.Icc a b) C)
    (hb : intrinsicGeodesic (I := I) g hEnorm O v b ∈
      maxSliceLocus I C) :
    Set.MapsTo (intrinsicGeodesic (I := I) g hEnorm O v)
      (Set.Ioc a b) (maxSliceLocus I C) := by
  rcases hab.eq_or_lt with rfl | hab
  · intro t ht
    exact (not_lt_of_ge ht.2 ht.1).elim
  let γ : ℝ → M := intrinsicGeodesic (I := I) g hEnorm O v
  have hγcont : Continuous γ :=
    intrinsicGeodesic_continuous (I := I) g hEnorm O v
  let A : Set (Set.Ioc a b) :=
    {t | γ t ∈ maxSliceLocus I C}
  let γC : Set.Ioc a b → C :=
    fun t ↦ ⟨γ t, hmapC ⟨t.property.1.le, t.property.2⟩⟩
  have hγCcont : Continuous γC :=
    (hγcont.comp continuous_subtype_val).subtype_mk _
  have hAopen : IsOpen A := by
    change IsOpen (γC ⁻¹' (C ↓∩ maxSliceLocus I C))
    exact (RiemannianMetricComplete.max_slice_rel_open hg hC).preimage hγCcont
  have hAcomp : IsOpen Aᶜ := by
    rw [isOpen_iff_mem_nhds]
    intro s hsA
    change γ (s : ℝ) ∉ maxSliceLocus I C at hsA
    have hsne : (s : ℝ) ≠ b := by
      intro hs
      apply hsA
      rw [hs]
      exact hb
    have hsIoo : (s : ℝ) ∈ Set.Ioo a b :=
      ⟨s.property.1, lt_of_le_of_ne s.property.2 hsne⟩
    let r : Set.Ioc a b → ℝ := fun u ↦ 2 * (s : ℝ) - (u : ℝ)
    have hrcont : Continuous r := continuous_const.sub continuous_subtype_val
    have hrself : r s = (s : ℝ) := by
      dsimp only [r]
      ring
    have hrmem : ∀ᶠ u in 𝓝 s, r u ∈ Set.Ioo a b := by
      apply hrcont.continuousAt
      apply isOpen_Ioo.mem_nhds
      rw [hrself]
      exact hsIoo
    let B := stdBranch (I := I) g hEnorm (γ s)
    let pair : Set.Ioc a b → M × M :=
      fun u ↦ (γ u, γ (r u))
    have hpaircont : Continuous pair :=
      (hγcont.comp continuous_subtype_val).prodMk (hγcont.comp hrcont)
    have hpair : ∀ᶠ u : Set.Ioc a b in 𝓝 s,
        γ u ∈ maxSliceLocus I C → γ (r u) ∈ C →
          ∀ t ∈ Set.Ioc (0 : ℝ) 1,
            minJoin (I := I) g hEnorm (γ (r u)) (γ u) t ∈
              maxSliceLocus I C := by
      have hlim : Filter.Tendsto pair (𝓝 s) (𝓝 (γ s, γ s)) := by
        have hscont : Filter.Tendsto pair (𝓝 s) (𝓝 (pair s)) :=
          hpaircont.continuousAt
        simpa only [pair, hrself] using hscont
      exact hlim.eventually (B.max_slice_pair g hEnorm hC)
    let times : Set.Ioc a b → ℝ × ℝ := fun u ↦ ((u : ℝ), r u)
    have htimes : Filter.Tendsto times (𝓝 s) (𝓝 ((s : ℝ), (s : ℝ))) := by
      have hcont : Continuous times := continuous_subtype_val.prodMk hrcont
      have hscont : Filter.Tendsto times (𝓝 s) (𝓝 (times s)) :=
        hcont.continuousAt
      simpa only [times, hrself] using hscont
    have hchord : ∀ᶠ u : Set.Ioc a b in 𝓝 s, ∀ t : ℝ,
        minJoin (I := I) g hEnorm (γ (r u)) (γ u) t =
          γ (t * ((u : ℝ) - r u) + r u) := by
      have h := htimes.eventually
        (B.min_join_chord v (s : ℝ))
      simpa only [times, γ] using h
    filter_upwards [hrmem, hpair, hchord] with u hru hpair hchord
    intro huA
    change γ (u : ℝ) ∈ maxSliceLocus I C at huA
    have hruC : γ (r u) ∈ C := hmapC ⟨hru.1.le, hru.2.le⟩
    have hmid := hpair huA hruC (1 / 2 : ℝ) (by constructor <;> norm_num)
    rw [hchord (1 / 2 : ℝ)] at hmid
    have htime : (1 / 2 : ℝ) * ((u : ℝ) - r u) + r u = (s : ℝ) := by
      dsimp only [r]
      ring
    rw [htime] at hmid
    exact hsA hmid
  have hAclosed : IsClosed A := by
    rw [← isOpen_compl_iff]
    exact hAcomp
  letI : PreconnectedSpace (Set.Ioc a b) :=
    Subtype.preconnectedSpace isPreconnected_Ioc
  have hAne : A.Nonempty := by
    exact ⟨⟨b, ⟨hab, le_rfl⟩⟩, hb⟩
  have hAuniv : A = Set.univ := IsClopen.eq_univ ⟨hAclosed, hAopen⟩ hAne
  intro t ht
  have htA : (⟨t, ht⟩ : Set.Ioc a b) ∈ A := by
    rw [hAuniv]
    exact Set.mem_univ _
  exact htA

theorem max_slice_forward
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (hg : RiemannianMetricComplete (I := I) g)
    {C : Set M} (hC : IsTotallyConvex (I := I) g C)
    {q p : M} (hq : q ∈ C) (hp : p ∈ maxSliceLocus I C) :
    ∀ t ∈ Set.Ioc (0 : ℝ) 1,
      minJoin (I := I) g hEnorm q p t ∈ maxSliceLocus I C := by
  have hmap := hC.minJoin hEnorm hq (max_slice_subset hp)
  have hend : intrinsicGeodesic (I := I) g hEnorm q
      (minimizingVec (I := I) g hEnorm q p) 1 ∈ maxSliceLocus I C := by
    simpa only [← expMapIntrinsic_def, minimizingVec_exp] using hp
  simpa only [minJoin] using
    (max_slice_intrinsic g hEnorm hg hC
      (minimizingVec (I := I) g hEnorm q p) zero_le_one hmap hend)

theorem max_slice_tot_conv
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (hg : RiemannianMetricComplete (I := I) g)
    {C : Set M} (hC : IsTotallyConvex (I := I) g C) :
    IsTotallyConvex (I := I) g (maxSliceLocus I C) := by
  intro γ a b hab hgeo hcont ha hb
  obtain ⟨Γ, hΓgeo, hΓsmooth, hEq⟩ :=
    exists_geo_eqOn_Icc (I := I) g hEnorm hab hgeo hcont
  let O : M := Γ 0
  let v : TangentSpace I O := mfderiv 𝓘(ℝ, ℝ) I Γ 0 1
  let κ : ℝ → M := intrinsicGeodesic (I := I) g hEnorm O v
  have hκgeo : Geodesic.IsGeodesic (I := I) g κ :=
    intrinsicGeodesic_isGeodesic (I := I) g hEnorm O v
  have hκcont : Continuous κ :=
    intrinsicGeodesic_continuous (I := I) g hEnorm O v
  have hfoot : Γ 0 = κ 0 := by
    simpa only [O, κ] using
      (intrinsicGeodesic_zero (I := I) g hEnorm O v).symm
  have hvel : (mfderiv 𝓘(ℝ, ℝ) I Γ 0 (1 : ℝ) : E) =
      (mfderiv 𝓘(ℝ, ℝ) I κ 0 (1 : ℝ) : E) := by
    simpa only [v, κ] using
      (intrinsicGeodesic_mfderiv_zero (I := I) g hEnorm O v).symm
  have hΓκ : Γ = κ :=
    isGeodesic_eq_of_initial (I := I) g hΓgeo hκgeo
      hΓsmooth.continuous hκcont hfoot hvel
  have hEqκ : Set.EqOn γ κ (Set.Icc a b) := by
    intro t ht
    exact (hEq ht).trans (congrFun hΓκ t)
  have hmapC : Set.MapsTo κ (Set.Icc a b) C := by
    intro t ht
    rw [← hEqκ ht]
    exact hC hab hgeo hcont (max_slice_subset ha) (max_slice_subset hb) ht
  have hbκ : κ b ∈ maxSliceLocus I C := by
    rw [← hEqκ ⟨hab, le_rfl⟩]
    exact hb
  have hprop := max_slice_intrinsic g hEnorm hg hC v hab hmapC hbκ
  intro t ht
  rcases ht.1.eq_or_lt with hta | hat
  · subst t
    exact ha
  · rw [hEqκ ht]
    exact hprop ⟨hat, ht.2⟩

theorem max_slice_tot_geo
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (hg : RiemannianMetricComplete (I := I) g)
    {C : Set M} (hC : IsTotallyConvex (I := I) g C) :
    IsTotallyGeodesic (I := I) g (maxSliceLocus I C) :=
  (max_slice_tot_conv g hEnorm hg hC).is_totally_geodesic

theorem max_slice_path_conn
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (hg : RiemannianMetricComplete (I := I) g)
    {C : Set M} (hC : IsTotallyConvex (I := I) g C)
    (hCne : C.Nonempty) : IsPathConnected (maxSliceLocus I C) := by
  rw [isPathConnected_iff]
  refine ⟨max_slice_nonempty (I := I) hCne, ?_⟩
  intro a ha b hb
  refine JoinedIn.ofLine
    (minJoin_cont (I := I) g hEnorm a b).continuousOn
    (minJoin_zero (I := I) g hEnorm a b)
    (minJoin_one (I := I) g hEnorm a b) ?_
  rintro _ ⟨t, ht, rfl⟩
  rcases eq_or_ne t 0 with rfl | ht0
  · simpa only [minJoin_zero] using ha
  · exact max_slice_forward g hEnorm hg hC (max_slice_subset ha) hb t
      ⟨lt_of_le_of_ne ht.1 (Ne.symm ht0), ht.2⟩

theorem max_slice_connected
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (hg : RiemannianMetricComplete (I := I) g)
    {C : Set M} (hC : IsTotallyConvex (I := I) g C)
    (hCne : C.Nonempty) : IsConnected (maxSliceLocus I C) :=
  (max_slice_path_conn g hEnorm hg hC hCne).isConnected

theorem max_slice_dense
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (hg : RiemannianMetricComplete (I := I) g)
    {C : Set M} (hC : IsTotallyConvex (I := I) g C)
    (hCne : C.Nonempty) : Set.closureIn C (maxSliceLocus I C) = C := by
  apply Set.Subset.antisymm Set.closureIn_carrier
  obtain ⟨p, hp⟩ := max_slice_nonempty (I := I) hCne
  intro q hq
  let γ : ℝ → M := minJoin (I := I) g hEnorm q p
  have hγcont : Continuous γ := minJoin_cont (I := I) g hEnorm q p
  have hpC : p ∈ C := max_slice_subset hp
  let τ : ℕ → ℝ := fun n ↦ 1 / ((n : ℝ) + 1)
  have hτmem (n : ℕ) : τ n ∈ Set.Ioc (0 : ℝ) 1 := by
    dsimp only [τ]
    constructor
    · positivity
    · apply (div_le_one (by positivity)).2
      have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith
  let f : ℕ → C := fun n ↦
    ⟨γ (τ n), hC.minJoin hEnorm hq hpC
      ⟨(hτmem n).1.le, (hτmem n).2⟩⟩
  have hτ : Filter.Tendsto τ Filter.atTop (𝓝 (0 : ℝ)) := by
    simpa only [τ] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hf : Filter.Tendsto f Filter.atTop (𝓝 (⟨q, hq⟩ : C)) := by
    rw [tendsto_subtype_rng]
    have hγ0 : Filter.Tendsto γ (𝓝 (0 : ℝ)) (𝓝 (γ 0)) :=
      hγcont.continuousAt
    have h := hγ0.comp hτ
    simpa only [f, γ, minJoin_zero] using h
  have hcl : (⟨q, hq⟩ : C) ∈ closure (C ↓∩ maxSliceLocus I C) := by
    apply mem_closure_of_tendsto hf
    filter_upwards [] with n
    change γ (τ n) ∈ maxSliceLocus I C
    exact max_slice_forward g hEnorm hg hC hq hp (τ n) (hτmem n)
  exact ⟨⟨q, hq⟩, hcl, rfl⟩

theorem max_stratum_of_enorm
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (hg : RiemannianMetricComplete (I := I) g)
    {C : Set M} (hC : IsTotallyConvex (I := I) g C)
    (hCne : C.Nonempty) :
    (maxSliceLocus I C).Nonempty ∧
      maxSliceLocus I C ⊆ C ∧
      IsEmbeddedSlice I (maxSliceDim I C) (maxSliceLocus I C) ∧
      IsOpen (C ↓∩ maxSliceLocus I C) ∧
      Set.closureIn C (maxSliceLocus I C) = C ∧
      IsConnected (maxSliceLocus I C) ∧
      IsTotallyConvex (I := I) g (maxSliceLocus I C) ∧
      IsTotallyGeodesic (I := I) g (maxSliceLocus I C) := by
  exact ⟨max_slice_nonempty (I := I) hCne,
    max_slice_subset,
    RiemannianMetricComplete.max_slice_is_slice hg hC,
    RiemannianMetricComplete.max_slice_rel_open hg hC,
    max_slice_dense g hEnorm hg hC hCne,
    max_slice_connected g hEnorm hg hC hCne,
    max_slice_tot_conv g hEnorm hg hC,
    max_slice_tot_geo g hEnorm hg hC⟩

end Geometry.Riemannian

namespace RiemannianMetricComplete

open Geometry Geometry.Riemannian

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [T2Space (TangentBundle I M)]
  [SigmaCompactSpace M] [ConnectedSpace M]

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace

theorem max_stratum_spec
    {g : SmoothRiemannianMetric I M}
    (hg : RiemannianMetricComplete (I := I) g)
    {C : Set M} (hC : IsTotallyConvex (I := I) g C)
    (hCne : C.Nonempty) :
    (maxSliceLocus I C).Nonempty ∧
      maxSliceLocus I C ⊆ C ∧
      IsEmbeddedSlice I (maxSliceDim I C) (maxSliceLocus I C) ∧
      IsOpen (C ↓∩ maxSliceLocus I C) ∧
      Set.closureIn C (maxSliceLocus I C) = C ∧
      IsConnected (maxSliceLocus I C) ∧
      IsTotallyConvex (I := I) g (maxSliceLocus I C) ∧
      IsTotallyGeodesic (I := I) g (maxSliceLocus I C) := by
  letI : IsManifold I 1 M :=
    IsManifold.of_le (I := I) (M := M) (n := (∞ : WithTop ℕ∞))
      (by decide : (1 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞))
  letI : TopologicalSpace.MetrizableSpace M := Manifold.metrizableSpace I M
  letI : T3Space M := inferInstance
  letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
    ⟨g.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle E
      (fun x : M ↦ TangentSpace I x) :=
    ⟨⟨g.inner, g.contMDiff.continuous, by intro x v w; rfl⟩⟩
  letI : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
  letI : CompleteSpace M := by simpa only using hg.complete
  let hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)) :=
    fun x v => tensor0SBundle_enorm_eq_riemannianBundle_enorm
      (I := I) g x v
  exact max_stratum_of_enorm g hEnorm hg hC hCne

theorem exists_max_stratum
    {g : SmoothRiemannianMetric I M}
    (hg : RiemannianMetricComplete (I := I) g)
    {C : Set M} (hC : IsTotallyConvex (I := I) g C)
    (hCne : C.Nonempty) :
    ∃ d : ℕ, ∃ N : Set M,
      d = maxSliceDim I C ∧ N = maxSliceLocus I C ∧
      N.Nonempty ∧ N ⊆ C ∧ IsEmbeddedSlice I d N ∧
      IsOpen (C ↓∩ N) ∧ Set.closureIn C N = C ∧ IsConnected N ∧
      IsTotallyConvex (I := I) g N ∧ IsTotallyGeodesic (I := I) g N := by
  rcases max_stratum_spec hg hC hCne with
    ⟨hne, hsub, hslice, hopen, hdense, hconn, hconv, hgeo⟩
  exact ⟨maxSliceDim I C, maxSliceLocus I C, rfl, rfl, hne, hsub, hslice,
    hopen, hdense, hconn, hconv, hgeo⟩

end RiemannianMetricComplete
end DifferentialGeometry
