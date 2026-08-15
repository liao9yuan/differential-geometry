import DifferentialGeometry.Geometry.Comparison.HopfRinowProper
import DifferentialGeometry.Geometry.Comparison.MinimizingBranch
import DifferentialGeometry.Geometry.Exponential.DiagExpDerivative
import DifferentialGeometry.Geometry.Topology.ConeSlice
import DifferentialGeometry.Geometry.Topology.NearestPoint

set_option autoImplicit false

noncomputable section

open Bundle Filter Manifold Set Topology
open scoped ContDiff ENNReal Manifold Topology

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

end RiemannianMetricComplete
end DifferentialGeometry
