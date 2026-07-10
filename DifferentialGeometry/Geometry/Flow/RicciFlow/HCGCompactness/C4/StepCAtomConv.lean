import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.StepB1Producers
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.StepBLocalMetrics
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.StepCAtoms

/-!
# C-infinity convergence of quadratic Step-C atom readouts

This file supplies the reusable calculus bridge from simultaneous convergence
of bilinear-form fields and coordinate maps to convergence of their quadratic
readouts.  It is the analytic core needed for the intrinsic Step-C atoms.
-/

noncomputable section

open Set
open scoped ContDiff Topology

namespace DifferentialGeometry
namespace HCGCompactness

universe uX uV

section QuadraticReadout

variable {X : Type uX} [NormedAddCommGroup X] [NormedSpace Real X]
variable {V : Type uV} [NormedAddCommGroup V] [NormedSpace Real V]

/-- Composition preserves `C^infty` convergence when the intermediate space
is finite-dimensional.  This is the finite-dimensional interface to the
proper-space composition engine. -/
theorem mapCInf_comp_fd {Y Z : Type*}
    [NormedAddCommGroup Y] [NormedSpace Real Y] [FiniteDimensional Real Y]
    [NormedAddCommGroup Z] [NormedSpace Real Z]
    {U : Set X} {W : Set Y} (hU : IsOpen U) (hW : IsOpen W)
    {B : Nat -> X -> Y} {Binf : X -> Y}
    {A : Nat -> Y -> Z} {Ainf : Y -> Z}
    (hB : MapCInfConvOnCompacts U B Binf)
    (hA : MapCInfConvOnCompacts W A Ainf)
    (hBc : forall k, ContDiffOn Real (∞ : WithTop ℕ∞) (B k) U)
    (hBinfc : ContDiffOn Real (∞ : WithTop ℕ∞) Binf U)
    (hAc : forall k, ContDiffOn Real (∞ : WithTop ℕ∞) (A k) W)
    (hAinfc : ContDiffOn Real (∞ : WithTop ℕ∞) Ainf W)
    (hmap : Set.MapsTo Binf U W) (hmapk : forall k, Set.MapsTo (B k) U W) :
    MapCInfConvOnCompacts U (fun k x => A k (B k x))
      (fun x => Ainf (Binf x)) := by
  letI : ProperSpace Y := FiniteDimensional.proper Real Y
  exact MapCInfConvOnCompacts.comp hU hW hB hA hBc hBinfc hAc hAinfc hmap hmapk

/-- Restrict a convergent family to a fixed argument, viewed as a family of
constant maps on any other open source domain. -/
theorem mapCInf_constArg {Y F : Type*}
    [NormedAddCommGroup Y] [NormedSpace Real Y] [ProperSpace Y]
    [NormedAddCommGroup F] [NormedSpace Real F]
    {U : Set X} {W : Set Y} (hU : IsOpen U) (hW : IsOpen W)
    {A : Nat -> Y -> F} {Ainf : Y -> F} {y0 : Y}
    (hy0 : y0 ∈ W) (hA : MapCInfConvOnCompacts W A Ainf)
    (hAc : forall k, ContDiffOn Real (∞ : WithTop ℕ∞) (A k) W)
    (hAinfc : ContDiffOn Real (∞ : WithTop ℕ∞) Ainf W) :
    MapCInfConvOnCompacts U (fun k _ => A k y0) (fun _ => Ainf y0) := by
  have hconst : MapCInfConvOnCompacts U
      (fun _ : Nat => fun _ : X => y0) (fun _ : X => y0) :=
    mapCInfConv_const (U := U) (fun _ : X => y0)
  exact MapCInfConvOnCompacts.comp hU hW hconst hA
    (fun _ => contDiffOn_const) contDiffOn_const hAc hAinfc
    (fun _ _ => hy0) (fun _ _ _ => hy0)

/-- Evaluate a bilinear-form field twice on the same vector field. -/
def quadRead (B : X -> (V →L[Real] V →L[Real] Real))
    (v : X -> V) (x : X) : Real :=
  B x (v x) (v x)

/-- Smooth bilinear-form and vector fields have a smooth quadratic readout. -/
theorem quadRead_contDiff {B : X -> (V →L[Real] V →L[Real] Real)}
    {v : X -> V} {n : WithTop ℕ∞}
    (hB : ContDiff Real n B) (hv : ContDiff Real n v) :
    ContDiff Real n (quadRead B v) := by
  exact (hB.clm_apply hv).clm_apply hv

/-- Simultaneous `C^infty` convergence of bilinear-form fields and vector
fields passes to the quadratic readout `B(x)(v(x), v(x))`. -/
theorem quadRead_conv
    [FiniteDimensional Real V]
    {U : Set X} (hU : IsOpen U)
    {B : Nat -> X -> (V →L[Real] V →L[Real] Real)}
    {Binf : X -> (V →L[Real] V →L[Real] Real)}
    {v : Nat -> X -> V} {vinf : X -> V}
    (hB : MapCInfConvOnCompacts U B Binf)
    (hv : MapCInfConvOnCompacts U v vinf)
    (hBc : forall k, ContDiffOn Real (∞ : WithTop ℕ∞) (B k) U)
    (hBinfc : ContDiffOn Real (∞ : WithTop ℕ∞) Binf U)
    (hvc : forall k, ContDiffOn Real (∞ : WithTop ℕ∞) (v k) U)
    (hvinfc : ContDiffOn Real (∞ : WithTop ℕ∞) vinf U) :
    MapCInfConvOnCompacts U (fun k => quadRead (B k) (v k))
      (quadRead Binf vinf) := by
  let evalQuad : ((V →L[Real] V →L[Real] Real) × V) -> Real :=
    fun q => q.1 q.2 q.2
  have heval : ContDiff Real (∞ : WithTop ℕ∞) evalQuad := by
    exact (contDiff_fst.clm_apply contDiff_snd).clm_apply contDiff_snd
  have hpair := mapCInfConv_prodMk hU hB hv hBc hBinfc hvc hvinfc
  have hcomp := mapCInf_comp_fd hU isOpen_univ hpair
    (mapCInfConv_const (U := (Set.univ : Set ((V →L[Real] V →L[Real] Real) × V)))
      evalQuad)
    (fun k => (hBc k).prodMk (hvc k)) (hBinfc.prodMk hvinfc)
    (fun _ => heval.contDiffOn) heval.contDiffOn
    (Set.mapsTo_univ _ _) (fun _ => Set.mapsTo_univ _ _)
  exact hcomp

/-- Postcomposing a convergent quadratic readout with a fixed smooth scalar
function preserves `C^infty` convergence. -/
theorem quadBump_conv
    [FiniteDimensional Real V]
    {U : Set X} (hU : IsOpen U)
    {B : Nat -> X -> (V →L[Real] V →L[Real] Real)}
    {Binf : X -> (V →L[Real] V →L[Real] Real)}
    {v : Nat -> X -> V} {vinf : X -> V}
    (hB : MapCInfConvOnCompacts U B Binf)
    (hv : MapCInfConvOnCompacts U v vinf)
    (hBc : forall k, ContDiffOn Real (∞ : WithTop ℕ∞) (B k) U)
    (hBinfc : ContDiffOn Real (∞ : WithTop ℕ∞) Binf U)
    (hvc : forall k, ContDiffOn Real (∞ : WithTop ℕ∞) (v k) U)
    (hvinfc : ContDiffOn Real (∞ : WithTop ℕ∞) vinf U)
    (f : Real -> Real) (hf : ContDiff Real (∞ : WithTop ℕ∞) f) :
    MapCInfConvOnCompacts U
      (fun k x => f (quadRead (B k) (v k) x))
      (fun x => f (quadRead Binf vinf x)) := by
  have hquad := quadRead_conv hU hB hv hBc hBinfc hvc hvinfc
  have hqc : forall k, ContDiffOn Real (∞ : WithTop ℕ∞)
      (quadRead (B k) (v k)) U :=
    fun k => (hBc k).clm_apply (hvc k) |>.clm_apply (hvc k)
  have hqinfc : ContDiffOn Real (∞ : WithTop ℕ∞)
      (quadRead Binf vinf) U :=
    hBinfc.clm_apply hvinfc |>.clm_apply hvinfc
  exact MapCInfConvOnCompacts.comp hU isOpen_univ hquad
    (mapCInfConv_const (U := (Set.univ : Set Real)) f)
    hqc hqinfc (fun _ => hf.contDiffOn) hf.contDiffOn
    (Set.mapsTo_univ _ _) (fun _ => Set.mapsTo_univ _ _)

/-- A coordinate of a finite Pi-valued family inherits `C^infty` convergence
on compacts. -/
theorem mapCInf_apply {ι Q : Type*} [Fintype ι]
    [NormedAddCommGroup Q] [NormedSpace Real Q]
    {U : Set X} (hU : IsOpen U)
    {u : Nat -> X -> (ι -> Q)} {uinf : X -> (ι -> Q)}
    (hu : MapCInfConvOnCompacts U u uinf)
    (huc : forall k, ContDiffOn Real (∞ : WithTop ℕ∞) (u k) U)
    (huinfc : ContDiffOn Real (∞ : WithTop ℕ∞) uinf U) (i : ι) :
    MapCInfConvOnCompacts U (fun k x => u k x i) (fun x => uinf x i) := by
  intro K hK hKU p epsilon hepsilon
  obtain ⟨k0, hk0⟩ := hu K hK hKU p epsilon hepsilon
  refine ⟨k0, fun k hk r hr x hx => ?_⟩
  have hxU : x ∈ U := hKU hx
  have hle : ((r : ℕ∞) : WithTop ℕ∞) <= (∞ : WithTop ℕ∞) := by
    exact_mod_cast le_top
  have hcd : forall j : ι, ContDiffAt Real (r : ℕ∞)
      (fun y => u k y j - uinf y j) x := by
    intro j
    exact (((contDiffOn_pi.mp (huc k) j).sub (contDiffOn_pi.mp huinfc j)).contDiffAt
      (hU.mem_nhds hxU)).of_le hle
  have hbase := hk0 k hk r hr x hx
  simp only [mapDerivNorm] at hbase ⊢
  change ‖iteratedFDeriv Real r (fun y j => u k y j - uinf y j) x‖ <= epsilon at hbase
  rw [iteratedFDerivPi hcd le_rfl, ContinuousMultilinearMap.opNorm_pi] at hbase
  exact (norm_le_pi_norm (fun j =>
    iteratedFDeriv Real r (fun y => u k y j - uinf y j) x) i).trans hbase

/-- Finite-family variant of `quadBump_conv`: select one bilinear coefficient
from a convergent Pi-valued metric family and evaluate it twice on a convergent
vector field before applying a fixed smooth scalar function. -/
theorem quadPiBump_conv {ι : Type*} [Fintype ι]
    [FiniteDimensional Real V]
    {U : Set X} (hU : IsOpen U)
    {B : Nat -> X -> (ι -> (V →L[Real] V →L[Real] Real))}
    {Binf : X -> (ι -> (V →L[Real] V →L[Real] Real))}
    {v : Nat -> X -> V} {vinf : X -> V}
    (hB : MapCInfConvOnCompacts U B Binf)
    (hv : MapCInfConvOnCompacts U v vinf)
    (hBc : forall k, ContDiffOn Real (∞ : WithTop ℕ∞) (B k) U)
    (hBinfc : ContDiffOn Real (∞ : WithTop ℕ∞) Binf U)
    (hvc : forall k, ContDiffOn Real (∞ : WithTop ℕ∞) (v k) U)
    (hvinfc : ContDiffOn Real (∞ : WithTop ℕ∞) vinf U)
    (i : ι) (f : Real -> Real) (hf : ContDiff Real (∞ : WithTop ℕ∞) f) :
    MapCInfConvOnCompacts U
      (fun k x => f (B k x i (v k x) (v k x)))
      (fun x => f (Binf x i (vinf x) (vinf x))) := by
  exact quadBump_conv hU (mapCInf_apply hU hB hBc hBinfc i) hv
    (fun k => contDiffOn_pi.mp (hBc k) i) (contDiffOn_pi.mp hBinfc i)
    hvc hvinfc f hf

section WeightConvergence

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] in
/-- Smooth atom families give smooth base-killed raw numerators. -/
theorem cutRaw_contDiffOn {U : Set X} {a : ι -> X -> Real}
    (ha : forall i, ContDiffOn Real (∞ : WithTop ℕ∞) (a i) U)
    (i0 i : ι) :
    ContDiffOn Real (∞ : WithTop ℕ∞) (cutRaw (a i0) a i0 i) U := by
  by_cases hi : i = i0
  · subst i
    have heq : cutRaw (a i0) a i0 i0 = a i0 := by
      funext x
      exact cutRaw_same (a i0) a i0 x
    rw [heq]
    exact ha i0
  · have hkill : ContDiffOn Real (∞ : WithTop ℕ∞)
        (fun x => (1 : Real) - a i0 x) U :=
      (contDiffOn_const (c := (1 : Real))).sub (ha i0)
    refine ContDiffOn.congr (hkill.mul (ha i)) ?_
    intro x _hx
    exact cutRaw_of_ne (a i0) a i0 i x hi

omit [Fintype ι] in
/-- Base killing preserves per-slot `C^infty` convergence of atom families. -/
theorem cutRaw_conv {U : Set X} (hU : IsOpen U)
    {a : Nat -> ι -> X -> Real} {ainf : ι -> X -> Real}
    (hconv : forall i, MapCInfConvOnCompacts U (fun k => a k i) (ainf i))
    (hc : forall k i, ContDiffOn Real (∞ : WithTop ℕ∞) (a k i) U)
    (hcinf : forall i, ContDiffOn Real (∞ : WithTop ℕ∞) (ainf i) U)
    (i0 i : ι) :
    MapCInfConvOnCompacts U
      (fun k => cutRaw (a k i0) (a k) i0 i)
      (cutRaw (ainf i0) ainf i0 i) := by
  by_cases hi : i = i0
  · subst i
    have hseq : (fun k => cutRaw (a k i0) (a k) i0 i0) =
        (fun k => a k i0) := by
      funext k x
      exact cutRaw_same (a k i0) (a k) i0 x
    have hinf : cutRaw (ainf i0) ainf i0 i0 = ainf i0 := by
      funext x
      exact cutRaw_same (ainf i0) ainf i0 x
    rw [hseq, hinf]
    exact hconv i0
  · let oneSub : Real -> Real := fun t => 1 - t
    have hone : ContDiff Real (∞ : WithTop ℕ∞) oneSub :=
      contDiff_const.sub contDiff_id
    have hkill := mapCInf_comp_fd hU isOpen_univ (hconv i0)
      (mapCInfConv_const (U := (Set.univ : Set Real)) oneSub)
      (fun k => hc k i0) (hcinf i0) (fun _ => hone.contDiffOn) hone.contDiffOn
      (Set.mapsTo_univ _ _) (fun _ => Set.mapsTo_univ _ _)
    have hmul := mapCInfConv_mul hU hkill (hconv i)
      (fun k => contDiffOn_const.sub (hc k i0)) (contDiffOn_const.sub (hcinf i0))
      (fun k => hc k i) (hcinf i)
    refine hmul.congr hU (fun k x _ => ?_) (fun x _ => ?_)
    · simp only [oneSub]
      exact cutRaw_of_ne (a k i0) (a k) i0 i x hi
    · simp only [oneSub]
      exact cutRaw_of_ne (ainf i0) ainf i0 i x hi

omit [DecidableEq ι] in
/-- The arbitrary-base normalized weights specialize to the existing
model-space quotient convergence theorem. -/
theorem rawWeights_conv {U : Set X} (hU : IsOpen U)
    {num : Nat -> ι -> X -> Real} {numinf : ι -> X -> Real}
    {delta : Real} (hdelta : 0 < delta)
    (hconv : forall i, MapCInfConvOnCompacts U (fun k => num k i) (numinf i))
    (hc : forall k i, ContDiffOn Real (∞ : WithTop ℕ∞) (num k i) U)
    (hcinf : forall i, ContDiffOn Real (∞ : WithTop ℕ∞) (numinf i) U)
    (hlow : forall k, forall z, z ∈ U -> delta < ∑ j, num k j z)
    (hlowinf : forall z, z ∈ U -> delta < ∑ j, numinf j z) (i : ι) :
    MapCInfConvOnCompacts U
      (fun k z => rawWeights (num k) z i) (fun z => rawWeights numinf z i) := by
  simpa only [rawWeights, normWeights] using
    (normWeightsConv hU hdelta hconv hc hcinf hlow hlowinf i)

omit [NormedAddCommGroup X] [NormedSpace Real X] in
/-- If some atom is one and the base atom lies in `[0,1]`, the sum of the
base-killed raw numerators is at least one half. -/
theorem cutRaw_sum_half {a : ι -> X -> Real} {i0 : ι} {x : X}
    (hbase : a i0 x ∈ Set.Icc (0 : Real) 1)
    (hnn : forall i, 0 <= a i x) (hcover : exists i, a i x = 1) :
    (1 / 2 : Real) <= ∑ i, cutRaw (a i0) a i0 i x := by
  have hrawnn : forall i, 0 <= cutRaw (a i0) a i0 i x :=
    fun i => cutRaw_nonneg hbase hnn i
  by_cases hhalf : (1 / 2 : Real) <= a i0 x
  · exact hhalf.trans (by
      simpa only [cutRaw_same] using
        (Finset.single_le_sum (fun j _ => hrawnn j) (Finset.mem_univ i0)))
  · obtain ⟨j, hj⟩ := hcover
    have hji : j ≠ i0 := by
      intro h
      subst j
      linarith
    have hjraw : (1 / 2 : Real) <= cutRaw (a i0) a i0 j x := by
      rw [cutRaw_of_ne (a i0) a i0 j x hji, hj, mul_one]
      linarith
    exact hjraw.trans
      (Finset.single_le_sum (fun q _ => hrawnn q) (Finset.mem_univ j))

/-- Covered atom families yield convergent normalized base-killed weights.
The uniform denominator bound is intrinsic: one raw numerator is always at
least one half, and the same lower bound passes to the limit. -/
theorem cutWeights_conv {U : Set X} (hU : IsOpen U)
    {a : Nat -> ι -> X -> Real} {ainf : ι -> X -> Real}
    (hconv : forall i, MapCInfConvOnCompacts U (fun k => a k i) (ainf i))
    (hc : forall k i, ContDiffOn Real (∞ : WithTop ℕ∞) (a k i) U)
    (hcinf : forall i, ContDiffOn Real (∞ : WithTop ℕ∞) (ainf i) U)
    (i0 : ι)
    (hbase : forall k z, z ∈ U -> a k i0 z ∈ Set.Icc (0 : Real) 1)
    (hnn : forall k z, z ∈ U -> forall i, 0 <= a k i z)
    (hcover : forall k z, z ∈ U -> exists i, a k i z = 1)
    (i : ι) :
    MapCInfConvOnCompacts U
      (fun k z => rawWeights (cutRaw (a k i0) (a k) i0) z i)
      (fun z => rawWeights (cutRaw (ainf i0) ainf i0) z i) := by
  have hraw : forall j, MapCInfConvOnCompacts U
      (fun k => cutRaw (a k i0) (a k) i0 j)
      (cutRaw (ainf i0) ainf i0 j) :=
    fun j => cutRaw_conv hU hconv hc hcinf i0 j
  have hrawc : forall k j, ContDiffOn Real (∞ : WithTop ℕ∞)
      (cutRaw (a k i0) (a k) i0 j) U :=
    fun k j => cutRaw_contDiffOn (fun q => hc k q) i0 j
  have hrawcinf : forall j, ContDiffOn Real (∞ : WithTop ℕ∞)
      (cutRaw (ainf i0) ainf i0 j) U :=
    fun j => cutRaw_contDiffOn hcinf i0 j
  have hlow : forall k, forall z, z ∈ U ->
      (1 / 4 : Real) < ∑ j, cutRaw (a k i0) (a k) i0 j z := by
    intro k z hz
    have hhalf := cutRaw_sum_half (hbase k z hz) (hnn k z hz) (hcover k z hz)
    linarith
  have hlowinf : forall z, z ∈ U ->
      (1 / 4 : Real) < ∑ j, cutRaw (ainf i0) ainf i0 j z := by
    intro z hz
    have hsum : Filter.Tendsto
        (fun k => ∑ j, cutRaw (a k i0) (a k) i0 j z) Filter.atTop
        (nhds (∑ j, cutRaw (ainf i0) ainf i0 j z)) :=
      tendsto_finset_sum Finset.univ fun j _ => tendsto_of_cInf (hraw j) hz
    have hhalf : (1 / 2 : Real) <= ∑ j, cutRaw (ainf i0) ainf i0 j z :=
      ge_of_tendsto hsum (Filter.Eventually.of_forall fun k =>
        cutRaw_sum_half (hbase k z hz) (hnn k z hz) (hcover k z hz))
    linarith
  exact rawWeights_conv hU (by norm_num : (0 : Real) < 1 / 4)
    hraw hrawc hrawcinf hlow hlowinf i

end WeightConvergence

end QuadraticReadout

section OriginMetric

open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.NormalCoordinates
open scoped Manifold

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
variable [FiniteDimensional Real E] [NeZero (Module.finrank Real E)] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]

/-- At the origin of a normal chart, the pulled-back coordinate metric is the
metric inner product at the chart centre. -/
theorem normalMetric_zero
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) (c : Y.M) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    normalCoordMetric (I := I) Y c 0 = Y.metric.inner c := by
  letI : TopologicalSpace Y.M := Y.topology
  letI : ChartedSpace H Y.M := Y.charted
  letI : IsManifold I ∞ Y.M := Y.smooth
  letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  ext v w
  rw [normalCoordMetric_apply (I := I), expMapDiffeo_zero (I := I)]
  exact normalChartAt_metric_pullback_at_origin (I := I) Y.metric c v w

/-- On a normal-chart overlap, the intrinsic quadratic bump is the scalar bump
applied to the origin metric coefficient and the normal transition vector. -/
theorem quadNormal_readout
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) (beta gamma : Y.M)
    (f : ContDiffBump (0 : Real)) {z : E}
    (hsrc :
      letI : TopologicalSpace Y.M := Y.topology
      letI : ChartedSpace H Y.M := Y.charted
      letI : IsManifold I ∞ Y.M := Y.smooth
      letI : T2Space Y.M := Y.t2
      letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
      expMapDiffeo (I := I) Y.metric beta z ∈
        (normalChartAt (I := I) Y.metric gamma).source) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : T2Space Y.M := Y.t2
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    quadNormal Y.metric gamma f (expMapDiffeo (I := I) Y.metric beta z) =
      f (normalCoordMetric (I := I) Y gamma 0
        (normalTransition (I := I) Y beta gamma z)
        (normalTransition (I := I) Y beta gamma z)) := by
  letI : TopologicalSpace Y.M := Y.topology
  letI : ChartedSpace H Y.M := Y.charted
  letI : IsManifold I ∞ Y.M := Y.smooth
  letI : T2Space Y.M := Y.t2
  letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  rw [quadNormal_of_mem Y.metric gamma f hsrc,
    normalMetric_zero (I := I) Y gamma]
  rfl

/-- Chart formula for one concrete Step-C atom. -/
theorem stepCAtom_readout
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) (beta gamma : Y.M)
    (lam : Real) (hlam : 0 < lam) {z : E}
    (hsrc :
      letI : TopologicalSpace Y.M := Y.topology
      letI : ChartedSpace H Y.M := Y.charted
      letI : IsManifold I ∞ Y.M := Y.smooth
      letI : T2Space Y.M := Y.t2
      letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
      expMapDiffeo (I := I) Y.metric beta z ∈
        (normalChartAt (I := I) Y.metric gamma).source) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : T2Space Y.M := Y.t2
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    stepCAtom Y gamma lam hlam (expMapDiffeo (I := I) Y.metric beta z) =
      stepCBump lam hlam
        (normalCoordMetric (I := I) Y gamma 0
          (normalTransition (I := I) Y beta gamma z)
          (normalTransition (I := I) Y beta gamma z)) := by
  exact quadNormal_readout (I := I) Y beta gamma (stepCBump lam hlam) hsrc

/-- Pull one Step-C atom back by the exponential-side chart at `beta`. -/
noncomputable def stepCAtomChart
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) (beta gamma : Y.M)
    (lam : Real) (hlam : 0 < lam) (z : E) : Real :=
  letI : TopologicalSpace Y.M := Y.topology
  letI : ChartedSpace H Y.M := Y.charted
  letI : IsManifold I ∞ Y.M := Y.smooth
  letI : T2Space Y.M := Y.t2
  letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  stepCAtom Y gamma lam hlam (expMapDiffeo (I := I) Y.metric beta z)

/-- Concrete chart-pulled Step-C atoms converge once the finite family of
origin metric coefficients and the beta-to-gamma normal transitions converge
on one shared subsequence. -/
theorem stepCAtom_conv {ι : Type*} [Fintype ι]
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (center : ι -> forall k : Nat, (X.obj k).M)
    (beta : forall k : Nat, (X.obj k).M)
    (lam : ι -> Real) (hlam : forall i, 0 < lam i)
    {U : Set E} (hU : IsOpen U)
    {gInf : E -> (ι -> (E →L[Real] E →L[Real] Real))}
    (hg : MapCInfConvOnCompacts U
      (fun k _ i => normalCoordMetric (I := I) (X.obj k) (center i k) 0) gInf)
    (hginf : ContDiffOn Real (∞ : WithTop ℕ∞) gInf U)
    {Jinf : ι -> E -> E}
    (hJ : forall i, MapCInfConvOnCompacts U
      (fun k => normalTransition (I := I) (X.obj k) (beta k) (center i k))
      (Jinf i))
    (hJc : forall i k, ContDiffOn Real (∞ : WithTop ℕ∞)
      (normalTransition (I := I) (X.obj k) (beta k) (center i k)) U)
    (hJinfc : forall i, ContDiffOn Real (∞ : WithTop ℕ∞) (Jinf i) U)
    (hsrc : forall i k z, z ∈ U ->
      letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
      letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
      letI : T2Space (X.obj k).M := (X.obj k).t2
      letI : T2Space (TangentBundle I (X.obj k).M) := (X.obj k).t2TangentBundle
      expMapDiffeo (I := I) (X.obj k).metric (beta k) z ∈
        (normalChartAt (I := I) (X.obj k).metric (center i k)).source)
    (i : ι) :
    MapCInfConvOnCompacts U
      (fun k => stepCAtomChart (I := I) (X.obj k) (beta k) (center i k)
        (lam i) (hlam i))
      (fun z => stepCBump (lam i) (hlam i)
        (gInf z i (Jinf i z) (Jinf i z))) := by
  have hraw := quadPiBump_conv hU hg (hJ i)
    (fun _ => contDiffOn_const) hginf (hJc i) (hJinfc i)
    i (stepCBump (lam i) (hlam i)) (stepCBump (lam i) (hlam i)).contDiff
  refine hraw.congr hU (fun k z hz => ?_) (fun _ _ => rfl)
  simpa only [stepCAtomChart] using
    (stepCAtom_readout (I := I) (X.obj k) (beta k) (center i k)
      (lam i) (hlam i) (hsrc i k z hz))

/-- Extract a `C^infty` limit of the metric coefficients at a moving sequence
of normal-chart centres.  The maps are made constant in the auxiliary model
variable, so only the already uniform order-zero bound at the chart origin is
needed; no common positive normal-coordinate radius is assumed. -/
theorem existsOriginMetric
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (input : NormalCoordMetricBoundInput (I := I) X)
    (c : forall k : Nat, (X.obj k).M) :
    exists (phi : Nat -> Nat)
        (gInf : E -> (E →L[Real] E →L[Real] Real)),
      StrictMono phi ∧ ContDiffOn Real (∞ : WithTop ℕ∞) gInf Set.univ ∧
        MapCInfConvOnCompacts Set.univ
          (fun k _ => normalCoordMetric (I := I) (X.obj (phi k)) (c (phi k)) 0)
          gInf ∧
        forall z : E, forall v : E,
          (1 / 2 : Real) * ‖v‖ ^ 2 <= gInf z v v ∧
            gInf z v v <= 2 * ‖v‖ ^ 2 := by
  let g0 : Nat -> E -> (E →L[Real] E →L[Real] Real) :=
    fun k _ => normalCoordMetric (I := I) (X.obj k) (c k) 0
  have hzero : forall k, (0 : E) ∈ Metric.ball 0 (input.radius k (c k)) := by
    intro k
    rw [Metric.mem_ball, dist_self]
    exact input.radius_pos k (c k)
  have hsmooth : forall k, ContDiffOn Real (∞ : WithTop ℕ∞) (g0 k) Set.univ :=
    fun _ => contDiffOn_const
  have hbdd : forall r : Nat, forall K : Set E, IsCompact K -> K ⊆ Set.univ ->
      exists M : Real, forall k : Nat, forall x, x ∈ K ->
        ‖iteratedFDeriv Real r (g0 k) x‖ <= M := by
    intro r K _hK _hKU
    refine ⟨input.metricC 0, fun k x _hx => ?_⟩
    by_cases hr : r = 0
    · subst r
      simpa only [g0, norm_iteratedFDeriv_zero] using
        (input.metric_deriv k 0 (c k) 0 (hzero k))
    · simp only [g0, iteratedFDeriv_const_of_ne hr, Pi.zero_apply, norm_zero]
      exact input.metricC_nonneg 0
  have hequiv : forall k : Nat, forall z, z ∈ (Set.univ : Set E) -> forall v : E,
      (1 / 2 : Real) * ‖v‖ ^ 2 <= g0 k z v v ∧
        g0 k z v v <= 2 * ‖v‖ ^ 2 := by
    intro k _z _hz v
    exact input.metric_equiv k (c k) 0 (hzero k) v
  simpa only [g0, Set.mem_univ, forall_const] using
    (exists_metricLimit_on (E := E) isOpen_univ g0 hsmooth hbdd hequiv)

/-- Extract one shared subsequence for the origin metric coefficients of a
finite family of moving normal-chart centres.  Bundling all slots in a finite
Pi-space lets Arzela--Ascoli perform the finite diagonal in one step. -/
theorem existsMetric0Univ {ι : Type*} [Fintype ι]
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (input : NormalCoordMetricBoundInput (I := I) X)
    (c : ι -> forall k : Nat, (X.obj k).M) :
    exists (phi : Nat -> Nat)
        (gInf : E -> (ι -> (E →L[Real] E →L[Real] Real))),
      StrictMono phi ∧ ContDiffOn Real (∞ : WithTop ℕ∞) gInf Set.univ ∧
        MapCInfConvOnCompacts Set.univ
          (fun k _ i => normalCoordMetric (I := I) (X.obj (phi k))
            (c i (phi k)) 0)
          gInf := by
  let g0 : Nat -> E -> (ι -> (E →L[Real] E →L[Real] Real)) :=
    fun k _ i => normalCoordMetric (I := I) (X.obj k) (c i k) 0
  have hzero : forall k i,
      (0 : E) ∈ Metric.ball 0 (input.radius k (c i k)) := by
    intro k i
    rw [Metric.mem_ball, dist_self]
    exact input.radius_pos k (c i k)
  have hsmooth : forall k, ContDiffOn Real (∞ : WithTop ℕ∞) (g0 k) Set.univ :=
    fun _ => contDiffOn_const
  have hbdd : forall r : Nat, forall K : Set E, IsCompact K -> K ⊆ Set.univ ->
      exists M : Real, forall k : Nat, forall x, x ∈ K ->
        ‖iteratedFDeriv Real r (g0 k) x‖ <= M := by
    intro r K _hK _hKU
    refine ⟨input.metricC 0, fun k x _hx => ?_⟩
    by_cases hr : r = 0
    · subst r
      rw [norm_iteratedFDeriv_zero, pi_norm_le_iff_of_nonneg (input.metricC_nonneg 0)]
      intro i
      simpa only [g0, norm_iteratedFDeriv_zero] using
        (input.metric_deriv k 0 (c i k) 0 (hzero k i))
    · simp only [g0, iteratedFDeriv_const_of_ne hr, Pi.zero_apply, norm_zero]
      exact input.metricC_nonneg 0
  obtain ⟨phi, gInf, hphi, hginf, hconv⟩ :=
    exists_cInf_subseq_on isOpen_univ g0 hsmooth hbdd
  simpa only [g0] using ⟨phi, gInf, hphi, hginf, hconv⟩

end OriginMetric

end HCGCompactness
end DifferentialGeometry
