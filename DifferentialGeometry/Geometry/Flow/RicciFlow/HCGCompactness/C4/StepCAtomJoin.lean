import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.StepCAtomConv
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.StepBTransition

set_option autoImplicit false
set_option linter.style.longLine false

/-!
# Common metric/transition refinement for live Step-C atoms

The origin-metric and transition-map compactness arguments are parallel.  This
file runs the metric extraction first, runs the transition extraction on that
refined sequence, and preserves the metric limit along the second refinement.
Only stabilized live slots participate.  Since a live slot may still use its
totalized fallback centre at finitely many early indices, the geometric inputs
are required only eventually and a common finite prefix is discarded before
the transition extraction.
-/

noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace HCGCompactness

open Filter Topology
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.NormalCoordinates
open DifferentialGeometry.Geometry.Riemannian.Exponential
open scoped Manifold ContDiff Topology

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
variable [FiniteDimensional Real E] [NeZero (Module.finrank Real E)] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]

/-- One strict refinement carrying both the finite live-slot origin metrics and
the forward normal transitions from one fixed source-centre family `beta`.

The overlap, source-ball, and image hypotheses are eventual: stabilized live
slots need not be genuine centres at finitely many early indices.  Finiteness of
`LiveSlot` supplies one common tail.  The forward maps are then bundled into the
Pi-valued map `E -> (LiveSlot L pb r -> E)`, so one Arzela--Ascoli extraction
handles all live slots at once.  This theorem deliberately does not request or
discard reverse maps or cocycle hypotheses.  A later finite diagonal over the
source slot supplies the all-pairs chart system. -/
theorem existsLiveJoint
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (metricInput : NormalCoordMetricBoundInput (I := I) X)
    (transInput : ExpInverseDerivBoundInput (I := I) X)
    {hd : InjRadiusDecayInput (I := I) X} {D : Real}
    (P : forall k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData hd D P) (pb : hd.PackingBound D) (r : Real)
    (beta : forall k : Nat, (X.obj (L.φ k)).M)
    (U : Set E) (hU : IsOpen U)
    (hovlJ : forall gamma : LiveSlot L pb r, ∀ᶠ k in Filter.atTop,
      NormalOverlapOn (I := I) (X.obj (L.φ k)) (beta k)
        (seqCenterD hd P L k (gamma.1 : Nat)) U)
    (hUx : ∀ᶠ k in Filter.atTop,
      letI : TopologicalSpace (X.obj (L.φ k)).M := (X.obj (L.φ k)).topology
      letI : ChartedSpace H (X.obj (L.φ k)).M := (X.obj (L.φ k)).charted
      letI : IsManifold I ∞ (X.obj (L.φ k)).M := (X.obj (L.φ k)).smooth
      letI : T2Space (TangentBundle I (X.obj (L.φ k)).M) :=
        (X.obj (L.φ k)).t2TangentBundle
      U ⊆ Metric.ball (0 : E)
        (min transInput.r₁
          (expMapC2Radius (I := I) (X.obj (L.φ k)).metric (beta k))))
    (hmapsJ : forall gamma : LiveSlot L pb r, ∀ᶠ k in Filter.atTop,
      letI : TopologicalSpace (X.obj (L.φ k)).M := (X.obj (L.φ k)).topology
      letI : ChartedSpace H (X.obj (L.φ k)).M := (X.obj (L.φ k)).charted
      letI : IsManifold I ∞ (X.obj (L.φ k)).M := (X.obj (L.φ k)).smooth
      letI : T2Space (TangentBundle I (X.obj (L.φ k)).M) :=
        (X.obj (L.φ k)).t2TangentBundle
      Set.MapsTo
        (fun z => expMapDiffeo (I := I) (X.obj (L.φ k)).metric (beta k) z)
        U
        ((fun v : E => (expMap (I := I) (X.obj (L.φ k)).metric
            (seqCenterD hd P L k (gamma.1 : Nat))
            (show TangentSpace I (seqCenterD hd P L k (gamma.1 : Nat)) from v) :
              (X.obj (L.φ k)).M)) ''
          Metric.ball (0 : E)
            (min transInput.r₁ (expMapC2Radius (I := I) (X.obj (L.φ k)).metric
              (seqCenterD hd P L k (gamma.1 : Nat)))))) :
    exists (psi : Nat -> Nat)
        (gInf : E -> (LiveSlot L pb r -> (E →L[Real] E →L[Real] Real)))
        (Jinf : LiveSlot L pb r -> E -> E),
      StrictMono psi ∧
      ContDiffOn Real (∞ : WithTop ℕ∞) gInf Set.univ ∧
      MapCInfConvOnCompacts Set.univ
        (fun k _ gamma => normalCoordMetric (I := I) (X.obj (L.φ (psi k)))
          (seqCenterD hd P L (psi k) (gamma.1 : Nat)) 0) gInf ∧
      forall gamma : LiveSlot L pb r,
        ContDiffOn Real (∞ : WithTop ℕ∞) (Jinf gamma) U ∧
        MapCInfConvOnCompacts U
          (fun k => normalTransition (I := I) (X.obj (L.φ (psi k)))
            (beta (psi k)) (seqCenterD hd P L (psi k) (gamma.1 : Nat)))
          (Jinf gamma) ∧
        (forall k, ContDiffOn Real (∞ : WithTop ℕ∞)
          (normalTransition (I := I) (X.obj (L.φ (psi k)))
            (beta (psi k)) (seqCenterD hd P L (psi k) (gamma.1 : Nat))) U) ∧
        (forall k, NormalOverlapOn (I := I) (X.obj (L.φ (psi k)))
          (beta (psi k)) (seqCenterD hd P L (psi k) (gamma.1 : Nat)) U) ∧
        (forall k, seqCenter hd D P (L.φ (psi k)) (gamma.1 : Nat) =
          some (seqCenterD hd P L (psi k) (gamma.1 : Nat))) := by
  classical
  obtain ⟨psi1, gInf, hpsi1, hginf, hg⟩ :=
    existsLiveMetric0 (I := I) metricInput P L pb r
  have htail : ∀ᶠ k in Filter.atTop, forall gamma : LiveSlot L pb r,
      NormalOverlapOn (I := I) (X.obj (L.φ (psi1 k))) (beta (psi1 k))
          (seqCenterD hd P L (psi1 k) (gamma.1 : Nat)) U ∧
        (letI : TopologicalSpace (X.obj (L.φ (psi1 k))).M :=
            (X.obj (L.φ (psi1 k))).topology
         letI : ChartedSpace H (X.obj (L.φ (psi1 k))).M :=
            (X.obj (L.φ (psi1 k))).charted
         letI : IsManifold I ∞ (X.obj (L.φ (psi1 k))).M :=
            (X.obj (L.φ (psi1 k))).smooth
         letI : T2Space (TangentBundle I (X.obj (L.φ (psi1 k))).M) :=
            (X.obj (L.φ (psi1 k))).t2TangentBundle
         U ⊆ Metric.ball (0 : E)
            (min transInput.r₁ (expMapC2Radius (I := I)
              (X.obj (L.φ (psi1 k))).metric (beta (psi1 k))))) ∧
        (letI : TopologicalSpace (X.obj (L.φ (psi1 k))).M :=
            (X.obj (L.φ (psi1 k))).topology
         letI : ChartedSpace H (X.obj (L.φ (psi1 k))).M :=
            (X.obj (L.φ (psi1 k))).charted
         letI : IsManifold I ∞ (X.obj (L.φ (psi1 k))).M :=
            (X.obj (L.φ (psi1 k))).smooth
         letI : T2Space (TangentBundle I (X.obj (L.φ (psi1 k))).M) :=
            (X.obj (L.φ (psi1 k))).t2TangentBundle
         Set.MapsTo
            (fun z => expMapDiffeo (I := I) (X.obj (L.φ (psi1 k))).metric
              (beta (psi1 k)) z) U
            ((fun v : E => (expMap (I := I) (X.obj (L.φ (psi1 k))).metric
                (seqCenterD hd P L (psi1 k) (gamma.1 : Nat))
                (show TangentSpace I
                  (seqCenterD hd P L (psi1 k) (gamma.1 : Nat)) from v) :
                    (X.obj (L.φ (psi1 k))).M)) ''
              Metric.ball (0 : E)
                (min transInput.r₁ (expMapC2Radius (I := I)
                  (X.obj (L.φ (psi1 k))).metric
                  (seqCenterD hd P L (psi1 k) (gamma.1 : Nat)))))) ∧
        seqCenter hd D P (L.φ (psi1 k)) (gamma.1 : Nat) =
          some (seqCenterD hd P L (psi1 k) (gamma.1 : Nat)) := by
    filter_upwards
      [Filter.eventually_all.mpr (fun gamma =>
          hpsi1.tendsto_atTop.eventually (hovlJ gamma)),
        hpsi1.tendsto_atTop.eventually hUx,
        Filter.eventually_all.mpr (fun gamma =>
          hpsi1.tendsto_atTop.eventually (hmapsJ gamma)),
        Filter.eventually_all.mpr (fun gamma : LiveSlot L pb r =>
          hpsi1.tendsto_atTop.eventually
            (seqCenterD_live hd P L (gamma.1 : Nat) gamma.2))]
      with k hkOvl hkUx hkMaps hkLive
    exact fun gamma => ⟨hkOvl gamma, hkUx, hkMaps gamma, hkLive gamma⟩
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp htail
  let tau : Nat -> Nat := fun k => k + N
  have htau : StrictMono tau := by
    simpa only [tau] using strictMono_id.add_const N
  have hgeom (k : Nat) (gamma : LiveSlot L pb r) :=
    hN (tau k) (by simpa only [tau] using Nat.le_add_left N k) gamma
  let J : Nat -> E -> (LiveSlot L pb r -> E) := fun k z gamma =>
    normalTransition (I := I) (X.obj (L.φ (psi1 (tau k))))
      (beta (psi1 (tau k)))
      (seqCenterD hd P L (psi1 (tau k)) (gamma.1 : Nat)) z
  have hsmooth : forall k, ContDiffOn Real (∞ : WithTop ℕ∞) (J k) U := by
    intro k
    refine contDiffOn_pi.mpr fun gamma => ?_
    exact contDiffOn_normalTransition (I := I) (X.obj (L.φ (psi1 (tau k))))
      (beta (psi1 (tau k)))
      (seqCenterD hd P L (psi1 (tau k)) (gamma.1 : Nat))
      ((hgeom k gamma).2.1.trans
        (Metric.ball_subset_ball (min_le_right _ _)))
      ((hgeom k gamma).2.2.1.mono_right
        (Set.image_mono (Metric.ball_subset_ball (min_le_right _ _))))
  have hbdd : IsometryDerivBoundsOn U J := by
    intro order K _hK hKU
    refine ⟨transInput.derivC order, fun k z hz => ?_⟩
    have hle : ((order : ℕ∞) : WithTop ℕ∞) <= (∞ : WithTop ℕ∞) := by
      exact_mod_cast le_top
    have hcd : forall gamma : LiveSlot L pb r,
        ContDiffAt Real ((order : ℕ∞) : WithTop ℕ∞)
          (fun w => normalTransition (I := I) (X.obj (L.φ (psi1 (tau k))))
            (beta (psi1 (tau k)))
            (seqCenterD hd P L (psi1 (tau k)) (gamma.1 : Nat)) w) z :=
      fun gamma => ((contDiffOn_pi.mp (hsmooth k) gamma).contDiffAt
        (hU.mem_nhds (hKU hz))).of_le hle
    dsimp only [J]
    rw [iteratedFDerivPi hcd le_rfl, ContinuousMultilinearMap.opNorm_pi,
      pi_norm_le_iff_of_nonneg (transInput.derivC_nonneg order)]
    intro gamma
    exact transInput.exp_inv_deriv (L.φ (psi1 (tau k))) order
      (beta (psi1 (tau k)))
      (seqCenterD hd P L (psi1 (tau k)) (gamma.1 : Nat)) z
      (mem_ball_zero_iff.mp ((hgeom k gamma).2.1 (hKU hz)))
      ((hgeom k gamma).1 z (hKU hz)).1
      ((hgeom k gamma).2.2.1 (hKU hz))
      ((hgeom k gamma).1 z (hKU hz)).2
  obtain ⟨psi2, Jhat, hpsi2, hJhat, hJconv⟩ :=
    isometry_seq_cInf_on hU J hsmooth hbdd
  refine ⟨psi1 ∘ tau ∘ psi2, gInf, fun gamma z => Jhat z gamma,
    hpsi1.comp (htau.comp hpsi2), hginf, ?_, ?_⟩
  · simpa only [Function.comp_apply] using hg.comp_subseq (htau.comp hpsi2)
  · intro gamma
    refine ⟨contDiffOn_pi.mp hJhat gamma, ?_, ?_, ?_, ?_⟩
    · have hcoord := mapCInf_apply hU hJconv
        (fun k => hsmooth (psi2 k)) hJhat gamma
      simpa only [J, Function.comp_apply] using hcoord
    · intro k
      simpa only [Function.comp_apply] using
        (contDiffOn_pi.mp (hsmooth (psi2 k)) gamma)
    · intro k
      simpa only [Function.comp_apply] using (hgeom (psi2 k) gamma).1
    · intro k
      simpa only [Function.comp_apply] using (hgeom (psi2 k) gamma).2.2.2

end HCGCompactness
end DifferentialGeometry
