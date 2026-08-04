import DifferentialGeometry.Analysis.Schauder.Holder
import Mathlib.Analysis.Calculus.UniformLimitsDeriv

noncomputable section

open Filter Set
open scoped Topology

namespace DifferentialGeometry.Analysis.Schauder

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace Real E]
  [NormedAddCommGroup F] [NormedSpace Real F]

def ParabolicJetRealizesOn
    (Q : Set (ParabolicPoint E))
    (u dtimeU : ParabolicPoint E → F)
    (du : ParabolicPoint E → E →L[Real] F)
    (d2u : ParabolicPoint E → E →L[Real] E →L[Real] F) : Prop :=
  (∀ p ∈ Q, HasDerivAt (fun t ↦ u (parabolicPoint t p.space)) (dtimeU p) p.time) ∧
    (∀ p ∈ Q, HasFDerivAt (fun x ↦ u (parabolicPoint p.time x)) (du p) p.space) ∧
    ∀ p ∈ Q,
      HasFDerivAt (fun x ↦ du (parabolicPoint p.time x)) (d2u p) p.space

namespace ParabolicJetRealizesOn

theorem hasDerivAt_time
    {Q : Set (ParabolicPoint E)}
    {u dtimeU : ParabolicPoint E → F}
    {du : ParabolicPoint E → E →L[Real] F}
    {d2u : ParabolicPoint E → E →L[Real] E →L[Real] F}
    (h : ParabolicJetRealizesOn Q u dtimeU du d2u)
    {p : ParabolicPoint E} (hp : p ∈ Q) :
    HasDerivAt (fun t ↦ u (parabolicPoint t p.space)) (dtimeU p) p.time :=
  h.1 p hp

theorem hasFDerivAt_space
    {Q : Set (ParabolicPoint E)}
    {u dtimeU : ParabolicPoint E → F}
    {du : ParabolicPoint E → E →L[Real] F}
    {d2u : ParabolicPoint E → E →L[Real] E →L[Real] F}
    (h : ParabolicJetRealizesOn Q u dtimeU du d2u)
    {p : ParabolicPoint E} (hp : p ∈ Q) :
    HasFDerivAt (fun x ↦ u (parabolicPoint p.time x)) (du p) p.space :=
  h.2.1 p hp

theorem hasFDerivAt_gradient
    {Q : Set (ParabolicPoint E)}
    {u dtimeU : ParabolicPoint E → F}
    {du : ParabolicPoint E → E →L[Real] F}
    {d2u : ParabolicPoint E → E →L[Real] E →L[Real] F}
    (h : ParabolicJetRealizesOn Q u dtimeU du d2u)
    {p : ParabolicPoint E} (hp : p ∈ Q) :
    HasFDerivAt (fun x ↦ du (parabolicPoint p.time x)) (d2u p) p.space :=
  h.2.2 p hp

end ParabolicJetRealizesOn

theorem parabolic_jet_realizes_on_of_tendsto_locally_uniformly_on
    {ι : Type*} {l : Filter ι} [NeBot l]
    {Q : Set (ParabolicPoint E)} (hQ : IsOpen Q)
    {uApprox dtimeUApprox : ι → ParabolicPoint E → F}
    {duApprox : ι → ParabolicPoint E → E →L[Real] F}
    {d2uApprox : ι → ParabolicPoint E → E →L[Real] E →L[Real] F}
    {u dtimeU : ParabolicPoint E → F}
    {du : ParabolicPoint E → E →L[Real] F}
    {d2u : ParabolicPoint E → E →L[Real] E →L[Real] F}
    (hu : TendstoLocallyUniformlyOn uApprox u l Q)
    (hdtimeU : TendstoLocallyUniformlyOn dtimeUApprox dtimeU l Q)
    (hdu : TendstoLocallyUniformlyOn duApprox du l Q)
    (hd2u : TendstoLocallyUniformlyOn d2uApprox d2u l Q)
    (hrealize : ∀ i, ParabolicJetRealizesOn Q
      (uApprox i) (dtimeUApprox i) (duApprox i) (d2uApprox i)) :
    ParabolicJetRealizesOn Q u dtimeU du d2u := by
  refine ⟨?_, ?_, ?_⟩
  · intro p hp
    let timeSlice : Real → ParabolicPoint E := fun t ↦ parabolicPoint t p.space
    let timeDomain : Set Real := timeSlice ⁻¹' Q
    have htimeSlice : Continuous timeSlice := by
      simpa only [timeSlice, parabolicPoint] using
        Metric.Snowflaking.continuous_toSnowflaking.prodMk
          (continuous_const : Continuous (fun _ : Real ↦ p.space))
    have htimeDomain : IsOpen timeDomain := hQ.preimage htimeSlice
    have hpTime : p.time ∈ timeDomain := by
      change parabolicPoint p.time p.space ∈ Q
      simpa only [parabolicPoint_time_space] using hp
    have huTime := hu.comp timeSlice (fun _ h ↦ h) htimeSlice.continuousOn
    have hdtimeUTime :=
      hdtimeU.comp timeSlice (fun _ h ↦ h) htimeSlice.continuousOn
    have hderiv := hasDerivAt_of_tendstoLocallyUniformlyOn htimeDomain
      hdtimeUTime (Eventually.of_forall fun i t ht ↦ by
        have h := (hrealize i).hasDerivAt_time ht
        simpa only [timeSlice, parabolicPoint_space, parabolicPoint_time] using h)
      (fun t ht ↦ huTime.tendsto_at ht) hpTime
    simpa only [timeSlice, Function.comp_apply, parabolicPoint_time_space] using hderiv
  · intro p hp
    let spaceSlice : E → ParabolicPoint E := fun x ↦ parabolicPoint p.time x
    let spaceDomain : Set E := spaceSlice ⁻¹' Q
    have hspaceSlice : Continuous spaceSlice := by
      simpa only [spaceSlice, parabolicPoint] using
        (continuous_const : Continuous
          (fun _ : E ↦ Metric.Snowflaking.toSnowflaking p.time)).prodMk continuous_id
    have hspaceDomain : IsOpen spaceDomain := hQ.preimage hspaceSlice
    have hpSpace : p.space ∈ spaceDomain := by
      change parabolicPoint p.time p.space ∈ Q
      simpa only [parabolicPoint_time_space] using hp
    have huSpace := hu.comp spaceSlice (fun _ h ↦ h) hspaceSlice.continuousOn
    have hduSpace := hdu.comp spaceSlice (fun _ h ↦ h) hspaceSlice.continuousOn
    have hderiv := hasFDerivAt_of_tendstoLocallyUniformlyOn hspaceDomain
      hduSpace (fun i x hx ↦ by
        have h := (hrealize i).hasFDerivAt_space hx
        simpa only [spaceSlice, parabolicPoint_space, parabolicPoint_time] using h)
      (fun x hx ↦ huSpace.tendsto_at hx) hpSpace
    simpa only [spaceSlice, Function.comp_apply, parabolicPoint_time_space] using hderiv
  · intro p hp
    let spaceSlice : E → ParabolicPoint E := fun x ↦ parabolicPoint p.time x
    let spaceDomain : Set E := spaceSlice ⁻¹' Q
    have hspaceSlice : Continuous spaceSlice := by
      simpa only [spaceSlice, parabolicPoint] using
        (continuous_const : Continuous
          (fun _ : E ↦ Metric.Snowflaking.toSnowflaking p.time)).prodMk continuous_id
    have hspaceDomain : IsOpen spaceDomain := hQ.preimage hspaceSlice
    have hpSpace : p.space ∈ spaceDomain := by
      change parabolicPoint p.time p.space ∈ Q
      simpa only [parabolicPoint_time_space] using hp
    have hduSpace := hdu.comp spaceSlice (fun _ h ↦ h) hspaceSlice.continuousOn
    have hd2uSpace := hd2u.comp spaceSlice (fun _ h ↦ h) hspaceSlice.continuousOn
    have hderiv := hasFDerivAt_of_tendstoLocallyUniformlyOn hspaceDomain
      hd2uSpace (fun i x hx ↦ by
        have h := (hrealize i).hasFDerivAt_gradient hx
        simpa only [spaceSlice, parabolicPoint_space, parabolicPoint_time] using h)
      (fun x hx ↦ hduSpace.tendsto_at hx) hpSpace
    simpa only [spaceSlice, Function.comp_apply, parabolicPoint_time_space] using hderiv

end DifferentialGeometry.Analysis.Schauder

end
