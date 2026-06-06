import DifferentialGeometry.Geometry.Flow.RicciFlow.HamiltonDeTurckPullbackFlat
import DifferentialGeometry.Geometry.Flow.RicciFlow.Pullback.Cartan.EvaluationFormChainRule
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.RemainderShortTimeExistence
import DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricRealization.DeTurckGeometricNonlinearity
import DifferentialGeometry.Analysis.Spectral.Intrinsic.Garding.EigenCombination
import DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricRealization.TensorHsRealize
import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.ChartLocalExistence.ChartLocalPicard
import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.ChartLocalExistence.ChartOverlapUniqueness
import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.Regularity.BareFlowFromJointC1
import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.SmoothInSpace.CovariantIdentity.FlatIdentity
import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.SmoothDependence.GlobalClosedManifold
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTimeAssembly.FlatVariationalIdentity

/-!
# Window-glued identification of the bare and conjugating flow families

Identifies, on the interior `(0,T)`, the conjugating diffeomorphism family `Φ_fam` with the
bare flow `Φ` of the same time-dependent field, by a connectedness (clopen) globalisation of
window-local bare-flow uniqueness (`bare_integral_flow_eqOn_of_jointC1`).
-/

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle
open scoped Manifold ContDiff NNReal ENNReal Topology BigOperators
open DifferentialGeometry
open DifferentialGeometry.PDE
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.DeTurck
open DifferentialGeometry.PDE.RicciFlow.ODE
open DifferentialGeometry.PDE.RicciFlow.Pullback
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Parabolic.QuasiLinear

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [BoundarylessManifold I M]
      [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

set_option linter.unusedVariables false in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [SigmaCompactSpace M] in
theorem flow_family_identification
    (g_DT : ℝ → SmoothRiemannianMetric I M) (g₀ : SmoothRiemannianMetric I M)
    (T : ℝ) (Φ_fam : ℝ → (M ≃ₘ⟮I, I⟯ M)) (Φ : ℝ → M → M)
    (X : ℝ → ∀ x : M, TangentSpace I x)
    (hΦfam_ode : ∀ s ∈ Set.Ioo (0 : ℝ) T, ∀ x : M,
      HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun u : ℝ => (Φ_fam u : M → M) x) (Set.Ioo (0 : ℝ) T) s
        ((1 : ℝ →L[ℝ] ℝ).smulRight (X s ((Φ_fam s : M → M) x))))
    (hΦ_ode : ∀ s ∈ Set.Ioo (0 : ℝ) T, ∀ x : M,
      HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun u : ℝ => Φ u x) (Set.Ioo (0 : ℝ) T) s
        ((1 : ℝ →L[ℝ] ℝ).smulRight (X s (Φ s x))))
    (hwin : ∀ s ∈ Set.Ioo (0 : ℝ) T,
      ∃ (a b : ℝ) (Xt : ℝ → ∀ x : M, TangentSpace I x),
        s ∈ Set.Ioo a b ∧ Set.Ioo a b ⊆ Set.Ioo (0 : ℝ) T ∧
          AutonomizedFieldJointC1 (I := I) Xt ∧
          (∀ t ∈ Set.Ioo a b, ∀ x : M, Xt t x = X t x))
    (hstart : ∃ t₀ ∈ Set.Ioo (0 : ℝ) T, ∀ x : M, (Φ_fam t₀ : M → M) x = Φ t₀ x) :
    ∀ s ∈ Set.Ioo (0 : ℝ) T, ∀ x : M, (Φ_fam s : M → M) x = Φ s x := by
  have hwindow : ∀ s ∈ Set.Ioo (0 : ℝ) T, ∀ (a b : ℝ)
      (Xt : ℝ → ∀ x : M, TangentSpace I x),
      Set.Ioo a b ⊆ Set.Ioo (0 : ℝ) T → AutonomizedFieldJointC1 (I := I) Xt →
      (∀ t ∈ Set.Ioo a b, ∀ x : M, Xt t x = X t x) →
      ∀ t₀ ∈ Set.Ioo a b, (∀ x : M, (Φ_fam t₀ : M → M) x = Φ t₀ x) →
      ∀ t ∈ Set.Ioo a b, ∀ x : M, (Φ_fam t : M → M) x = Φ t x := by
    intro s _ a b Xt hsub hXtauto hXteq t₀ ht₀ hagree t ht x
    have hΦfamXt : ∀ r ∈ Set.Ioo a b,
        HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun u : ℝ => (Φ_fam u : M → M) x) (Set.Ioo a b) r
          ((1 : ℝ →L[ℝ] ℝ).smulRight (Xt r ((Φ_fam r : M → M) x))) := by
      intro r hr
      have hode := (hΦfam_ode r (hsub hr) x).mono hsub
      rw [hXteq r hr ((Φ_fam r : M → M) x)]; exact hode
    have hΦXt : ∀ r ∈ Set.Ioo a b,
        HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun u : ℝ => Φ u x) (Set.Ioo a b) r
          ((1 : ℝ →L[ℝ] ℝ).smulRight (Xt r (Φ r x))) := by
      intro r hr
      have hode := (hΦ_ode r (hsub hr) x).mono hsub
      rw [hXteq r hr (Φ r x)]; exact hode
    exact bare_integral_flow_eqOn_of_jointC1 (a := a) (b := b) (t₀ := t₀)
      Xt hXtauto (fun u : ℝ => (Φ_fam u : M → M)) Φ x x ht₀ hΦfamXt hΦXt (hagree x) t ht
  set Agree : ℝ → Prop := fun r => ∀ x : M, (Φ_fam r : M → M) x = Φ r x with hAgree
  set u : Set ℝ := {r : ℝ | ∃ (a b : ℝ) (Xt : ℝ → ∀ x : M, TangentSpace I x),
      r ∈ Set.Ioo a b ∧ Set.Ioo a b ⊆ Set.Ioo (0 : ℝ) T ∧
      AutonomizedFieldJointC1 (I := I) Xt ∧
      (∀ t ∈ Set.Ioo a b, ∀ x : M, Xt t x = X t x) ∧
      (∀ t ∈ Set.Ioo a b, Agree t)} with hu
  set v : Set ℝ := {r : ℝ | ∃ (a b : ℝ) (Xt : ℝ → ∀ x : M, TangentSpace I x),
      r ∈ Set.Ioo a b ∧ Set.Ioo a b ⊆ Set.Ioo (0 : ℝ) T ∧
      AutonomizedFieldJointC1 (I := I) Xt ∧
      (∀ t ∈ Set.Ioo a b, ∀ x : M, Xt t x = X t x) ∧
      (∀ t ∈ Set.Ioo a b, ¬ Agree t)} with hv
  have hu_open : IsOpen u := by
    rw [hu, isOpen_iff_forall_mem_open]
    rintro r ⟨a, b, Xt, hr, hsub, hauto, heq, hall⟩
    exact ⟨Set.Ioo a b, fun r' hr' => ⟨a, b, Xt, hr', hsub, hauto, heq, hall⟩, isOpen_Ioo, hr⟩
  have hv_open : IsOpen v := by
    rw [hv, isOpen_iff_forall_mem_open]
    rintro r ⟨a, b, Xt, hr, hsub, hauto, heq, hall⟩
    exact ⟨Set.Ioo a b, fun r' hr' => ⟨a, b, Xt, hr', hsub, hauto, heq, hall⟩, isOpen_Ioo, hr⟩
  have huv_disj : Disjoint u v := by
    rw [Set.disjoint_left]
    rintro r ⟨a, b, Xt, hr, _, _, _, hall⟩ ⟨a', b', Xt', hr', hsub', hauto', heq', hnall'⟩
    have hAgree_r : Agree r := hall r hr
    exact hnall' r hr'
      (hwindow r (hsub' hr') a' b' Xt' hsub' hauto' heq' r hr' hAgree_r r hr')
  have hcover : Set.Ioo (0 : ℝ) T ⊆ u ∪ v := by
    intro r hr
    obtain ⟨a, b, Xt, hr', hsub, hauto, heq⟩ := hwin r hr
    by_cases hcase : ∀ t ∈ Set.Ioo a b, Agree t
    · exact Or.inl ⟨a, b, Xt, hr', hsub, hauto, heq, hcase⟩
    · right
      refine ⟨a, b, Xt, hr', hsub, hauto, heq, ?_⟩
      intro t ht hAgree_t
      exact hcase fun t' ht' => hwindow r hr a b Xt hsub hauto heq t ht hAgree_t t' ht'
  obtain ⟨t₀, ht₀, hagree0⟩ := hstart
  have ht₀u : t₀ ∈ u := by
    obtain ⟨a, b, Xt, hr', hsub, hauto, heq⟩ := hwin t₀ ht₀
    exact ⟨a, b, Xt, hr', hsub, hauto, heq,
      fun t ht => hwindow t₀ ht₀ a b Xt hsub hauto heq t₀ hr' hagree0 t ht⟩
  have hsubu : Set.Ioo (0 : ℝ) T ⊆ u :=
    (isPreconnected_Ioo).subset_left_of_subset_union hu_open hv_open huv_disj hcover
      ⟨t₀, ht₀, ht₀u⟩
  intro s hs x
  obtain ⟨a, b, Xt, hr', _, _, _, hall⟩ := hsubu hs
  exact hall s hr' x

end DifferentialGeometry.PDE.RicciFlow
