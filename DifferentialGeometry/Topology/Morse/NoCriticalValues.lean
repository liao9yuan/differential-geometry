import DifferentialGeometry.Topology.Morse.RegularVectorField
import DifferentialGeometry.Topology.Morse.Flow
import DifferentialGeometry.Analysis.ODE.CompactSupportFlow
import Mathlib.Geometry.Manifold.Diffeomorph

namespace DifferentialGeometry.Topology.Morse

open Manifold Set
open scoped Manifold ContDiff
open DifferentialGeometry.Analysis.ODE

noncomputable section

variable {n : ℕ} {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M]
variable {I : ModelWithCorners ℝ (MorseModel n) H}

theorem no_critical_value_transport [I.Boundaryless] [IsManifold I (⊤ : WithTop ℕ∞) M]
    [T2Space M] [SigmaCompactSpace M]
    (f : M → ℝ) (hf : ContMDiff I 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞) f) {a b : ℝ} (hab : a ≤ b)
    (hcompact : IsCompact (f ⁻¹' Set.Icc a b))
    (hregular : ∀ x ∈ f ⁻¹' Set.Icc a b, ¬ IsCriticalPointAt I f x) :
    ∃ v : (x : M) → TangentSpace I x,
    ∃ Φ : Diffeomorph I I M M ∞,
        ContMDiff I (I.prod 𝓘(ℝ, MorseModel n)) ∞
          (fun x : M => (⟨x, v x⟩ : TangentBundle I M)) ∧
        IsCompact (tsupport v) ∧
        (∀ x ∈ f ⁻¹' Set.Icc a b,
          (NormedSpace.fromTangentSpace (f x)) ((mfderiv I 𝓘(ℝ, ℝ) f x) (v x)) = -1) ∧
        (∀ x,
          -1 ≤ (NormedSpace.fromTangentSpace (f x)) ((mfderiv I 𝓘(ℝ, ℝ) f x) (v x)) ∧
          (NormedSpace.fromTangentSpace (f x)) ((mfderiv I 𝓘(ℝ, ℝ) f x) (v x)) ≤ 0) ∧
        (∃ hcomplete : ∀ x : M, ∃ γ : ℝ → M, γ 0 = x ∧ IsMIntegralCurve γ v,
          (Φ.toEquiv '' sublevel f a) = sublevel f b ∧
          ∀ x : M, Φ.toEquiv x = curveAt v hcomplete x (a - b)) := by
  rcases exists_unitSpeedVectorField_on_strip I f hf a b hcompact hregular with
    ⟨v, hv, hsupp, hdfOn, hrate⟩
  have hcomplete := exists_globalIntegralCurve_of_compactSupport v hv hsupp
  have hv1 : ContMDiff I (I.prod 𝓘(ℝ, MorseModel n)) (1 : WithTop ℕ∞)
      (fun x : M => (⟨x, v x⟩ : TangentBundle I M)) :=
    hv.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ ∞)
  have htransport := sublevel_transport_of_stripUnitSpeedVectorField (I := I) f hf hab v hv1
    hdfOn hrate hcomplete
  let flow : ℝ → M → M := fun t x => curveAt v hcomplete x t
  have hflowSmooth : ∀ t : ℝ, ContMDiff I I ∞ (fun x : M => flow t x) := by
    intro t x
    exact contMDiffAt_globalFlow_of_compactSupport v hv hsupp t x
  have hflow0 : ∀ x : M, flow 0 x = x := fun x => by
    dsimp [flow]
    exact curveAt_zero v hcomplete x
  have hflowAdd : ∀ s t : ℝ, ∀ x : M, flow (s + t) x = flow t (flow s x) := fun s t x => by
    dsimp [flow]
    exact curveAt_add v hv1 hcomplete x s t
  let Φ : Diffeomorph I I M M ∞ :=
    { toEquiv :=
        { toFun := fun x => flow (a - b) x
          invFun := fun x => flow (b - a) x
          left_inv := by
            intro x
            have hh := hflowAdd (a - b) (b - a) x
            calc
              flow (b - a) (flow (a - b) x) = flow ((a - b) + (b - a)) x := hh.symm
              _ = flow 0 x := by rw [show (a - b) + (b - a) = 0 by ring]
              _ = x := hflow0 x
          right_inv := by
            intro x
            have hh := hflowAdd (b - a) (a - b) x
            calc
              flow (a - b) (flow (b - a) x) = flow ((b - a) + (a - b)) x := hh.symm
              _ = flow 0 x := by rw [show (b - a) + (a - b) = 0 by ring]
              _ = x := hflow0 x }
      contMDiff_toFun := hflowSmooth (a - b)
      contMDiff_invFun := hflowSmooth (b - a) }
  refine ⟨v, Φ, hv, hsupp, hdfOn, hrate, hcomplete, ?_, ?_⟩
  · change (fun x : M => flow (a - b) x) '' sublevel f a = sublevel f b
    simpa [flow] using htransport
  · intro x
    rfl

theorem no_critical_values [I.Boundaryless] [IsManifold I (⊤ : WithTop ℕ∞) M]
    [T2Space M] [SigmaCompactSpace M]
    (f : M → ℝ) (hf : ContMDiff I 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞) f) {a b : ℝ} (hab : a ≤ b)
    (hcompact : IsCompact (f ⁻¹' Set.Icc a b))
    (hregular : ∀ x ∈ f ⁻¹' Set.Icc a b, ¬ IsCriticalPointAt I f x) :
    ∃ Φ : Diffeomorph I I M M ∞, Φ.toEquiv '' sublevel f a = sublevel f b := by
  rcases no_critical_value_transport (I := I) f hf hab hcompact hregular with
    ⟨v, Φ, hv, hsupp, hdfOn, hrate, hcomplete, hflow, htie⟩
  exact ⟨Φ, hflow⟩

end

end DifferentialGeometry.Topology.Morse
