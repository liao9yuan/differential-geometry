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

noncomputable def levelSetCollarHomeomorph {n : ℕ} {H : Type} [TopologicalSpace H] {M : Type}
    [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
    (I : ModelWithCorners ℝ (MorseModel n) H) [I.Boundaryless]
    [IsManifold I (⊤ : WithTop ℕ∞) M] (f : M → ℝ)
    (hf : ContMDiff I 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞) f) {a b : ℝ}
    (v : (x : M) → TangentSpace I x)
    (hv : ContMDiff I (I.prod 𝓘(ℝ, MorseModel n)) ∞
      (fun x : M => (⟨x, v x⟩ : TangentBundle I M)))
    (hsupp : IsCompact (tsupport v))
    (hdfOn : ∀ x ∈ f ⁻¹' Set.Icc a b,
      (NormedSpace.fromTangentSpace (f x)) ((mfderiv I 𝓘(ℝ, ℝ) f x) (v x)) = -1)
    (hrate : ∀ x,
      -1 ≤ (NormedSpace.fromTangentSpace (f x)) ((mfderiv I 𝓘(ℝ, ℝ) f x) (v x)) ∧
      (NormedSpace.fromTangentSpace (f x)) ((mfderiv I 𝓘(ℝ, ℝ) f x) (v x)) ≤ 0) :
    (f ⁻¹' {a}) × Set.Icc (0 : ℝ) (b - a) ≃ₜ
      {x : M // x ∈ sublevel f b ∧ a ≤ f x} := by
  let hcomplete : ∀ x : M, ∃ γ : ℝ → M, γ 0 = x ∧ IsMIntegralCurve γ v :=
    exists_globalIntegralCurve_of_compactSupport v hv hsupp
  have hv1 : ContMDiff I (I.prod 𝓘(ℝ, MorseModel n)) (1 : WithTop ℕ∞)
      (fun x : M => (⟨x, v x⟩ : TangentBundle I M)) :=
    hv.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ ∞)
  have hfval : ∀ x : M, f x = a → ∀ t ∈ Set.Icc (0 : ℝ) (b - a),
      f (curveAt v hcomplete x (-t)) = a + t := by
    intro x hx t ht
    have hγ : IsMIntegralCurve (fun s : ℝ => curveAt v hcomplete x (-s)) (-v) := by
      have hc := IsMIntegralCurve.comp_mul (curveAt_integralCurve v hcomplete x) (-1)
      simpa [Pi.smul_apply] using hc
    have hdneg : ∀ y : M,
        (NormedSpace.fromTangentSpace (-f y)) ((mfderiv I 𝓘(ℝ, ℝ) (-f) y) ((-v) y)) =
          (NormedSpace.fromTangentSpace (f y)) ((mfderiv I 𝓘(ℝ, ℝ) f y) (v y)) := by
      intro y
      simp [NormedSpace.fromTangentSpace, mfderiv_neg]
      exact neg_neg ((mfderiv I 𝓘(ℝ, ℝ) f y) (v y))
    have hdfneg : ∀ y ∈ (-f) ⁻¹' Set.Icc (-b) (-a),
        (NormedSpace.fromTangentSpace (-f y)) ((mfderiv I 𝓘(ℝ, ℝ) (-f) y) ((-v) y)) = -1 := by
      intro y hy
      rw [hdneg y]
      apply hdfOn
      change a ≤ f y ∧ f y ≤ b
      have h1 : a ≤ f y := (neg_le_neg_iff.mp hy.2)
      have h2 : f y ≤ b := (neg_le_neg_iff.mp hy.1)
      exact ⟨h1, h2⟩
    have hrateneg : ∀ y : M,
        -1 ≤ (NormedSpace.fromTangentSpace (-f y)) ((mfderiv I 𝓘(ℝ, ℝ) (-f) y) ((-v) y)) ∧
          (NormedSpace.fromTangentSpace (-f y)) ((mfderiv I 𝓘(ℝ, ℝ) (-f) y) ((-v) y)) ≤ 0 := by
      intro y
      rw [hdneg y]
      exact hrate y
    have hstay : ∀ s ∈ Set.Icc (0 : ℝ) t, curveAt v hcomplete x (-s) ∈ f ⁻¹' Set.Icc a b := by
      intro s hs
      have hrb := f_rate_bounds_of_integralCurve (-f) hf.neg (-v) hrateneg (hγ := hγ) (t := s) hs.1
      have hxval : f (curveAt v hcomplete x (-0)) = a := by
        simpa [curveAt_zero v hcomplete x] using hx
      constructor
      · have hb : -f (curveAt v hcomplete x (-s)) ≤ -f (curveAt v hcomplete x (-0)) := hrb.2
        have hb' : -f (curveAt v hcomplete x (-s)) ≤ -a := by
          rw [← hxval]
          exact hb
        exact (neg_le_neg_iff.mp hb')
      · have hb : -f (curveAt v hcomplete x (-0)) - s ≤ -f (curveAt v hcomplete x (-s)) := hrb.1
        have hb' : -a - s ≤ -f (curveAt v hcomplete x (-s)) := by
          rw [← hxval]
          exact hb
        have hle : f (curveAt v hcomplete x (-s)) ≤ a + s := by linarith
        exact le_trans hle (by linarith [hs.2, ht.2])
    have hstay' : ∀ s ∈ Set.Icc (0 : ℝ) t, curveAt v hcomplete x (-s) ∈ (-f) ⁻¹' Set.Icc (-b) (-a) := by
      intro s hs
      have hmem := hstay s hs
      change -b ≤ -f (curveAt v hcomplete x (-s)) ∧ -f (curveAt v hcomplete x (-s)) ≤ -a
      exact ⟨neg_le_neg hmem.2, neg_le_neg_iff.mpr hmem.1⟩
    have heq := f_eq_sub_of_integralCurve_on_strip (a := -b) (b := -a) (-f) hf.neg (-v) hdfneg
      (hγ := hγ) (t := t) ht.1 hstay'
    have hmain : -f (curveAt v hcomplete x (-t)) = -f (curveAt v hcomplete x (-0)) - t := heq
    have hxval : f (curveAt v hcomplete x (-0)) = a := by
      simpa [curveAt_zero v hcomplete x] using hx
    have hneg : -f (curveAt v hcomplete x (-t)) = -a - t := by
      rw [hxval] at hmain
      exact hmain
    linarith
  let toCollar : (f ⁻¹' {a}) × Set.Icc (0 : ℝ) (b - a) → {x : M // x ∈ sublevel f b ∧ a ≤ f x} :=
    fun p => ⟨curveAt v hcomplete p.1.1 (-(p.2 : ℝ)), by
      have hfval' := hfval p.1.1 p.1.2 (p.2 : ℝ) ⟨p.2.2.1, p.2.2.2⟩
      have hval : f (curveAt v hcomplete p.1.1 (-(p.2 : ℝ))) = a + (p.2 : ℝ) := hfval'
      have ht0 : 0 ≤ (p.2 : ℝ) := p.2.2.1
      have ht1 : (p.2 : ℝ) ≤ b - a := p.2.2.2
      constructor
      · simpa [sublevel] using (show f (curveAt v hcomplete p.1.1 (-(p.2 : ℝ))) ≤ b by
          linarith [hval, ht1])
      · linarith [hval, ht0]⟩
  let fromCollar : {x : M // x ∈ sublevel f b ∧ a ≤ f x} →
      (f ⁻¹' {a}) × Set.Icc (0 : ℝ) (b - a) :=
    fun z => ⟨⟨curveAt v hcomplete z.1 (f z.1 - a), by
      have hmem : z.1 ∈ f ⁻¹' Set.Icc a b := by
        change a ≤ f z.1 ∧ f z.1 ≤ b
        exact ⟨z.2.2, z.2.1⟩
      have hstay : ∀ s ∈ Set.Icc (0 : ℝ) (f z.1 - a), curveAt v hcomplete z.1 s ∈ f ⁻¹' Set.Icc a b := by
        intro s hs
        have hrb := f_rate_bounds_of_integralCurve f hf v hrate
          (hγ := curveAt_integralCurve v hcomplete z.1) (t := s) hs.1
        constructor
        · change a ≤ f (curveAt v hcomplete z.1 s)
          have hle : a ≤ f z.1 - s := by linarith [hs.2]
          exact le_trans hle (by simpa [curveAt_zero v hcomplete z.1] using hrb.1)
        · change f (curveAt v hcomplete z.1 s) ≤ b
          exact le_trans hrb.2 (by simpa [curveAt_zero v hcomplete z.1] using z.2.1)
      have heq := f_eq_sub_of_integralCurve_on_strip (a := a) (b := b) f hf v hdfOn
        (hγ := curveAt_integralCurve v hcomplete z.1) (t := f z.1 - a) (by linarith [z.2.2]) hstay
      have hmain : f (curveAt v hcomplete z.1 (f z.1 - a)) = f z.1 - (f z.1 - a) := by
        simpa [curveAt_zero v hcomplete z.1] using heq
      simp [hmain]⟩, ⟨f z.1 - a, by
        constructor
        · exact sub_nonneg.mpr z.2.2
        · exact sub_le_sub_right z.2.1 a⟩⟩
  refine
    { toFun := toCollar
      invFun := fromCollar
      left_inv := by
        intro p
        apply Prod.ext
        · apply Subtype.ext
          change curveAt v hcomplete (curveAt v hcomplete p.1.1 (-(p.2 : ℝ))) (f (curveAt v hcomplete p.1.1 (-(p.2 : ℝ))) - a) =
            p.1.1
          have hfval' := hfval p.1.1 p.1.2 (p.2 : ℝ) ⟨p.2.2.1, p.2.2.2⟩
          have hval : f (curveAt v hcomplete p.1.1 (-(p.2 : ℝ))) = a + (p.2 : ℝ) := hfval'
          rw [hval]
          have hh := curveAt_add v hv1 hcomplete p.1.1 (-(p.2 : ℝ)) (p.2 : ℝ)
          have hz : -(p.2 : ℝ) + (p.2 : ℝ) = 0 := by ring
          rw [hz] at hh
          simpa [curveAt_zero v hcomplete p.1.1] using hh.symm
        · apply Subtype.ext
          change f (curveAt v hcomplete p.1.1 (-(p.2 : ℝ))) - a = (p.2 : ℝ)
          have hfval' := hfval p.1.1 p.1.2 (p.2 : ℝ) ⟨p.2.2.1, p.2.2.2⟩
          linarith
      right_inv := by
        intro z
        apply Subtype.ext
        change curveAt v hcomplete (curveAt v hcomplete z.1 (f z.1 - a)) (-(f z.1 - a)) = z.1
        have hh := curveAt_add v hv1 hcomplete z.1 (f z.1 - a) (-(f z.1 - a))
        have hz : (f z.1 - a) + (-(f z.1 - a)) = 0 := by ring
        rw [hz] at hh
        simpa [curveAt_zero v hcomplete z.1] using hh.symm
      continuous_toFun := by
        have hjoint := contMDiff_globalFlow_joint_of_compactSupport v hv hsupp
        have hjointc : Continuous (fun p : ℝ × M =>
            curveAt v hcomplete p.2 p.1) := hjoint.continuous
        have hpair : Continuous (fun p : (f ⁻¹' {a}) × Set.Icc (0 : ℝ) (b - a) =>
            (-(p.2 : ℝ), p.1.1)) := by
          fun_prop
        have hmain : Continuous (fun p : (f ⁻¹' {a}) × Set.Icc (0 : ℝ) (b - a) =>
            curveAt v hcomplete p.1.1 (-(p.2 : ℝ))) :=
          hjointc.comp hpair
        exact Continuous.subtype_mk hmain (by
          intro p
          have hfval' := hfval p.1.1 p.1.2 (p.2 : ℝ) ⟨p.2.2.1, p.2.2.2⟩
          have hval : f (curveAt v hcomplete p.1.1 (-(p.2 : ℝ))) = a + (p.2 : ℝ) := hfval'
          have ht0 : 0 ≤ (p.2 : ℝ) := p.2.2.1
          have ht1 : (p.2 : ℝ) ≤ b - a := p.2.2.2
          constructor
          · simpa [sublevel] using (show f (curveAt v hcomplete p.1.1 (-(p.2 : ℝ))) ≤ b by
              linarith [hval, ht1])
          · linarith [hval, ht0])
      continuous_invFun := by
        have hjoint := contMDiff_globalFlow_joint_of_compactSupport v hv hsupp
        have hjointc : Continuous (fun p : ℝ × M =>
            curveAt v hcomplete p.2 p.1) := hjoint.continuous
        have hpair : Continuous (fun z : {x : M // x ∈ sublevel f b ∧ a ≤ f x} =>
            (f z.1 - a, z.1)) := by
          exact ((hf.continuous.comp continuous_subtype_val).sub continuous_const).prodMk continuous_subtype_val
        have hmain : Continuous (fun z : {x : M // x ∈ sublevel f b ∧ a ≤ f x} =>
            curveAt v hcomplete z.1 (f z.1 - a)) :=
          hjointc.comp hpair
        have hfst : Continuous (fun z : {x : M // x ∈ sublevel f b ∧ a ≤ f x} => f z.1 - a) := by
          exact (hf.continuous.comp continuous_subtype_val).sub continuous_const
        have htime : Continuous (fun z : {x : M // x ∈ sublevel f b ∧ a ≤ f x} =>
            (⟨f z.1 - a, by
              constructor
              · exact sub_nonneg.mpr z.2.2
              · exact sub_le_sub_right z.2.1 a⟩ : Set.Icc (0 : ℝ) (b - a))) := by
          exact Continuous.subtype_mk hfst (by
            intro z
            constructor
            · exact sub_nonneg.mpr z.2.2
            · exact sub_le_sub_right z.2.1 a)
        have hsrc : Continuous (fun z : {x : M // x ∈ sublevel f b ∧ a ≤ f x} =>
            (⟨curveAt v hcomplete z.1 (f z.1 - a), by
              have hmem : z.1 ∈ f ⁻¹' Set.Icc a b := by
                change a ≤ f z.1 ∧ f z.1 ≤ b
                exact ⟨z.2.2, z.2.1⟩
              have hstay : ∀ s ∈ Set.Icc (0 : ℝ) (f z.1 - a), curveAt v hcomplete z.1 s ∈ f ⁻¹' Set.Icc a b := by
                intro s hs
                have hrb := f_rate_bounds_of_integralCurve f hf v hrate
                  (hγ := curveAt_integralCurve v hcomplete z.1) (t := s) hs.1
                constructor
                · change a ≤ f (curveAt v hcomplete z.1 s)
                  have hle : a ≤ f z.1 - s := by linarith [hs.2]
                  exact le_trans hle (by simpa [curveAt_zero v hcomplete z.1] using hrb.1)
                · change f (curveAt v hcomplete z.1 s) ≤ b
                  exact le_trans hrb.2 (by simpa [curveAt_zero v hcomplete z.1] using z.2.1)
              have heq := f_eq_sub_of_integralCurve_on_strip (a := a) (b := b) f hf v hdfOn
                (hγ := curveAt_integralCurve v hcomplete z.1) (t := f z.1 - a) (by linarith [z.2.2]) hstay
              have hmain' : f (curveAt v hcomplete z.1 (f z.1 - a)) = f z.1 - (f z.1 - a) := by
                simpa [curveAt_zero v hcomplete z.1] using heq
              simp [hmain']⟩ : f ⁻¹' {a})) := by
          exact Continuous.subtype_mk hmain (by
            intro z
            have hmem : z.1 ∈ f ⁻¹' Set.Icc a b := by
              change a ≤ f z.1 ∧ f z.1 ≤ b
              exact ⟨z.2.2, z.2.1⟩
            have hstay : ∀ s ∈ Set.Icc (0 : ℝ) (f z.1 - a), curveAt v hcomplete z.1 s ∈ f ⁻¹' Set.Icc a b := by
              intro s hs
              have hrb := f_rate_bounds_of_integralCurve f hf v hrate
                (hγ := curveAt_integralCurve v hcomplete z.1) (t := s) hs.1
              constructor
              · change a ≤ f (curveAt v hcomplete z.1 s)
                have hle : a ≤ f z.1 - s := by linarith [hs.2]
                exact le_trans hle (by simpa [curveAt_zero v hcomplete z.1] using hrb.1)
              · change f (curveAt v hcomplete z.1 s) ≤ b
                exact le_trans hrb.2 (by simpa [curveAt_zero v hcomplete z.1] using z.2.1)
            have heq := f_eq_sub_of_integralCurve_on_strip (a := a) (b := b) f hf v hdfOn
              (hγ := curveAt_integralCurve v hcomplete z.1) (t := f z.1 - a) (by linarith [z.2.2]) hstay
            have hmain' : f (curveAt v hcomplete z.1 (f z.1 - a)) = f z.1 - (f z.1 - a) := by
              simpa [curveAt_zero v hcomplete z.1] using heq
            simp [hmain'])
        exact hsrc.prodMk htime }

end

end DifferentialGeometry.Topology.Morse
