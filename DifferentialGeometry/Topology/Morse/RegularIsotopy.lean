import DifferentialGeometry.Topology.Morse.RegularVectorField
import DifferentialGeometry.Topology.Morse.RegularSublevel
import DifferentialGeometry.Analysis.ODE.CompactSupportFlow

namespace DifferentialGeometry.Topology.Morse

open Manifold Set
open scoped Manifold ContDiff Topology

noncomputable section

variable {m : ℕ} {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M]

private theorem familyChartRep_contDiffOn
    {I : ModelWithCorners ℝ (MorseModel (m + 1)) H} [I.Boundaryless]
    [IsManifold I (⊤ : WithTop ℕ∞) M] (F : M → ℝ → ℝ)
    (hF : ContMDiff (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : M × ℝ => F q.1 q.2)) (x₀ : M) :
    ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : MorseModel (m + 1) × ℝ => F ((extChartAt I x₀).symm q.1) q.2)
      ((extChartAt I x₀).target ×ˢ Set.univ) := by
  have hFOn : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : M × ℝ => F q.1 q.2) Set.univ := by
    intro x hx
    exact hF x
  have hc' : ContMDiffOn 𝓘(ℝ, MorseModel (m + 1) × ℝ) 𝓘(ℝ, ℝ)
      (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : MorseModel (m + 1) × ℝ =>
        F ((extChartAt I x₀).symm q.1) q.2)
      ((extChartAt I x₀).target ×ˢ Set.univ) := by
    have hraw := (contMDiffOn_iff_source_of_mem_maximalAtlas
      (I := I.prod 𝓘(ℝ, ℝ)) (I' := 𝓘(ℝ, ℝ))
      (f := fun q : M × ℝ => F q.1 q.2) (n := (↑(⊤ : ℕ∞) : WithTop ℕ∞))
      (e := chartAt (ModelProd H ℝ) (x₀, (0 : ℝ)))
      (IsManifold.chart_mem_maximalAtlas (M := M × ℝ) (x₀, (0 : ℝ)))
      (s := (chartAt H x₀).source ×ˢ Set.univ)
      (hs := by intro x hx; exact ⟨hx.1, trivial⟩)).1
      (hFOn.mono (by intro x hx; trivial))
    convert hraw using 1
    ext q
    constructor
    · rintro ⟨⟨hq1, hq2⟩, hq3⟩
      refine ⟨((chartAt H x₀).symm (I.symm q.1), q.2), ⟨?_, hq3⟩, ?_⟩
      · exact (chartAt H x₀).symm.mapsTo hq2
      · change (I (chartAt H x₀ ((chartAt H x₀).symm (I.symm q.1))), q.2) = q
        apply Prod.ext
        · ext i
          rw [show chartAt H x₀ ((chartAt H x₀).symm (I.symm q.1)) = I.symm q.1 by
            exact (chartAt H x₀).right_inv hq2]
          exact congrFun (I.right_inv (by simpa [ModelWithCorners.target_eq] using hq1)) i
        · rfl
    · rintro ⟨a, ha, hx⟩
      have hx1 : I (chartAt H x₀ a.1) = q.1 := congrArg Prod.fst hx
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · rw [← hx1]
        simp [ModelWithCorners.target_eq]
      · rw [← hx1]
        change I.symm (I (chartAt H x₀ a.1)) ∈ (chartAt H x₀).target
        simpa using (chartAt H x₀).mapsTo ha.1
      · trivial
  exact (contMDiffOn_iff_contDiffOn (𝕜 := ℝ) (E := MorseModel (m + 1) × ℝ) (E' := ℝ)
    (f := fun q : MorseModel (m + 1) × ℝ => F ((extChartAt I x₀).symm q.1) q.2)
    (s := (extChartAt I x₀).target ×ˢ Set.univ) (n := (↑(⊤ : ℕ∞) : WithTop ℕ∞))).1 hc'

private theorem familyChartRep_fderiv_apply_contDiffOn
    {I : ModelWithCorners ℝ (MorseModel (m + 1)) H} [I.Boundaryless]
    [IsManifold I (⊤ : WithTop ℕ∞) M] (F : M → ℝ → ℝ)
    (hF : ContMDiff (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : M × ℝ => F q.1 q.2)) (x₀ : M) (i : Fin (m + 1)) :
    ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : (MorseModel (m + 1)) × ℝ =>
        (fderiv ℝ (fun q' : (MorseModel (m + 1)) × ℝ => F ((extChartAt I x₀).symm q'.1) q'.2) q)
          (ContinuousLinearMap.inl ℝ (MorseModel (m + 1)) ℝ (Pi.single i (1 : ℝ))))
      ((extChartAt I x₀).target ×ˢ Set.univ) := by
  have hgOn := familyChartRep_contDiffOn (I := I) F hF x₀
  have hfderiv : ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (fderiv ℝ (fun q : (MorseModel (m + 1)) × ℝ => F ((extChartAt I x₀).symm q.1) q.2))
      ((extChartAt I x₀).target ×ˢ Set.univ) := by
    exact ((contDiffOn_infty_iff_fderiv_of_isOpen
      (IsOpen.prod (isOpen_extChartAt_target x₀) isOpen_univ)).1 hgOn).2
  exact hfderiv.clm_apply (contDiffOn_const : ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
    (fun _ : (MorseModel (m + 1)) × ℝ =>
      ContinuousLinearMap.inl ℝ (MorseModel (m + 1)) ℝ (Pi.single i (1 : ℝ)))
    ((extChartAt I x₀).target ×ˢ Set.univ))

private theorem familyChartRep_fderiv_curry
    {I : ModelWithCorners ℝ (MorseModel (m + 1)) H} [I.Boundaryless]
    [IsManifold I (⊤ : WithTop ℕ∞) M] (F : M → ℝ → ℝ)
    (hF : ContMDiff (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : M × ℝ => F q.1 q.2)) (x₀ : M) (y : MorseModel (m + 1)) (s : ℝ)
    (hy : y ∈ (extChartAt I x₀).target) :
    fderiv ℝ (fun z : MorseModel (m + 1) => F ((extChartAt I x₀).symm z) s) y =
      (fderiv ℝ (fun q : (MorseModel (m + 1)) × ℝ => F ((extChartAt I x₀).symm q.1) q.2) (y, s)).comp
        (ContinuousLinearMap.inl ℝ (MorseModel (m + 1)) ℝ) := by
  let g : (MorseModel (m + 1)) × ℝ → ℝ := fun q => F ((extChartAt I x₀).symm q.1) q.2
  have hgOn := familyChartRep_contDiffOn (I := I) F hF x₀
  have hmem : (y, s) ∈ (extChartAt I x₀).target ×ˢ Set.univ := ⟨hy, trivial⟩
  have hgdiff : DifferentiableAt ℝ g (y, s) := by
    exact ((hgOn (y, s) hmem).contDiffAt
      ((IsOpen.prod (isOpen_extChartAt_target x₀) isOpen_univ).mem_nhds hmem)).differentiableAt
      (by norm_num : (↑(⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0)
  have hpair : HasFDerivAt (fun z : MorseModel (m + 1) => (z, s))
      (ContinuousLinearMap.inl ℝ (MorseModel (m + 1)) ℝ) y := by
    exact hasFDerivAt_prodMk_left y s
  have hfd : HasFDerivAt (fun z : MorseModel (m + 1) => g (z, s))
      ((fderiv ℝ g (y, s)).comp (ContinuousLinearMap.inl ℝ (MorseModel (m + 1)) ℝ)) y := by
    simpa [g] using (hgdiff.hasFDerivAt.comp y hpair)
  simpa [g] using hfd.fderiv

private theorem familyChartRep_coefficient_contMDiffOn
    {I : ModelWithCorners ℝ (MorseModel (m + 1)) H} [I.Boundaryless]
    [IsManifold I (⊤ : WithTop ℕ∞) M] (F : M → ℝ → ℝ)
    (hF : ContMDiff (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : M × ℝ => F q.1 q.2)) (x₀ : M) (i : Fin (m + 1)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : M × ℝ => (fderiv ℝ (fun q : (MorseModel (m + 1)) × ℝ =>
        F ((extChartAt I x₀).symm q.1) q.2) ((extChartAt I x₀) p.1, p.2))
          (ContinuousLinearMap.inl ℝ (MorseModel (m + 1)) ℝ (Pi.single i (1 : ℝ))))
      ((extChartAt I x₀).source ×ˢ Set.univ) := by
  have ha' : ContMDiffOn 𝓘(ℝ, (MorseModel (m + 1)) × ℝ) 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : (MorseModel (m + 1)) × ℝ =>
        (fderiv ℝ (fun q' : (MorseModel (m + 1)) × ℝ => F ((extChartAt I x₀).symm q'.1) q'.2) q)
          (ContinuousLinearMap.inl ℝ (MorseModel (m + 1)) ℝ (Pi.single i (1 : ℝ))))
      ((extChartAt I x₀).target ×ˢ Set.univ) := by
    exact (contMDiffOn_iff_contDiffOn (𝕜 := ℝ) (E := (MorseModel (m + 1)) × ℝ) (E' := ℝ)
      (f := fun q : (MorseModel (m + 1)) × ℝ =>
        (fderiv ℝ (fun q' : (MorseModel (m + 1)) × ℝ => F ((extChartAt I x₀).symm q'.1) q'.2) q)
          (ContinuousLinearMap.inl ℝ (MorseModel (m + 1)) ℝ (Pi.single i (1 : ℝ))))
      (s := (extChartAt I x₀).target ×ˢ Set.univ) (n := (↑(⊤ : ℕ∞) : WithTop ℕ∞))).2
      (familyChartRep_fderiv_apply_contDiffOn (I := I) F hF x₀ i)
  have hφ : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, (MorseModel (m + 1)) × ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : M × ℝ => ((extChartAt I x₀) p.1, p.2))
      ((extChartAt I x₀).source ×ˢ Set.univ) := by
    have hc := contMDiffOn_extChartAt (I := I.prod 𝓘(ℝ, ℝ)) (n := (↑(⊤ : ℕ∞) : WithTop ℕ∞))
      (x := (x₀, (0 : ℝ)))
    simpa [extChartAt_prod, extChartAt_source (I := I) (x := x₀)] using hc
  exact (ha'.comp hφ (by intro p hp; exact ⟨(extChartAt I x₀).map_source hp.1, trivial⟩)).congr
    (by intro p hp; rfl)

private theorem familyTangentSection_contMDiffWithinAt_section_iff
    {I : ModelWithCorners ℝ (MorseModel (m + 1)) H} [I.Boundaryless]
    [IsManifold I (⊤ : WithTop ℕ∞) M] [T2Space M] [SigmaCompactSpace M]
    {W : (x : M) → (s : ℝ) → TangentSpace I x} {a : Set (M × ℝ)} {p : M × ℝ}
    (ha : a ⊆ (extChartAt I p.1).source ×ˢ Set.univ) :
    ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, MorseModel (m + 1))) (↑(⊤ : ℕ∞) : WithTop ℕ∞)
        (fun q : M × ℝ => (⟨q.1, W q.1 q.2⟩ : TangentBundle I M)) a p ↔
      ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, MorseModel (m + 1)) (↑(⊤ : ℕ∞) : WithTop ℕ∞)
        (fun q : M × ℝ => (trivializationAt (MorseModel (m + 1)) (TangentSpace I) p.1
          ⟨q.1, W q.1 q.2⟩).2) a p := by
  let σ : M × ℝ → TangentBundle I M := fun q => ⟨q.1, W q.1 q.2⟩
  have hσp : (σ p).proj = p.1 := rfl
  have hπ : ContinuousWithinAt (fun q : M × ℝ => (σ q).proj) a p := by
    have hfst : ContinuousWithinAt (fun q : M × ℝ => q.1) a p := continuousWithinAt_fst
    simpa [σ] using hfst
  constructor
  · intro h
    have hcont := h.continuousWithinAt
    have hcont' := (FiberBundle.continuousWithinAt_totalSpace (f := σ) (s := a) (x₀ := p)).1 hcont
    have h2 : ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, (MorseModel (m + 1)) × MorseModel (m + 1))
        (↑(⊤ : ℕ∞) : WithTop ℕ∞)
        (extChartAt (I.prod 𝓘(ℝ, MorseModel (m + 1))) (σ p) ∘ σ) a p :=
      (contMDiffWithinAt_iff_target (I := I.prod 𝓘(ℝ, ℝ)) (I' := I.prod 𝓘(ℝ, MorseModel (m + 1)))
        (f := σ) (s := a) (x := p) (n := (↑(⊤ : ℕ∞) : WithTop ℕ∞))).1 h |>.2
    have h2' : ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, (MorseModel (m + 1)) × MorseModel (m + 1))
        (↑(⊤ : ℕ∞) : WithTop ℕ∞)
        (fun q : M × ℝ => ((extChartAt I p.1)
          ((trivializationAt (MorseModel (m + 1)) (TangentSpace I) p.1 (σ q)).1),
          (trivializationAt (MorseModel (m + 1)) (TangentSpace I) p.1 (σ q)).2)) a p := by
      simpa [FiberBundle.extChartAt, hσp, Function.comp_def, PartialEquiv.trans_apply,
        PartialEquiv.prod_coe, PartialEquiv.refl_coe] using h2
    have hfiber : ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, MorseModel (m + 1)) (↑(⊤ : ℕ∞) : WithTop ℕ∞)
        (fun q : M × ℝ => (trivializationAt (MorseModel (m + 1)) (TangentSpace I) p.1 (σ q)).2) a p := by
      have hsplit := (contMDiffWithinAt_prod_module_iff (𝕜 := ℝ) (I := I.prod 𝓘(ℝ, ℝ))
        (F₁ := MorseModel (m + 1)) (F₂ := MorseModel (m + 1))
        (f := fun q : M × ℝ => ((extChartAt I p.1)
          ((trivializationAt (MorseModel (m + 1)) (TangentSpace I) p.1 (σ q)).1),
          (trivializationAt (MorseModel (m + 1)) (TangentSpace I) p.1 (σ q)).2))
        (s := a) (x := p) (n := (↑(⊤ : ℕ∞) : WithTop ℕ∞))).1 h2'
      simpa using hsplit.2
    simpa [σ, hσp] using (contMDiffWithinAt_iff_target (I := I.prod 𝓘(ℝ, ℝ)) (I' := 𝓘(ℝ, MorseModel (m + 1)))
      (f := fun q : M × ℝ => (trivializationAt (MorseModel (m + 1)) (TangentSpace I) p.1 (σ q)).2)
      (s := a) (x := p) (n := (↑(⊤ : ℕ∞) : WithTop ℕ∞))).mpr
      ⟨hcont'.2, hfiber⟩
  · intro hfib
    have hcontfib : ContinuousWithinAt (fun q : M × ℝ =>
        (trivializationAt (MorseModel (m + 1)) (TangentSpace I) p.1 (σ q)).2) a p :=
      hfib.continuousWithinAt
    have hcont : ContinuousWithinAt σ a p := by
      exact (FiberBundle.continuousWithinAt_totalSpace (f := σ) (s := a) (x₀ := p)).2
        ⟨hπ, by simpa [hσp] using hcontfib⟩
    have hfst : ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ)) I (↑(⊤ : ℕ∞) : WithTop ℕ∞) (fun q : M × ℝ => q.1) a p :=
      contMDiffWithinAt_fst
    have hxsrc : p.1 ∈ (chartAt H p.1).source := mem_chart_source (H := H) (M := M) p.1
    have hchart : ContMDiffAt I 𝓘(ℝ, MorseModel (m + 1)) (↑(⊤ : ℕ∞) : WithTop ℕ∞) (extChartAt I p.1) p.1 :=
      contMDiffAt_extChartAt' (I := I) (n := (↑(⊤ : ℕ∞) : WithTop ℕ∞)) (x := p.1) hxsrc
    have hfirst : ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, MorseModel (m + 1)) (↑(⊤ : ℕ∞) : WithTop ℕ∞)
        (fun q : M × ℝ => (extChartAt I p.1) q.1) a p :=
      hchart.contMDiffWithinAt.comp p hfst (by intro q hq; exact (ha hq).1)
    have hfirst' : ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, MorseModel (m + 1)) (↑(⊤ : ℕ∞) : WithTop ℕ∞)
        (fun q : M × ℝ => (extChartAt I p.1)
          ((trivializationAt (MorseModel (m + 1)) (TangentSpace I) p.1 (σ q)).1)) a p := by
      have heq : (fun q : M × ℝ => (extChartAt I p.1)
          ((trivializationAt (MorseModel (m + 1)) (TangentSpace I) p.1 (σ q)).1)) =ᶠ[nhdsWithin p a]
          (fun q : M × ℝ => (extChartAt I p.1) q.1) := by
        filter_upwards [self_mem_nhdsWithin] with q hq
        have hmem : q.1 ∈ (trivializationAt (MorseModel (m + 1)) (TangentSpace I) p.1).baseSet := by
          have hq' := ha hq
          simpa [← extChartAt_source] using hq'.1
        rw [(trivializationAt (MorseModel (m + 1)) (TangentSpace I) p.1).coe_fst' hmem]
      exact hfirst.congr_of_eventuallyEq heq (by
        exact congrArg (extChartAt I p.1)
          ((trivializationAt (MorseModel (m + 1)) (TangentSpace I) p.1).coe_fst'
            (mem_baseSet_trivializationAt (MorseModel (m + 1)) (TangentSpace I) p.1)))
    have hpair : ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, (MorseModel (m + 1)) × MorseModel (m + 1))
        (↑(⊤ : ℕ∞) : WithTop ℕ∞)
        (fun q : M × ℝ => ((extChartAt I p.1)
          ((trivializationAt (MorseModel (m + 1)) (TangentSpace I) p.1 (σ q)).1),
          (trivializationAt (MorseModel (m + 1)) (TangentSpace I) p.1 (σ q)).2)) a p := by
      exact (contMDiffWithinAt_prod_module_iff (𝕜 := ℝ) (I := I.prod 𝓘(ℝ, ℝ))
        (F₁ := MorseModel (m + 1)) (F₂ := MorseModel (m + 1))
        (f := fun q : M × ℝ => ((extChartAt I p.1)
          ((trivializationAt (MorseModel (m + 1)) (TangentSpace I) p.1 (σ q)).1),
          (trivializationAt (MorseModel (m + 1)) (TangentSpace I) p.1 (σ q)).2))
        (s := a) (x := p) (n := (↑(⊤ : ℕ∞) : WithTop ℕ∞))).2 ⟨hfirst', hfib⟩
    have hσcmd : ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, MorseModel (m + 1)))
        (↑(⊤ : ℕ∞) : WithTop ℕ∞) σ a p := by
      simpa [FiberBundle.extChartAt, hσp, Function.comp_def, PartialEquiv.trans_apply,
        PartialEquiv.prod_coe, PartialEquiv.refl_coe] using
        (contMDiffWithinAt_iff_target (I := I.prod 𝓘(ℝ, ℝ)) (I' := I.prod 𝓘(ℝ, MorseModel (m + 1)))
          (f := σ) (s := a) (x := p) (n := (↑(⊤ : ℕ∞) : WithTop ℕ∞))).mpr ⟨hcont, hpair⟩
    exact hσcmd

private theorem familyTangentSection_contMDiffWithinAt_section_iff'
    {I : ModelWithCorners ℝ (MorseModel (m + 1)) H} [I.Boundaryless]
    [IsManifold I (⊤ : WithTop ℕ∞) M] [T2Space M] [SigmaCompactSpace M]
    {W : (x : M) → (s : ℝ) → TangentSpace I x} {a : Set (M × ℝ)} {p : M × ℝ}
    (x₀ : M) (hp : p.1 ∈ (trivializationAt (MorseModel (m + 1)) (TangentSpace I) x₀).baseSet) :
    ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, MorseModel (m + 1)) (↑(⊤ : ℕ∞) : WithTop ℕ∞)
        (fun q : M × ℝ => (trivializationAt (MorseModel (m + 1)) (TangentSpace I) p.1
          ⟨q.1, W q.1 q.2⟩).2) a p ↔
      ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, MorseModel (m + 1)) (↑(⊤ : ℕ∞) : WithTop ℕ∞)
        (fun q : M × ℝ => (trivializationAt (MorseModel (m + 1)) (TangentSpace I) x₀
          ⟨q.1, W q.1 q.2⟩).2) a p := by
  let e : Bundle.Trivialization (MorseModel (m + 1))
      (Bundle.TotalSpace.proj : TangentBundle I M → M) :=
    trivializationAt (MorseModel (m + 1)) (TangentSpace I) x₀
  let σ : M × ℝ → TangentBundle I M := fun q => ⟨q.1, W q.1 q.2⟩
  have hproj : ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ)) I (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (Bundle.TotalSpace.proj ∘ σ) a p := by
    have hfst : ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ)) I (↑(⊤ : ℕ∞) : WithTop ℕ∞)
        (fun q : M × ℝ => q.1) a p := by
      exact contMDiffWithinAt_fst
    simpa [σ] using hfst
  have he₁ : σ p ∈ (trivializationAt (MorseModel (m + 1)) (TangentSpace I) p.1).source := by
    dsimp [σ]
    simp
  have he₂ : σ p ∈ e.source := by
    dsimp [σ]
    rw [e.mem_source]
    simpa using hp
  have hiff := Bundle.Trivialization.contMDiffWithinAt_snd_comp_iff₂ (f := σ)
    (hp := hproj) (he := he₁) (he' := he₂)
  change ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, MorseModel (m + 1)) (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : M × ℝ => (trivializationAt (MorseModel (m + 1)) (TangentSpace I) p.1 (σ q)).2) a p ↔
    ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, MorseModel (m + 1)) (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : M × ℝ => (e (σ q)).2) a p
  exact hiff

theorem localUnitSpeedFamilyVectorField_at_noncritical
    (I : ModelWithCorners ℝ (MorseModel (m + 1)) H) [I.Boundaryless]
    [IsManifold I (⊤ : WithTop ℕ∞) M] [T2Space M] [SigmaCompactSpace M]
    (F : M → ℝ → ℝ)
    (hF : ContMDiff (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : M × ℝ => F q.1 q.2)) {x₀ : M} {s₀ : ℝ}
    (hcrit : ¬ IsCriticalPointAt I (fun x => F x s₀) x₀) :
    ∃ (U : Set (M × ℝ)), (x₀, s₀) ∈ U ∧ IsOpen U ∧
      ∃ W : (x : M) → (s : ℝ) → TangentSpace I x,
        (∀ p ∈ U, (NormedSpace.fromTangentSpace (F p.1 p.2))
          ((mfderiv I 𝓘(ℝ, ℝ) (fun x : M => F x p.2) p.1) (W p.1 p.2)) = -1) ∧
        ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, MorseModel (m + 1))) (↑(⊤ : ℕ∞) : WithTop ℕ∞)
          (fun q : M × ℝ => (⟨q.1, W q.1 q.2⟩ : TangentBundle I M)) U := by
  let g : (MorseModel (m + 1)) × ℝ → ℝ := fun q => F ((extChartAt I x₀).symm q.1) q.2
  have hgOn : ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) g ((extChartAt I x₀).target ×ˢ Set.univ) := by
    simpa [g] using familyChartRep_contDiffOn (I := I) F hF x₀
  have hfSlice : ContMDiff I 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞) (fun x : M => F x s₀) := by
    have hpair : ContMDiff I (I.prod 𝓘(ℝ, ℝ)) (↑(⊤ : ℕ∞) : WithTop ℕ∞) (fun x : M => (x, s₀)) := by
      exact (contMDiff_id (I := I) (n := (↑(⊤ : ℕ∞) : WithTop ℕ∞))).prodMk
        (contMDiff_const : ContMDiff I 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞) (fun _ : M => s₀))
    simpa using hF.comp hpair
  have hcritChart : fderiv ℝ (fun y : MorseModel (m + 1) => F ((extChartAt I x₀).symm y) s₀)
      (extChartAt I x₀ x₀) ≠ 0 := by
    have hiff := isCriticalPointAt_iff_chart_fderiv I (fun x : M => F x s₀) hfSlice x₀
    intro hz
    exact hcrit (hiff.2 hz)
  rcases exists_coord_of_fderiv_ne_zero (fun y : MorseModel (m + 1) => F ((extChartAt I x₀).symm y) s₀)
    (extChartAt I x₀ x₀) hcritChart with ⟨i, hi⟩
  have hpi : Pi.single i (1 : ℝ) = fun j : Fin (m + 1) => if j = i then (1 : ℝ) else 0 := by
    ext j
    simp [Pi.single, Function.update_apply]
  let a : M × ℝ → ℝ := fun p =>
    (fderiv ℝ g ((extChartAt I x₀) p.1, p.2))
      (ContinuousLinearMap.inl ℝ (MorseModel (m + 1)) ℝ (Pi.single i (1 : ℝ)))
  have hcont : ContinuousOn a ((extChartAt I x₀).source ×ˢ Set.univ) := by
    have hcont' : ContinuousOn (fun q : (MorseModel (m + 1)) × ℝ =>
        (fderiv ℝ g q) (ContinuousLinearMap.inl ℝ (MorseModel (m + 1)) ℝ (Pi.single i (1 : ℝ))))
        ((extChartAt I x₀).target ×ˢ Set.univ) :=
      (familyChartRep_fderiv_apply_contDiffOn (I := I) F hF x₀ i).continuousOn
    have hce : ContinuousOn (fun p : M × ℝ => ((extChartAt I x₀) p.1, p.2))
        ((extChartAt I x₀).source ×ˢ Set.univ) := by
      have hc1 : ContinuousOn (extChartAt I x₀) (extChartAt I x₀).source := by
        simpa [extChartAt_source (I := I) (x := x₀)] using
          (contMDiffOn_extChartAt (I := I) (n := (↑(⊤ : ℕ∞) : WithTop ℕ∞)) (x := x₀)).continuousOn
      exact hc1.prodMap continuousOn_id
    exact hcont'.comp hce (by intro p hp; exact ⟨(extChartAt I x₀).map_source hp.1, trivial⟩)
  have hmem₀ : (x₀, s₀) ∈ (extChartAt I x₀).source ×ˢ Set.univ :=
    ⟨mem_extChartAt_source x₀, trivial⟩
  have hne₀ : a (x₀, s₀) ≠ 0 := by
    have hcurry := familyChartRep_fderiv_curry (I := I) F hF x₀ (extChartAt I x₀ x₀) s₀
      ((extChartAt I x₀).map_source (mem_extChartAt_source x₀))
    have heq : (fderiv ℝ (fun y : MorseModel (m + 1) => F ((extChartAt I x₀).symm y) s₀)
        (extChartAt I x₀ x₀)) (Pi.single i (1 : ℝ)) = a (x₀, s₀) := by
      rw [hcurry]
      change ((fderiv ℝ (fun q : (MorseModel (m + 1)) × ℝ => F ((extChartAt I x₀).symm q.1) q.2)
        (extChartAt I x₀ x₀, s₀)).comp (ContinuousLinearMap.inl ℝ (MorseModel (m + 1)) ℝ))
          (Pi.single i (1 : ℝ)) = (fderiv ℝ (fun q : (MorseModel (m + 1)) × ℝ =>
        F ((extChartAt I x₀).symm q.1) q.2) (extChartAt I x₀ x₀, s₀))
          (ContinuousLinearMap.inl ℝ (MorseModel (m + 1)) ℝ (Pi.single i (1 : ℝ)))
      rfl
    have hi' : (fderiv ℝ (fun y : MorseModel (m + 1) => F ((extChartAt I x₀).symm y) s₀)
        (extChartAt I x₀ x₀)) (Pi.single i (1 : ℝ)) ≠ 0 := by
      rw [hpi]
      simpa using hi
    rwa [heq] at hi'
  have hV : {p : M × ℝ | a p ≠ 0} ∈ nhds (x₀, s₀) := by
    exact (hcont (x₀, s₀) hmem₀).continuousAt
      ((IsOpen.prod (isOpen_extChartAt_source x₀) isOpen_univ).mem_nhds hmem₀)
      (isOpen_ne.mem_nhds hne₀)
  rcases mem_nhds_iff.mp hV with ⟨V, hVsub, hVopen, hV₀⟩
  let U : Set (M × ℝ) := V ∩ ((extChartAt I x₀).source ×ˢ Set.univ)
  have hUopen : IsOpen U := hVopen.inter (IsOpen.prod (isOpen_extChartAt_source x₀) isOpen_univ)
  let W : (x : M) → (s : ℝ) → TangentSpace I x := fun x s =>
    (mfderivWithin 𝓘(ℝ, MorseModel (m + 1)) I (extChartAt I x₀).symm (range I)
      (extChartAt I x₀ x)) (-(a (x, s))⁻¹ • (Pi.single i (1 : ℝ) : MorseModel (m + 1)))
  refine ⟨U, ⟨hV₀, hmem₀⟩, hUopen, W, ?_, ?_⟩
  · intro p hp
    have hxsrc : p.1 ∈ (extChartAt I x₀).source := hp.2.1
    have hpV : p ∈ V := hp.1
    have ha : a p ≠ 0 := hVsub hpV
    let e : PartialEquiv M (MorseModel (m + 1)) := extChartAt I x₀
    have hepx : e.symm (e p.1) = p.1 := e.left_inv hxsrc
    have hmemxy : (e p.1, p.2) ∈ (extChartAt I x₀).target ×ˢ Set.univ :=
      ⟨e.map_source hxsrc, trivial⟩
    have hmdg := ((hgOn (e p.1, p.2) hmemxy).contDiffAt
      ((IsOpen.prod (isOpen_extChartAt_target x₀) isOpen_univ).mem_nhds hmemxy)).differentiableAt
      (by norm_num : (↑(⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0)
    have hmdg' : MDifferentiableAt 𝓘(ℝ, MorseModel (m + 1)) 𝓘(ℝ, ℝ)
        (fun y : MorseModel (m + 1) => g (y, p.2)) (e p.1) := by
      have hpair : ContDiffAt ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) (fun y : MorseModel (m + 1) => (y, p.2)) (e p.1) := by
        exact (contDiffAt_id.prodMk contDiffAt_const)
      have hgAt : ContDiffAt ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) g (e p.1, p.2) :=
        (hgOn (e p.1, p.2) hmemxy).contDiffAt
          ((IsOpen.prod (isOpen_extChartAt_target x₀) isOpen_univ).mem_nhds hmemxy)
      exact ((ContDiffAt.contMDiffAt (ContDiffAt.comp (𝕜 := ℝ) (n := (↑(⊤ : ℕ∞) : WithTop ℕ∞)) (g := g)
        (f := fun y : MorseModel (m + 1) => (y, p.2)) (e p.1) hgAt hpair)).mdifferentiableAt
        (by norm_num : (↑(⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0))
    have hmdchart := (contMDiffAt_extChartAt' (I := I) (n := (↑(⊤ : ℕ∞) : WithTop ℕ∞)) (x := x₀)
      (by simpa [extChartAt_source] using hxsrc)).mdifferentiableAt (by norm_num)
    have hcomp : mfderiv I 𝓘(ℝ, ℝ) (fun y : M => g (e y, p.2)) p.1 =
        (mfderiv 𝓘(ℝ, MorseModel (m + 1)) 𝓘(ℝ, ℝ) (fun y : MorseModel (m + 1) => g (y, p.2)) (e p.1)).comp
          (mfderiv I 𝓘(ℝ, MorseModel (m + 1)) e p.1) := by
      simpa using (mfderiv_comp (x := p.1) (g := (fun y : MorseModel (m + 1) => g (y, p.2))) (f := e)
        (hg := hmdg') (hf := hmdchart))
    have hfuneq : (fun y : M => F y p.2) =ᶠ[nhds p.1] (fun y : M => g (e y, p.2)) := by
      have hsrcopen : IsOpen e.source := isOpen_extChartAt_source x₀
      exact Filter.eventuallyEq_of_mem (by simpa [e] using (hsrcopen.mem_nhds hxsrc))
        (fun y hy => congrArg (fun z => F z p.2) (e.left_inv hy).symm)
    have heq := Filter.EventuallyEq.mfderiv_eq (I := I) (I' := 𝓘(ℝ, ℝ)) hfuneq
    have hge : mfderiv 𝓘(ℝ, MorseModel (m + 1)) 𝓘(ℝ, ℝ) (fun y : MorseModel (m + 1) => g (y, p.2)) (e p.1) =
        fderiv ℝ (fun y : MorseModel (m + 1) => g (y, p.2)) (e p.1) := by
      exact (mfderiv_eq_fderiv (𝕜 := ℝ) (E := MorseModel (m + 1)) (E' := ℝ)
        (f := fun y : MorseModel (m + 1) => g (y, p.2)) (x := e p.1))
    have hcurry := familyChartRep_fderiv_curry (I := I) F hF x₀ (e p.1) p.2 hmemxy.1
    have hslice : fderiv ℝ (fun y : MorseModel (m + 1) => g (y, p.2)) (e p.1) =
        (fderiv ℝ g (e p.1, p.2)).comp (ContinuousLinearMap.inl ℝ (MorseModel (m + 1)) ℝ) := by
      simpa [g] using hcurry
    have hid := mfderiv_extChartAt_comp_mfderivWithin_extChartAt_symm (I := I) (x := x₀)
      (y := e p.1) (by simpa [e] using hmemxy.1)
    have hid' : (mfderiv I 𝓘(ℝ, MorseModel (m + 1)) e p.1) ∘L
        (mfderivWithin 𝓘(ℝ, MorseModel (m + 1)) I e.symm (range I) (e p.1)) =
        ContinuousLinearMap.id _ _ := by
      rw [hepx] at hid
      exact hid
    have hidapply : ∀ w : MorseModel (m + 1),
        (mfderiv I 𝓘(ℝ, MorseModel (m + 1)) e p.1)
          ((mfderivWithin 𝓘(ℝ, MorseModel (m + 1)) I e.symm (range I) (e p.1)) w) = w := by
      intro w
      change (((mfderiv I 𝓘(ℝ, MorseModel (m + 1)) e p.1).comp
        (mfderivWithin 𝓘(ℝ, MorseModel (m + 1)) I e.symm (range I) (e p.1)))) w = w
      rw [hid']
      simp
    have hchartW : ((mfderiv I 𝓘(ℝ, MorseModel (m + 1)) e p.1) : TangentSpace I p.1 →L[ℝ] MorseModel (m + 1))
        (W p.1 p.2) = -(a p)⁻¹ • (Pi.single i (1 : ℝ) : MorseModel (m + 1)) := by
      dsimp [W, a]
      exact hidapply (-(a p)⁻¹ • (Pi.single i (1 : ℝ) : MorseModel (m + 1)))
    have hfinal : (fderiv ℝ (fun y : MorseModel (m + 1) => g (y, p.2)) (e p.1))
        (-(a p)⁻¹ • (Pi.single i (1 : ℝ) : MorseModel (m + 1))) = -1 := by
      rw [hslice]
      rw [ContinuousLinearMap.comp_apply]
      have hinl : ContinuousLinearMap.inl ℝ (MorseModel (m + 1)) ℝ
          (-(a p)⁻¹ • (Pi.single i (1 : ℝ) : MorseModel (m + 1))) =
          -(a p)⁻¹ • ContinuousLinearMap.inl ℝ (MorseModel (m + 1)) ℝ (Pi.single i (1 : ℝ)) := by
        ext <;> simp
      rw [hinl]
      rw [(fderiv ℝ g (e p.1, p.2)).map_smul]
      rw [smul_eq_mul]
      have haval : (fderiv ℝ g (e p.1, p.2))
          (ContinuousLinearMap.inl ℝ (MorseModel (m + 1)) ℝ (Pi.single i (1 : ℝ))) = a p := by
        rfl
      rw [haval]
      field_simp [ha]
    have hmain : (mfderiv I 𝓘(ℝ, ℝ) (fun y : M => F y p.2) p.1) (W p.1 p.2) = (-1 : ℝ) := by
      rw [heq]
      rw [hcomp]
      change ((mfderiv 𝓘(ℝ, MorseModel (m + 1)) 𝓘(ℝ, ℝ) (fun y : MorseModel (m + 1) => g (y, p.2)) (e p.1) :
          MorseModel (m + 1) →L[ℝ] ℝ))
        (((mfderiv I 𝓘(ℝ, MorseModel (m + 1)) e p.1) : TangentSpace I p.1 →L[ℝ] MorseModel (m + 1))
          (W p.1 p.2)) = (-1 : ℝ)
      rw [hge]
      rw [hchartW]
      exact hfinal
    have hts : (NormedSpace.fromTangentSpace (F p.1 p.2))
        ((mfderiv I 𝓘(ℝ, ℝ) (fun x : M => F x p.2) p.1) (W p.1 p.2)) =
        (mfderiv I 𝓘(ℝ, ℝ) (fun x : M => F x p.2) p.1) (W p.1 p.2) := by
      rfl
    rw [hts]
    exact hmain
  · intro p hp
    let U' : Set (M × ℝ) := U ∩ ((extChartAt I p.1).source ×ˢ Set.univ)
    have hU'sub : U' ⊆ (extChartAt I p.1).source ×ˢ Set.univ := by
      intro q hq
      exact hq.2
    have hpU' : p ∈ U' := ⟨hp, ⟨mem_extChartAt_source p.1, trivial⟩⟩
    have hiff := familyTangentSection_contMDiffWithinAt_section_iff (I := I)
      (W := W) (a := U') (p := p) hU'sub
    have hiff' := familyTangentSection_contMDiffWithinAt_section_iff' (I := I)
      (W := W) (a := U') (p := p) x₀ (by
        have hp' := hp.2.1
        simpa [extChartAt_source (I := I) (x := x₀)] using hp')
    have hfibVal : ∀ q ∈ U', (trivializationAt (MorseModel (m + 1)) (TangentSpace I) x₀
        ⟨q.1, W q.1 q.2⟩).2 = -(a q)⁻¹ • (Pi.single i (1 : ℝ) : MorseModel (m + 1)) := by
      intro q hq
      have hqsrc : q.1 ∈ (extChartAt I x₀).source := hq.1.2.1
      rw [tangentTrivializationAt_apply I x₀ q.1 hqsrc (W q.1 q.2)]
      dsimp [W, a]
      have hid := mfderiv_extChartAt_comp_mfderivWithin_extChartAt_symm (I := I) (x := x₀)
        (y := (extChartAt I x₀) q.1) (by
          simpa using (extChartAt I x₀).map_source hqsrc)
      have hep : (extChartAt I x₀).symm ((extChartAt I x₀) q.1) = q.1 :=
        (extChartAt I x₀).left_inv hqsrc
      have hid'' : (mfderiv I 𝓘(ℝ, MorseModel (m + 1)) (extChartAt I x₀) q.1) ∘L
          (mfderivWithin 𝓘(ℝ, MorseModel (m + 1)) I (extChartAt I x₀).symm (range I)
            ((extChartAt I x₀) q.1)) = ContinuousLinearMap.id _ _ := by
        rw [hep] at hid
        exact hid
      change (((mfderiv I 𝓘(ℝ, MorseModel (m + 1)) (extChartAt I x₀) q.1).comp
        (mfderivWithin 𝓘(ℝ, MorseModel (m + 1)) I (extChartAt I x₀).symm (range I)
          ((extChartAt I x₀) q.1)))) (-(a q)⁻¹ • (Pi.single i (1 : ℝ) : MorseModel (m + 1))) =
        -(a q)⁻¹ • (Pi.single i (1 : ℝ) : MorseModel (m + 1))
      rw [hid'']
      rfl
    have haU : ∀ q ∈ U', a q ≠ 0 := by
      intro q hq
      exact hVsub hq.1.1
    have hcmd : ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞) a U' p :=
      (familyChartRep_coefficient_contMDiffOn (I := I) F hF x₀ i).mono
        (by intro q hq; exact hq.1.2) p hpU'
    have hinv : ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞)
        (fun q : M × ℝ => (a q)⁻¹) U' p :=
      hcmd.inv₀ (haU p hpU')
    have hsmul : ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, MorseModel (m + 1)) (↑(⊤ : ℕ∞) : WithTop ℕ∞)
        (fun q : M × ℝ => -(a q)⁻¹ • (Pi.single i (1 : ℝ) : MorseModel (m + 1))) U' p := by
      have hconst : ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, MorseModel (m + 1))
          (↑(⊤ : ℕ∞) : WithTop ℕ∞)
          (fun _ : M × ℝ => (Pi.single i (1 : ℝ) : MorseModel (m + 1))) U' p :=
        contMDiffWithinAt_const
      exact hinv.neg.smul hconst
    have heqfib : (fun q : M × ℝ => (trivializationAt (MorseModel (m + 1)) (TangentSpace I) x₀
        ⟨q.1, W q.1 q.2⟩).2) =ᶠ[nhdsWithin p U']
        (fun q : M × ℝ => -(a q)⁻¹ • (Pi.single i (1 : ℝ) : MorseModel (m + 1))) := by
      filter_upwards [self_mem_nhdsWithin] with q hq
      exact hfibVal q hq
    have hfib : ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, MorseModel (m + 1)) (↑(⊤ : ℕ∞) : WithTop ℕ∞)
        (fun q : M × ℝ => (trivializationAt (MorseModel (m + 1)) (TangentSpace I) x₀
          ⟨q.1, W q.1 q.2⟩).2) U' p :=
      hsmul.congr_of_eventuallyEq heqfib (hfibVal p hpU')
    have hσU' : ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, MorseModel (m + 1)))
        (↑(⊤ : ℕ∞) : WithTop ℕ∞) (fun q : M × ℝ => (⟨q.1, W q.1 q.2⟩ : TangentBundle I M)) U' p := by
      rw [hiff, hiff']
      exact hfib
    exact hσU'.mono_of_mem_nhdsWithin (by
      have hC : (extChartAt I p.1).source ×ˢ Set.univ ∈ nhds p :=
        (IsOpen.prod (isOpen_extChartAt_source p.1) isOpen_univ).mem_nhds
          ⟨mem_extChartAt_source p.1, trivial⟩
      exact inter_mem_nhdsWithin U hC)

end
end DifferentialGeometry.Topology.Morse
