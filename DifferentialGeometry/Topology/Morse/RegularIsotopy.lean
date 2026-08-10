import DifferentialGeometry.Topology.Morse.RegularVectorField
import DifferentialGeometry.Topology.Morse.RegularSublevel
import DifferentialGeometry.Analysis.ODE.CompactSupportFlow

namespace DifferentialGeometry.Topology.Morse

open Manifold Set Filter
open scoped Manifold ContDiff Topology Filter

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

private theorem family_mfderiv_decomp
    {I : ModelWithCorners ℝ (MorseModel (m + 1)) H} [I.Boundaryless]
    [IsManifold I (⊤ : WithTop ℕ∞) M] (F : M → ℝ → ℝ)
    (hF : ContMDiff (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : M × ℝ => F q.1 q.2)) (x : M) (s : ℝ)
    (w : TangentSpace (I.prod 𝓘(ℝ, ℝ)) (x, s)) :
    (NormedSpace.fromTangentSpace (F x s)) ((mfderiv (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ)
        (fun q : M × ℝ => F q.1 q.2) (x, s)) w) =
      (NormedSpace.fromTangentSpace (F x s)) ((mfderiv I 𝓘(ℝ, ℝ) (fun y : M => F y s) x)
        ((mfderiv (I.prod 𝓘(ℝ, ℝ)) I (fun q : M × ℝ => q.1) (x, s)) w)) +
        ((fderiv ℝ (fun t : ℝ => F x t) s) 1) *
          (NormedSpace.fromTangentSpace (s : ℝ))
            ((mfderiv (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) (fun q : M × ℝ => q.2) (x, s)) w) := by
  let Fp : M × ℝ → ℝ := fun q => F q.1 q.2
  let w₁ : TangentSpace I x := (mfderiv (I.prod 𝓘(ℝ, ℝ)) I (fun q : M × ℝ => q.1) (x, s)) w
  let w₂ : TangentSpace 𝓘(ℝ, ℝ) s := (mfderiv (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) (fun q : M × ℝ => q.2) (x, s)) w
  let inlMap : M → M × ℝ := fun y => (y, s)
  let inrMap : ℝ → M × ℝ := fun t => (x, t)
  have hFp : MDifferentiableAt (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) Fp (x, s) :=
    (hF (x, s)).mdifferentiableAt (by norm_num)
  have hπ₁ : MDifferentiableAt (I.prod 𝓘(ℝ, ℝ)) I (fun q : M × ℝ => q.1) (x, s) :=
    mdifferentiableAt_fst
  have hπ₂ : MDifferentiableAt (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) (fun q : M × ℝ => q.2) (x, s) :=
    mdifferentiableAt_snd
  have hinl : MDifferentiableAt I (I.prod 𝓘(ℝ, ℝ)) inlMap x := by
    exact (mdifferentiableAt_id.prodMk mdifferentiableAt_const)
  have hinr : MDifferentiableAt 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, ℝ)) inrMap s := by
    exact (mdifferentiableAt_const.prodMk mdifferentiableAt_id)
  have hw₁ : w₁ = (show TangentSpace I x from w.1) := by
    dsimp [w₁]
    have hm := mfderiv_fst (𝕜 := ℝ) (E := MorseModel (m + 1)) (H := H) (I := I) (M := M)
      (E' := ℝ) (H' := ℝ) (I' := 𝓘(ℝ, ℝ)) (M' := ℝ) (x := (x, s))
    have hv : w = (show TangentSpace (I.prod 𝓘(ℝ, ℝ)) (x, s) from (w.1, w.2)) := by
      rfl
    rw [hv]
    rw [show (mfderiv (I.prod 𝓘(ℝ, ℝ)) I Prod.fst (x, s)) =
        ContinuousLinearMap.fst ℝ (TangentSpace I x) (TangentSpace 𝓘(ℝ, ℝ) s) from hm]
    change (ContinuousLinearMap.fst ℝ (TangentSpace I x) (TangentSpace 𝓘(ℝ, ℝ) s))
        (show TangentSpace I x × TangentSpace 𝓘(ℝ, ℝ) s from
          (show TangentSpace (I.prod 𝓘(ℝ, ℝ)) (x, s) from (w.1, w.2))) =
      (show TangentSpace I x from w.1)
    change (show TangentSpace I x from w.1) = (show TangentSpace I x from w.1)
    rfl
  have hw₂ : w₂ = (show TangentSpace 𝓘(ℝ, ℝ) s from w.2) := by
    dsimp [w₂]
    have hm := mfderiv_snd (𝕜 := ℝ) (E := MorseModel (m + 1)) (H := H) (I := I) (M := M)
      (E' := ℝ) (H' := ℝ) (I' := 𝓘(ℝ, ℝ)) (M' := ℝ) (x := (x, s))
    have hv : w = (show TangentSpace (I.prod 𝓘(ℝ, ℝ)) (x, s) from (w.1, w.2)) := by
      rfl
    rw [hv]
    rw [show (mfderiv (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) Prod.snd (x, s)) =
        ContinuousLinearMap.snd ℝ (TangentSpace I x) (TangentSpace 𝓘(ℝ, ℝ) s) from hm]
    change (ContinuousLinearMap.snd ℝ (TangentSpace I x) (TangentSpace 𝓘(ℝ, ℝ) s))
        (show TangentSpace I x × TangentSpace 𝓘(ℝ, ℝ) s from
          (show TangentSpace (I.prod 𝓘(ℝ, ℝ)) (x, s) from (w.1, w.2))) =
      (show TangentSpace 𝓘(ℝ, ℝ) s from w.2)
    change (show TangentSpace 𝓘(ℝ, ℝ) s from w.2) = (show TangentSpace 𝓘(ℝ, ℝ) s from w.2)
    rfl
  have hinlval : (mfderiv I (I.prod 𝓘(ℝ, ℝ)) inlMap x) w₁ =
      (show TangentSpace (I.prod 𝓘(ℝ, ℝ)) (x, s) from
        (w₁, (0 : TangentSpace 𝓘(ℝ, ℝ) s))) := by
    have hid : MDifferentiableAt I I (fun y : M => y) x := mdifferentiableAt_id
    have hc : MDifferentiableAt I 𝓘(ℝ, ℝ) (fun _ : M => s) x := mdifferentiableAt_const
    have hprod := mfderiv_prodMk (hf := hid) (hg := hc)
    change (mfderiv I (I.prod 𝓘(ℝ, ℝ)) (fun y : M => (y, s)) x) w₁ =
      (show TangentSpace (I.prod 𝓘(ℝ, ℝ)) (x, s) from (w₁, (0 : TangentSpace 𝓘(ℝ, ℝ) s)))
    rw [hprod]
    change (((mfderiv I I (fun y : M => y) x) w₁),
        ((mfderiv I 𝓘(ℝ, ℝ) (fun _ : M => s) x) w₁)) =
      (show TangentSpace (I.prod 𝓘(ℝ, ℝ)) (x, s) from (w₁, (0 : TangentSpace 𝓘(ℝ, ℝ) s)))
    have hidv : (mfderiv I I (fun y : M => y) x) w₁ = w₁ := by
      change ((mfderiv I I (@id M) x) w₁) = w₁
      rw [show (mfderiv I I (@id M) x) = ContinuousLinearMap.id ℝ (TangentSpace I x) by
        exact mfderiv_id (𝕜 := ℝ) (E := MorseModel (m + 1)) (H := H) (I := I) (M := M) (x := x)]
      rfl
    have hcv : (mfderiv I 𝓘(ℝ, ℝ) (fun _ : M => s) x) w₁ = (0 : TangentSpace 𝓘(ℝ, ℝ) s) := by
      have hm := mfderiv_const (𝕜 := ℝ) (I := I) (I' := 𝓘(ℝ, ℝ)) (x := x) (c := s)
      rw [show (mfderiv I 𝓘(ℝ, ℝ) (fun _ : M => s) x) =
          (0 : TangentSpace I x →L[ℝ] TangentSpace 𝓘(ℝ, ℝ) s) from hm]
      rfl
    rw [hidv, hcv]
    rfl
  have hinrval : (mfderiv 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, ℝ)) inrMap s) w₂ =
      (show TangentSpace (I.prod 𝓘(ℝ, ℝ)) (x, s) from
        ((0 : TangentSpace I x), w₂)) := by
    have hc : MDifferentiableAt 𝓘(ℝ, ℝ) I (fun _ : ℝ => x) s := mdifferentiableAt_const
    have hid : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun t : ℝ => t) s := mdifferentiableAt_id
    have hprod := mfderiv_prodMk (hf := hc) (hg := hid)
    change (mfderiv 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, ℝ)) (fun t : ℝ => (x, t)) s) w₂ =
      (show TangentSpace (I.prod 𝓘(ℝ, ℝ)) (x, s) from ((0 : TangentSpace I x), w₂))
    rw [hprod]
    change (((mfderiv 𝓘(ℝ, ℝ) I (fun _ : ℝ => x) s) w₂),
        ((mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun t : ℝ => t) s) w₂)) =
      (show TangentSpace (I.prod 𝓘(ℝ, ℝ)) (x, s) from ((0 : TangentSpace I x), w₂))
    have hcv : (mfderiv 𝓘(ℝ, ℝ) I (fun _ : ℝ => x) s) w₂ = (0 : TangentSpace I x) := by
      have hm := mfderiv_const (𝕜 := ℝ) (I := 𝓘(ℝ, ℝ)) (I' := I) (x := s) (c := x)
      rw [show (mfderiv 𝓘(ℝ, ℝ) I (fun _ : ℝ => x) s) =
          (0 : TangentSpace 𝓘(ℝ, ℝ) s →L[ℝ] TangentSpace I x) from hm]
      rfl
    have hidv : (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun t : ℝ => t) s) w₂ = w₂ := by
      change ((mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (@id ℝ) s) w₂) = w₂
      rw [show (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (@id ℝ) s) =
          ContinuousLinearMap.id ℝ (TangentSpace 𝓘(ℝ, ℝ) s) by
        exact mfderiv_id (𝕜 := ℝ) (E := ℝ) (H := ℝ) (I := 𝓘(ℝ, ℝ)) (M := ℝ) (x := s)]
      rfl
    rw [hcv, hidv]
    rfl
  have hsplit : w = (show TangentSpace (I.prod 𝓘(ℝ, ℝ)) (x, s) from
      (((mfderiv I (I.prod 𝓘(ℝ, ℝ)) inlMap x) w₁) +
        ((mfderiv 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, ℝ)) inrMap s) w₂))) := by
    rw [hinlval, hinrval]
    change w = (show TangentSpace (I.prod 𝓘(ℝ, ℝ)) (x, s) from
      ((w₁, (0 : TangentSpace 𝓘(ℝ, ℝ) s)) + ((0 : TangentSpace I x), w₂)))
    rw [hw₁, hw₂]
    simp
  have hmain : (mfderiv (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) Fp (x, s)) w =
      (mfderiv I 𝓘(ℝ, ℝ) (fun y : M => F y s) x) w₁ +
        (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun t : ℝ => F x t) s) w₂ := by
    rw [hsplit]
    change (mfderiv (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) Fp (x, s))
        ((mfderiv I (I.prod 𝓘(ℝ, ℝ)) inlMap x) w₁ +
          (mfderiv 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, ℝ)) inrMap s) w₂) =
      (mfderiv I 𝓘(ℝ, ℝ) (fun y : M => F y s) x) w₁ +
        (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun t : ℝ => F x t) s) w₂
    rw [map_add]
    have hinlcomp : (mfderiv (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) Fp (x, s))
        ((mfderiv I (I.prod 𝓘(ℝ, ℝ)) inlMap x) w₁) =
        (mfderiv I 𝓘(ℝ, ℝ) (fun y : M => F y s) x) w₁ := by
      have hc := mfderiv_comp (x := x) (g := Fp) (f := inlMap) (hg := hFp) (hf := hinl)
      have hfun : (Fp ∘ inlMap) = (fun y : M => F y s) := by
        funext y
        dsimp [Fp, inlMap]
      rw [hfun] at hc
      change ((mfderiv (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) Fp (x, s)).comp
          (mfderiv I (I.prod 𝓘(ℝ, ℝ)) inlMap x)) w₁ = (mfderiv I 𝓘(ℝ, ℝ) (fun y : M => F y s) x) w₁
      rw [← hc]
    have hinrcomp : (mfderiv (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) Fp (x, s))
        ((mfderiv 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, ℝ)) inrMap s) w₂) =
        (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun t : ℝ => F x t) s) w₂ := by
      have hc := mfderiv_comp (x := s) (g := Fp) (f := inrMap) (hg := hFp) (hf := hinr)
      have hfun : (Fp ∘ inrMap) = (fun t : ℝ => F x t) := by
        funext t
        dsimp [Fp, inrMap]
      rw [hfun] at hc
      change ((mfderiv (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) Fp (x, s)).comp
          (mfderiv 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, ℝ)) inrMap s)) w₂ =
        (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun t : ℝ => F x t) s) w₂
      rw [← hc]
    rw [hinlcomp, hinrcomp]
  have hge : (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun t : ℝ => F x t) s) =
      fderiv ℝ (fun t : ℝ => F x t) s := by
    exact (mfderiv_eq_fderiv (𝕜 := ℝ) (E := ℝ) (E' := ℝ)
      (f := fun t : ℝ => F x t) (x := s))
  rw [hmain]
  change (NormedSpace.fromTangentSpace (F x s))
      ((mfderiv I 𝓘(ℝ, ℝ) (fun y : M => F y s) x) w₁ +
        (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun t : ℝ => F x t) s) w₂) =
      (NormedSpace.fromTangentSpace (F x s)) ((mfderiv I 𝓘(ℝ, ℝ) (fun y : M => F y s) x) w₁) +
        ((fderiv ℝ (fun t : ℝ => F x t) s) 1) *
          (NormedSpace.fromTangentSpace (s : ℝ)) w₂
  have hsum : (NormedSpace.fromTangentSpace (F x s))
      ((mfderiv I 𝓘(ℝ, ℝ) (fun y : M => F y s) x) w₁ +
        (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun t : ℝ => F x t) s) w₂) =
      (NormedSpace.fromTangentSpace (F x s)) ((mfderiv I 𝓘(ℝ, ℝ) (fun y : M => F y s) x) w₁) +
        (NormedSpace.fromTangentSpace (F x s)) ((mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun t : ℝ => F x t) s) w₂) := by
    rw [map_add]
  rw [hsum]
  have hlin : (NormedSpace.fromTangentSpace (F x s))
      ((mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun t : ℝ => F x t) s) w₂) =
      ((fderiv ℝ (fun t : ℝ => F x t) s) 1) * (NormedSpace.fromTangentSpace (s : ℝ)) w₂ := by
    have hlin' : (fderiv ℝ (fun t : ℝ => F x t) s) (NormedSpace.fromTangentSpace (s : ℝ) w₂) =
        ((fderiv ℝ (fun t : ℝ => F x t) s) 1) * (NormedSpace.fromTangentSpace (s : ℝ) w₂) := by
      calc
        (fderiv ℝ (fun t : ℝ => F x t) s) (NormedSpace.fromTangentSpace (s : ℝ) w₂)
            = (fderiv ℝ (fun t : ℝ => F x t) s)
                ((NormedSpace.fromTangentSpace (s : ℝ) w₂) • (1 : ℝ)) := by
              rw [smul_eq_mul, mul_one]
        _ = (NormedSpace.fromTangentSpace (s : ℝ) w₂) •
            ((fderiv ℝ (fun t : ℝ => F x t) s) 1) := by
              rw [← (fderiv ℝ (fun t : ℝ => F x t) s).map_smul]
        _ = ((fderiv ℝ (fun t : ℝ => F x t) s) 1) * (NormedSpace.fromTangentSpace (s : ℝ) w₂) := by
              rw [smul_eq_mul, mul_comm]
    change (NormedSpace.fromTangentSpace (F x s))
        ((mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun t : ℝ => F x t) s)
          (show TangentSpace 𝓘(ℝ, ℝ) s from (NormedSpace.fromTangentSpace (s : ℝ) w₂))) =
      ((fderiv ℝ (fun t : ℝ => F x t) s) 1) * (NormedSpace.fromTangentSpace (s : ℝ)) w₂
    rw [hge]
    exact hlin'
  rw [hlin]

private theorem suspension_level_equation
    {I : ModelWithCorners ℝ (MorseModel (m + 1)) H} [I.Boundaryless]
    [IsManifold I (⊤ : WithTop ℕ∞) M] (F : M → ℝ → ℝ)
    (hF : ContMDiff (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : M × ℝ => F q.1 q.2)) (x : M) (s : ℝ)
    (v : TangentSpace I x) (ρs : ℝ) :
    (NormedSpace.fromTangentSpace (F x s))
      ((mfderiv (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) (fun q : M × ℝ => F q.1 q.2) (x, s))
        (show TangentSpace (I.prod 𝓘(ℝ, ℝ)) (x, s) from (v, ρs))) =
      (NormedSpace.fromTangentSpace (F x s)) ((mfderiv I 𝓘(ℝ, ℝ) (fun y : M => F y s) x) v) +
        ((fderiv ℝ (fun t : ℝ => F x t) s) 1) * ρs := by
  have hd := family_mfderiv_decomp (I := I) F hF x s
    (show TangentSpace (I.prod 𝓘(ℝ, ℝ)) (x, s) from (v, ρs))
  have hw₁ : (mfderiv (I.prod 𝓘(ℝ, ℝ)) I (fun q : M × ℝ => q.1) (x, s))
      (show TangentSpace (I.prod 𝓘(ℝ, ℝ)) (x, s) from (v, ρs)) = v := by
    have hm := mfderiv_fst (𝕜 := ℝ) (E := MorseModel (m + 1)) (H := H) (I := I) (M := M)
      (E' := ℝ) (H' := ℝ) (I' := 𝓘(ℝ, ℝ)) (M' := ℝ) (x := (x, s))
    rw [show (mfderiv (I.prod 𝓘(ℝ, ℝ)) I Prod.fst (x, s)) =
        ContinuousLinearMap.fst ℝ (TangentSpace I x) (TangentSpace 𝓘(ℝ, ℝ) s) from hm]
    change (ContinuousLinearMap.fst ℝ (TangentSpace I x) (TangentSpace 𝓘(ℝ, ℝ) s))
        (show TangentSpace I x × TangentSpace 𝓘(ℝ, ℝ) s from
          (show TangentSpace (I.prod 𝓘(ℝ, ℝ)) (x, s) from (v, ρs))) = v
    change v = v
    rfl
  have hw₂ : (mfderiv (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) (fun q : M × ℝ => q.2) (x, s))
      (show TangentSpace (I.prod 𝓘(ℝ, ℝ)) (x, s) from (v, ρs)) =
      (show TangentSpace 𝓘(ℝ, ℝ) s from ρs) := by
    have hm := mfderiv_snd (𝕜 := ℝ) (E := MorseModel (m + 1)) (H := H) (I := I) (M := M)
      (E' := ℝ) (H' := ℝ) (I' := 𝓘(ℝ, ℝ)) (M' := ℝ) (x := (x, s))
    rw [show (mfderiv (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) Prod.snd (x, s)) =
        ContinuousLinearMap.snd ℝ (TangentSpace I x) (TangentSpace 𝓘(ℝ, ℝ) s) from hm]
    change (ContinuousLinearMap.snd ℝ (TangentSpace I x) (TangentSpace 𝓘(ℝ, ℝ) s))
        (show TangentSpace I x × TangentSpace 𝓘(ℝ, ℝ) s from
          (show TangentSpace (I.prod 𝓘(ℝ, ℝ)) (x, s) from (v, ρs))) =
      (show TangentSpace 𝓘(ℝ, ℝ) s from ρs)
    change (show TangentSpace 𝓘(ℝ, ℝ) s from ρs) = (show TangentSpace 𝓘(ℝ, ℝ) s from ρs)
    rfl
  have hw₂' : (NormedSpace.fromTangentSpace (s : ℝ))
      ((mfderiv (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) (fun q : M × ℝ => q.2) (x, s))
        (show TangentSpace (I.prod 𝓘(ℝ, ℝ)) (x, s) from (v, ρs))) = ρs := by
    rw [hw₂]
    rfl
  rw [hd, hw₁, hw₂']


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

private theorem familyTangentSection_smul_section
    {I : ModelWithCorners ℝ (MorseModel (m + 1)) H} [I.Boundaryless]
    [IsManifold I (⊤ : WithTop ℕ∞) M] [T2Space M] [SigmaCompactSpace M]
    {W : (x : M) → (s : ℝ) → TangentSpace I x} {ψ : M × ℝ → ℝ} {u : Set (M × ℝ)} {p : M × ℝ}
    (hψ : ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞) ψ u p)
    (hW : ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, MorseModel (m + 1))) (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : M × ℝ => (⟨q.1, W q.1 q.2⟩ : TangentBundle I M)) u p) :
    ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, MorseModel (m + 1))) (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : M × ℝ => (⟨q.1, ψ q • W q.1 q.2⟩ : TangentBundle I M)) u p := by
  let u' : Set (M × ℝ) := u ∩ ((extChartAt I p.1).source ×ˢ Set.univ)
  have hu'sub : u' ⊆ (extChartAt I p.1).source ×ˢ Set.univ := by
    intro q hq
    exact hq.2
  have hψ' : ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞) ψ u' p :=
    hψ.mono (by intro q hq; exact hq.1)
  have hW' : ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, MorseModel (m + 1)))
      (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : M × ℝ => (⟨q.1, W q.1 q.2⟩ : TangentBundle I M)) u' p :=
    hW.mono (by intro q hq; exact hq.1)
  have hiff := familyTangentSection_contMDiffWithinAt_section_iff (I := I)
    (W := W) (a := u') (p := p) hu'sub
  have hfib : ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, MorseModel (m + 1)) (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : M × ℝ => (trivializationAt (MorseModel (m + 1)) (TangentSpace I) p.1
        ⟨q.1, W q.1 q.2⟩).2) u' p :=
    hiff.mp hW'
  have hsmul : ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, MorseModel (m + 1)) (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : M × ℝ => ψ q • (trivializationAt (MorseModel (m + 1)) (TangentSpace I) p.1
        ⟨q.1, W q.1 q.2⟩).2) u' p :=
    hψ'.smul hfib
  let e : Bundle.Trivialization (MorseModel (m + 1))
      (Bundle.TotalSpace.proj : TangentBundle I M → M) :=
    trivializationAt (MorseModel (m + 1)) (TangentSpace I) p.1
  have hlin : (fun q : M × ℝ => (trivializationAt (MorseModel (m + 1)) (TangentSpace I) p.1
      ⟨q.1, ψ q • W q.1 q.2⟩).2) =ᶠ[nhdsWithin p u']
      (fun q : M × ℝ => ψ q • (trivializationAt (MorseModel (m + 1)) (TangentSpace I) p.1
        ⟨q.1, W q.1 q.2⟩).2) := by
    filter_upwards [self_mem_nhdsWithin] with q hq
    have hqbase : q.1 ∈ e.baseSet := by
      have hq' := hu'sub hq
      simpa [← extChartAt_source] using hq'.1
    exact (e.linear ℝ hqbase).2 (ψ q) (W q.1 q.2)
  have hsmul' : ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, MorseModel (m + 1)) (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : M × ℝ => (trivializationAt (MorseModel (m + 1)) (TangentSpace I) p.1
        ⟨q.1, ψ q • W q.1 q.2⟩).2) u' p :=
    hsmul.congr_of_eventuallyEq hlin (by
      exact (e.linear ℝ (mem_baseSet_trivializationAt (MorseModel (m + 1)) (TangentSpace I) p.1)).2
        (ψ p) (W p.1 p.2))
  have hiff' := familyTangentSection_contMDiffWithinAt_section_iff (I := I)
    (W := fun x s => ψ (x, s) • W x s) (a := u') (p := p) hu'sub
  have hgoal : ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, MorseModel (m + 1)))
      (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : M × ℝ => (⟨q.1, ψ q • W q.1 q.2⟩ : TangentBundle I M)) u' p :=
    hiff'.mpr hsmul'
  exact hgoal.mono_of_mem_nhdsWithin (by
    have hC : (extChartAt I p.1).source ×ˢ Set.univ ∈ nhds p :=
      (IsOpen.prod (isOpen_extChartAt_source p.1) isOpen_univ).mem_nhds
        ⟨mem_extChartAt_source p.1, trivial⟩
    exact inter_mem_nhdsWithin u hC)

private theorem familyTangentSection_finsum_of_locallyFinite
    {I : ModelWithCorners ℝ (MorseModel (m + 1)) H} [I.Boundaryless]
    [IsManifold I (⊤ : WithTop ℕ∞) M] [T2Space M] [SigmaCompactSpace M]
    {ι : Type*} {t : ι → (x : M) → (s : ℝ) → TangentSpace I x}
    (ht : LocallyFinite (fun i : ι => {q : M × ℝ | t i q.1 q.2 ≠ 0}))
    (ht' : ∀ i, ContMDiff (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, MorseModel (m + 1))) (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : M × ℝ => (⟨q.1, t i q.1 q.2⟩ : TangentBundle I M))) :
    ContMDiff (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, MorseModel (m + 1))) (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : M × ℝ => (⟨q.1, ∑ᶠ i, t i q.1 q.2⟩ : TangentBundle I M)) := by
  intro p
  rcases ht p with ⟨U, hUp, hfin⟩
  let F : Finset ι := hfin.toFinset
  have hFcover : ∀ i, i ∉ F → t i p.1 p.2 = 0 := by
    intro i hi
    by_contra hnot
    have hmem : ((fun i : ι => {q : M × ℝ | t i q.1 q.2 ≠ 0}) i ∩ U).Nonempty :=
      ⟨p, ⟨by simpa [Function.support] using hnot, mem_of_mem_nhds hUp⟩⟩
    exact hi (by simpa [F] using hfin.mem_toFinset.mpr hmem)
  have hsup : Function.support (fun i : ι => t i p.1 p.2) ⊆ F := by
    intro i hi
    by_contra hnot
    exact False.elim (hi (hFcover i hnot))
  have hsum : (∑ᶠ i, t i p.1 p.2) = ∑ i ∈ F, t i p.1 p.2 := by
    exact finsum_eq_sum_of_support_subset (fun i : ι => t i p.1 p.2) hsup
  have hsumOn : ∀ q ∈ U, (∑ᶠ i, t i q.1 q.2) = ∑ i ∈ F, t i q.1 q.2 := by
    intro q hq
    have hsup' : Function.support (fun i : ι => t i q.1 q.2) ⊆ F := by
      intro i hi
      by_contra hnot
      have hmem : ((fun i : ι => {q : M × ℝ | t i q.1 q.2 ≠ 0}) i ∩ U).Nonempty :=
        ⟨q, ⟨hi, hq⟩⟩
      exact hnot (by simpa [F] using hfin.mem_toFinset.mpr hmem)
    exact finsum_eq_sum_of_support_subset (fun i : ι => t i q.1 q.2) hsup'
  let U' : Set (M × ℝ) := U ∩ ((extChartAt I p.1).source ×ˢ Set.univ)
  have hU'sub : U' ⊆ (extChartAt I p.1).source ×ˢ Set.univ := by
    intro q hq
    exact hq.2
  have hpU' : p ∈ U' := ⟨mem_of_mem_nhds hUp, ⟨mem_extChartAt_source p.1, trivial⟩⟩
  have hfinite : ∀ q ∈ U', (∑ᶠ i, t i q.1 q.2) = ∑ i ∈ F, t i q.1 q.2 := by
    intro q hq
    exact hsumOn q hq.1
  have hfibsum : ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, MorseModel (m + 1)) (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : M × ℝ => (trivializationAt (MorseModel (m + 1)) (TangentSpace I) p.1
        ⟨q.1, ∑ i ∈ F, t i q.1 q.2⟩).2) U' p := by
    let e : Bundle.Trivialization (MorseModel (m + 1))
        (Bundle.TotalSpace.proj : TangentBundle I M → M) :=
      trivializationAt (MorseModel (m + 1)) (TangentSpace I) p.1
    have hlin : ∀ q ∈ U', (e ⟨q.1, ∑ i ∈ F, t i q.1 q.2⟩).2 =
        ∑ i ∈ F, (e ⟨q.1, t i q.1 q.2⟩).2 := by
      intro q hq
      have hqbase : q.1 ∈ e.baseSet := by
        have hq' := hU'sub hq
        simpa [← extChartAt_source] using hq'.1
      let L : TangentSpace I q.1 →+ MorseModel (m + 1) :=
        { toFun := fun v => (e ⟨q.1, v⟩).2
          map_zero' := (e.linear ℝ hqbase).map_zero
          map_add' := (e.linear ℝ hqbase).1 }
      classical
      induction F using Finset.induction_on with
      | empty =>
        simpa only [Finset.sum_empty] using (e.linear ℝ hqbase).map_zero
      | insert i s hi ih =>
        calc
          (e ⟨q.1, ∑ j ∈ insert i s, t j q.1 q.2⟩).2
              = (e ⟨q.1, t i q.1 q.2 + ∑ j ∈ s, t j q.1 q.2⟩).2 := by
                rw [Finset.sum_insert hi]
          _ = (e ⟨q.1, t i q.1 q.2⟩).2 + (e ⟨q.1, ∑ j ∈ s, t j q.1 q.2⟩).2 := by
                exact (e.linear ℝ hqbase).1 (t i q.1 q.2) (∑ j ∈ s, t j q.1 q.2)
          _ = (e ⟨q.1, t i q.1 q.2⟩).2 + ∑ j ∈ s, (e ⟨q.1, t j q.1 q.2⟩).2 := by
                rw [ih]
          _ = ∑ j ∈ insert i s, (e ⟨q.1, t j q.1 q.2⟩).2 := by
                rw [Finset.sum_insert hi]
    have hfibs : ∀ i, ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, MorseModel (m + 1))
        (↑(⊤ : ℕ∞) : WithTop ℕ∞)
        (fun q : M × ℝ => (e ⟨q.1, t i q.1 q.2⟩).2) U' p := by
      intro i
      have hiff := familyTangentSection_contMDiffWithinAt_section_iff (I := I)
        (W := t i) (a := U') (p := p) hU'sub
      exact hiff.mp (((ht' i) p).contMDiffWithinAt (s := U'))
    have hsum' : ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, MorseModel (m + 1)) (↑(⊤ : ℕ∞) : WithTop ℕ∞)
        (fun q : M × ℝ => ∑ i ∈ F, (e ⟨q.1, t i q.1 q.2⟩).2) U' p := by
      classical
      induction F using Finset.induction_on with
      | empty =>
        simpa only [Finset.sum_empty] using
          (contMDiffWithinAt_const : ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, MorseModel (m + 1))
            (↑(⊤ : ℕ∞) : WithTop ℕ∞) (fun _ : M × ℝ => (0 : MorseModel (m + 1))) U' p)
      | insert i s hi ih =>
        simpa only [Finset.sum_insert hi] using (hfibs i).add ih
    exact hsum'.congr_of_eventuallyEq (by
      filter_upwards [self_mem_nhdsWithin] with q hq
      exact hlin q hq) (hlin p hpU')
  have hiffs := familyTangentSection_contMDiffWithinAt_section_iff (I := I)
    (W := fun x s => ∑ᶠ i, t i x s) (a := U') (p := p) hU'sub
  have hsec : ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, MorseModel (m + 1)))
      (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : M × ℝ => (⟨q.1, ∑ᶠ i, t i q.1 q.2⟩ : TangentBundle I M)) U' p := by
    apply hiffs.mpr
    refine hfibsum.congr_of_eventuallyEq ?_ ?_
    · filter_upwards [self_mem_nhdsWithin] with q hq
      rw [hfinite q hq]
    · change (trivializationAt (MorseModel (m + 1)) (TangentSpace I) p.1
        ⟨p.1, ∑ᶠ i, t i p.1 p.2⟩).2 = (trivializationAt (MorseModel (m + 1)) (TangentSpace I) p.1
          ⟨p.1, ∑ i ∈ F, t i p.1 p.2⟩).2
      rw [hsum]
  exact hsec.mono_of_mem_nhdsWithin (by
    have hC : (extChartAt I p.1).source ×ˢ Set.univ ∈ nhds p :=
      (IsOpen.prod (isOpen_extChartAt_source p.1) isOpen_univ).mem_nhds
        ⟨mem_extChartAt_source p.1, trivial⟩
    simpa [U', nhdsWithin_univ] using (Filter.inter_mem hUp hC))

private theorem familyTangentSection_smul_of_tsupport
    {I : ModelWithCorners ℝ (MorseModel (m + 1)) H} [I.Boundaryless]
    [IsManifold I (⊤ : WithTop ℕ∞) M] [T2Space M] [SigmaCompactSpace M]
    {W : (x : M) → (s : ℝ) → TangentSpace I x} {ψ : M × ℝ → ℝ} {u : Set (M × ℝ)}
    (hψ : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞) ψ u)
    (ht : IsOpen u) (ht' : tsupport ψ ⊆ u)
    (hW : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, MorseModel (m + 1))) (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : M × ℝ => (⟨q.1, W q.1 q.2⟩ : TangentBundle I M)) u) :
    ContMDiff (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, MorseModel (m + 1))) (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : M × ℝ => (⟨q.1, ψ q • W q.1 q.2⟩ : TangentBundle I M)) := by
  apply contMDiff_of_contMDiffOn_union_of_isOpen
  · intro p hp
    exact familyTangentSection_smul_section (I := I) (W := W) (ψ := ψ) (u := u) (p := p)
      (hψ p hp) (hW p hp)
  · intro p hp
    have hzero : ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, MorseModel (m + 1)))
        (↑(⊤ : ℕ∞) : WithTop ℕ∞)
        (fun q : M × ℝ => (⟨q.1, (0 : TangentSpace I q.1)⟩ : TangentBundle I M))
        (tsupport ψ)ᶜ p := by
      let u' : Set (M × ℝ) := (tsupport ψ)ᶜ ∩ ((extChartAt I p.1).source ×ˢ Set.univ)
      have hu'sub : u' ⊆ (extChartAt I p.1).source ×ˢ Set.univ := by
        intro q hq
        exact hq.2
      have hp' : p ∈ u' := ⟨hp, ⟨mem_extChartAt_source p.1, trivial⟩⟩
      have hiff := familyTangentSection_contMDiffWithinAt_section_iff (I := I)
        (W := fun _ _ => (0 : TangentSpace I _)) (a := u') (p := p) hu'sub
      let e : Bundle.Trivialization (MorseModel (m + 1))
          (Bundle.TotalSpace.proj : TangentBundle I M → M) :=
        trivializationAt (MorseModel (m + 1)) (TangentSpace I) p.1
      have hfib : ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, MorseModel (m + 1))
          (↑(⊤ : ℕ∞) : WithTop ℕ∞)
          (fun q : M × ℝ => (e ⟨q.1, (0 : TangentSpace I q.1)⟩).2) u' p := by
        have hconst : ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, MorseModel (m + 1))
            (↑(⊤ : ℕ∞) : WithTop ℕ∞) (fun _ : M × ℝ => (0 : MorseModel (m + 1))) u' p :=
          contMDiffWithinAt_const
        have heq : (fun q : M × ℝ => (e ⟨q.1, (0 : TangentSpace I q.1)⟩).2) =ᶠ[nhdsWithin p u']
            (fun _ : M × ℝ => (0 : MorseModel (m + 1))) := by
          filter_upwards [self_mem_nhdsWithin] with q hq
          have hqbase : q.1 ∈ e.baseSet := by
            have hq' := hu'sub hq
            simpa [← extChartAt_source] using hq'.1
          exact (e.linear ℝ hqbase).map_zero
        exact hconst.congr_of_eventuallyEq heq (by
          exact (e.linear ℝ (mem_baseSet_trivializationAt (MorseModel (m + 1)) (TangentSpace I) p.1)).map_zero)
      have hgoal : ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, MorseModel (m + 1)))
          (↑(⊤ : ℕ∞) : WithTop ℕ∞)
          (fun q : M × ℝ => (⟨q.1, (0 : TangentSpace I q.1)⟩ : TangentBundle I M)) u' p :=
        hiff.mpr hfib
      exact hgoal.mono_of_mem_nhdsWithin (by
        have hC : (extChartAt I p.1).source ×ˢ Set.univ ∈ nhds p :=
          (IsOpen.prod (isOpen_extChartAt_source p.1) isOpen_univ).mem_nhds
            ⟨mem_extChartAt_source p.1, trivial⟩
        exact inter_mem_nhdsWithin (tsupport ψ)ᶜ hC)
    exact hzero.congr_of_eventuallyEq (by
      filter_upwards [self_mem_nhdsWithin] with q hq
      simp [image_eq_zero_of_notMem_tsupport hq]) (by
      simp [image_eq_zero_of_notMem_tsupport hp])
  · exact Set.compl_subset_iff_union.mp <| Set.compl_subset_compl.mpr ht'
  · exact ht
  · exact (isClosed_tsupport ψ).isOpen_compl

private theorem suspensionSection_contMDiff
    {I : ModelWithCorners ℝ (MorseModel (m + 1)) H} [I.Boundaryless]
    [IsManifold I (⊤ : WithTop ℕ∞) M] [T2Space M] [SigmaCompactSpace M]
    {W : (x : M) → (s : ℝ) → TangentSpace I x}
    (hW : ContMDiff (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, MorseModel (m + 1))) (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : M × ℝ => (⟨q.1, W q.1 q.2⟩ : TangentBundle I M))) :
    ContMDiff (I.prod 𝓘(ℝ, ℝ)) ((I.prod 𝓘(ℝ, ℝ)).prod 𝓘(ℝ, (MorseModel (m + 1)) × ℝ))
      (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : M × ℝ => (⟨q, (show TangentSpace (I.prod 𝓘(ℝ, ℝ)) q from
        (W q.1 q.2, (1 : ℝ)))⟩ : TangentBundle (I.prod 𝓘(ℝ, ℝ)) (M × ℝ))) := by
  have hψ : ContMDiff (I.prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : M × ℝ => (⟨q.2, (1 : TangentSpace 𝓘(ℝ, ℝ) q.2)⟩ : TangentBundle 𝓘(ℝ, ℝ) ℝ)) := by
    have hone : ContMDiff 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) (↑(⊤ : ℕ∞) : WithTop ℕ∞)
        (fun t : ℝ => (⟨t, (1 : TangentSpace 𝓘(ℝ, ℝ) t)⟩ : TangentBundle 𝓘(ℝ, ℝ) ℝ)) := by
      intro t₀
      rw [Bundle.contMDiffAt_section]
      simpa using (contMDiffAt_const (c := (1 : ℝ)))
    exact hone.comp contMDiff_snd
  have hpair : ContMDiff (I.prod 𝓘(ℝ, ℝ))
      ((I.prod 𝓘(ℝ, MorseModel (m + 1))).prod (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)))
      (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : M × ℝ =>
        ((⟨q.1, W q.1 q.2⟩ : TangentBundle I M),
          (⟨q.2, (1 : TangentSpace 𝓘(ℝ, ℝ) q.2)⟩ : TangentBundle 𝓘(ℝ, ℝ) ℝ))) :=
    hW.prodMk hψ
  have hsymm : ContMDiff ((I.prod 𝓘(ℝ, MorseModel (m + 1))).prod (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)))
      ((I.prod 𝓘(ℝ, ℝ)).prod 𝓘(ℝ, (MorseModel (m + 1)) × ℝ))
      (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      ((equivTangentBundleProd I M 𝓘(ℝ, ℝ) ℝ).symm) := by
    haveI : IsManifold I (1 : WithTop ℕ∞) M := IsManifold.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ ∞)
    haveI : IsManifold 𝓘(ℝ, ℝ) (1 : WithTop ℕ∞) ℝ := IsManifold.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ ∞)
    exact contMDiff_equivTangentBundleProd_symm
  exact hsymm.comp hpair

private lemma sublevel_const_of_deriv_eq_zero_ge'
    {f : ℝ → ℝ} (hf : DifferentiableOn ℝ f Set.univ) {L : ℝ} (_hL : 0 < L) {a : ℝ}
    (hfa : f a ∈ Set.Ioo (-L) L)
    (hderiv : ∀ t : ℝ, f t ∈ Set.Icc (-L) L → deriv f t = 0)
    {t₁ : ℝ} (ht₁ : a ≤ t₁) (hgt : f a < f t₁) : f t₁ = f a := by
  let S : Set ℝ := {u : ℝ | u ∈ Set.Icc a t₁ ∧ f a < f u}
  have hSne : S.Nonempty := ⟨t₁, ⟨⟨ht₁, le_rfl⟩, hgt⟩⟩
  have hSbdd : BddBelow S := ⟨a, by intro u hu; exact hu.1.1⟩
  let t₀ : ℝ := sInf S
  have ht₀a : a ≤ t₀ := le_csInf hSne (by intro u hu; exact hu.1.1)
  have ht₀t₁ : t₀ ≤ t₁ := csInf_le hSbdd ⟨⟨ht₁, le_rfl⟩, hgt⟩
  have hcont : ContinuousAt f t₀ := (hf.continuousOn t₀ trivial).continuousAt Filter.univ_mem
  have hf₀_ge : f a ≤ f t₀ := by
    have hcl : t₀ ∈ closure S := csInf_mem_closure hSne hSbdd
    have hright : ∀ᶠ u in nhdsWithin t₀ S, f a ≤ f u := by
      rw [Filter.eventually_iff_exists_mem]
      exact ⟨S ∩ Set.univ, inter_mem_nhdsWithin S Filter.univ_mem, by
        intro u hu
        exact le_of_lt (hu.1).2⟩
    have htend : Tendsto f (nhdsWithin t₀ S) (nhds (f t₀)) := hcont.tendsto.mono_left nhdsWithin_le_nhds
    haveI : (nhdsWithin t₀ S).NeBot := mem_closure_iff_nhdsWithin_neBot.mp hcl
    exact ge_of_tendsto htend hright
  have hsub : ∀ u : ℝ, a < u → u < t₀ → f u ≤ f a := by
    intro u hu₁ hu₂
    by_cases huS : u ∈ S
    · have : t₀ ≤ u := csInf_le hSbdd huS
      linarith
    · have hucc : u ∈ Set.Icc a t₁ := ⟨le_of_lt hu₁, le_of_lt (lt_of_lt_of_le hu₂ ht₀t₁)⟩
      exact le_of_not_gt (fun hfu => huS ⟨hucc, hfu⟩)
  have hf₀_le : f t₀ ≤ f a := by
    by_cases ht₀a' : a = t₀
    · simp [ht₀a']
    · have hlt₀ : a < t₀ := lt_of_le_of_ne ht₀a (by intro h; exact ht₀a' h)
      have hleft : ∀ᶠ u in nhdsWithin t₀ (Set.Iio t₀), f u ≤ f a := by
        have hU : {u : ℝ | a < u} ∈ nhds t₀ := isOpen_Ioi.mem_nhds hlt₀
        rw [Filter.eventually_iff_exists_mem]
        exact ⟨Set.Iio t₀ ∩ {u : ℝ | a < u}, inter_mem_nhdsWithin (Set.Iio t₀) hU, by
          intro u hu
          exact hsub u hu.2 hu.1⟩
      have htend : Tendsto f (nhdsWithin t₀ (Set.Iio t₀)) (nhds (f t₀)) :=
        hcont.tendsto.mono_left nhdsWithin_le_nhds
      have ht₀cl : t₀ ∈ closure (Set.Iio t₀) := by
        rw [closure_Iio]
        change t₀ ≤ t₀
        exact le_rfl
      haveI : (nhdsWithin t₀ (Set.Iio t₀)).NeBot := mem_closure_iff_nhdsWithin_neBot.mp ht₀cl
      exact le_of_tendsto htend hleft
  have hf₀ : f t₀ = f a := le_antisymm hf₀_le hf₀_ge
  have hinner : f t₀ ∈ Set.Ioo (-L) L := by
    rw [hf₀]
    exact hfa
  have hloc : ∀ᶠ u in nhds t₀, f u = f t₀ := by
    have hopen : {u : ℝ | f u ∈ Set.Ioo (-L) L} ∈ nhds t₀ :=
      hcont.preimage_mem_nhds (isOpen_Ioo.mem_nhds hinner)
    rcases Metric.mem_nhds_iff.mp hopen with ⟨δ, hδ, hball⟩
    have hdOn : ∀ v ∈ Metric.ball t₀ δ, deriv f v = 0 := by
      intro v hv
      exact hderiv v ⟨le_of_lt (hball hv).1, le_of_lt (hball hv).2⟩
    filter_upwards [Metric.ball_mem_nhds t₀ hδ] with u hu
    exact (isOpen_Ioo.is_const_of_deriv_eq_zero isPreconnected_Ioo
      (hf.mono (by intro v hv; trivial))
      (by
        intro v hv
        exact hdOn v (by simpa [Real.ball_eq_Ioo] using hv))
      (by simpa [Real.ball_eq_Ioo] using hu)
      (by simpa [Real.ball_eq_Ioo] using (Metric.mem_ball_self (α := ℝ) (ε := δ) hδ : t₀ ∈ Metric.ball t₀ δ)))
  rcases hloc.exists_mem with ⟨U, hU, hball⟩
  rcases Metric.mem_nhds_iff.mp hU with ⟨δ, hδ, hballU⟩
  have hSarb : ∃ u ∈ S, u < t₀ + δ := by
    by_contra hnot
    have hleall : ∀ u ∈ S, t₀ + δ ≤ u := by
      intro u hu
      exact le_of_not_gt (fun h => hnot ⟨u, hu, h⟩)
    have : t₀ + δ ≤ sInf S := le_csInf hSne hleall
    linarith
  rcases hSarb with ⟨u, huS, hult⟩
  have hδlt : u > t₀ := by
    by_contra hnot'
    have hu_le : u ≤ t₀ := le_of_not_gt hnot'
    have ht₀_le : t₀ ≤ u := csInf_le hSbdd huS
    have hu_eq : u = t₀ := le_antisymm hu_le ht₀_le
    have hfua : f a < f u := huS.2
    have hcontr : f a < f a := by
      calc
        f a = f t₀ := hf₀.symm
        _ = f u := by rw [hu_eq]
        _ > f a := hfua
    exact (lt_irrefl (f a)) hcontr
  have hu_near : u ∈ Metric.ball t₀ δ := by
    rw [Metric.mem_ball, Real.dist_eq]
    rw [abs_of_pos (sub_pos.mpr hδlt)]
    linarith [hult]
  have hfu : f u = f t₀ := hball u (hballU hu_near)
  have hfua' : f a < f u := huS.2
  have hcontr : f a < f a := by
    calc
      f a = f t₀ := hf₀.symm
      _ = f u := hfu.symm
      _ > f a := hfua'
  exact False.elim (lt_irrefl (f a) hcontr)

private lemma sublevel_const_of_deriv_eq_zero_ge
    {f : ℝ → ℝ} (hf : DifferentiableOn ℝ f Set.univ) {L : ℝ} (hL : 0 < L) {a : ℝ}
    (hfa : f a ∈ Set.Ioo (-L) L)
    (hderiv : ∀ t : ℝ, f t ∈ Set.Icc (-L) L → deriv f t = 0) :
    ∀ t : ℝ, a ≤ t → f t = f a := by
  intro t₁ ht₁
  by_cases heq : f t₁ = f a
  · exact heq
  · rcases lt_or_gt_of_ne heq with hlt | hgt
    · let g : ℝ → ℝ := fun u => -f u
      have hg : DifferentiableOn ℝ g Set.univ := by
        intro u hu
        exact hf u hu |>.neg
      have hgfa : g a ∈ Set.Ioo (-L) L := by
        change -f a ∈ Set.Ioo (-L) L
        constructor
        · exact neg_lt_neg hfa.2
        · simpa using neg_lt_neg hfa.1
      have hgderiv : ∀ u : ℝ, g u ∈ Set.Icc (-L) L → deriv g u = 0 := by
        intro u hu
        have h0 : deriv g u = -deriv f u := by
          dsimp [g]
          simpa only [neg_one_smul] using (deriv_const_smul (c := (-1 : ℝ)) (f := f) (x := u) (hf := (hf u trivial).differentiableAt Filter.univ_mem))
        rw [h0]
        have hu' : f u ∈ Set.Icc (-L) L := by
          dsimp [g] at hu
          constructor
          · simpa using (neg_le_neg hu.2)
          · simpa using (neg_le_neg hu.1)
        rw [hderiv u hu']
        simp
      have hgmain := sublevel_const_of_deriv_eq_zero_ge' hg hL hgfa hgderiv ht₁ (by
        dsimp [g]
        exact neg_lt_neg hlt)
      have hgval : g t₁ = -f t₁ := rfl
      have hgvala : g a = -f a := rfl
      rw [hgval, hgvala] at hgmain
      exact neg_inj.mp hgmain
    · exact sublevel_const_of_deriv_eq_zero_ge' hf hL hfa hderiv ht₁ hgt

private lemma sublevel_const_of_deriv_eq_zero_on_interval
    {f : ℝ → ℝ} (hf : DifferentiableOn ℝ f Set.univ) {L : ℝ} (hL : 0 < L) {a : ℝ}
    (hfa : f a ∈ Set.Ioo (-L) L)
    (hderiv : ∀ t : ℝ, f t ∈ Set.Icc (-L) L → deriv f t = 0) :
    ∀ t : ℝ, f t = f a := by
  intro t₁
  by_cases ht₁a : a ≤ t₁
  · exact sublevel_const_of_deriv_eq_zero_ge hf hL hfa hderiv t₁ ht₁a
  · have hlt : t₁ < a := lt_of_not_ge ht₁a
    let g : ℝ → ℝ := fun u => f (a - u)
    have hg : DifferentiableOn ℝ g Set.univ := by
      intro u hu
      dsimp [g]
      refine DifferentiableWithinAt.comp (𝕜 := ℝ) (E := ℝ) (F := ℝ) (G := ℝ)
        (f := fun u : ℝ => a - u) (g := f) (s := Set.univ) (t := Set.univ) (x := u) ?_ ?_ ?_
      · exact hf (a - u) trivial
      · exact DifferentiableWithinAt.sub (f := fun _ : ℝ => a) (g := fun u : ℝ => u)
          (differentiableWithinAt_const (c := a) (x := u)) differentiableWithinAt_id
      · intro y hy; trivial
    have hgfa : g 0 ∈ Set.Ioo (-L) L := by
      simpa [g] using hfa
    have hgderiv : ∀ u : ℝ, g u ∈ Set.Icc (-L) L → deriv g u = 0 := by
      intro u hu
      have h0 : deriv g u = -deriv f (a - u) := by
        dsimp [g]
        have hin : DifferentiableAt ℝ (fun u : ℝ => a - u) u := by fun_prop
        have hout : DifferentiableAt ℝ f (a - u) :=
          (hf (a - u) trivial).differentiableAt Filter.univ_mem
        change deriv (f ∘ (fun u : ℝ => a - u)) u = -deriv f (a - u)
        rw [deriv_comp u hout hin]
        · have hd : deriv (fun u : ℝ => a - u) u = -1 := by
            simpa [deriv_id] using (deriv_const_sub (c := a) (f := fun u : ℝ => u) (x := u))
          rw [hd]
          simp
      rw [h0]
      rw [hderiv (a - u) hu]
      simp
    have hle : 0 ≤ a - t₁ := by linarith
    have hmain := sublevel_const_of_deriv_eq_zero_ge hg hL hgfa hgderiv (a - t₁) hle
    have hgval : g (a - t₁) = f t₁ := by
      dsimp [g]
      ring_nf
    rw [hgval] at hmain
    simpa [g] using hmain

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

theorem exists_unitSpeedFamilyVectorField_on_compact
    (I : ModelWithCorners ℝ (MorseModel (m + 1)) H) [I.Boundaryless]
    [IsManifold I (⊤ : WithTop ℕ∞) M] [T2Space M] [SigmaCompactSpace M]
    (F : M → ℝ → ℝ) (hF : ContMDiff (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : M × ℝ => F q.1 q.2)) (K : Set (M × ℝ)) (hcompact : IsCompact K)
    (hregular : ∀ p ∈ K, ¬ IsCriticalPointAt I (fun x => F x p.2) p.1) :
    ∃ V : (x : M) → (s : ℝ) → TangentSpace I x,
      ContMDiff (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, MorseModel (m + 1))) (↑(⊤ : ℕ∞) : WithTop ℕ∞)
        (fun q : M × ℝ => (⟨q.1, V q.1 q.2⟩ : TangentBundle I M)) ∧
      IsCompact (tsupport (fun q : M × ℝ => V q.1 q.2)) ∧
      (∀ p ∈ K, (NormedSpace.fromTangentSpace (F p.1 p.2))
        ((mfderiv I 𝓘(ℝ, ℝ) (fun x : M => F x p.2) p.1) (V p.1 p.2)) = -1) ∧
      (∀ q : M × ℝ, -1 ≤ (NormedSpace.fromTangentSpace (F q.1 q.2))
          ((mfderiv I 𝓘(ℝ, ℝ) (fun x : M => F x q.2) q.1) (V q.1 q.2)) ∧
        (NormedSpace.fromTangentSpace (F q.1 q.2))
          ((mfderiv I 𝓘(ℝ, ℝ) (fun x : M => F x q.2) q.1) (V q.1 q.2)) ≤ 0) := by
  let K : Set (M × ℝ) := K
  have hpts : ∀ x : K, ∃ U : Set (M × ℝ), x.1 ∈ U ∧ IsOpen U ∧
      ∃ W : (x : M) → (s : ℝ) → TangentSpace I x,
        (∀ y ∈ U, (NormedSpace.fromTangentSpace (F y.1 y.2))
          ((mfderiv I 𝓘(ℝ, ℝ) (fun x : M => F x y.2) y.1) (W y.1 y.2)) = -1) ∧
        ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, MorseModel (m + 1))) (↑(⊤ : ℕ∞) : WithTop ℕ∞)
          (fun y : M × ℝ => (⟨y.1, W y.1 y.2⟩ : TangentBundle I M)) U :=
    fun x => localUnitSpeedFamilyVectorField_at_noncritical I F hF (hregular x x.2)
  choose U hUmem hUopen W hWdf hWsec using hpts
  have hKclosed : IsClosed K := hcompact.isClosed
  haveI : LocallyCompactSpace H := I.locallyCompactSpace
  haveI : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace H M
  rcases exists_open_between_and_isCompact_closure hcompact isOpen_univ (subset_univ K)
    with ⟨W₀, hW₀open, hKW₀, hW₀cl, hW₀compact⟩
  let U' : K → Set (M × ℝ) := fun x => U x ∩ W₀
  have hU'mem : ∀ x : K, x.1 ∈ U' x := fun x => ⟨hUmem x, hKW₀ x.2⟩
  have hU'open : ∀ x : K, IsOpen (U' x) := fun x => (hUopen x).inter hW₀open
  have hcov : K ⊆ ⋃ x : K, U' x := by
    intro y hy
    exact Set.mem_iUnion_of_mem ⟨y, hy⟩ (hU'mem ⟨y, hy⟩)
  rcases SmoothPartitionOfUnity.exists_isSubordinate (I := I.prod 𝓘(ℝ, ℝ)) (s := K) (U := U')
    (hs := hKclosed) (ho := hU'open) (hU := hcov) with ⟨ρ, hρsub⟩
  let V : (x : M) → (s : ℝ) → TangentSpace I x := fun y s =>
    ∑ᶠ x : K, (ρ x (y, s) : ℝ) • (W x y s : TangentSpace I y)
  have hdfsum : ∀ y : M × ℝ,
      (NormedSpace.fromTangentSpace (F y.1 y.2)) ((mfderiv I 𝓘(ℝ, ℝ) (fun x : M => F x y.2) y.1) (V y.1 y.2)) =
        -(∑ᶠ x : K, (ρ x y : ℝ)) := by
    intro y
    let L : TangentSpace I y.1 →L[ℝ] ℝ :=
      (NormedSpace.fromTangentSpace (𝕜 := ℝ) (F y.1 y.2) : TangentSpace 𝓘(ℝ, ℝ) (F y.1 y.2) →L[ℝ] ℝ).comp
        (mfderiv I 𝓘(ℝ, ℝ) (fun x : M => F x y.2) y.1)
    have hVdef : (NormedSpace.fromTangentSpace (F y.1 y.2)) ((mfderiv I 𝓘(ℝ, ℝ) (fun x : M => F x y.2) y.1) (V y.1 y.2)) = L (V y.1 y.2) := by
      simp [L]
    rw [hVdef]
    have hfinSuppρ : Function.HasFiniteSupport (fun x : K => ρ x y) := by
      have hlf : LocallyFinite (fun x : K => {z : M × ℝ | ρ x z ≠ 0}) := ρ.locallyFinite
      have hlfy := hlf y
      rcases hlfy with ⟨N, hN, hfinN⟩
      have hsub : (Function.support fun x : K => ρ x y) ⊆
          {x : K | ((fun x : K => {z : M × ℝ | ρ x z ≠ 0}) x ∩ N).Nonempty} := by
        intro x hx
        rw [Function.support] at hx
        exact ⟨y, ⟨hx, mem_of_mem_nhds hN⟩⟩
      exact Set.Finite.subset hfinN hsub
    have hfinSupp : Function.HasFiniteSupport (fun x : K => ρ x y • W x y.1 y.2) := by
      exact Set.Finite.subset hfinSuppρ (by intro x hx; exact fun hρ0 => hx (by simp [hρ0]))
    have hlin : L (V y.1 y.2) = ∑ᶠ x : K, L (ρ x y • W x y.1 y.2) := by
      dsimp [V]
      have hmap := (AddMonoidHom.map_finsum (g := (L : TangentSpace I y.1 →+ ℝ)) (hf := hfinSupp))
      simpa using hmap
    rw [hlin]
    have hterm : ∀ x : K, L (ρ x y • W x y.1 y.2) = ρ x y • L (W x y.1 y.2) := by
      intro x
      rw [map_smul]
    have hrew : (∑ᶠ x : K, L (ρ x y • W x y.1 y.2)) = ∑ᶠ x : K, ρ x y • (-1 : ℝ) := by
      apply finsum_congr
      intro x
      rw [hterm x]
      by_cases hyU : y ∈ U' x
      · have hdf := hWdf x y hyU.1
        have hLval : L (W x y.1 y.2) = -1 := by
          dsimp [L]
          simpa using hdf
        rw [hLval]
      · have hρ0 : ρ x y = 0 := by
          have hts' : y ∉ tsupport (ρ x) := fun h => hyU (hρsub x h)
          have hnot : y ∉ Function.support (ρ x) := fun hs => hts' (subset_closure hs)
          by_contra h
          exact hnot (by simpa [Function.support] using h)
        simp [hρ0]
    rw [hrew]
    have hsum : (∑ᶠ x : K, ρ x y • (-1 : ℝ)) = -(∑ᶠ x : K, (ρ x y : ℝ)) := by
      have hsmul' : (∑ᶠ x : K, ρ x y • (-1 : ℝ)) = (∑ᶠ x : K, ρ x y) • (-1 : ℝ) := by
        exact (finsum_smul' hfinSuppρ (-1 : ℝ)).symm
      rw [hsmul']
      simp
    exact hsum
  refine ⟨V, ?_, ?_, ?_, ?_⟩
  · have hsummand : ∀ x : K, ContMDiff (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, MorseModel (m + 1)))
        (↑(⊤ : ℕ∞) : WithTop ℕ∞)
        (fun y : M × ℝ => (⟨y.1, ρ x y • W x y.1 y.2⟩ : TangentBundle I M)) := by
      intro x
      have hρOn : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞)
          (ρ x : M × ℝ → ℝ) (U' x) := by
        have hc' : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞)
            (ρ x : M × ℝ → ℝ) Set.univ := by
          simpa using (ρ x).property.contMDiffOn
        exact (hc'.mono (subset_univ _)).of_le le_rfl
      exact familyTangentSection_smul_of_tsupport (I := I) (W := W x) (ψ := ρ x) (u := U' x)
        hρOn (hU'open x) (hρsub x) ((hWsec x).mono (by intro y hy; exact hy.1))
    have hfin : LocallyFinite (fun x : K => {y : M × ℝ | ρ x y • W x y.1 y.2 ≠ 0}) := by
      exact ρ.locallyFinite.subset (fun x => by
        intro y hy
        have hρy : ρ x y ≠ 0 := by
          intro hρ0
          apply hy
          simp [hρ0]
        exact hρy)
    simpa [V] using (familyTangentSection_finsum_of_locallyFinite (I := I)
      (t := fun x : K => fun y s => ρ x (y, s) • W x y s) hfin hsummand)
  · have hmem : ∀ y, y ∈ Function.support (fun q : M × ℝ => V q.1 q.2) → y ∈ ⋃ x : K, tsupport (ρ x) := by
      intro y hy
      by_contra hnot
      have hy' : V y.1 y.2 ≠ 0 := hy
      apply hy'
      have hall : ∀ x : K, (ρ x y : ℝ) • (W x y.1 y.2 : TangentSpace I y.1) = 0 := by
        intro x
        by_contra hx
        apply hnot
        exact Set.mem_iUnion.mpr ⟨x, subset_closure (by
          intro hρ0
          apply hx
          simp [hρ0])⟩
      have hV0 : (∑ᶠ x : K, (ρ x y : ℝ) • (W x y.1 y.2 : TangentSpace I y.1)) = 0 :=
        finsum_eq_zero_of_forall_eq_zero hall
      simpa [V] using hV0
    have hsupp₀ : Function.support (fun q : M × ℝ => V q.1 q.2) ⊆ W₀ := by
      intro y hy
      rcases Set.mem_iUnion.mp (hmem y hy) with ⟨x, hx⟩
      exact (hρsub x hx).2
    have hts : tsupport (fun q : M × ℝ => V q.1 q.2) ⊆ closure W₀ := closure_mono hsupp₀
    exact hW₀compact.of_isClosed_subset (isClosed_tsupport (fun q : M × ℝ => V q.1 q.2)) hts
  · intro y hy
    rw [hdfsum y]
    have hs1 : (∑ᶠ x : K, ρ x y) = 1 := ρ.sum_eq_one hy
    rw [hs1]
  · intro y
    rw [hdfsum y]
    have hnonneg : 0 ≤ ∑ᶠ x : K, (ρ x y : ℝ) := finsum_nonneg (fun x => ρ.nonneg x y)
    have hle1 : (∑ᶠ x : K, (ρ x y : ℝ)) ≤ 1 := ρ.sum_le_one y
    constructor <;> linarith


end
end DifferentialGeometry.Topology.Morse
