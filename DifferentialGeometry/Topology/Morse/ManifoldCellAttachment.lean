import DifferentialGeometry.Topology.Morse.CellAttachment
import DifferentialGeometry.Topology.Morse.Manifold

namespace DifferentialGeometry.Topology.Morse

open Manifold
open scoped Topology Manifold

noncomputable section

namespace ManifoldCellAttachment

open CellAttachment

def homeoToOpenPartialHomeomorph {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (h : X ≃ₜ Y) : OpenPartialHomeomorph X Y where
  toPartialEquiv :=
    { toFun := h
      invFun := h.symm
      source := Set.univ
      target := Set.univ
      map_source' := by intro x hx; trivial
      map_target' := by intro y hy; trivial
      left_inv' := by intro x hx; exact h.left_inv x
      right_inv' := by intro y hy; exact h.right_inv y }
  open_source := isOpen_univ
  open_target := isOpen_univ
  continuousOn_toFun := h.continuous.continuousOn
  continuousOn_invFun := h.symm.continuous.continuousOn

def openPartialHomeomorphSourceHomeo {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (ψ : OpenPartialHomeomorph X Y) : ψ.source ≃ₜ ψ.target :=
  { toFun := fun x => ⟨ψ x, ψ.map_source x.2⟩
    invFun := fun y => ⟨ψ.symm y, ψ.map_target y.2⟩
    left_inv := by
      intro x
      apply Subtype.ext
      exact ψ.left_inv x.2
    right_inv := by
      intro y
      apply Subtype.ext
      exact ψ.right_inv y.2
    continuous_toFun := by
      exact (Topology.IsInducing.subtypeVal.continuous_iff).2
        (continuousOn_iff_continuous_restrict.mp ψ.continuousOn_toFun)
    continuous_invFun := by
      exact (Topology.IsInducing.subtypeVal.continuous_iff).2
        (continuousOn_iff_continuous_restrict.mp ψ.continuousOn_invFun) }

def addHomeo (n : ℕ) (a : MorseModel n) : MorseModel n ≃ₜ MorseModel n where
  toFun := fun z => a + z
  invFun := fun z => z - a
  left_inv := by intro z; simp
  right_inv := by intro z; simp
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

def reindexHomeo {n : ℕ} (σe : Fin n ≃ Fin n) : MorseModel n ≃ₜ MorseModel n where
  toFun := fun y => y ∘ σe.symm
  invFun := fun y => y ∘ σe
  left_inv := by
    intro y
    funext i
    simp
  right_inv := by
    intro y
    funext i
    simp
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

theorem supNorm_le_morseNorm {n : ℕ} (y : MorseModel n) : ‖y‖ ≤ morseNorm n y := by
  rw [Pi.norm_def]
  exact_mod_cast (Finset.sup_le (s := Finset.univ) (f := fun i : Fin n => ‖y i‖₊)
    (a := ⟨morseNorm n y, norm_nonneg _⟩) (by
      intro i hi
      exact PiLp.norm_apply_le (x := (WithLp.toLp 2 y : EuclideanSpace ℝ (Fin n))) i))

def subtypeSubtypeOfSubset {X : Type} [TopologicalSpace X] {s t : Set X} (hst : s ⊆ t) :
    {x : X // x ∈ s} ≃ₜ {x : {x : X // x ∈ t} // x.1 ∈ s} where
  toFun := fun x => ⟨⟨x.1, hst x.2⟩, x.2⟩
  invFun := fun x => ⟨x.1.1, x.2⟩
  left_inv := by intro x; rfl
  right_inv := by intro x; rfl
  continuous_toFun := by
    fun_prop
  continuous_invFun := by
    fun_prop

def subtypeSubtypeValHomeo {X : Type} [TopologicalSpace X] {s t : Set X} (ht : t ⊆ s) :
    {x : {y : X // y ∈ s} // x.1 ∈ t} ≃ₜ {x : X // x ∈ t} where
  toFun := fun x => ⟨x.1.1, x.2⟩
  invFun := fun x => ⟨⟨x.1, ht x.2⟩, x.2⟩
  left_inv := by intro x; rfl
  right_inv := by intro x; rfl
  continuous_toFun := by
    fun_prop
  continuous_invFun := by
    fun_prop

def homeoRestrictPred {A B : Type} [TopologicalSpace A] [TopologicalSpace B] (h : A ≃ₜ B)
    (p : A → Prop) (q : B → Prop) (hpq : ∀ a, p a ↔ q (h a)) :
    {a : A // p a} ≃ₜ {b : B // q b} where
  toFun := fun a => ⟨h a.1, (hpq a.1).1 a.2⟩
  invFun := fun b => ⟨h.symm b.1, (hpq (h.symm b.1)).2 (by
    have hb : q b.1 := b.2
    have hround : h (h.symm b.1) = b.1 := h.apply_symm_apply b.1
    simpa [hround] using hb)⟩
  left_inv := by
    intro a
    apply Subtype.ext
    exact h.symm_apply_apply a.1
  right_inv := by
    intro b
    apply Subtype.ext
    exact h.apply_symm_apply b.1
  continuous_toFun := by
    fun_prop
  continuous_invFun := by
    fun_prop

def subtypeAndNestedHomeo {X : Type} [TopologicalSpace X] (p q : X → Prop) :
    {x : X // p x ∧ q x} ≃ₜ {x : {x : X // p x} // q x.1} where
  toFun := fun x => ⟨⟨x.1, x.2.1⟩, x.2.2⟩
  invFun := fun x => ⟨x.1.1, ⟨x.1.2, x.2⟩⟩
  left_inv := by intro x; rfl
  right_inv := by intro x; rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

def andSwapHomeo {X : Type} [TopologicalSpace X] (p q : X → Prop) :
    {x : X // p x ∧ q x} ≃ₜ {x : X // q x ∧ p x} where
  toFun := fun x => ⟨x.1, ⟨x.2.2, x.2.1⟩⟩
  invFun := fun x => ⟨x.1, ⟨x.2.2, x.2.1⟩⟩
  left_inv := by intro x; rfl
  right_inv := by intro x; rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

theorem exists_reindexEquiv {n k : ℕ} (hk : k ≤ n) (w : Fin n → ℝ)
    (hw : ∀ i, w i = -1 ∨ w i = 1) (hcard : {i : Fin n | w i < 0}.ncard = k) :
    ∃ σe : Fin n ≃ Fin n,
      (∀ i : Fin k, w (σe (negIdx hk i)) = -1) ∧
      (∀ j : Fin (n - k), w (σe (posIdx hk j)) = 1) := by
  let negs : Finset (Fin n) := Finset.univ.filter (fun i => w i = -1)
  let poss : Finset (Fin n) := Finset.univ.filter (fun i => w i = 1)
  have hneg_card : negs.card = k := by
    have hset : {i : Fin n | w i < 0} = {i : Fin n | w i = -1} := by
      ext i
      constructor
      · intro hi
        rcases hw i with h | h
        · exact h
        · exfalso
          norm_num [h] at hi
      · intro hi
        change w i < 0
        rw [hi]
        norm_num
    have hcard' : ({i : Fin n | w i = -1} : Set (Fin n)).ncard = k := by
      simpa [hset] using hcard
    have hto : ({i : Fin n | w i = -1} : Set (Fin n)).toFinset = negs := by
      ext i
      simp [negs]
    have hncard := Set.ncard_eq_toFinset_card ({i : Fin n | w i = -1} : Set (Fin n)) (Set.toFinite _)
    have hto' : (Set.toFinite ({i : Fin n | w i = -1} : Set (Fin n))).toFinset = negs := by
      ext i
      simp [negs]
    rw [← hto']
    exact hncard.symm.trans hcard'
  have hdisj : Disjoint negs poss := by
    rw [Finset.disjoint_left]
    intro i hi hp
    have h1 : w i = -1 := (Finset.mem_filter.mp hi).2
    have h2 : w i = 1 := (Finset.mem_filter.mp hp).2
    linarith
  have hpos_card : poss.card = n - k := by
    have hunion : negs ∪ poss = Finset.univ := by
      ext i
      rcases hw i with h | h
      · simp [negs, poss, h]
      · simp [negs, poss, h]
    have hcard' : negs.card + poss.card = n := by
      rw [← Finset.card_union_of_disjoint hdisj, hunion, Finset.card_univ, Fintype.card_fin]
    omega
  let e0 : Sum (Fin k) (Fin (n - k)) ≃ Fin n :=
    { toFun := Sum.elim (negIdx hk) (posIdx hk)
      invFun := fun z => if h : z.val < k then Sum.inl ⟨z.val, h⟩ else Sum.inr ⟨z.val - k, by
        have hkle : k ≤ z.val := le_of_not_gt h
        have hz : z.val < n := z.isLt
        omega⟩
      left_inv := by
        intro s
        cases s with
        | inl i => simp [negIdx]
        | inr j => simp [posIdx]
      right_inv := by
        intro z
        by_cases h : z.val < k
        · simp [h, negIdx]
        · apply Fin.ext
          simp [h, posIdx]
          omega }
  let e1 : Sum (Fin k) (Fin (n - k)) ≃ Fin n :=
    { toFun := Sum.elim (fun i : Fin k => ((negs.orderIsoOfFin hneg_card) i : Fin n))
        (fun j : Fin (n - k) => ((poss.orderIsoOfFin hpos_card) j : Fin n))
      invFun := fun z => if h : z ∈ negs then
          Sum.inl ((negs.orderIsoOfFin hneg_card).symm ⟨z, h⟩)
        else
          Sum.inr ((poss.orderIsoOfFin hpos_card).symm ⟨z, by
            have hne : w z ≠ -1 := by
              intro hz
              exact h (by simp [negs, hz])
            rcases hw z with hwz | hwz
            · exact (hne hwz).elim
            · simp [poss, hwz]⟩)
      left_inv := by
        intro s
        cases s with
        | inl i =>
            have hmem : ((negs.orderIsoOfFin hneg_card) i : Fin n) ∈ negs :=
              ((negs.orderIsoOfFin hneg_card) i).2
            have hmem' : negs.orderEmbOfFin hneg_card i ∈ negs := by
              rw [← Finset.coe_orderIsoOfFin_apply]
              exact hmem
            dsimp
            rw [dif_pos hmem']
            apply congrArg Sum.inl
            exact (negs.orderIsoOfFin hneg_card).symm_apply_apply i
        | inr j =>
            have hmem : ((poss.orderIsoOfFin hpos_card) j : Fin n) ∈ poss :=
              ((poss.orderIsoOfFin hpos_card) j).2
            have hnot : ((poss.orderIsoOfFin hpos_card) j : Fin n) ∉ negs := by
              exact (Finset.disjoint_left.mp (Disjoint.symm hdisj)) hmem
            have hnot' : poss.orderEmbOfFin hpos_card j ∉ negs := by
              rw [← Finset.coe_orderIsoOfFin_apply]
              exact hnot
            dsimp
            rw [dif_neg hnot']
            apply congrArg Sum.inr
            convert (poss.orderIsoOfFin hpos_card).symm_apply_apply j using 1
      right_inv := by
        intro z
        by_cases h : z ∈ negs
        · dsimp
          rw [dif_pos h]
          exact congrArg (fun w : negs => (w : Fin n))
            ((negs.orderIsoOfFin hneg_card).apply_symm_apply ⟨z, h⟩)
        · have hposs' : z ∈ poss := by
            have hne : w z ≠ -1 := by
              intro hz
              exact h (by simp [negs, hz])
            rcases hw z with hwz | hwz
            · exact (hne hwz).elim
            · simp [poss, hwz]
          dsimp
          rw [dif_neg h]
          exact congrArg (fun w : poss => (w : Fin n))
            ((poss.orderIsoOfFin hpos_card).apply_symm_apply ⟨z, hposs'⟩) }
  refine ⟨e0.symm.trans e1, ?_, ?_⟩
  · intro i
    have hz : e0.symm (negIdx hk i) = Sum.inl i := by
      dsimp [e0]
      simp [negIdx]
    change w (e1 (e0.symm (negIdx hk i))) = -1
    rw [hz]
    change w ((negs.orderIsoOfFin hneg_card) i : Fin n) = -1
    exact (Finset.mem_filter.mp ((negs.orderIsoOfFin hneg_card) i).2).2
  · intro j
    have hz : e0.symm (posIdx hk j) = Sum.inr j := by
      dsimp [e0]
      simp [posIdx]
    change w (e1 (e0.symm (posIdx hk j))) = 1
    rw [hz]
    change w ((poss.orderIsoOfFin hpos_card) j : Fin n) = 1
    exact (Finset.mem_filter.mp ((poss.orderIsoOfFin hpos_card) j).2).2

theorem w_sum_reindexed {n k : ℕ} (hk : k ≤ n) (w : Fin n → ℝ)
    (σe : Fin n ≃ Fin n) (hwneg : ∀ i : Fin k, w (σe (negIdx hk i)) = -1)
    (hwpos : ∀ j : Fin (n - k), w (σe (posIdx hk j)) = 1) (y : MorseModel n) :
    (∑ i : Fin n, w i * (y (σe.symm i)) ^ 2) =
      (∑ i : Fin k, - (y (negIdx hk i)) ^ 2) + (∑ j : Fin (n - k), (y (posIdx hk j)) ^ 2) := by
  calc
    (∑ i : Fin n, w i * (y (σe.symm i)) ^ 2)
        = ∑ j : Fin n, w (σe j) * (y j) ^ 2 := by
          symm
          exact Fintype.sum_equiv σe
            (fun j : Fin n => w (σe j) * (y j) ^ 2)
            (fun i : Fin n => w i * (y (σe.symm i)) ^ 2)
            (by intro j; simp)
    _ = (∑ i : Fin k, - (y (negIdx hk i)) ^ 2) + (∑ j : Fin (n - k), (y (posIdx hk j)) ^ 2) := by
      rw [sum_split_fin hk (fun j : Fin n => w (σe j) * (y j) ^ 2)]
      congr 1
      · apply Finset.sum_congr rfl
        intro i hi
        rw [hwneg i]
        ring
      · apply Finset.sum_congr rfl
        intro j hj
        rw [hwpos j]
        simp

private theorem exists_morseChart {n : ℕ} {H : Type} [TopologicalSpace H] {M : Type}
    [TopologicalSpace M] [ChartedSpace H M] (I : ModelWithCorners ℝ (MorseModel n) H) [I.Boundaryless]
    [IsManifold I (⊤ : WithTop ℕ∞) M] (f : M → ℝ) (hf : ContMDiff I 𝓘(ℝ, ℝ) (⊤ : WithTop ℕ∞) f)
    (p : M) (c : ℝ) (k : ℕ) (hk : k ≤ n)
    (hcrit : fderiv ℝ (fun y => f ((extChartAt I p).symm y)) (extChartAt I p p) = 0)
    (hnd : (QuadraticMap.associated (R := ℝ)
      (chartHessianAt (g := fun y => f ((extChartAt I p).symm y)) (extChartAt I p p))).SeparatingLeft)
    (hindex : sigNeg (chartHessianAt (g := fun y => f ((extChartAt I p).symm y)) (extChartAt I p p)) = k)
    (hfp : f p = c) :
    ∃ R : ℝ, 0 < R ∧
    ∃ χ : OpenPartialHomeomorph (MorseModel n) M,
      (∀ y : MorseModel n, morseNorm n y ≤ R → f (χ y) = morseNormalForm hk c y) ∧
      (∀ y : MorseModel n, morseNorm n y ≤ R → y ∈ χ.source) := by
  rcases morseLemma_of_contMDiff I f hf p hcrit hnd with ⟨ψ, hψsrc, hψtarget, hψ0, w, hw, hsig, L, hnormal⟩
  have hcard : {i : Fin n | w i < 0}.ncard = k := by
    exact hsig.trans hindex
  rcases exists_reindexEquiv hk w hw hcard with ⟨σe, hwneg, hwpos⟩
  let e₀ : MorseModel n := extChartAt I p p
  let Lh : MorseModel n ≃ₜ MorseModel n := L.symm.toContinuousLinearEquiv.toHomeomorph
  let chart : OpenPartialHomeomorph (MorseModel n) M :=
    { toPartialEquiv := (extChartAt I p).symm
      open_source := isOpen_extChartAt_target p
      open_target := isOpen_extChartAt_source p
      continuousOn_toFun := continuousOn_extChartAt_symm p
      continuousOn_invFun := continuousOn_extChartAt p }
  let κ : OpenPartialHomeomorph (MorseModel n) M :=
    ((ψ.trans (homeoToOpenPartialHomeomorph Lh)).trans
      (homeoToOpenPartialHomeomorph (addHomeo n e₀))).trans
      chart
  let T : MorseModel n ≃ₜ MorseModel n := reindexHomeo σe
  let χ : OpenPartialHomeomorph (MorseModel n) M :=
    (homeoToOpenPartialHomeomorph T).trans κ
  let S : Set (MorseModel n) := κ.source ∩ ψ.target
  have hSopen : IsOpen S := κ.open_source.inter ψ.open_target
  have hS0 : (0 : MorseModel n) ∈ S := by
    dsimp [S]
    constructor
    · have h1 : (0 : MorseModel n) ∈ (ψ.trans (homeoToOpenPartialHomeomorph Lh)).source := by
        rw [OpenPartialHomeomorph.trans_source]
        exact ⟨hψsrc, by simp [homeoToOpenPartialHomeomorph]⟩
      have h2 : (0 : MorseModel n) ∈
          ((ψ.trans (homeoToOpenPartialHomeomorph Lh)).trans
            (homeoToOpenPartialHomeomorph (addHomeo n e₀))).source := by
        rw [OpenPartialHomeomorph.trans_source]
        refine ⟨h1, ?_⟩
        simp [homeoToOpenPartialHomeomorph]
      have h3 : (0 : MorseModel n) ∈ κ.source := by
        rw [OpenPartialHomeomorph.trans_source]
        refine ⟨h2, ?_⟩
        have hval : ((ψ.trans (homeoToOpenPartialHomeomorph Lh)).trans
            (homeoToOpenPartialHomeomorph (addHomeo n e₀))) 0 = e₀ := by
          have hL0 : Lh 0 = 0 := by
            dsimp [Lh]
            exact L.symm.map_zero
          simp [addHomeo, homeoToOpenPartialHomeomorph, OpenPartialHomeomorph.trans_apply, hψ0, hL0,
            add_zero]
        change ((ψ.trans (homeoToOpenPartialHomeomorph Lh)).trans
          (homeoToOpenPartialHomeomorph (addHomeo n e₀))) 0 ∈ chart.source
        rw [hval]
        change e₀ ∈ (extChartAt I p).target
        dsimp [e₀]
        exact (extChartAt I p).map_source (mem_extChartAt_source p)
      exact h3
    · exact hψtarget
  have hTpre : IsOpen (T ⁻¹' S) := T.continuous.isOpen_preimage S hSopen
  have hT0 : (0 : MorseModel n) ∈ T ⁻¹' S := by
    apply Set.mem_preimage.mpr
    simpa using hS0
  rcases (Metric.isOpen_iff.mp hTpre) 0 hT0 with ⟨r, hr, hrball⟩
  let R : ℝ := r / 2
  have hRpos : 0 < R := by dsimp [R]; positivity
  have hRlt : R < r := by dsimp [R]; linarith
  have hball : ∀ y : MorseModel n, morseNorm n y ≤ R → y ∈ T ⁻¹' S := by
    intro y hy
    have hsup : ‖y‖ ≤ R := le_trans (supNorm_le_morseNorm y) hy
    have hmem : y ∈ Metric.ball (0 : MorseModel n) r := by
      rw [Metric.mem_ball, dist_zero_right]
      linarith
    exact hrball hmem
  have hχsrc : ∀ y : MorseModel n, morseNorm n y ≤ R → y ∈ χ.source := by
    intro y hy
    have hyS : T y ∈ S := (Set.mem_preimage.mp (hball y hy))
    have hyκ : T y ∈ κ.source := hyS.1
    dsimp [χ]
    dsimp [homeoToOpenPartialHomeomorph]
    simp [hyκ]
  have hnormal' : ∀ y : MorseModel n, morseNorm n y ≤ R → f (χ y) = morseNormalForm hk c y := by
    intro y hy
    have hyS : T y ∈ S := (Set.mem_preimage.mp (hball y hy))
    have hyT : T y ∈ ψ.target := hyS.2
    have hwf : f ((extChartAt I p).symm (extChartAt I p p + L.symm (ψ (T y)))) =
        f p + (1 / 2) * ∑ i : Fin n, w i * (T y i) * (T y i) := hnormal (T y) hyT
    have hwf' : f (κ (T y)) = f p + (1 / 2) * ∑ i : Fin n, w i * (T y i) * (T y i) := by
      simpa [κ] using hwf
    have hTval : ∀ i : Fin n, T y i = y (σe.symm i) := by
      intro i
      dsimp [T]
      rfl
    have hwsum : (∑ i : Fin n, w i * (T y i) * (T y i)) =
        (∑ i : Fin k, - (y (negIdx hk i)) ^ 2) + (∑ j : Fin (n - k), (y (posIdx hk j)) ^ 2) := by
      calc
        (∑ i : Fin n, w i * (T y i) * (T y i))
            = (∑ i : Fin n, w i * (y (σe.symm i)) ^ 2) := by
              apply Finset.sum_congr rfl
              intro i hi
              rw [hTval i]
              ring
        _ = (∑ i : Fin k, - (y (negIdx hk i)) ^ 2) + (∑ j : Fin (n - k), (y (posIdx hk j)) ^ 2) :=
          w_sum_reindexed hk w σe hwneg hwpos y
    have hwf'' : f (κ (T y)) = f p + (1 / 2) * ((∑ i : Fin k, - (y (negIdx hk i)) ^ 2) +
        (∑ j : Fin (n - k), (y (posIdx hk j)) ^ 2)) := by
      rw [hwf']
      exact congrArg (fun s : ℝ => f p + (1 / 2 : ℝ) * s) hwsum
    have hfp' : f p = c := hfp
    dsimp [χ]
    change f (κ (T y)) = morseNormalForm hk c y
    rw [hwf'', hfp']
    rfl
  refine ⟨R, hRpos, χ, hnormal', hχsrc⟩

private theorem chartBallHomeo_eval {n : ℕ} {M : Type} [TopologicalSpace M]
    (χ : OpenPartialHomeomorph (MorseModel n) M) (R : ℝ)
    (hχsrc : ∀ y : MorseModel n, morseNorm n y ≤ R → y ∈ χ.source) :
    ∃ he : {y : MorseModel n // morseNorm n y ≤ R} ≃ₜ
        {x : M // x ∈ χ '' {y : MorseModel n | morseNorm n y ≤ R}},
      ∀ y : {y : MorseModel n // morseNorm n y ≤ R}, (he y : M) = χ y.1 := by
  let ball : Set (MorseModel n) := {y : MorseModel n | morseNorm n y ≤ R}
  let U : Set M := χ '' ball
  let hχ : χ.source ≃ₜ χ.target := openPartialHomeomorphSourceHomeo χ
  have himg : χ '' ball ⊆ χ.target := by
    intro x hx
    rcases hx with ⟨y, hy, hxy⟩
    rw [← hxy]
    exact χ.map_source (hχsrc y hy)
  let he : {y : MorseModel n // morseNorm n y ≤ R} ≃ₜ {x : M // x ∈ U} :=
    { toFun := fun y => ⟨χ y.1, ⟨y.1, y.2, rfl⟩⟩
      invFun := fun x => ⟨χ.symm x.1, by
        rcases x.2 with ⟨y, hy, hxy⟩
        have hyin : y ∈ χ.source := hχsrc y hy
        have hround : χ.symm x.1 = y := by
          rw [← hxy]
          exact χ.left_inv hyin
        rw [hround]
        exact hy⟩
      left_inv := by
        intro y
        apply Subtype.ext
        exact χ.left_inv (hχsrc y.1 y.2)
      right_inv := by
        intro x
        apply Subtype.ext
        exact χ.right_inv (himg x.2)
      continuous_toFun := by
        have h1 : Continuous (fun y : {y : MorseModel n // y ∈ χ.source} => χ y.1) :=
          continuousOn_iff_continuous_restrict.mp χ.continuousOn_toFun
        have h2 : Continuous (fun y : {y : MorseModel n // morseNorm n y ≤ R} =>
            (⟨y.1, hχsrc y.1 y.2⟩ : {y : MorseModel n // y ∈ χ.source})) := by
          exact (Topology.IsInducing.subtypeVal.continuous_iff).2 continuous_subtype_val
        exact (Topology.IsInducing.subtypeVal.continuous_iff).2 (h1.comp h2)
      continuous_invFun := by
        have h1 : Continuous (fun x : {x : M // x ∈ χ.target} => χ.symm x.1) :=
          continuousOn_iff_continuous_restrict.mp χ.continuousOn_invFun
        have h2 : Continuous (fun x : {x : M // x ∈ U} =>
            (⟨x.1, himg x.2⟩ : {x : M // x ∈ χ.target})) := by
          exact (Topology.IsInducing.subtypeVal.continuous_iff).2 continuous_subtype_val
        exact (Topology.IsInducing.subtypeVal.continuous_iff).2 (h1.comp h2) }
  have heval : ∀ y : {y : MorseModel n // morseNorm n y ≤ R}, (he y : M) = χ y.1 := by
    intro y
    simp [he]
  exact ⟨he, heval⟩

theorem morseCellAttachment {n : ℕ} {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M]
    [ChartedSpace H M] (I : ModelWithCorners ℝ (MorseModel n) H) [I.Boundaryless]
    [IsManifold I (⊤ : WithTop ℕ∞) M] (f : M → ℝ) (hf : ContMDiff I 𝓘(ℝ, ℝ) (⊤ : WithTop ℕ∞) f)
    (p : M) (c : ℝ) (k : ℕ) (hk : k ≤ n)
    (hcrit : fderiv ℝ (fun y => f ((extChartAt I p).symm y)) (extChartAt I p p) = 0)
    (hnd : (QuadraticMap.associated (R := ℝ)
      (chartHessianAt (g := fun y => f ((extChartAt I p).symm y)) (extChartAt I p p))).SeparatingLeft)
    (hindex : sigNeg (chartHessianAt (g := fun y => f ((extChartAt I p).symm y)) (extChartAt I p p)) = k)
    (hfp : f p = c) :
    ∃ R : ℝ, 0 < R ∧
    ∃ χ : OpenPartialHomeomorph (MorseModel n) M,
      (∀ y : MorseModel n, morseNorm n y ≤ R → f (χ y) = morseNormalForm hk c y) ∧
      (∀ y : MorseModel n, morseNorm n y ≤ R → y ∈ χ.source) ∧
      ∃ ε : ℝ, 0 < ε ∧ Real.sqrt (2 * ε) ≤ R ∧
        ∃ φ : CellBoundary k →
            {x : {x : M // x ∈ χ '' {y : MorseModel n | morseNorm n y ≤ R}} //
              x.1 ∈ sublevel f (c - ε)},
          Nonempty (ContinuousMap.HomotopyEquiv
            {x : M // x ∈ χ '' {y : MorseModel n | morseNorm n y ≤ R} ∧ x ∈ sublevel f (c + ε)}
            (CellAdjunctionSpace k φ)) := by
  rcases exists_morseChart I f hf p c k hk hcrit hnd hindex hfp with ⟨R, hRpos, χ, hnorm, hχsrc⟩
  let ε : ℝ := R ^ 2 / 4
  have hεpos : 0 < ε := by dsimp [ε]; positivity
  have hεR : Real.sqrt (2 * ε) ≤ R := by
    dsimp [ε]
    have hRnonneg : 0 ≤ R := le_of_lt hRpos
    have hsq : (Real.sqrt (2 * (R ^ 2 / 4))) ^ 2 ≤ R ^ 2 := by
      rw [Real.sq_sqrt (by positivity : 0 ≤ 2 * (R ^ 2 / 4))]
      ring_nf
      nlinarith [sq_nonneg R]
    have habs := sq_le_sq.mp hsq
    calc
      Real.sqrt (2 * (R ^ 2 / 4)) = |Real.sqrt (2 * (R ^ 2 / 4))| :=
        (abs_of_nonneg (Real.sqrt_nonneg _)).symm
      _ ≤ |R| := habs
      _ = R := abs_of_nonneg hRnonneg
  let he : {y : MorseModel n // morseNorm n y ≤ R} ≃ₜ
      {x : M // x ∈ χ '' {y : MorseModel n | morseNorm n y ≤ R}} :=
    Classical.choose (chartBallHomeo_eval (M := M) χ R hχsrc)
  have heval : ∀ y : {y : MorseModel n // morseNorm n y ≤ R}, (he y : M) = χ y.1 :=
    Classical.choose_spec (chartBallHomeo_eval (M := M) χ R hχsrc)
  let ball : Set (MorseModel n) := {y : MorseModel n | morseNorm n y ≤ R}
  let U : Set M := χ '' ball
  refine ⟨R, hRpos, χ, hnorm, hχsrc, ε, hεpos, hεR, ?_⟩
  have hpLower : ∀ y : {y : MorseModel n // morseNorm n y ≤ R},
      y.1 ∈ sublevel (morseNormalForm hk c) (c - ε) ↔ (he y : M) ∈ sublevel f (c - ε) := by
    intro y
    have hval : f (he y : M) = morseNormalForm hk c y.1 := by
      rw [heval y]
      exact hnorm y.1 y.2
    constructor
    · intro hy
      change f (he y : M) ≤ c - ε
      rw [hval]
      exact hy
    · intro hy
      change morseNormalForm hk c y.1 ≤ c - ε
      rw [← hval]
      exact hy
  let hLower : {y : MorseModel n // y ∈ sublevel (morseNormalForm hk c) (c - ε) ∧ morseNorm n y ≤ R} ≃ₜ
      {x : {x : M // x ∈ U} // x.1 ∈ sublevel f (c - ε)} :=
    (andSwapHomeo (fun y : MorseModel n => y ∈ sublevel (morseNormalForm hk c) (c - ε))
      (fun y : MorseModel n => morseNorm n y ≤ R)).trans
      ((subtypeAndNestedHomeo (fun y : MorseModel n => morseNorm n y ≤ R)
        (fun y : MorseModel n => y ∈ sublevel (morseNormalForm hk c) (c - ε))).trans
      (homeoRestrictPred he (fun y => y.1 ∈ sublevel (morseNormalForm hk c) (c - ε))
        (fun x => x.1 ∈ sublevel f (c - ε)) hpLower))
  let φB : CellBoundary k →
      {y : MorseModel n // y ∈ sublevel (morseNormalForm hk c) (c - ε) ∧ morseNorm n y ≤ R} :=
    ballAttachMap hk c ε R (le_of_lt hεpos) hεR
  let φ : CellBoundary k → {x : {x : M // x ∈ U} // x.1 ∈ sublevel f (c - ε)} := hLower ∘ φB
  have hUpper : {x : M // x ∈ U ∧ x ∈ sublevel f (c + ε)} ≃ₜ ballUpperSublevel hk c ε R := by
    have hpUpper : ∀ y : {y : MorseModel n // morseNorm n y ≤ R},
        y.1 ∈ sublevel (morseNormalForm hk c) (c + ε) ↔ (he y : M) ∈ sublevel f (c + ε) := by
      intro y
      have hval : f (he y : M) = morseNormalForm hk c y.1 := by
        rw [heval y]
        exact hnorm y.1 y.2
      constructor
      · intro hy
        change f (he y : M) ≤ c + ε
        rw [hval]
        exact hy
      · intro hy
        change morseNormalForm hk c y.1 ≤ c + ε
        rw [← hval]
        exact hy
    have hU' : {y : {y : MorseModel n // morseNorm n y ≤ R} // y.1 ∈ sublevel (morseNormalForm hk c) (c + ε)} ≃ₜ
        {x : {x : M // x ∈ U} // x.1 ∈ sublevel f (c + ε)} :=
      homeoRestrictPred he (fun y => y.1 ∈ sublevel (morseNormalForm hk c) (c + ε))
        (fun x => x.1 ∈ sublevel f (c + ε)) hpUpper
    have hcast : {y : {y : MorseModel n // morseNorm n y ≤ R} //
        y.1 ∈ sublevel (morseNormalForm hk c) (c + ε)} ≃ₜ ballUpperSublevel hk c ε R :=
      ((andSwapHomeo (fun y : MorseModel n => y ∈ sublevel (morseNormalForm hk c) (c + ε))
        (fun y : MorseModel n => morseNorm n y ≤ R)).trans
        (subtypeAndNestedHomeo (fun y : MorseModel n => morseNorm n y ≤ R)
          (fun y : MorseModel n => y ∈ sublevel (morseNormalForm hk c) (c + ε)))).symm
    exact (subtypeAndNestedHomeo (fun x : M => x ∈ U) (fun x : M => x ∈ sublevel f (c + ε))).trans
      (hU'.symm.trans hcast)
  have hAdj : CellAdjunctionSpace k φB ≃ₜ CellAdjunctionSpace k φ :=
    (adjunctionHomeoOfLowerEquiv (cellBoundaryInclusion k) φB hLower).symm
  exact ⟨φ, ⟨(hUpper.toHomotopyEquiv.trans
    (ballCellAttachmentModel hk c ε R hεpos hεR)).trans hAdj.toHomotopyEquiv⟩⟩

end ManifoldCellAttachment

end
end DifferentialGeometry.Topology.Morse
