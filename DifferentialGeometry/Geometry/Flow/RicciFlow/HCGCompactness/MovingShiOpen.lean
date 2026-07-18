import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.IteratedRmTowerSolution
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.BernsteinComplete
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.TowerNormRegularity
import DifferentialGeometry.Geometry.Curvature.RicciOperatorNormBoundFlow
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.Basic
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.RicciTowerTrace
import DifferentialGeometry.Geometry.Operator.GradientRegularity

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# Complete Shi estimates on canonical open windows

This file is the HCG-facing boundary of the arbitrary-dimensional complete
Shi route.  Its lower theorem has an explicit constant depending only on the
dimension, the curvature bound, the buffered time slab, and the requested
order.  Consequently the sequence wrapper chooses its constant before the
sequence member; it does not try to uniformize a family of memberwise
existential constants.
-/

noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace HCGCompactness

open Bundle Set
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.PDE.RicciFlow
open scoped Manifold ContDiff BigOperators

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
variable [FiniteDimensional Real E] [NeZero (Module.finrank Real E)] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]

section AnchorComparison

variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M] [IsManifold I 1 M]
variable [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
variable [SigmaCompactSpace M] [T2Space M]

private theorem tensor_eval_cont
    {K : Set Real}
    {A : (t : Real) → (x : M) →
      Tensor0SBundle.Tensor0SSpace
        (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x}
    (hA : Tensor0SFamilyContinuousOnSet (I := I) (M := M) 2 K A)
    (x : M) (v w : TangentSpace I x) :
    ContinuousOn (fun s : Real ↦ A s x (vec2 v w)) K := by
  rw [continuousOn_iff_continuous_restrict]
  exact hA.eval_continuous (P := {s : Real // s ∈ K}) (τ := Subtype.val)
    (b := fun _ ↦ x) continuous_subtype_val (fun p ↦ p.2) continuous_const
    (v := fun i _ ↦ vec2 v w i) (fun _ ↦ continuous_const)

private theorem deriv_Ici_start
    {a b : Real} (hab : a < b) (f e : Real → Real)
    (hcont : ContinuousOn f (Set.Icc a b))
    (hecont : ContinuousWithinAt e (Set.Ioi a) a)
    (hint : ∀ t ∈ Set.Ioo a b,
      HasDerivWithinAt f (e t) (Set.Ici a) t) :
    HasDerivWithinAt f (e a) (Set.Ici a) a := by
  have hopen : IsOpen (Set.Ioo a b) := isOpen_Ioo
  have hsub : Set.Ioo a b ⊆ Set.Ici a := fun _ ht ↦ ht.1.le
  have hwithin : ∀ t ∈ Set.Ioo a b,
      HasDerivWithinAt f (e t) (Set.Ioo a b) t :=
    fun t ht ↦ (hint t ht).mono hsub
  have hdiff : DifferentiableOn Real f (Set.Ioo a b) :=
    fun t ht ↦ (hwithin t ht).differentiableWithinAt
  have hderiv : ∀ t ∈ Set.Ioo a b, deriv f t = e t := by
    intro t ht
    rw [← derivWithin_of_isOpen hopen ht]
    exact (hwithin t ht).derivWithin (hopen.uniqueDiffWithinAt ht)
  refine hasDerivWithinAt_Ici_of_tendsto_deriv (s := Set.Ioo a b)
    hdiff ?_ ?_ ?_
  · exact (hcont.continuousWithinAt ⟨le_rfl, hab.le⟩).mono
      Set.Ioo_subset_Icc_self
  · exact Ioo_mem_nhdsGT hab
  · exact hecont.tendsto.congr'
      (Filter.eventuallyEq_of_mem (Ioo_mem_nhdsGT hab) hderiv).symm

private theorem metric_pde_start
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    {alpha psi : Real} (halphaPsi : alpha < psi)
    (hslab : Set.Icc alpha psi ⊆ D.carrier)
    (hreg : Set.Ioc alpha psi ⊆ D.regular) :
    ∀ t ∈ Set.Icc alpha psi, ∀ x : M, ∀ v w : TangentSpace I x,
      HasDerivWithinAt
        (fun s : Real ↦ (S.base.metric s).inner x v w)
        ((-2 : Real) * ricciTensor (I := I) (S.base.metric t) x v w)
        (Set.Icc alpha psi) t := by
  have hmetricCont : ∀ x : M, ∀ v w : TangentSpace I x,
      ContinuousOn (fun s : Real ↦ (S.base.metric s).inner x v w)
        (Set.Icc alpha psi) := by
    intro x v w
    refine (tensor_eval_cont (I := I) hS.smoothMetric.metricTensor_cont x v w).mono ?_
    exact hslab
  have hricCont : ∀ x : M, ∀ v w : TangentSpace I x,
      ContinuousOn
        (fun s : Real ↦
          (-2 : Real) * ricciTensor (I := I) (S.base.metric s) x v w)
        (Set.Icc alpha psi) := by
    intro x v w
    have hcont := (tensor_eval_cont (I := I) hS.ricciCont x v w).mono hslab
    refine (hcont.congr fun s _ ↦ ?_).const_mul (-2)
    simp only [SolutionOn.ricci, SolutionFamily.ricci_apply,
      SolutionFamily.ricciAt]
    exact (metricRicciAt_apply_eq_ricciTensor (S.base.metric s) x v w).symm
  intro t ht x v w
  rcases eq_or_lt_of_le ht.1 with rfl | halphaT
  · have hecont : ContinuousWithinAt
        (fun s : Real ↦
          (-2 : Real) * ricciTensor (I := I) (S.base.metric s) x v w)
        (Set.Ioi alpha) alpha := by
      have hmem : Set.Icc alpha psi ∈ nhdsWithin alpha (Set.Ioi alpha) :=
        Filter.mem_of_superset (Ioo_mem_nhdsGT halphaPsi)
          (fun s hs ↦ ⟨hs.1.le, hs.2.le⟩)
      exact ((hricCont x v w).continuousWithinAt ⟨le_rfl, halphaPsi.le⟩)
        |>.mono_of_mem_nhdsWithin hmem
    have hint : ∀ s ∈ Set.Ioo alpha psi,
        HasDerivWithinAt
          (fun r : Real ↦ (S.base.metric r).inner x v w)
          ((-2 : Real) * ricciTensor (I := I) (S.base.metric s) x v w)
          (Set.Ici alpha) s := by
      intro s hs
      let tau : RealTimeInterval.RegularTime D :=
        ⟨s, hreg ⟨hs.1, hs.2.le⟩⟩
      have hraw := metricDerivAt (I := I) S hS tau x v w
      simpa [SolutionFamily.ricciAt, PDE.RicciFlow.metricRicciAt,
        metricRicciAt_apply_eq_ricciTensor] using hraw.hasDerivWithinAt
    exact (deriv_Ici_start halphaPsi _ _ (hmetricCont x v w) hecont hint).mono
      (fun _ hs ↦ hs.1)
  · let tau : RealTimeInterval.RegularTime D :=
      ⟨t, hreg ⟨halphaT, ht.2⟩⟩
    have hraw := metricDerivAt (I := I) S hS tau x v w
    simpa [SolutionFamily.ricciAt, PDE.RicciFlow.metricRicciAt,
      metricRicciAt_apply_eq_ricciTensor] using hraw.hasDerivWithinAt

private theorem exp_bounds_log
    {fa fb R : Real} (hfa : 0 < fa) (hfb : 0 < fb)
    (hlog : |Real.log fb - Real.log fa| ≤ R) :
    Real.exp (-R) * fa ≤ fb ∧ fb ≤ Real.exp R * fa := by
  have hlo : -R ≤ Real.log fb - Real.log fa := (abs_le.mp hlog).1
  have hhi : Real.log fb - Real.log fa ≤ R := (abs_le.mp hlog).2
  constructor
  · have hratio : Real.exp (-R) ≤ fb / fa := by
      apply (Real.le_log_iff_exp_le (div_pos hfb hfa)).mp
      simpa [Real.log_div hfb.ne' hfa.ne'] using hlo
    calc
      Real.exp (-R) * fa ≤ (fb / fa) * fa :=
        mul_le_mul_of_nonneg_right hratio hfa.le
      _ = fb := by field_simp
  · have hratio : fb / fa ≤ Real.exp R := by
      apply (Real.log_le_iff_le_exp (div_pos hfb hfa)).mp
      simpa [Real.log_div hfb.ne' hfa.ne'] using hhi
    calc
      fb = (fb / fa) * fa := by field_simp
      _ ≤ Real.exp R * fa := mul_le_mul_of_nonneg_right hratio hfa.le

private theorem metric_equiv_start
    (g : Real → SmoothRiemannianMetric I M)
    {alpha psi K : Real}
    (hpde : ∀ t ∈ Set.Icc alpha psi, ∀ x : M,
      ∀ v w : TangentSpace I x,
        HasDerivWithinAt (fun s : Real ↦ (g s).inner x v w)
          ((-2 : Real) * ricciTensor (I := I) (g t) x v w)
          (Set.Icc alpha psi) t)
    (hric : ∀ t ∈ Set.Icc alpha psi, ∀ x : M,
      ∀ v : TangentSpace I x,
        |ricciTensor (I := I) (g t) x v v| ≤
          K * (g t).inner x v v) :
    ∀ s ∈ Set.Icc alpha psi, ∀ x : M,
      ∀ v : TangentSpace I x,
        Real.exp (-(2 * K * (s - alpha))) * (g alpha).inner x v v ≤
            (g s).inner x v v ∧
          (g s).inner x v v ≤
            Real.exp (2 * K * (s - alpha)) * (g alpha).inner x v v := by
  intro s hs x v
  rcases eq_or_ne v 0 with rfl | hv
  · simp
  have hpos : ∀ t : Real, 0 < (g t).inner x v v :=
    fun t ↦ (g t).pos x v hv
  have hsub : Set.Icc alpha s ⊆ Set.Icc alpha psi :=
    fun _ ht ↦ ⟨ht.1, ht.2.trans hs.2⟩
  have hderiv : ∀ t ∈ Set.Icc alpha s,
      HasDerivWithinAt
        (fun r : Real ↦ Real.log ((g r).inner x v v))
        ((-2 : Real) * ricciTensor (I := I) (g t) x v v /
          (g t).inner x v v)
        (Set.Icc alpha s) t := by
    intro t ht
    exact ((hpde t (hsub ht) x v v).mono hsub).log (hpos t).ne'
  have hbound : ∀ t ∈ Set.Icc alpha s,
      ‖(-2 : Real) * ricciTensor (I := I) (g t) x v v /
          (g t).inner x v v‖ ≤ 2 * K := by
    intro t ht
    have hden := hpos t
    have hricT := hric t (hsub ht) x v
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hden, div_le_iff₀ hden]
    rw [abs_mul]
    norm_num
    nlinarith
  have hmvt := (convex_Icc alpha s).norm_image_sub_le_of_norm_hasDerivWithin_le
    hderiv hbound (Set.left_mem_Icc.mpr hs.1) (Set.right_mem_Icc.mpr hs.1)
  have hlog :
      |Real.log ((g s).inner x v v) - Real.log ((g alpha).inner x v v)| ≤
        2 * K * (s - alpha) := by
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (sub_nonneg.mpr hs.1)] at hmvt
    exact hmvt
  exact exp_bounds_log (hpos alpha) (hpos s) hlog

end AnchorComparison

section CompleteTruncation

variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]
variable [VectorBundle Real E (TangentSpace I : M → Type _)]
variable [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
variable [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]

private theorem complete_of_heat
    {D : RealTimeInterval}
    (G : RealizedMetricFamily (I := I) (M := M) Real)
    {w wLap : Nat → Real → M → Real}
    (levelC : Nat → Real)
    (K aScale T : Real)
    (hT : 0 < T) (hK : 0 < K) (haScale : 0 ≤ aScale)
    (hslab : Set.Icc 0 T ⊆ D.carrier)
    (hregular : ∀ t : Real, t ∈ Set.Icc 0 T → 0 < t → t ∈ D.regular)
    (hw_nonneg : ∀ k : Nat, ∀ t : Real, ∀ x : M, 0 ≤ w k t x)
    (hw0_bound : ∀ t : Real, t ∈ Set.Icc 0 T → ∀ x : M,
      w 0 t x ≤ K ^ 2)
    (hTK : T ≤ aScale / K)
    (hheat : ∀ k : Nat, TowerHeatBoundOn (D := D) w wLap (levelC k) k)
    (hLap : ∀ k : Nat, ∀ t : Real, t ∈ Set.Icc 0 T → 0 < t → ∀ x : M,
      heatOperatorWithDrift (I := I) G t
        (fun _y : M ↦ (0 : TangentSpace I _y)) (w k t) x = wLap k t x)
    (hw_cont : ∀ k : Nat, ContinuousOn (fun p : Real × M ↦ w k p.1 p.2)
      (spacetimeSlab (M := M) T))
    (hw_space : ∀ k : Nat, ∀ t : Real, t ∈ Set.Icc 0 T → 0 < t → ∀ y : M,
      MDifferentiableAt I (modelWithCornersSelf Real Real) (w k t) y)
    (hw_grad : ∀ k : Nat, ∀ t : Real, t ∈ Set.Icc 0 T → 0 < t → ∀ x : M,
      MDiffAt (T% fun y : M ↦ gradientFun (I := I) (G.metric t) (w k t) y) x)
    (m : Nat) (c : Real) (hc : 0 ≤ c)
    (hlevelC : ∀ k : Nat, k ≤ m → levelC k ≤ c)
    (Ceq Kric : Real) (hCeq : 1 ≤ Ceq) (hKric : 0 ≤ Kric)
    (hequiv : ∀ t : Real, t ∈ Set.Icc 0 T → ∀ x : M,
      ∀ v : TangentSpace I x,
        Ceq⁻¹ * ‖v‖ ^ 2 ≤ (G.metric t).inner x v v ∧
          (G.metric t).inner x v v ≤ Ceq * ‖v‖ ^ 2)
    (hric : ∀ t : Real, t ∈ Set.Icc 0 T → ∀ x : M,
      ∀ v : TangentSpace I x,
        -Kric * (G.metric t).inner x v v ≤
          ricciTensor (I := I) (G.metric t) x v v)
    {t : Real} (htmem : t ∈ Set.Icc 0 T) (htpos : 0 < t) (x : M) :
    w m t x ≤ (towerConst c aScale m) ^ 2 * K ^ 2 / t ^ m := by
  classical
  let w' : Nat → Real → M → Real := fun k ↦
    if k ≤ m then w k else fun _ _ ↦ 0
  let wLap' : Nat → Real → M → Real := fun k ↦
    if k ≤ m then wLap k else fun _ _ ↦ 0
  have hw'_le : ∀ k : Nat, k ≤ m → w' k = w k := by
    intro k hk
    simp only [w', if_pos hk]
  have hw'_gt : ∀ k : Nat, ¬ k ≤ m → w' k = fun _ _ ↦ 0 := by
    intro k hk
    simp only [w', if_neg hk]
  have hwLap'_le : ∀ k : Nat, k ≤ m → wLap' k = wLap k := by
    intro k hk
    simp only [wLap', if_pos hk]
  have hwLap'_gt : ∀ k : Nat, ¬ k ≤ m → wLap' k = fun _ _ ↦ 0 := by
    intro k hk
    simp only [wLap', if_neg hk]
  have hw'_val_le : ∀ k : Nat, k ≤ m → ∀ s : Real, ∀ y : M,
      w' k s y = w k s y := by
    intro k hk s y
    rw [hw'_le k hk]
  have hw'_val_gt : ∀ k : Nat, ¬ k ≤ m → ∀ s : Real, ∀ y : M,
      w' k s y = 0 := by
    intro k hk s y
    rw [hw'_gt k hk]
  have hwLap'_val_le : ∀ k : Nat, k ≤ m → ∀ s : Real, ∀ y : M,
      wLap' k s y = wLap k s y := by
    intro k hk s y
    rw [hwLap'_le k hk]
  have hwLap'_val_gt : ∀ k : Nat, ¬ k ≤ m → ∀ s : Real, ∀ y : M,
      wLap' k s y = 0 := by
    intro k hk s y
    rw [hwLap'_gt k hk]
  have hw'_nonneg : ∀ k : Nat, ∀ s : Real, ∀ y : M, 0 ≤ w' k s y := by
    intro k s y
    by_cases hk : k ≤ m
    · rw [hw'_val_le k hk]
      exact hw_nonneg k s y
    · rw [hw'_val_gt k hk]
  have hreact_eq : ∀ k : Nat, k ≤ m → ∀ s : Real, ∀ y : M,
      towerReactionSum (M := M) w' c k s y =
        towerReactionSum (M := M) w c k s y := by
    intro k hk s y
    unfold towerReactionSum
    apply Finset.sum_congr rfl
    intro j hj
    simp only [Finset.mem_range] at hj
    have hjk : j ≤ k := by omega
    rw [hw'_val_le j (hjk.trans hk),
      hw'_val_le (k - j) ((Nat.sub_le k j).trans hk), hw'_val_le k hk]
  let B : BernsteinTower (I := I) G :=
    { D := D
      w := w'
      wLap := wLap'
      c := c
      K := K
      α := aScale
      T := T
      hT := hT
      hc := hc
      hK := hK
      hα := haScale
      hslab := hslab
      hregular := hregular
      hw_nonneg := by
        intro k s _hs y
        exact hw'_nonneg k s y
      hw0_bound := by
        intro s hs y
        rw [hw'_val_le 0 (Nat.zero_le m)]
        exact hw0_bound s hs y
      hTK := hTK
      hheat := by
        intro k tau y
        rcases lt_trichotomy k m with hlt | rfl | hgt
        · have hk : k ≤ m := hlt.le
          obtain ⟨d, hd, hle⟩ := hheat k tau y
          refine ⟨d, ?_, ?_⟩
          · simpa only [hw'_val_le k hk] using hd
          · rw [hwLap'_val_le k hk, hw'_val_le (k + 1) hlt,
              hreact_eq k hk]
            have hmono := towerReactionSum_mono_const w
              (hlevelC k hk) k (tau : Real) y
            linarith
        · obtain ⟨d, hd, hle⟩ := hheat m tau y
          refine ⟨d, ?_, ?_⟩
          · simpa only [hw'_val_le m le_rfl] using hd
          · rw [hwLap'_val_le m le_rfl,
              hw'_val_gt (m + 1) (by omega), hreact_eq m le_rfl]
            have hmono := towerReactionSum_mono_const w
              (hlevelC m le_rfl) m (tau : Real) y
            have hnn := hw_nonneg (m + 1) (tau : Real) y
            nlinarith
        · have hk : ¬ k ≤ m := by omega
          refine ⟨0, ?_, ?_⟩
          · have hfun : (fun s : Real ↦ w' k s y) = fun _ ↦ 0 := by
              funext s
              rw [hw'_val_gt k hk]
            rw [hfun]
            exact hasDerivWithinAt_const _ _ _
          · rw [hwLap'_val_gt k hk,
              hw'_val_gt (k + 1) (by omega)]
            have hzero : towerReactionSum (M := M) w' c k (tau : Real) y = 0 := by
              unfold towerReactionSum
              apply Finset.sum_eq_zero
              intro j _
              rw [hw'_val_gt k hk]
              simp
            rw [hzero]
            norm_num
      hLap := by
        intro k s hs hspos y
        by_cases hk : k ≤ m
        · have hfun : w' k s = w k s := by
            funext z
            rw [hw'_val_le k hk]
          rw [hwLap'_val_le k hk, hfun]
          exact hLap k s hs hspos y
        · have hfun : w' k s = fun _z : M ↦ (0 : Real) := by
            funext z
            rw [hw'_val_gt k hk]
          rw [hwLap'_val_gt k hk, hfun,
            heatOperatorWithDrift_zero_drift, heatOperator_eq_laplacianAt,
            laplacianAt_eq]
          exact laplacian_const (I := I) (G.connection s) (G.metric s) 0 y
      hw_cont := by
        intro k
        by_cases hk : k ≤ m
        · have hfun : (fun p : Real × M ↦ w' k p.1 p.2) =
              fun p : Real × M ↦ w k p.1 p.2 := by
            funext p
            rw [hw'_val_le k hk]
          rw [hfun]
          exact hw_cont k
        · have hfun : (fun p : Real × M ↦ w' k p.1 p.2) =
              fun _ : Real × M ↦ (0 : Real) := by
            funext p
            rw [hw'_val_gt k hk]
          rw [hfun]
          exact continuousOn_const
      hw_space := by
        intro k s hs hspos y
        by_cases hk : k ≤ m
        · have hfun : w' k s = w k s := by
            funext z
            rw [hw'_val_le k hk]
          rw [hfun]
          exact hw_space k s hs hspos y
        · have hfun : w' k s = fun _ : M ↦ (0 : Real) := by
            funext z
            rw [hw'_val_gt k hk]
          rw [hfun]
          exact mdifferentiableAt_const
      hw_grad := by
        intro k s hs hspos y
        by_cases hk : k ≤ m
        · have hfun : w' k s = w k s := by
            funext z
            rw [hw'_val_le k hk]
          simp only [hfun]
          exact hw_grad k s hs hspos y
        · have hfun : w' k s = fun _ : M ↦ (0 : Real) := by
            funext z
            rw [hw'_val_gt k hk]
          simp only [hfun]
          refine (mdifferentiableAt_zeroSection
            (𝕜 := Real) (F := E) (E := (TangentSpace I : M → Type _))
            (x := y)).congr_of_eventuallyEq ?_
          filter_upwards with z
          exact congrArg (fun v ↦ (⟨z, v⟩ : TotalSpace E (TangentSpace I)))
            (gradientFun_const (I := I) (G.metric s) 0 z) }
  have hkey := B.estimate_complete Ceq Kric hCeq hKric hequiv hric
    m t htmem htpos x
  have hdiv : B.w m t x ≤
      (towerConst B.c B.α m) ^ 2 * B.K ^ 2 / t ^ m := by
    rw [le_div_iff₀ (pow_pos htpos m)]
    nlinarith
  simp only [B] at hdiv
  rw [hw'_val_le m le_rfl t x] at hdiv
  exact hdiv

end CompleteTruncation

/-- An explicit constants-first envelope for the complete Shi estimate.

The sum replaces two finite maxima: first over the reaction constants through
order `N`, then over the resulting Ricci-derivative bounds.  On a buffered slab
`alpha < beta <= psi` every summand is nonnegative, so this sum is a valid
common envelope.  Its important API property is that it depends on no flow or
sequence member. -/
noncomputable def shiOpenConst
    (d : Nat) (C alpha beta psi : Real) (N : Nat) : Real :=
  let K := max 1 C
  let c := max 0
    (∑ k ∈ Finset.range (N + 1), 2 * (d : Real) ^ (6 + k))
  Real.sqrt
    (∑ k ∈ Finset.range (N + 1),
      (d : Real) ^ ((2 + k) + 2) *
        ((towerConst c (K * (psi - alpha)) k) ^ 2 * K ^ 2 /
          ((beta - alpha) / 2) ^ k))

/-- The explicit complete-Shi envelope is nonnegative. -/
theorem shiOpenConst_nonneg
    (d : Nat) (C alpha beta psi : Real) (N : Nat) :
    0 <= shiOpenConst d C alpha beta psi N := by
  exact Real.sqrt_nonneg _

/-- Constants-first complete Shi estimate on a buffered slab.

This is the unique analytic proof frontier owned by this module.  Its future
proof assembles the arbitrary-dimensional solution tower, the complete
noncompact Bernstein maximum principle, the Ricci trace estimate, and metric
equivalence to the complete left-anchor metric.  The displayed constant is
independent of the particular flow, which is what permits the sequence
wrapper below. -/
theorem movingShi_of_bound
    {D : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D)
    {alpha beta psi C : Real}
    (halphaBeta : alpha < beta)
    (hbetaPsi : beta <= psi)
    (hslab : Set.Icc alpha psi ⊆ D.carrier)
    (hreg : Set.Ioc alpha psi ⊆ D.regular)
    (hcomplete : MetricComplete (I := I) (F.atTime (I := I) alpha))
    (hC : 0 <= C)
    (hcurv : ∀ t ∈ Set.Icc alpha psi, ∀ x : F.M,
      F.rmNormSq (I := I) t x <= C)
    (N : Nat) :
    letI : TopologicalSpace F.M := F.topology
    letI : ChartedSpace H F.M := F.charted
    letI : IsManifold I ∞ F.M := F.smooth
    letI : IsManifold I 1 F.M :=
      IsManifold.of_le (I := I) (M := F.M) (n := ∞) (by decide)
    letI : IsManifold I 2 F.M :=
      IsManifold.of_le (I := I) (M := F.M) (n := ∞) (by decide)
    letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) F.M := by
      change IsManifold I ∞ F.M
      infer_instance
    letI : SigmaCompactSpace F.M := F.sigmaCompact
    letI : T2Space F.M := F.t2
    MovingShiBoundOn (I := I) Set.univ beta psi
      (fun _ t => F.S.family.metric t) N
      (shiOpenConst (Module.finrank Real E) C alpha beta psi N) := by
  sorry

/-- A complete Ricci flow with a curvature bound on a larger left-buffered
slab has moving Shi bounds through every prescribed finite order. -/
theorem movingShi_complete
    {D : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D)
    {alpha beta psi C : Real}
    (halphaBeta : alpha < beta)
    (hbetaPsi : beta <= psi)
    (hslab : Set.Icc alpha psi ⊆ D.carrier)
    (hreg : Set.Ioc alpha psi ⊆ D.regular)
    (hcomplete : MetricComplete (I := I) (F.atTime (I := I) alpha))
    (hC : 0 <= C)
    (hcurv : ∀ t ∈ Set.Icc alpha psi, ∀ x : F.M,
      F.rmNormSq (I := I) t x <= C)
    (N : Nat) :
    ∃ KShi : Real, 0 <= KShi ∧
      letI : TopologicalSpace F.M := F.topology
      letI : ChartedSpace H F.M := F.charted
      letI : IsManifold I ∞ F.M := F.smooth
      letI : IsManifold I 1 F.M :=
        IsManifold.of_le (I := I) (M := F.M) (n := ∞) (by decide)
      letI : IsManifold I 2 F.M :=
        IsManifold.of_le (I := I) (M := F.M) (n := ∞) (by decide)
      letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) F.M := by
        change IsManifold I ∞ F.M
        infer_instance
      letI : SigmaCompactSpace F.M := F.sigmaCompact
      letI : T2Space F.M := F.t2
      MovingShiBoundOn (I := I) Set.univ beta psi
        (fun _ t => F.S.family.metric t) N KShi := by
  refine ⟨shiOpenConst (Module.finrank Real E) C alpha beta psi N,
    shiOpenConst_nonneg _ _ _ _ _ _, ?_⟩
  exact movingShi_of_bound (I := I) F halphaBeta hbetaPsi hslab hreg
    hcomplete hC hcurv N

namespace CurvBoundInput

/-- Uniform complete Shi estimates on every canonical compact window of a
pointed Ricci-flow sequence on an open interval.  The curvature constant is
chosen on the larger left-buffered slab before the sequence member, and the
same explicit Shi constant is then used for every member. -/
theorem movingShi_open
    {a b : Real} (h0 : (0 : Real) ∈ Set.Ioo a b)
    (X : PointedFlowSeq.{u, uE, uH} (I := I))
    (hD : X.D = RealTimeInterval.openInterval a b 0 h0)
    (hcomplete : CompleteInput (I := I) X)
    (hcurv : CurvBoundInput (I := I) X) :
    ∀ n N : Nat, ∃ KShi : Real, 0 <= KShi ∧
      ∀ k : Nat,
        letI : TopologicalSpace (X.term k).M := (X.term k).topology
        letI : ChartedSpace H (X.term k).M := (X.term k).charted
        letI : IsManifold I ∞ (X.term k).M := (X.term k).smooth
        letI : IsManifold I 1 (X.term k).M :=
          IsManifold.of_le (I := I) (M := (X.term k).M) (n := ∞) (by decide)
        letI : IsManifold I 2 (X.term k).M :=
          IsManifold.of_le (I := I) (M := (X.term k).M) (n := ∞) (by decide)
        letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) (X.term k).M := by
          change IsManifold I ∞ (X.term k).M
          infer_instance
        letI : SigmaCompactSpace (X.term k).M := (X.term k).sigmaCompact
        letI : T2Space (X.term k).M := (X.term k).t2
        MovingShiBoundOn (I := I) Set.univ
          (RealTimeInterval.openWindowLeft a 0 n)
          (RealTimeInterval.openWindowRight b 0 n)
          (fun _ t => (X.term k).S.family.metric t) N KShi := by
  intro n N
  let alpha := RealTimeInterval.openWindowLeft a 0 (n + 1)
  let beta := RealTimeInterval.openWindowLeft a 0 n
  let psi := RealTimeInterval.openWindowRight b 0 n
  have halphaBeta : alpha < beta := by
    have hnum : 0 < (0 : Real) - a := sub_pos.mpr h0.1
    have hdenAlpha : 0 < ((n + 1 : Nat) : Real) + 2 := by positivity
    have hdenBeta : 0 < (n : Real) + 2 := by positivity
    simp only [alpha, beta, RealTimeInterval.openWindowLeft]
    rw [add_lt_add_iff_left, div_lt_div_iff₀ hdenAlpha hdenBeta]
    norm_num at hdenAlpha ⊢
    nlinarith
  have hbetaPsi : beta <= psi := by
    simpa only [beta, psi, RealTimeInterval.openWindow] using
      (RealTimeInterval.initial_mem_window h0 n).1.trans
        (RealTimeInterval.initial_mem_window h0 n).2
  have hright : psi <= RealTimeInterval.openWindowRight b 0 (n + 1) := by
    have hmem : psi ∈ RealTimeInterval.openWindow a b 0 n := by
      exact ⟨hbetaPsi, le_rfl⟩
    have hmono := RealTimeInterval.openWindow_mono h0 (Nat.le_succ n) hmem
    exact hmono.2
  have hslab : Set.Icc alpha psi ⊆ X.D.carrier := by
    intro t ht
    have htWindow : t ∈ RealTimeInterval.openWindow a b 0 (n + 1) :=
      ⟨ht.1, ht.2.trans hright⟩
    rw [hD]
    exact RealTimeInterval.openWindow_subset h0 (n + 1) htWindow
  have hreg : Set.Ioc alpha psi ⊆ X.D.regular := by
    intro t ht
    have htWindow : t ∈ RealTimeInterval.openWindow a b 0 (n + 1) :=
      ⟨ht.1.le, ht.2.trans hright⟩
    rw [hD]
    exact RealTimeInterval.openWindow_subset h0 (n + 1) htWindow
  obtain ⟨C, hC, hcurvC⟩ := hcurv.bound_on_window alpha psi hslab
  let KShi := shiOpenConst (Module.finrank Real E) C alpha beta psi N
  refine ⟨KShi, shiOpenConst_nonneg _ _ _ _ _ _, ?_⟩
  intro k
  have halphaCarrier : alpha ∈ X.D.carrier :=
    hslab ⟨le_rfl, halphaBeta.le.trans hbetaPsi⟩
  exact movingShi_of_bound (I := I) (X.term k) halphaBeta hbetaPsi hslab hreg
    (hcomplete.complete_on k alpha halphaCarrier) hC
    (fun t ht x => hcurvC k t ht x) N

end CurvBoundInput
end HCGCompactness
end DifferentialGeometry
