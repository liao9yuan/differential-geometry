import DifferentialGeometry.Topology.Morse.LevelSet
import DifferentialGeometry.Topology.Morse.Manifold
import DifferentialGeometry.Analysis.ODE.CompactSupportFlow
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.Instances.Icc

namespace DifferentialGeometry.Topology.Morse

open DifferentialGeometry.Analysis.ODE
open scoped Manifold Topology

noncomputable section

variable {m : ℕ} {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M]
variable (I : ModelWithCorners ℝ (MorseModel (m + 1)) H)

theorem fderiv_sublevelPullback_ne_zero [I.Boundaryless] [IsManifold I (⊤ : WithTop ℕ∞) M]
    (f : M → ℝ) (hf : ContMDiff I 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞) f) (a : ℝ)
    (hreg : ∀ x : M, f x = a → ¬ IsCriticalPointAt I f x)
    {p : M} {y : MorseModel (m + 1)}
    (hy : f ((extChartAt I p).symm y) = a) (hyt : y ∈ (extChartAt I p).target) :
    fderiv ℝ (fun y : MorseModel (m + 1) => f ((extChartAt I p).symm y)) y ≠ 0 := by
  classical
  let q : M := (extChartAt I p).symm y
  have hq : f q = a := hy
  have hregq : ¬ IsCriticalPointAt I f q := hreg q hq
  have hψq : (extChartAt I p) q = y := (extChartAt I p).right_inv hyt
  have hleft : ((extChartAt I p).symm ∘ (extChartAt I p)) =ᶠ[nhds q] id := by
    have hsrc : q ∈ (extChartAt I p).source := (extChartAt I p).map_target hyt
    have hopen : IsOpen (extChartAt I p).source := isOpen_extChartAt_source (I := I) p
    exact Filter.eventuallyEq_of_mem (by simpa [q] using hopen.mem_nhds hsrc)
      (fun x hx => (extChartAt I p).left_inv hx)
  have hright : ((extChartAt I p) ∘ (extChartAt I p).symm) =ᶠ[nhds y] id := by
    exact Filter.eventuallyEq_of_mem ((isOpen_extChartAt_target (I := I) p).mem_nhds hyt)
      (fun x hx => (extChartAt I p).right_inv hx)
  have hσmd : MDifferentiableAt I 𝓘(ℝ, MorseModel (m + 1)) (extChartAt I p) q := by
    have hsrc : q ∈ (chartAt H p).source := by
      simpa [q, extChartAt_source (I := I)] using (extChartAt I p).map_target hyt
    exact (contMDiffAt_extChartAt' (I := I) (n := (↑(⊤ : ℕ∞) : WithTop ℕ∞)) (x := p)
      (by simpa [q] using hsrc)).mdifferentiableAt (by norm_num)
  have hτmd : MDifferentiableAt 𝓘(ℝ, MorseModel (m + 1)) I (extChartAt I p).symm y := by
    have hc : ContMDiffAt 𝓘(ℝ, MorseModel (m + 1)) I ((↑(⊤ : ℕ∞) : WithTop ℕ∞))
        (extChartAt I p).symm y := by
      have hon : ContMDiffOn 𝓘(ℝ, MorseModel (m + 1)) I ((↑(⊤ : ℕ∞) : WithTop ℕ∞))
          (extChartAt I p).symm (extChartAt I p).target :=
        contMDiffOn_extChartAt_symm (n := (↑(⊤ : ℕ∞) : WithTop ℕ∞)) p
      exact hon.contMDiffAt ((isOpen_extChartAt_target (I := I) p).mem_nhds hyt)
    exact hc.mdifferentiableAt (by norm_num)
  have hh : ContMDiffAt 𝓘(ℝ, MorseModel (m + 1)) 𝓘(ℝ, ℝ) ((↑(⊤ : ℕ∞) : WithTop ℕ∞))
      (f ∘ (extChartAt I p).symm) y := by
    have hc : ContMDiffAt 𝓘(ℝ, MorseModel (m + 1)) I ((↑(⊤ : ℕ∞) : WithTop ℕ∞))
        (extChartAt I p).symm y := by
      have hon : ContMDiffOn 𝓘(ℝ, MorseModel (m + 1)) I ((↑(⊤ : ℕ∞) : WithTop ℕ∞))
          (extChartAt I p).symm (extChartAt I p).target :=
        contMDiffOn_extChartAt_symm (n := (↑(⊤ : ℕ∞) : WithTop ℕ∞)) p
      exact hon.contMDiffAt ((isOpen_extChartAt_target (I := I) p).mem_nhds hyt)
    have hfq : ContMDiffAt I 𝓘(ℝ, ℝ) ((↑(⊤ : ℕ∞) : WithTop ℕ∞)) f q := hf q
    exact ContMDiffAt.comp (x := y) (g := f) (f := (extChartAt I p).symm)
      (hg := hfq) (hf := hc)
  have htrans : IsCriticalPointAt I ((f ∘ (extChartAt I p).symm) ∘ (extChartAt I p)) q ↔
      fderiv ℝ (f ∘ (extChartAt I p).symm) y = 0 := by
    have htr := isCriticalPointAt_iff_fderiv_of_localInverse I (x := q) (σ := (extChartAt I p))
      (τ := (extChartAt I p).symm) (h := f ∘ (extChartAt I p).symm)
      (hleft := hleft) (hright := by
        rw [hψq]
        exact hright)
      (hσmd := hσmd) (hτmd := by
        rw [hψq]
        exact hτmd) (hh := by
          rw [hψq]
          exact hh)
    rw [hψq] at htr
    exact htr
  have hfuneq : (f ∘ (extChartAt I p).symm) ∘ (extChartAt I p) =ᶠ[nhds q] f := by
    have hsrc : q ∈ (extChartAt I p).source := (extChartAt I p).map_target hyt
    have hopen : IsOpen (extChartAt I p).source := isOpen_extChartAt_source (I := I) p
    exact Filter.eventuallyEq_of_mem (by simpa [q] using hopen.mem_nhds hsrc)
      (fun x hx => congrArg f ((extChartAt I p).left_inv hx))
  have hcrit_eq : IsCriticalPointAt I ((f ∘ (extChartAt I p).symm) ∘ (extChartAt I p)) q ↔
      IsCriticalPointAt I f q := by
    change mfderiv I 𝓘(ℝ, ℝ) ((f ∘ (extChartAt I p).symm) ∘ (extChartAt I p)) q = 0 ↔
      mfderiv I 𝓘(ℝ, ℝ) f q = 0
    exact Iff.of_eq (congrArg (fun L : TangentSpace I q →L[ℝ] ℝ => L = 0)
      (Filter.EventuallyEq.mfderiv_eq (I := I) (I' := 𝓘(ℝ, ℝ)) hfuneq))
  have hne : fderiv ℝ (f ∘ (extChartAt I p).symm) y ≠ 0 := by
    intro hzero
    have hcrit : IsCriticalPointAt I ((f ∘ (extChartAt I p).symm) ∘ (extChartAt I p)) q :=
      htrans.2 hzero
    exact hregq (hcrit_eq.mp hcrit)
  change fderiv ℝ (fun y : MorseModel (m + 1) => f ((extChartAt I p).symm y)) y ≠ 0
  simpa [q] using hne

noncomputable def sublevelPullback (f : M → ℝ) (p : M) : MorseModel (m + 1) → ℝ :=
  fun y => f ((extChartAt I p).symm y)

theorem contDiffOn_sublevelPullback [I.Boundaryless] [IsManifold I (⊤ : WithTop ℕ∞) M]
    (f : M → ℝ) (hf : ContMDiff I 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞) f) (p : M) :
    ContDiffOn ℝ (⊤ : ℕ∞) (sublevelPullback I f p) (extChartAt I p).target := by
  have hcomp : ContMDiffOn 𝓘(ℝ, MorseModel (m + 1)) 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (fun y : MorseModel (m + 1) => f ((extChartAt I p).symm y)) (extChartAt I p).target := by
    exact hf.contMDiffOn.comp (t := (Set.univ : Set M)) (contMDiffOn_extChartAt_symm (I := I)
      (n := (↑(⊤ : ℕ∞) : WithTop ℕ∞)) p) (by intro y hy; exact Set.mem_preimage.mpr (Set.mem_univ _))
  have hcf : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun y : MorseModel (m + 1) => f ((extChartAt I p).symm y)) (extChartAt I p).target :=
    (contMDiffOn_iff_contDiffOn (𝕜 := ℝ) (E := MorseModel (m + 1)) (E' := ℝ)).mp hcomp
  simpa [sublevelPullback] using hcf

theorem sublevelPullbackBump_spec [I.Boundaryless] (x : M) :
    ∃ b : ContDiffBump ((extChartAt I x) x),
      Metric.closedBall ((extChartAt I x) x) b.rOut ⊆ (extChartAt I x).target := by
  classical
  let p : MorseModel (m + 1) := (extChartAt I x) x
  have hp : p ∈ (extChartAt I x).target :=
    (extChartAt I x).map_source (mem_extChartAt_source (I := I) x)
  rcases Metric.mem_nhds_iff.mp ((isOpen_extChartAt_target (I := I) x).mem_nhds hp) with
    ⟨δ, hδ, hball⟩
  let rOut : ℝ := δ / 2
  let rIn : ℝ := rOut / 2
  have hrOut : 0 < rOut := by
    dsimp [rOut]
    positivity
  have hrIn : 0 < rIn := by
    dsimp [rIn]
    positivity
  refine ⟨⟨rIn, rOut, hrIn, half_lt_self hrOut⟩, ?_⟩
  intro y hy
  exact hball (by
    rw [Metric.mem_ball]
    have hy' : dist y p ≤ rOut := by simpa [Metric.mem_closedBall] using hy
    exact lt_of_le_of_lt hy' (by dsimp [rOut]; exact half_lt_self hδ))

noncomputable def sublevelPullbackBump [I.Boundaryless] (x : M) :
    ContDiffBump ((extChartAt I x) x) :=
  Classical.choose (sublevelPullbackBump_spec I x)

theorem sublevelPullbackBump_closedBall_target [I.Boundaryless] (x : M) :
    Metric.closedBall ((extChartAt I x) x) (sublevelPullbackBump I x).rOut ⊆
      (extChartAt I x).target :=
  Classical.choose_spec (sublevelPullbackBump_spec I x)

noncomputable def sublevelPullbackCutoff (f : M → ℝ) (x : M)
    (b : ContDiffBump ((extChartAt I x) x)) : MorseModel (m + 1) → ℝ :=
  fun y => b y * sublevelPullback I f x y

theorem sublevelPullbackCutoff_eqOn (f : M → ℝ) (x : M) (b : ContDiffBump ((extChartAt I x) x))
    {y : MorseModel (m + 1)} (hy : y ∈ Metric.ball ((extChartAt I x) x) b.rIn) :
    sublevelPullbackCutoff I f x b y = sublevelPullback I f x y := by
  have hb : b y = 1 := b.one_of_mem_closedBall (Metric.ball_subset_closedBall hy)
  unfold sublevelPullbackCutoff
  rw [hb, one_mul]

theorem sublevelPullbackCutoff_eventuallyEq [I.Boundaryless] [IsManifold I (⊤ : WithTop ℕ∞) M]
    (f : M → ℝ) (x : M) (b : ContDiffBump ((extChartAt I x) x)) :
    sublevelPullbackCutoff I f x b =ᶠ[nhds ((extChartAt I x) x)] sublevelPullback I f x := by
  exact Filter.eventuallyEq_of_mem (Metric.ball_mem_nhds ((extChartAt I x) x) b.rIn_pos)
    (fun z hz => sublevelPullbackCutoff_eqOn I f x b hz)

theorem contDiff_sublevelPullbackCutoff [I.Boundaryless] [IsManifold I (⊤ : WithTop ℕ∞) M]
    (f : M → ℝ) (hf : ContMDiff I 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞) f) (x : M)
    (b : ContDiffBump ((extChartAt I x) x))
    (hb : Metric.closedBall ((extChartAt I x) x) b.rOut ⊆ (extChartAt I x).target) :
    ContDiff ℝ (⊤ : ℕ∞) (sublevelPullbackCutoff I f x b) := by
  classical
  let p : MorseModel (m + 1) := (extChartAt I x) x
  have hball : Metric.ball p b.rIn ⊆ (extChartAt I x).target := by
    exact ((Metric.ball_subset_ball (le_of_lt b.rIn_lt_rOut)).trans
      Metric.ball_subset_closedBall).trans hb
  rw [← contDiffOn_univ]
  intro y hy
  rw [contDiffWithinAt_univ]
  by_cases hy : ‖y - p‖ ≤ b.rOut
  · have hyc : y ∈ Metric.closedBall p b.rOut := by
      rw [Metric.mem_closedBall]
      exact hy
    have hg : ContDiffAt ℝ (⊤ : ℕ∞) (sublevelPullback I f x) y := by
      exact (contDiffOn_sublevelPullback I f hf x).contDiffAt
        ((isOpen_extChartAt_target (I := I) x).mem_nhds (hb hyc))
    change ContDiffAt ℝ (⊤ : ℕ∞) (fun z : MorseModel (m + 1) =>
      (b : MorseModel (m + 1) → ℝ) z * sublevelPullback I f x z) y
    exact b.contDiffAt.mul hg
  · have hy' : b.rOut < ‖y - p‖ := lt_of_not_ge hy
    have hopen : IsOpen {z : MorseModel (m + 1) | b.rOut < ‖z - p‖} := by
      exact isOpen_lt continuous_const
        (continuous_norm.comp (continuous_id.sub continuous_const))
    have hzero : (fun z : MorseModel (m + 1) => sublevelPullbackCutoff I f x b z) =ᶠ[nhds y]
        (fun _ : MorseModel (m + 1) => (0 : ℝ)) := by
      filter_upwards [hopen.mem_nhds hy'] with z hz
      unfold sublevelPullbackCutoff
      have hb0 : b z = 0 := b.zero_of_le_dist (by
        change b.rOut ≤ dist z p
        rw [dist_eq_norm]
        exact le_of_lt hz)
      rw [hb0, zero_mul]
    exact (contDiffAt_const : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun _ : MorseModel (m + 1) => (0 : ℝ)) y).congr_of_eventuallyEq hzero

theorem fderiv_sublevelPullbackCutoff_ne_zero [I.Boundaryless] [IsManifold I (⊤ : WithTop ℕ∞) M]
    (f : M → ℝ) (x : M) (b : ContDiffBump ((extChartAt I x) x))
    (hne : fderiv ℝ (sublevelPullback I f x) ((extChartAt I x) x) ≠ 0) :
    fderiv ℝ (sublevelPullbackCutoff I f x b) ((extChartAt I x) x) ≠ 0 := by
  intro h
  apply hne
  rw [← (sublevelPullbackCutoff_eventuallyEq I f x b).fderiv_eq]
  exact h

noncomputable def sublevelPullbackCutoffPoint (f : M → ℝ) (a : ℝ) (x : SublevelSpace f a)
    (b : ContDiffBump ((extChartAt I x.1) x.1)) :
    SublevelSpace (sublevelPullbackCutoff I f x.1 b) a :=
  ⟨(extChartAt I x.1) x.1, by
    change (sublevelPullbackCutoff I f x.1 b) ((extChartAt I x.1) x.1) ≤ a
    have hpball : (extChartAt I x.1) x.1 ∈ Metric.ball ((extChartAt I x.1) x.1) b.rIn :=
      Metric.mem_ball_self b.rIn_pos
    rw [sublevelPullbackCutoff_eqOn I f x.1 b hpball]
    change f ((extChartAt I x.1).symm ((extChartAt I x.1) x.1)) ≤ a
    rw [(extChartAt I x.1).left_inv (mem_extChartAt_source (I := I) x.1)]
    exact x.2⟩

theorem sublevelPullbackCutoffPoint_value (f : M → ℝ) (a : ℝ) (x : SublevelSpace f a)
    (b : ContDiffBump ((extChartAt I x.1) x.1)) (hx : f x.1 = a) :
    (sublevelPullbackCutoff I f x.1 b) (sublevelPullbackCutoffPoint I f a x b).1 = a := by
  change (sublevelPullbackCutoff I f x.1 b) ((extChartAt I x.1) x.1) = a
  have hpball : (extChartAt I x.1) x.1 ∈ Metric.ball ((extChartAt I x.1) x.1) b.rIn :=
    Metric.mem_ball_self b.rIn_pos
  rw [sublevelPullbackCutoff_eqOn I f x.1 b hpball]
  change f ((extChartAt I x.1).symm ((extChartAt I x.1) x.1)) = a
  rw [(extChartAt I x.1).left_inv (mem_extChartAt_source (I := I) x.1)]
  exact hx

theorem sublevelPullbackCutoffPoint_value_lt (f : M → ℝ) (a : ℝ) (x : SublevelSpace f a)
    (b : ContDiffBump ((extChartAt I x.1) x.1)) (hx : f x.1 < a) :
    (sublevelPullbackCutoff I f x.1 b) (sublevelPullbackCutoffPoint I f a x b).1 < a := by
  change (sublevelPullbackCutoff I f x.1 b) ((extChartAt I x.1) x.1) < a
  have hpball : (extChartAt I x.1) x.1 ∈ Metric.ball ((extChartAt I x.1) x.1) b.rIn :=
    Metric.mem_ball_self b.rIn_pos
  rw [sublevelPullbackCutoff_eqOn I f x.1 b hpball]
  change f ((extChartAt I x.1).symm ((extChartAt I x.1) x.1)) < a
  rw [(extChartAt I x.1).left_inv (mem_extChartAt_source (I := I) x.1)]
  exact hx

theorem fderiv_sublevelPullbackCutoffPoint_ne_zero [I.Boundaryless]
    [IsManifold I (⊤ : WithTop ℕ∞) M] (f : M → ℝ)
    (hf : ContMDiff I 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞) f) (a : ℝ)
    (hreg : ∀ x : M, f x = a → ¬ IsCriticalPointAt I f x) (x : SublevelSpace f a)
    (b : ContDiffBump ((extChartAt I x.1) x.1)) (hx : f x.1 = a) :
    fderiv ℝ (sublevelPullbackCutoff I f x.1 b) (sublevelPullbackCutoffPoint I f a x b).1 ≠ 0 := by
  change fderiv ℝ (sublevelPullbackCutoff I f x.1 b) ((extChartAt I x.1) x.1) ≠ 0
  apply fderiv_sublevelPullbackCutoff_ne_zero I f x.1 b
  have hx₀ : f ((extChartAt I x.1).symm ((extChartAt I x.1) x.1)) = a := by
    rw [(extChartAt I x.1).left_inv (mem_extChartAt_source (I := I) x.1)]
    exact hx
  have hyt : (extChartAt I x.1) x.1 ∈ (extChartAt I x.1).target :=
    (extChartAt I x.1).map_source (mem_extChartAt_source (I := I) x.1)
  exact fderiv_sublevelPullback_ne_zero I f hf a hreg hx₀ hyt

noncomputable def sublevelPullbackChart (f : M → ℝ) (a : ℝ) (x : SublevelSpace f a)
    (b : ContDiffBump ((extChartAt I x.1) x.1))
    (hb : Metric.closedBall ((extChartAt I x.1) x.1) b.rOut ⊆ (extChartAt I x.1).target) :
    OpenPartialHomeomorph (SublevelSpace f a)
      (SublevelSpace (sublevelPullbackCutoff I f x.1 b) a) := by
  classical
  let e : PartialEquiv M (MorseModel (m + 1)) := extChartAt I x.1
  let p : MorseModel (m + 1) := (extChartAt I x.1) x.1
  let toFun' : SublevelSpace f a → SublevelSpace (sublevelPullbackCutoff I f x.1 b) a :=
    fun x' =>
      if hx : x'.1 ∈ e.source ∧ e x'.1 ∈ Metric.ball p b.rIn then
        ⟨e x'.1, by
          change (sublevelPullbackCutoff I f x.1 b) (e x'.1) ≤ a
          rw [sublevelPullbackCutoff_eqOn I f x.1 b hx.2]
          change f ((extChartAt I x.1).symm (e x'.1)) ≤ a
          rw [(extChartAt I x.1).left_inv hx.1]
          exact x'.2⟩
      else
        ⟨p, by
          change (sublevelPullbackCutoff I f x.1 b) p ≤ a
          have hpball : p ∈ Metric.ball p b.rIn := Metric.mem_ball_self b.rIn_pos
          rw [sublevelPullbackCutoff_eqOn I f x.1 b hpball]
          change f ((extChartAt I x.1).symm ((extChartAt I x.1) x.1)) ≤ a
          rw [(extChartAt I x.1).left_inv (mem_extChartAt_source (I := I) x.1)]
          exact x.2⟩
  let invFun' : SublevelSpace (sublevelPullbackCutoff I f x.1 b) a → SublevelSpace f a :=
    fun z =>
      if hz : z.1 ∈ Metric.ball p b.rIn then
        ⟨(extChartAt I x.1).symm z.1, by
          change f ((extChartAt I x.1).symm z.1) ≤ a
          change (sublevelPullback I f x.1 z.1) ≤ a
          rw [← sublevelPullbackCutoff_eqOn I f x.1 b hz]
          exact z.2⟩
      else ⟨x.1, x.2⟩
  exact
    { toPartialEquiv :=
        { toFun := toFun'
          invFun := invFun'
          source := {x' : SublevelSpace f a | x'.1 ∈ e.source ∧ e x'.1 ∈ Metric.ball p b.rIn}
          target := {z : SublevelSpace (sublevelPullbackCutoff I f x.1 b) a |
            z.1 ∈ Metric.ball p b.rIn}
          map_source' := by
            intro x' hx'
            change x'.1 ∈ e.source ∧ e x'.1 ∈ Metric.ball p b.rIn at hx'
            change (toFun' x').1 ∈ Metric.ball p b.rIn
            simp only [toFun']
            rw [dif_pos hx']
            exact hx'.2
          map_target' := by
            intro z hz
            change z.1 ∈ Metric.ball p b.rIn at hz
            change (invFun' z).1 ∈ e.source ∧ e ((invFun' z).1) ∈ Metric.ball p b.rIn
            simp only [invFun']
            rw [dif_pos hz]
            change (extChartAt I x.1).symm z.1 ∈ e.source ∧
              e ((extChartAt I x.1).symm z.1) ∈ Metric.ball p b.rIn
            have hzt : z.1 ∈ (extChartAt I x.1).target :=
              ((Metric.ball_subset_ball (le_of_lt b.rIn_lt_rOut)).trans
                Metric.ball_subset_closedBall).trans hb hz
            constructor
            · exact (extChartAt I x.1).map_target hzt
            · rw [(extChartAt I x.1).right_inv hzt]
              exact hz
          left_inv' := by
            intro x' hx'
            change x'.1 ∈ e.source ∧ e x'.1 ∈ Metric.ball p b.rIn at hx'
            apply Subtype.ext
            change (invFun' (toFun' x')).1 = x'.1
            simp only [toFun']
            rw [dif_pos hx']
            simp only [invFun']
            rw [dif_pos (by exact hx'.2)]
            change (extChartAt I x.1).symm (e x'.1) = x'.1
            exact (extChartAt I x.1).left_inv hx'.1
          right_inv' := by
            intro z hz
            change z.1 ∈ Metric.ball p b.rIn at hz
            apply Subtype.ext
            change (toFun' (invFun' z)).1 = z.1
            simp only [invFun']
            rw [dif_pos hz]
            have hzt : z.1 ∈ (extChartAt I x.1).target :=
              ((Metric.ball_subset_ball (le_of_lt b.rIn_lt_rOut)).trans
                Metric.ball_subset_closedBall).trans hb hz
            have hsrc : (extChartAt I x.1).symm z.1 ∈ e.source :=
              (extChartAt I x.1).map_target hzt
            have hcond : (extChartAt I x.1).symm z.1 ∈ e.source ∧
                e ((extChartAt I x.1).symm z.1) ∈ Metric.ball p b.rIn := by
              constructor
              · exact hsrc
              · rw [(extChartAt I x.1).right_inv hzt]
                exact hz
            simp only [toFun']
            rw [dif_pos hcond]
            change (extChartAt I x.1) ((extChartAt I x.1).symm z.1) = z.1
            exact (extChartAt I x.1).right_inv hzt }
      open_source := by
        have hcont : Continuous (fun x' : SublevelSpace f a => (x' : M)) := continuous_subtype_val
        have h₁ : IsOpen {x' : SublevelSpace f a | x'.1 ∈ e.source} :=
          (isOpen_extChartAt_source (I := I) x.1).preimage hcont
        have hf : ContinuousOn (fun x' : SublevelSpace f a => e x'.1)
            {x' : SublevelSpace f a | x'.1 ∈ e.source} := by
          exact (continuousOn_extChartAt x.1).comp hcont.continuousOn (by intro x' hx'; exact hx')
        simpa using (hf.isOpen_inter_preimage h₁ (Metric.isOpen_ball))
      open_target := by
        have hcont : Continuous (fun z : SublevelSpace (sublevelPullbackCutoff I f x.1 b) a =>
            (z : MorseModel (m + 1))) := continuous_subtype_val
        exact (Metric.isOpen_ball).preimage hcont
      continuousOn_toFun := by
        refine continuousOn_iff_continuous_restrict.mpr ?_
        have hcont : Continuous (fun x' : {x' : SublevelSpace f a |
            x'.1 ∈ e.source ∧ e x'.1 ∈ Metric.ball p b.rIn} => e x'.1.1) := by
          exact continuousOn_univ.mp ((continuousOn_extChartAt x.1).comp
            (Continuous.continuousOn (continuous_subtype_val.comp continuous_subtype_val))
            (by intro x' hx'; exact x'.2.1))
        refine (Continuous.subtype_mk hcont (by
          intro x'
          change (sublevelPullbackCutoff I f x.1 b) (e x'.1.1) ≤ a
          rw [sublevelPullbackCutoff_eqOn I f x.1 b x'.2.2]
          change f ((extChartAt I x.1).symm (e x'.1.1)) ≤ a
          rw [(extChartAt I x.1).left_inv x'.2.1]
          exact x'.1.2)).congr ?_
        intro x'
        simp only [Set.restrict]
        apply Subtype.ext
        change e x'.1.1 = (toFun' x'.1).1
        simp only [toFun']
        rw [dif_pos (show x'.1.1 ∈ e.source ∧ e x'.1.1 ∈ Metric.ball p b.rIn from x'.2)]
      continuousOn_invFun := by
        refine continuousOn_iff_continuous_restrict.mpr ?_
        have hcont : Continuous (fun z : {z : SublevelSpace (sublevelPullbackCutoff I f x.1 b) a |
            z.1 ∈ Metric.ball p b.rIn} => (extChartAt I x.1).symm z.1.1) := by
          exact continuousOn_univ.mp ((continuousOn_extChartAt_symm x.1).comp
            (Continuous.continuousOn (continuous_subtype_val.comp continuous_subtype_val))
            (by intro z hz; exact ((Metric.ball_subset_ball (le_of_lt b.rIn_lt_rOut)).trans
              Metric.ball_subset_closedBall).trans hb z.2))
        refine (Continuous.subtype_mk hcont (by
          intro z
          change f ((extChartAt I x.1).symm z.1.1) ≤ a
          change (sublevelPullback I f x.1 z.1.1) ≤ a
          rw [← sublevelPullbackCutoff_eqOn I f x.1 b z.2]
          exact z.1.2)).congr ?_
        intro z
        simp only [Set.restrict]
        apply Subtype.ext
        change (extChartAt I x.1).symm z.1.1 = (invFun' z.1).1
        simp only [invFun']
        rw [dif_pos (show z.1.1 ∈ Metric.ball p b.rIn from z.2)]
      }

theorem mem_sublevelPullbackChart_source (f : M → ℝ) (a : ℝ) (x : SublevelSpace f a)
    (b : ContDiffBump ((extChartAt I x.1) x.1))
    (hb : Metric.closedBall ((extChartAt I x.1) x.1) b.rOut ⊆ (extChartAt I x.1).target) :
    x ∈ (sublevelPullbackChart I f a x b hb).source := by
  simpa [sublevelPullbackChart] using (show x.1 ∈ (extChartAt I x.1).source ∧
    (extChartAt I x.1) x.1 ∈ Metric.ball ((extChartAt I x.1) x.1) b.rIn from by
      constructor
      · exact mem_extChartAt_source (I := I) x.1
      · exact Metric.mem_ball_self b.rIn_pos)

theorem sublevelPullbackChart_apply_of_mem (f : M → ℝ) (a : ℝ) (x : SublevelSpace f a)
    (b : ContDiffBump ((extChartAt I x.1) x.1))
    (hb : Metric.closedBall ((extChartAt I x.1) x.1) b.rOut ⊆ (extChartAt I x.1).target)
    {x' : SublevelSpace f a} (hx : x' ∈ (sublevelPullbackChart I f a x b hb).source) :
    (sublevelPullbackChart I f a x b hb x').1 = (extChartAt I x.1) x'.1 := by
  have hx' : x'.1 ∈ (extChartAt I x.1).source ∧
      (extChartAt I x.1) x'.1 ∈ Metric.ball ((extChartAt I x.1) x.1) b.rIn := by
    simpa [sublevelPullbackChart] using hx
  change x'.1 ∈ (chartAt H x.1).source ∩ (chartAt H x.1) ⁻¹' I.source ∧
      I ((chartAt H x.1) x'.1) ∈ Metric.ball (I ((chartAt H x.1) x.1)) b.rIn at hx'
  dsimp [sublevelPullbackChart]
  rw [dif_pos hx']

theorem sublevelPullbackChart_symm_value (f : M → ℝ) (a : ℝ) (x : SublevelSpace f a)
    (b : ContDiffBump ((extChartAt I x.1) x.1))
    (hb : Metric.closedBall ((extChartAt I x.1) x.1) b.rOut ⊆ (extChartAt I x.1).target)
    {z : SublevelSpace (sublevelPullbackCutoff I f x.1 b) a}
    (hz : z ∈ (sublevelPullbackChart I f a x b hb).target) :
    ((sublevelPullbackChart I f a x b hb).symm z).1 = (extChartAt I x.1).symm z.1 := by
  have hz' : z.1 ∈ Metric.ball ((extChartAt I x.1) x.1) b.rIn := by
    simpa [sublevelPullbackChart] using hz
  change z.1 ∈ Metric.ball (I ((chartAt H x.1) x.1)) b.rIn at hz'
  dsimp [sublevelPullbackChart]
  rw [dif_pos hz']

noncomputable def sublevelChartTransition (x₁ x₂ : M) : MorseModel (m + 1) → MorseModel (m + 1) :=
  fun y => (extChartAt I x₂) ((extChartAt I x₁).symm y)

noncomputable def sublevelChartTransitionDomain (x₁ x₂ : M) : Set (MorseModel (m + 1)) :=
  {y : MorseModel (m + 1) | y ∈ (extChartAt I x₁).target ∧
    (extChartAt I x₁).symm y ∈ (extChartAt I x₂).source}

theorem isOpen_sublevelChartTransitionDomain [I.Boundaryless] (x₁ x₂ : M) :
    IsOpen (sublevelChartTransitionDomain I x₁ x₂) := by
  have hcont : ContinuousOn (extChartAt I x₁).symm (extChartAt I x₁).target :=
    continuousOn_extChartAt_symm x₁
  simpa [sublevelChartTransitionDomain] using
    (hcont.isOpen_inter_preimage (isOpen_extChartAt_target (I := I) x₁)
      (isOpen_extChartAt_source (I := I) x₂))

theorem contDiffOn_sublevelChartTransition [I.Boundaryless] [IsManifold I (⊤ : WithTop ℕ∞) M]
    (x₁ x₂ : M) :
    ContDiffOn ℝ (⊤ : ℕ∞) (sublevelChartTransition I x₁ x₂)
      (sublevelChartTransitionDomain I x₁ x₂) := by
  have hcomp : ContMDiffOn 𝓘(ℝ, MorseModel (m + 1)) 𝓘(ℝ, MorseModel (m + 1))
      (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (fun y : MorseModel (m + 1) => (extChartAt I x₂) ((extChartAt I x₁).symm y))
      (sublevelChartTransitionDomain I x₁ x₂) := by
    simpa [sublevelChartTransitionDomain, extChartAt_source] using
      ((contMDiffOn_extChartAt (I := I) (n := (↑(⊤ : ℕ∞) : WithTop ℕ∞)) (x := x₂)).comp'
        (contMDiffOn_extChartAt_symm (I := I) (n := (↑(⊤ : ℕ∞) : WithTop ℕ∞)) x₁))
  have hcf : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun y : MorseModel (m + 1) => (extChartAt I x₂) ((extChartAt I x₁).symm y))
      (sublevelChartTransitionDomain I x₁ x₂) :=
    (contMDiffOn_iff_contDiffOn (𝕜 := ℝ) (E := MorseModel (m + 1))
      (E' := MorseModel (m + 1))).mp hcomp
  simpa [sublevelChartTransition, sublevelChartTransitionDomain, extChartAt_source] using hcf

noncomputable def manifoldSublevelBoundaryChart [I.Boundaryless]
    [IsManifold I (⊤ : WithTop ℕ∞) M] (f : M → ℝ) (a : ℝ)
    (x : SublevelSpace f a) (hx : f x.1 = a)
    (hf : ContMDiff I 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞) f)
    (hreg : ∀ x : M, f x = a → ¬ IsCriticalPointAt I f x) :
    OpenPartialHomeomorph (SublevelSpace f a) (MorseHalfSpace m) :=
  let b : ContDiffBump ((extChartAt I x.1) x.1) := sublevelPullbackBump I x.1
  let hb : Metric.closedBall ((extChartAt I x.1) x.1) b.rOut ⊆ (extChartAt I x.1).target :=
    sublevelPullbackBump_closedBall_target (I := I) x.1
  sublevelPullbackChart I f a x b hb ≫ₕ
    sublevelBoundaryChart (sublevelPullbackCutoff I f x.1 b) a
      (sublevelPullbackCutoffPoint I f a x b)
      (sublevelPullbackCutoffPoint_value I f a x b hx)
      (contDiff_sublevelPullbackCutoff I f hf x.1 b hb)
      (fderiv_sublevelPullbackCutoffPoint_ne_zero I f hf a hreg x b hx)

noncomputable def manifoldSublevelInteriorChart [I.Boundaryless]
    [IsManifold I (⊤ : WithTop ℕ∞) M] (f : M → ℝ) (a : ℝ)
    (x : SublevelSpace f a) (hx : f x.1 < a)
    (hf : ContMDiff I 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞) f) :
    OpenPartialHomeomorph (SublevelSpace f a) (MorseHalfSpace m) :=
  let b : ContDiffBump ((extChartAt I x.1) x.1) := sublevelPullbackBump I x.1
  let hb : Metric.closedBall ((extChartAt I x.1) x.1) b.rOut ⊆ (extChartAt I x.1).target :=
    sublevelPullbackBump_closedBall_target (I := I) x.1
  sublevelPullbackChart I f a x b hb ≫ₕ
    sublevelInteriorChart (sublevelPullbackCutoff I f x.1 b) a
      (sublevelPullbackCutoffPoint I f a x b)
      (sublevelPullbackCutoffPoint_value_lt I f a x b hx)
      (contDiff_sublevelPullbackCutoff I f hf x.1 b hb)

theorem mem_manifoldSublevelBoundaryChart_source [I.Boundaryless]
    [IsManifold I (⊤ : WithTop ℕ∞) M] (f : M → ℝ) (a : ℝ)
    (x : SublevelSpace f a) (hx : f x.1 = a)
    (hf : ContMDiff I 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞) f)
    (hreg : ∀ x : M, f x = a → ¬ IsCriticalPointAt I f x) :
    x ∈ (manifoldSublevelBoundaryChart I f a x hx hf hreg).source := by
  let b : ContDiffBump ((extChartAt I x.1) x.1) := sublevelPullbackBump I x.1
  let hb : Metric.closedBall ((extChartAt I x.1) x.1) b.rOut ⊆ (extChartAt I x.1).target :=
    sublevelPullbackBump_closedBall_target (I := I) x.1
  dsimp [manifoldSublevelBoundaryChart]
  constructor
  · exact mem_sublevelPullbackChart_source I f a x b hb
  · change (sublevelPullbackChart I f a x b hb) x ∈
      (sublevelBoundaryChart (sublevelPullbackCutoff I f x.1 b) a
        (sublevelPullbackCutoffPoint I f a x b)
        (sublevelPullbackCutoffPoint_value I f a x b hx)
        (contDiff_sublevelPullbackCutoff I f hf x.1 b hb)
        (fderiv_sublevelPullbackCutoffPoint_ne_zero I f hf a hreg x b hx)).source
    have hpt : (sublevelPullbackChart I f a x b hb) x = sublevelPullbackCutoffPoint I f a x b := by
      apply Subtype.ext
      change ((sublevelPullbackChart I f a x b hb) x).1 = (sublevelPullbackCutoffPoint I f a x b).1
      rw [sublevelPullbackChart_apply_of_mem I f a x b hb
        (mem_sublevelPullbackChart_source I f a x b hb)]
      rfl
    rw [hpt]
    exact mem_sublevelBoundaryChart_source (sublevelPullbackCutoff I f x.1 b) a
      (sublevelPullbackCutoffPoint I f a x b)
      (sublevelPullbackCutoffPoint_value I f a x b hx)
      (contDiff_sublevelPullbackCutoff I f hf x.1 b hb)
      (fderiv_sublevelPullbackCutoffPoint_ne_zero I f hf a hreg x b hx)

theorem mem_manifoldSublevelInteriorChart_source [I.Boundaryless]
    [IsManifold I (⊤ : WithTop ℕ∞) M] (f : M → ℝ) (a : ℝ)
    (x : SublevelSpace f a) (hx : f x.1 < a)
    (hf : ContMDiff I 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞) f) :
    x ∈ (manifoldSublevelInteriorChart I f a x hx hf).source := by
  let b : ContDiffBump ((extChartAt I x.1) x.1) := sublevelPullbackBump I x.1
  let hb : Metric.closedBall ((extChartAt I x.1) x.1) b.rOut ⊆ (extChartAt I x.1).target :=
    sublevelPullbackBump_closedBall_target (I := I) x.1
  dsimp [manifoldSublevelInteriorChart]
  constructor
  · exact mem_sublevelPullbackChart_source I f a x b hb
  · change (sublevelPullbackChart I f a x b hb) x ∈
      (sublevelInteriorChart (sublevelPullbackCutoff I f x.1 b) a
        (sublevelPullbackCutoffPoint I f a x b)
        (sublevelPullbackCutoffPoint_value_lt I f a x b hx)
        (contDiff_sublevelPullbackCutoff I f hf x.1 b hb)).source
    have hpt : (sublevelPullbackChart I f a x b hb) x = sublevelPullbackCutoffPoint I f a x b := by
      apply Subtype.ext
      change ((sublevelPullbackChart I f a x b hb) x).1 = (sublevelPullbackCutoffPoint I f a x b).1
      rw [sublevelPullbackChart_apply_of_mem I f a x b hb
        (mem_sublevelPullbackChart_source I f a x b hb)]
      rfl
    rw [hpt]
    exact mem_sublevelInteriorChart_source (sublevelPullbackCutoff I f x.1 b) a
      (sublevelPullbackCutoffPoint I f a x b)
      (sublevelPullbackCutoffPoint_value_lt I f a x b hx)
      (contDiff_sublevelPullbackCutoff I f hf x.1 b hb)

private theorem sublevelPullbackChart_transition_mem_aux
    [I.Boundaryless] [IsManifold I (⊤ : WithTop ℕ∞) M]
    (f : M → ℝ) (a : ℝ) (x₁ x₂ : SublevelSpace f a)
    (b₁ : ContDiffBump ((extChartAt I x₁.1) x₁.1))
    (hb₁ : Metric.closedBall ((extChartAt I x₁.1) x₁.1) b₁.rOut ⊆ (extChartAt I x₁.1).target)
    (b₂ : ContDiffBump ((extChartAt I x₂.1) x₂.1))
    (hb₂ : Metric.closedBall ((extChartAt I x₂.1) x₂.1) b₂.rOut ⊆ (extChartAt I x₂.1).target)
    (m₁ : OpenPartialHomeomorph (SublevelSpace (sublevelPullbackCutoff I f x₁.1 b₁) a)
      (MorseHalfSpace m))
    (m₂ : OpenPartialHomeomorph (SublevelSpace (sublevelPullbackCutoff I f x₂.1 b₂) a)
      (MorseHalfSpace m))
    {y : MorseModel (m + 1)}
    (hy : y ∈ (morseModelWithCornersHalfSpace m).symm ⁻¹'
        ((sublevelPullbackChart I f a x₁ b₁ hb₁ ≫ₕ m₁).symm ≫ₕ
          (sublevelPullbackChart I f a x₂ b₂ hb₂ ≫ₕ m₂)).source ∩
      Set.range (morseModelWithCornersHalfSpace m)) :
    (morseModelWithCornersHalfSpace m).symm y ∈ m₁.target ∧
    m₁.symm ((morseModelWithCornersHalfSpace m).symm y) ∈
      (sublevelPullbackChart I f a x₁ b₁ hb₁).target ∧
    (sublevelPullbackChart I f a x₁ b₁ hb₁).symm (m₁.symm ((morseModelWithCornersHalfSpace m).symm y)) ∈
      (sublevelPullbackChart I f a x₂ b₂ hb₂).source ∧
    (sublevelPullbackChart I f a x₂ b₂ hb₂)
      ((sublevelPullbackChart I f a x₁ b₁ hb₁).symm (m₁.symm ((morseModelWithCornersHalfSpace m).symm y))) ∈
      m₂.source := by
  classical
  let I' : ModelWithCorners ℝ (MorseModel (m + 1)) (MorseHalfSpace m) :=
    morseModelWithCornersHalfSpace m
  let e₁ : OpenPartialHomeomorph (SublevelSpace f a)
      (SublevelSpace (sublevelPullbackCutoff I f x₁.1 b₁) a) :=
    sublevelPullbackChart I f a x₁ b₁ hb₁
  let e₂ : OpenPartialHomeomorph (SublevelSpace f a)
      (SublevelSpace (sublevelPullbackCutoff I f x₂.1 b₂) a) :=
    sublevelPullbackChart I f a x₂ b₂ hb₂
  let c₁ : OpenPartialHomeomorph (SublevelSpace f a) (MorseHalfSpace m) := e₁ ≫ₕ m₁
  let c₂ : OpenPartialHomeomorph (SublevelSpace f a) (MorseHalfSpace m) := e₂ ≫ₕ m₂
  have hy2 : y ∈ Set.range I' := hy.2
  have hy2' : 0 ≤ y (Fin.last m) := by
    rw [range_morseModelWithCornersHalfSpace] at hy2
    exact hy2
  let z : MorseHalfSpace m := ⟨y, hy2'⟩
  have hclamp : I'.symm y = z := by
    apply Subtype.ext
    exact morseHalfSpaceClamp_of_mem m hy2'
  have hy1 : z ∈ (c₁.symm ≫ₕ c₂).source := by
    rw [← hclamp]
    exact hy.1
  have hz1 : z ∈ c₁.target := by
    rw [OpenPartialHomeomorph.trans_source] at hy1
    simpa using hy1.1
  have hz1c : z ∈ (e₁ ≫ₕ m₁).target := by
    simpa [c₁] using hz1
  have hm₁ : z ∈ m₁.target := by
    rw [OpenPartialHomeomorph.trans_target] at hz1c
    exact hz1c.1
  have hme₁ : m₁.symm z ∈ e₁.target := by
    rw [OpenPartialHomeomorph.trans_target] at hz1c
    exact hz1c.2
  have hc₁₂ : c₁.symm z ∈ c₂.source := by
    rw [OpenPartialHomeomorph.trans_source] at hy1
    exact hy1.2
  have hcs : c₁.symm z = e₁.symm (m₁.symm z) := by
    rw [show c₁.symm = (e₁ ≫ₕ m₁).symm from rfl]
    rw [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm]
    rfl
  have hc₁₂e₂ : e₁.symm (m₁.symm z) ∈ e₂.source := by
    simpa [hcs] using hc₁₂.1
  have hm₂ : e₂ (e₁.symm (m₁.symm z)) ∈ m₂.source := by
    rw [OpenPartialHomeomorph.trans_source] at hc₁₂
    simpa [hcs] using hc₁₂.2
  change (morseModelWithCornersHalfSpace m).symm y ∈ m₁.target ∧
    m₁.symm ((morseModelWithCornersHalfSpace m).symm y) ∈ e₁.target ∧
    e₁.symm (m₁.symm ((morseModelWithCornersHalfSpace m).symm y)) ∈ e₂.source ∧
    e₂ (e₁.symm (m₁.symm ((morseModelWithCornersHalfSpace m).symm y))) ∈ m₂.source
  rw [hclamp]
  exact ⟨hm₁, hme₁, hc₁₂e₂, hm₂⟩

private theorem sublevelPullbackChart_transition_reduce_aux
    [I.Boundaryless] [IsManifold I (⊤ : WithTop ℕ∞) M]
    (f : M → ℝ) (a : ℝ) (x₁ x₂ : SublevelSpace f a)
    (b₁ : ContDiffBump ((extChartAt I x₁.1) x₁.1))
    (hb₁ : Metric.closedBall ((extChartAt I x₁.1) x₁.1) b₁.rOut ⊆ (extChartAt I x₁.1).target)
    (b₂ : ContDiffBump ((extChartAt I x₂.1) x₂.1))
    (hb₂ : Metric.closedBall ((extChartAt I x₂.1) x₂.1) b₂.rOut ⊆ (extChartAt I x₂.1).target)
    (m₁ : OpenPartialHomeomorph (SublevelSpace (sublevelPullbackCutoff I f x₁.1 b₁) a)
      (MorseHalfSpace m))
    (m₂ : OpenPartialHomeomorph (SublevelSpace (sublevelPullbackCutoff I f x₂.1 b₂) a)
      (MorseHalfSpace m))
    (w₁ : MorseHalfSpace m → MorseModel (m + 1))
    (v₂ : MorseModel (m + 1) → MorseModel (m + 1))
    (hW₁val : ∀ z : MorseHalfSpace m, z ∈ m₁.target → (m₁.symm z).1 = w₁ z)
    (hV₂val : ∀ w : SublevelSpace (sublevelPullbackCutoff I f x₂.1 b₂) a,
      w ∈ m₂.source → (m₂ w : MorseModel (m + 1)) = v₂ w.1)
    {y : MorseModel (m + 1)}
    (hy : y ∈ (morseModelWithCornersHalfSpace m).symm ⁻¹'
        ((sublevelPullbackChart I f a x₁ b₁ hb₁ ≫ₕ m₁).symm ≫ₕ
          (sublevelPullbackChart I f a x₂ b₂ hb₂ ≫ₕ m₂)).source ∩
      Set.range (morseModelWithCornersHalfSpace m)) :
    (morseModelWithCornersHalfSpace m)
      (((sublevelPullbackChart I f a x₁ b₁ hb₁ ≫ₕ m₁).symm ≫ₕ
        (sublevelPullbackChart I f a x₂ b₂ hb₂ ≫ₕ m₂)) ((morseModelWithCornersHalfSpace m).symm y)) =
      v₂ (sublevelChartTransition I x₁.1 x₂.1 (w₁ ((morseModelWithCornersHalfSpace m).symm y))) := by
  classical
  let I' : ModelWithCorners ℝ (MorseModel (m + 1)) (MorseHalfSpace m) :=
    morseModelWithCornersHalfSpace m
  let e₁ : OpenPartialHomeomorph (SublevelSpace f a)
      (SublevelSpace (sublevelPullbackCutoff I f x₁.1 b₁) a) :=
    sublevelPullbackChart I f a x₁ b₁ hb₁
  let e₂ : OpenPartialHomeomorph (SublevelSpace f a)
      (SublevelSpace (sublevelPullbackCutoff I f x₂.1 b₂) a) :=
    sublevelPullbackChart I f a x₂ b₂ hb₂
  let c₁ : OpenPartialHomeomorph (SublevelSpace f a) (MorseHalfSpace m) := e₁ ≫ₕ m₁
  let c₂ : OpenPartialHomeomorph (SublevelSpace f a) (MorseHalfSpace m) := e₂ ≫ₕ m₂
  have hy2 : y ∈ Set.range I' := hy.2
  have hy2' : 0 ≤ y (Fin.last m) := by
    rw [range_morseModelWithCornersHalfSpace] at hy2
    exact hy2
  let z : MorseHalfSpace m := ⟨y, hy2'⟩
  have hclamp : I'.symm y = z := by
    apply Subtype.ext
    exact morseHalfSpaceClamp_of_mem m hy2'
  have hmems := sublevelPullbackChart_transition_mem_aux I f a x₁ x₂ b₁ hb₁ b₂ hb₂ m₁ m₂ hy
  have hm₁ : z ∈ m₁.target := by
    rw [hclamp] at hmems
    exact hmems.1
  rw [hclamp]
  change (m₂ (e₂ (e₁.symm (m₁.symm z))) : MorseModel (m + 1)) =
    v₂ (sublevelChartTransition I x₁.1 x₂.1 (w₁ z))
  rw [hV₂val (e₂ (e₁.symm (m₁.symm z))) (by
    rw [hclamp] at hmems
    exact hmems.2.2.2)]
  rw [sublevelPullbackChart_apply_of_mem I f a x₂ b₂ hb₂ (by
    rw [hclamp] at hmems
    exact hmems.2.2.1)]
  rw [sublevelPullbackChart_symm_value I f a x₁ b₁ hb₁ (by
    rw [hclamp] at hmems
    exact hmems.2.1)]
  rw [hW₁val z hm₁]
  rfl

private theorem sublevelPullbackChart_transition_w₁_mem_aux
    [I.Boundaryless] [IsManifold I (⊤ : WithTop ℕ∞) M]
    (f : M → ℝ) (a : ℝ) (x₁ x₂ : SublevelSpace f a)
    (b₁ : ContDiffBump ((extChartAt I x₁.1) x₁.1))
    (hb₁ : Metric.closedBall ((extChartAt I x₁.1) x₁.1) b₁.rOut ⊆ (extChartAt I x₁.1).target)
    (b₂ : ContDiffBump ((extChartAt I x₂.1) x₂.1))
    (hb₂ : Metric.closedBall ((extChartAt I x₂.1) x₂.1) b₂.rOut ⊆ (extChartAt I x₂.1).target)
    (m₁ : OpenPartialHomeomorph (SublevelSpace (sublevelPullbackCutoff I f x₁.1 b₁) a)
      (MorseHalfSpace m))
    (m₂ : OpenPartialHomeomorph (SublevelSpace (sublevelPullbackCutoff I f x₂.1 b₂) a)
      (MorseHalfSpace m))
    (w₁ : MorseHalfSpace m → MorseModel (m + 1))
    (hW₁val : ∀ z : MorseHalfSpace m, z ∈ m₁.target → (m₁.symm z).1 = w₁ z)
    {y : MorseModel (m + 1)}
    (hy : y ∈ (morseModelWithCornersHalfSpace m).symm ⁻¹'
        ((sublevelPullbackChart I f a x₁ b₁ hb₁ ≫ₕ m₁).symm ≫ₕ
          (sublevelPullbackChart I f a x₂ b₂ hb₂ ≫ₕ m₂)).source ∩
      Set.range (morseModelWithCornersHalfSpace m)) :
    w₁ ((morseModelWithCornersHalfSpace m).symm y) ∈
      sublevelChartTransitionDomain I x₁.1 x₂.1 := by
  classical
  let I' : ModelWithCorners ℝ (MorseModel (m + 1)) (MorseHalfSpace m) :=
    morseModelWithCornersHalfSpace m
  have hy2 : y ∈ Set.range I' := hy.2
  have hy2' : 0 ≤ y (Fin.last m) := by
    rw [range_morseModelWithCornersHalfSpace] at hy2
    exact hy2
  let z : MorseHalfSpace m := ⟨y, hy2'⟩
  have hclamp : I'.symm y = z := by
    apply Subtype.ext
    exact morseHalfSpaceClamp_of_mem m hy2'
  have hmems := sublevelPullbackChart_transition_mem_aux I f a x₁ x₂ b₁ hb₁ b₂ hb₂ m₁ m₂ hy
  have hm₁ : z ∈ m₁.target := by
    rw [hclamp] at hmems
    exact hmems.1
  have hw₁z : (m₁.symm z).1 = w₁ z := hW₁val z hm₁
  have htarget : (m₁.symm z).1 ∈ (extChartAt I x₁.1).target := by
    have hball : (m₁.symm z).1 ∈ Metric.ball ((extChartAt I x₁.1) x₁.1) b₁.rIn := by
      rw [hclamp] at hmems
      simpa [sublevelPullbackChart] using hmems.2.1
    exact ((Metric.ball_subset_ball (le_of_lt b₁.rIn_lt_rOut)).trans
      Metric.ball_subset_closedBall).trans hb₁ hball
  have hsrc : (extChartAt I x₁.1).symm ((m₁.symm z).1) ∈ (extChartAt I x₂.1).source := by
    have hmem₂ : (sublevelPullbackChart I f a x₁ b₁ hb₁).symm (m₁.symm z) ∈
        (sublevelPullbackChart I f a x₂ b₂ hb₂).source := by
      rw [hclamp] at hmems
      exact hmems.2.2.1
    have hval : ((sublevelPullbackChart I f a x₁ b₁ hb₁).symm (m₁.symm z)).1 =
        (extChartAt I x₁.1).symm ((m₁.symm z).1) :=
      sublevelPullbackChart_symm_value I f a x₁ b₁ hb₁ (by
        rw [hclamp] at hmems
        exact hmems.2.1)
    have hmem₂' : ((sublevelPullbackChart I f a x₁ b₁ hb₁).symm (m₁.symm z)).1 ∈
        (chartAt H x₂.1).source := by
      have hconj : ((sublevelPullbackChart I f a x₁ b₁ hb₁).symm (m₁.symm z)).1 ∈
          (extChartAt I x₂.1).source ∧
        (extChartAt I x₂.1) ((sublevelPullbackChart I f a x₁ b₁ hb₁).symm (m₁.symm z)).1 ∈
          Metric.ball ((extChartAt I x₂.1) x₂.1) b₂.rIn := hmem₂
      simpa [extChartAt_source] using hconj.1
    rw [← hval]
    simpa [extChartAt_source] using hmem₂'
  rw [hclamp]
  change w₁ z ∈ sublevelChartTransitionDomain I x₁.1 x₂.1
  rw [sublevelChartTransitionDomain]
  constructor
  · rwa [← hw₁z]
  · rwa [← hw₁z]

private theorem sublevelPullbackChart_transition_contDiffOn_aux
    [I.Boundaryless] [IsManifold I (⊤ : WithTop ℕ∞) M]
    (f : M → ℝ) (a : ℝ) (x₁ x₂ : SublevelSpace f a)
    (b₁ : ContDiffBump ((extChartAt I x₁.1) x₁.1))
    (hb₁ : Metric.closedBall ((extChartAt I x₁.1) x₁.1) b₁.rOut ⊆ (extChartAt I x₁.1).target)
    (b₂ : ContDiffBump ((extChartAt I x₂.1) x₂.1))
    (hb₂ : Metric.closedBall ((extChartAt I x₂.1) x₂.1) b₂.rOut ⊆ (extChartAt I x₂.1).target)
    (m₁ : OpenPartialHomeomorph (SublevelSpace (sublevelPullbackCutoff I f x₁.1 b₁) a)
      (MorseHalfSpace m))
    (m₂ : OpenPartialHomeomorph (SublevelSpace (sublevelPullbackCutoff I f x₂.1 b₂) a)
      (MorseHalfSpace m))
    (w₁ : MorseHalfSpace m → MorseModel (m + 1))
    (v₂ : MorseModel (m + 1) → MorseModel (m + 1)) (D₁ : Set (MorseModel (m + 1)))
    (hW₁ : ContDiffOn ℝ (⊤ : ℕ∞) (fun y : MorseModel (m + 1) =>
      w₁ ((morseModelWithCornersHalfSpace m).symm y)) D₁)
    (hV₂ : ContDiff ℝ (⊤ : ℕ∞) v₂)
    (hW₁val : ∀ z : MorseHalfSpace m, z ∈ m₁.target → (m₁.symm z).1 = w₁ z)
    (hV₂val : ∀ w : SublevelSpace (sublevelPullbackCutoff I f x₂.1 b₂) a,
      w ∈ m₂.source → (m₂ w : MorseModel (m + 1)) = v₂ w.1)
    (hD₁ : ∀ y : MorseModel (m + 1), 0 ≤ y (Fin.last m) →
      (morseModelWithCornersHalfSpace m).symm y ∈ m₁.target → y ∈ D₁) :
    ContDiffOn ℝ (⊤ : ℕ∞)
      (morseModelWithCornersHalfSpace m ∘
        ((sublevelPullbackChart I f a x₁ b₁ hb₁ ≫ₕ m₁).symm ≫ₕ
          (sublevelPullbackChart I f a x₂ b₂ hb₂ ≫ₕ m₂)) ∘
        (morseModelWithCornersHalfSpace m).symm)
      ((morseModelWithCornersHalfSpace m).symm ⁻¹'
          ((sublevelPullbackChart I f a x₁ b₁ hb₁ ≫ₕ m₁).symm ≫ₕ
            (sublevelPullbackChart I f a x₂ b₂ hb₂ ≫ₕ m₂)).source ∩
        Set.range (morseModelWithCornersHalfSpace m)) := by
  classical
  let I' : ModelWithCorners ℝ (MorseModel (m + 1)) (MorseHalfSpace m) :=
    morseModelWithCornersHalfSpace m
  let s : Set (MorseModel (m + 1)) := I'.symm ⁻¹'
      ((sublevelPullbackChart I f a x₁ b₁ hb₁ ≫ₕ m₁).symm ≫ₕ
        (sublevelPullbackChart I f a x₂ b₂ hb₂ ≫ₕ m₂)).source ∩ Set.range I'
  intro y hy
  have hw : ContDiffWithinAt ℝ (⊤ : ℕ∞)
      (fun y' : MorseModel (m + 1) => w₁ ((morseModelWithCornersHalfSpace m).symm y')) s y := by
    exact (hW₁.mono (by
      intro y' hy'
      have hy2' : 0 ≤ y' (Fin.last m) := by
        have hy2'' : y' ∈ Set.range (morseModelWithCornersHalfSpace m) := hy'.2
        rw [range_morseModelWithCornersHalfSpace] at hy2''
        exact hy2''
      exact hD₁ y' hy2' (by
        have hmems' := sublevelPullbackChart_transition_mem_aux I f a x₁ x₂ b₁ hb₁ b₂ hb₂ m₁ m₂ hy'
        have hclamp' : (morseModelWithCornersHalfSpace m).symm y' = ⟨y', hy2'⟩ := by
          apply Subtype.ext
          exact morseHalfSpaceClamp_of_mem m hy2'
        simpa [hclamp'] using hmems'.1))) y hy
  have hwt : w₁ ((morseModelWithCornersHalfSpace m).symm y) ∈
      sublevelChartTransitionDomain I x₁.1 x₂.1 :=
    sublevelPullbackChart_transition_w₁_mem_aux I f a x₁ x₂ b₁ hb₁ b₂ hb₂ m₁ m₂ w₁ hW₁val hy
  have hφ : ContDiffWithinAt ℝ (⊤ : ℕ∞) (sublevelChartTransition I x₁.1 x₂.1)
      (sublevelChartTransitionDomain I x₁.1 x₂.1) (w₁ ((morseModelWithCornersHalfSpace m).symm y)) :=
    (contDiffOn_sublevelChartTransition I x₁.1 x₂.1) _ hwt
  have hφw : ContDiffWithinAt ℝ (⊤ : ℕ∞)
      (sublevelChartTransition I x₁.1 x₂.1 ∘
        fun y' : MorseModel (m + 1) => w₁ ((morseModelWithCornersHalfSpace m).symm y')) s y := by
    refine hφ.comp y hw ?_
    intro y' hy'
    exact sublevelPullbackChart_transition_w₁_mem_aux I f a x₁ x₂ b₁ hb₁ b₂ hb₂ m₁ m₂ w₁ hW₁val hy'
  have hv : ContDiffWithinAt ℝ (⊤ : ℕ∞) v₂ (Set.univ)
      (sublevelChartTransition I x₁.1 x₂.1 (w₁ ((morseModelWithCornersHalfSpace m).symm y))) :=
    hV₂.contDiffAt.contDiffWithinAt
  have hcd : ContDiffWithinAt ℝ (⊤ : ℕ∞)
      (v₂ ∘ sublevelChartTransition I x₁.1 x₂.1 ∘
        fun y' : MorseModel (m + 1) => w₁ ((morseModelWithCornersHalfSpace m).symm y')) s y := by
    refine hv.comp y hφw ?_
    intro y' hy'
    trivial
  change ContDiffWithinAt ℝ (⊤ : ℕ∞)
    (fun y' : MorseModel (m + 1) =>
      (morseModelWithCornersHalfSpace m)
        (((sublevelPullbackChart I f a x₁ b₁ hb₁ ≫ₕ m₁).symm ≫ₕ
          (sublevelPullbackChart I f a x₂ b₂ hb₂ ≫ₕ m₂)) ((morseModelWithCornersHalfSpace m).symm y')))
    s y
  refine hcd.congr_of_eventuallyEq ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with y' hy'
    simpa using (sublevelPullbackChart_transition_reduce_aux I f a x₁ x₂ b₁ hb₁ b₂ hb₂ m₁ m₂
      w₁ v₂ hW₁val hV₂val hy')
  · simpa using (sublevelPullbackChart_transition_reduce_aux I f a x₁ x₂ b₁ hb₁ b₂ hb₂ m₁ m₂
      w₁ v₂ hW₁val hV₂val hy)

theorem contDiffOn_manifoldSublevelBoundary_transition [I.Boundaryless]
    [IsManifold I (⊤ : WithTop ℕ∞) M] (f : M → ℝ) (a : ℝ)
    (hf : ContMDiff I 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞) f)
    (hreg : ∀ x : M, f x = a → ¬ IsCriticalPointAt I f x)
    (x₁ x₂ : SublevelSpace f a) (hx₁ : f x₁.1 = a) (hx₂ : f x₂.1 = a) :
    ContDiffOn ℝ (⊤ : ℕ∞)
      (morseModelWithCornersHalfSpace m ∘
        (manifoldSublevelBoundaryChart I f a x₁ hx₁ hf hreg).symm ≫ₕ
          (manifoldSublevelBoundaryChart I f a x₂ hx₂ hf hreg) ∘
        (morseModelWithCornersHalfSpace m).symm)
      ((morseModelWithCornersHalfSpace m).symm ⁻¹'
          ((manifoldSublevelBoundaryChart I f a x₁ hx₁ hf hreg).symm ≫ₕ
            (manifoldSublevelBoundaryChart I f a x₂ hx₂ hf hreg)).source ∩
        Set.range (morseModelWithCornersHalfSpace m)) := by
  classical
  let b₁ : ContDiffBump ((extChartAt I x₁.1) x₁.1) := sublevelPullbackBump I x₁.1
  let hb₁ : Metric.closedBall ((extChartAt I x₁.1) x₁.1) b₁.rOut ⊆ (extChartAt I x₁.1).target :=
    sublevelPullbackBump_closedBall_target (I := I) x₁.1
  let b₂ : ContDiffBump ((extChartAt I x₂.1) x₂.1) := sublevelPullbackBump I x₂.1
  let hb₂ : Metric.closedBall ((extChartAt I x₂.1) x₂.1) b₂.rOut ⊆ (extChartAt I x₂.1).target :=
    sublevelPullbackBump_closedBall_target (I := I) x₂.1
  let g₁ : MorseModel (m + 1) → ℝ := sublevelPullbackCutoff I f x₁.1 b₁
  let g₂ : MorseModel (m + 1) → ℝ := sublevelPullbackCutoff I f x₂.1 b₂
  let p₁ : SublevelSpace g₁ a := sublevelPullbackCutoffPoint I f a x₁ b₁
  let p₂ : SublevelSpace g₂ a := sublevelPullbackCutoffPoint I f a x₂ b₂
  let hx₁' : g₁ p₁.1 = a := sublevelPullbackCutoffPoint_value I f a x₁ b₁ hx₁
  let hx₂' : g₂ p₂.1 = a := sublevelPullbackCutoffPoint_value I f a x₂ b₂ hx₂
  let hg₁ : ContDiff ℝ (⊤ : ℕ∞) g₁ := contDiff_sublevelPullbackCutoff I f hf x₁.1 b₁ hb₁
  let hg₂ : ContDiff ℝ (⊤ : ℕ∞) g₂ := contDiff_sublevelPullbackCutoff I f hf x₂.1 b₂ hb₂
  let hr₁ : fderiv ℝ g₁ p₁.1 ≠ 0 :=
    fderiv_sublevelPullbackCutoffPoint_ne_zero I f hf a hreg x₁ b₁ hx₁
  let hr₂ : fderiv ℝ g₂ p₂.1 ≠ 0 :=
    fderiv_sublevelPullbackCutoffPoint_ne_zero I f hf a hreg x₂ b₂ hx₂
  let m₁ : OpenPartialHomeomorph (SublevelSpace g₁ a) (MorseHalfSpace m) :=
    sublevelBoundaryChart g₁ a p₁ hx₁' hg₁ hr₁
  let m₂ : OpenPartialHomeomorph (SublevelSpace g₂ a) (MorseHalfSpace m) :=
    sublevelBoundaryChart g₂ a p₂ hx₂' hg₂ hr₂
  let w₁ : MorseHalfSpace m → MorseModel (m + 1) :=
    sublevelBoundaryChartInvValue g₁ a p₁ hx₁' hg₁ hr₁
  let v₂ : MorseModel (m + 1) → MorseModel (m + 1) :=
    sublevelBoundaryChartValue g₂ a p₂ hx₂' hg₂ hr₂
  let D₁ : Set (MorseModel (m + 1)) :=
    {y : MorseModel (m + 1) | y ∈ sublevelBoundaryChartDomain g₁ a p₁ hx₁' hg₁ hr₁ ∧
      0 ≤ y (Fin.last m)}
  have hW₁ : ContDiffOn ℝ (⊤ : ℕ∞) (fun y : MorseModel (m + 1) =>
      w₁ ((morseModelWithCornersHalfSpace m).symm y)) D₁ := by
    have hraw : ContDiffOn ℝ (⊤ : ℕ∞) (sublevelBoundaryChartInvValueRaw g₁ a p₁ hx₁' hg₁ hr₁)
        (sublevelBoundaryChartDomain g₁ a p₁ hx₁' hg₁ hr₁) :=
      contDiffOn_sublevelBoundaryChartInvValueRaw g₁ a p₁ hx₁' hg₁ hr₁
    have hcongr : ∀ y ∈ D₁, (fun y : MorseModel (m + 1) =>
        w₁ ((morseModelWithCornersHalfSpace m).symm y)) y =
        sublevelBoundaryChartInvValueRaw g₁ a p₁ hx₁' hg₁ hr₁ y := by
      intro y hy
      have hy0 : 0 ≤ y (Fin.last m) := hy.2
      have hclamp : (morseModelWithCornersHalfSpace m).symm y = ⟨y, hy0⟩ := by
        apply Subtype.ext
        exact morseHalfSpaceClamp_of_mem m hy0
      dsimp [w₁]
      rw [hclamp]
      rfl
    exact (hraw.mono (by intro y hy; exact hy.1)).congr hcongr
  have hV₂ : ContDiff ℝ (⊤ : ℕ∞) v₂ :=
    contDiff_sublevelBoundaryChartValue g₂ a p₂ hx₂' hg₂ hr₂
  have hW₁val : ∀ z : MorseHalfSpace m, z ∈ m₁.target → (m₁.symm z).1 = w₁ z := by
    intro z hz
    rw [sublevelBoundaryChart_symm_value' g₁ a p₁ hx₁' hg₁ hr₁ hz]
  have hV₂val : ∀ w : SublevelSpace g₂ a, w ∈ m₂.source → (m₂ w : MorseModel (m + 1)) = v₂ w.1 := by
    intro w hw
    exact sublevelBoundaryChart_apply_value' g₂ a p₂ hx₂' hg₂ hr₂ w
  have hD₁ : ∀ y : MorseModel (m + 1), 0 ≤ y (Fin.last m) →
      (morseModelWithCornersHalfSpace m).symm y ∈ m₁.target → y ∈ D₁ := by
    intro y hy0 hz
    constructor
    · have hclamp : (morseModelWithCornersHalfSpace m).symm y = ⟨y, hy0⟩ := by
        apply Subtype.ext
        exact morseHalfSpaceClamp_of_mem m hy0
      rw [hclamp] at hz
      simpa [sublevelBoundaryChartDomain] using hz
    · exact hy0
  simpa [manifoldSublevelBoundaryChart, b₁, b₂, hb₁, hb₂, g₁, g₂, p₁, p₂, m₁, m₂] using
    (sublevelPullbackChart_transition_contDiffOn_aux I f a x₁ x₂ b₁ hb₁ b₂ hb₂ m₁ m₂
      w₁ v₂ D₁ hW₁ hV₂ hW₁val hV₂val hD₁)

theorem contDiffOn_manifoldSublevelInterior_transition [I.Boundaryless]
    [IsManifold I (⊤ : WithTop ℕ∞) M] (f : M → ℝ) (a : ℝ)
    (hf : ContMDiff I 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞) f)
    (x₁ x₂ : SublevelSpace f a) (hx₁ : f x₁.1 < a) (hx₂ : f x₂.1 < a) :
    ContDiffOn ℝ (⊤ : ℕ∞)
      (morseModelWithCornersHalfSpace m ∘
        (manifoldSublevelInteriorChart I f a x₁ hx₁ hf).symm ≫ₕ
          (manifoldSublevelInteriorChart I f a x₂ hx₂ hf) ∘
        (morseModelWithCornersHalfSpace m).symm)
      ((morseModelWithCornersHalfSpace m).symm ⁻¹'
          ((manifoldSublevelInteriorChart I f a x₁ hx₁ hf).symm ≫ₕ
            (manifoldSublevelInteriorChart I f a x₂ hx₂ hf)).source ∩
        Set.range (morseModelWithCornersHalfSpace m)) := by
  classical
  let b₁ : ContDiffBump ((extChartAt I x₁.1) x₁.1) := sublevelPullbackBump I x₁.1
  let hb₁ : Metric.closedBall ((extChartAt I x₁.1) x₁.1) b₁.rOut ⊆ (extChartAt I x₁.1).target :=
    sublevelPullbackBump_closedBall_target (I := I) x₁.1
  let b₂ : ContDiffBump ((extChartAt I x₂.1) x₂.1) := sublevelPullbackBump I x₂.1
  let hb₂ : Metric.closedBall ((extChartAt I x₂.1) x₂.1) b₂.rOut ⊆ (extChartAt I x₂.1).target :=
    sublevelPullbackBump_closedBall_target (I := I) x₂.1
  let g₁ : MorseModel (m + 1) → ℝ := sublevelPullbackCutoff I f x₁.1 b₁
  let g₂ : MorseModel (m + 1) → ℝ := sublevelPullbackCutoff I f x₂.1 b₂
  let p₁ : SublevelSpace g₁ a := sublevelPullbackCutoffPoint I f a x₁ b₁
  let p₂ : SublevelSpace g₂ a := sublevelPullbackCutoffPoint I f a x₂ b₂
  let hx₁' : g₁ p₁.1 < a := sublevelPullbackCutoffPoint_value_lt I f a x₁ b₁ hx₁
  let hx₂' : g₂ p₂.1 < a := sublevelPullbackCutoffPoint_value_lt I f a x₂ b₂ hx₂
  let hg₁ : ContDiff ℝ (⊤ : ℕ∞) g₁ := contDiff_sublevelPullbackCutoff I f hf x₁.1 b₁ hb₁
  let hg₂ : ContDiff ℝ (⊤ : ℕ∞) g₂ := contDiff_sublevelPullbackCutoff I f hf x₂.1 b₂ hb₂
  let c₁ : ℝ := sublevelInteriorShift g₁ a p₁ hx₁' hg₁
  let c₂ : ℝ := sublevelInteriorShift g₂ a p₂ hx₂' hg₂
  let m₁ : OpenPartialHomeomorph (SublevelSpace g₁ a) (MorseHalfSpace m) :=
    sublevelInteriorChart g₁ a p₁ hx₁' hg₁
  let m₂ : OpenPartialHomeomorph (SublevelSpace g₂ a) (MorseHalfSpace m) :=
    sublevelInteriorChart g₂ a p₂ hx₂' hg₂
  let w₁ : MorseHalfSpace m → MorseModel (m + 1) :=
    fun z => morseHalfSpaceShift (-c₁) (z : MorseModel (m + 1))
  let v₂ : MorseModel (m + 1) → MorseModel (m + 1) := fun w => morseHalfSpaceShift c₂ w
  let D₁ : Set (MorseModel (m + 1)) := {y : MorseModel (m + 1) | 0 ≤ y (Fin.last m)}
  have hW₁ : ContDiffOn ℝ (⊤ : ℕ∞) (fun y : MorseModel (m + 1) =>
      w₁ ((morseModelWithCornersHalfSpace m).symm y)) D₁ := by
    have hshift : ContDiffOn ℝ (⊤ : ℕ∞) (fun y : MorseModel (m + 1) =>
        morseHalfSpaceShift (-c₁) y) D₁ :=
      (contDiff_morseHalfSpaceShift (-c₁)).contDiffOn
    have hcongr : ∀ y ∈ D₁, (fun y : MorseModel (m + 1) =>
        w₁ ((morseModelWithCornersHalfSpace m).symm y)) y = morseHalfSpaceShift (-c₁) y := by
      intro y hy
      have hclamp : (morseModelWithCornersHalfSpace m).symm y = ⟨y, hy⟩ := by
        apply Subtype.ext
        exact morseHalfSpaceClamp_of_mem m hy
      dsimp [w₁]
      rw [hclamp]
    exact hshift.congr hcongr
  have hV₂ : ContDiff ℝ (⊤ : ℕ∞) v₂ := by
    dsimp [v₂]
    exact contDiff_morseHalfSpaceShift c₂
  have hW₁val : ∀ z : MorseHalfSpace m, z ∈ m₁.target → (m₁.symm z).1 = w₁ z := by
    intro z hz
    rw [sublevelInteriorChart_symm_value g₁ a p₁ hx₁' hg₁ hz]
  have hV₂val : ∀ w : SublevelSpace g₂ a, w ∈ m₂.source → (m₂ w : MorseModel (m + 1)) = v₂ w.1 := by
    intro w hw
    have hw' : dist w.1 p₂.1 < sublevelInteriorRadius g₂ a p₂ hx₂' hg₂ := by
      simpa [m₂, sublevelInteriorChart] using hw
    rw [sublevelInteriorChart_apply_value g₂ a p₂ hx₂' hg₂ w hw']
  have hD₁ : ∀ y : MorseModel (m + 1), 0 ≤ y (Fin.last m) →
      (morseModelWithCornersHalfSpace m).symm y ∈ m₁.target → y ∈ D₁ := by
    intro y hy0 hz
    exact hy0
  simpa [manifoldSublevelInteriorChart, b₁, b₂, hb₁, hb₂, g₁, g₂, p₁, p₂, m₁, m₂] using
    (sublevelPullbackChart_transition_contDiffOn_aux I f a x₁ x₂ b₁ hb₁ b₂ hb₂ m₁ m₂
      w₁ v₂ D₁ hW₁ hV₂ hW₁val hV₂val hD₁)

theorem contDiffOn_manifoldSublevelBoundaryInterior_transition [I.Boundaryless]
    [IsManifold I (⊤ : WithTop ℕ∞) M] (f : M → ℝ) (a : ℝ)
    (hf : ContMDiff I 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞) f)
    (hreg : ∀ x : M, f x = a → ¬ IsCriticalPointAt I f x)
    (x₁ x₂ : SublevelSpace f a) (hx₁ : f x₁.1 = a) (hx₂ : f x₂.1 < a) :
    ContDiffOn ℝ (⊤ : ℕ∞)
      (morseModelWithCornersHalfSpace m ∘
        (manifoldSublevelBoundaryChart I f a x₁ hx₁ hf hreg).symm ≫ₕ
          (manifoldSublevelInteriorChart I f a x₂ hx₂ hf) ∘
        (morseModelWithCornersHalfSpace m).symm)
      ((morseModelWithCornersHalfSpace m).symm ⁻¹'
          ((manifoldSublevelBoundaryChart I f a x₁ hx₁ hf hreg).symm ≫ₕ
            (manifoldSublevelInteriorChart I f a x₂ hx₂ hf)).source ∩
        Set.range (morseModelWithCornersHalfSpace m)) := by
  classical
  let b₁ : ContDiffBump ((extChartAt I x₁.1) x₁.1) := sublevelPullbackBump I x₁.1
  let hb₁ : Metric.closedBall ((extChartAt I x₁.1) x₁.1) b₁.rOut ⊆ (extChartAt I x₁.1).target :=
    sublevelPullbackBump_closedBall_target (I := I) x₁.1
  let b₂ : ContDiffBump ((extChartAt I x₂.1) x₂.1) := sublevelPullbackBump I x₂.1
  let hb₂ : Metric.closedBall ((extChartAt I x₂.1) x₂.1) b₂.rOut ⊆ (extChartAt I x₂.1).target :=
    sublevelPullbackBump_closedBall_target (I := I) x₂.1
  let g₁ : MorseModel (m + 1) → ℝ := sublevelPullbackCutoff I f x₁.1 b₁
  let g₂ : MorseModel (m + 1) → ℝ := sublevelPullbackCutoff I f x₂.1 b₂
  let p₁ : SublevelSpace g₁ a := sublevelPullbackCutoffPoint I f a x₁ b₁
  let p₂ : SublevelSpace g₂ a := sublevelPullbackCutoffPoint I f a x₂ b₂
  let hx₁' : g₁ p₁.1 = a := sublevelPullbackCutoffPoint_value I f a x₁ b₁ hx₁
  let hx₂' : g₂ p₂.1 < a := sublevelPullbackCutoffPoint_value_lt I f a x₂ b₂ hx₂
  let hg₁ : ContDiff ℝ (⊤ : ℕ∞) g₁ := contDiff_sublevelPullbackCutoff I f hf x₁.1 b₁ hb₁
  let hg₂ : ContDiff ℝ (⊤ : ℕ∞) g₂ := contDiff_sublevelPullbackCutoff I f hf x₂.1 b₂ hb₂
  let hr₁ : fderiv ℝ g₁ p₁.1 ≠ 0 :=
    fderiv_sublevelPullbackCutoffPoint_ne_zero I f hf a hreg x₁ b₁ hx₁
  let c₂ : ℝ := sublevelInteriorShift g₂ a p₂ hx₂' hg₂
  let m₁ : OpenPartialHomeomorph (SublevelSpace g₁ a) (MorseHalfSpace m) :=
    sublevelBoundaryChart g₁ a p₁ hx₁' hg₁ hr₁
  let m₂ : OpenPartialHomeomorph (SublevelSpace g₂ a) (MorseHalfSpace m) :=
    sublevelInteriorChart g₂ a p₂ hx₂' hg₂
  let w₁ : MorseHalfSpace m → MorseModel (m + 1) :=
    sublevelBoundaryChartInvValue g₁ a p₁ hx₁' hg₁ hr₁
  let v₂ : MorseModel (m + 1) → MorseModel (m + 1) := fun w => morseHalfSpaceShift c₂ w
  let D₁ : Set (MorseModel (m + 1)) :=
    {y : MorseModel (m + 1) | y ∈ sublevelBoundaryChartDomain g₁ a p₁ hx₁' hg₁ hr₁ ∧
      0 ≤ y (Fin.last m)}
  have hW₁ : ContDiffOn ℝ (⊤ : ℕ∞) (fun y : MorseModel (m + 1) =>
      w₁ ((morseModelWithCornersHalfSpace m).symm y)) D₁ := by
    have hraw : ContDiffOn ℝ (⊤ : ℕ∞) (sublevelBoundaryChartInvValueRaw g₁ a p₁ hx₁' hg₁ hr₁)
        (sublevelBoundaryChartDomain g₁ a p₁ hx₁' hg₁ hr₁) :=
      contDiffOn_sublevelBoundaryChartInvValueRaw g₁ a p₁ hx₁' hg₁ hr₁
    have hcongr : ∀ y ∈ D₁, (fun y : MorseModel (m + 1) =>
        w₁ ((morseModelWithCornersHalfSpace m).symm y)) y =
        sublevelBoundaryChartInvValueRaw g₁ a p₁ hx₁' hg₁ hr₁ y := by
      intro y hy
      have hy0 : 0 ≤ y (Fin.last m) := hy.2
      have hclamp : (morseModelWithCornersHalfSpace m).symm y = ⟨y, hy0⟩ := by
        apply Subtype.ext
        exact morseHalfSpaceClamp_of_mem m hy0
      dsimp [w₁]
      rw [hclamp]
      rfl
    exact (hraw.mono (by intro y hy; exact hy.1)).congr hcongr
  have hV₂ : ContDiff ℝ (⊤ : ℕ∞) v₂ := by
    dsimp [v₂]
    exact contDiff_morseHalfSpaceShift c₂
  have hW₁val : ∀ z : MorseHalfSpace m, z ∈ m₁.target → (m₁.symm z).1 = w₁ z := by
    intro z hz
    rw [sublevelBoundaryChart_symm_value' g₁ a p₁ hx₁' hg₁ hr₁ hz]
  have hV₂val : ∀ w : SublevelSpace g₂ a, w ∈ m₂.source → (m₂ w : MorseModel (m + 1)) = v₂ w.1 := by
    intro w hw
    have hw' : dist w.1 p₂.1 < sublevelInteriorRadius g₂ a p₂ hx₂' hg₂ := by
      simpa [m₂, sublevelInteriorChart] using hw
    rw [sublevelInteriorChart_apply_value g₂ a p₂ hx₂' hg₂ w hw']
  have hD₁ : ∀ y : MorseModel (m + 1), 0 ≤ y (Fin.last m) →
      (morseModelWithCornersHalfSpace m).symm y ∈ m₁.target → y ∈ D₁ := by
    intro y hy0 hz
    constructor
    · have hclamp : (morseModelWithCornersHalfSpace m).symm y = ⟨y, hy0⟩ := by
        apply Subtype.ext
        exact morseHalfSpaceClamp_of_mem m hy0
      rw [hclamp] at hz
      simpa [sublevelBoundaryChartDomain] using hz
    · exact hy0
  simpa [manifoldSublevelBoundaryChart, manifoldSublevelInteriorChart, b₁, b₂, hb₁, hb₂,
    g₁, g₂, p₁, p₂, m₁, m₂] using
    (sublevelPullbackChart_transition_contDiffOn_aux I f a x₁ x₂ b₁ hb₁ b₂ hb₂ m₁ m₂
      w₁ v₂ D₁ hW₁ hV₂ hW₁val hV₂val hD₁)

theorem contDiffOn_manifoldSublevelInteriorBoundary_transition [I.Boundaryless]
    [IsManifold I (⊤ : WithTop ℕ∞) M] (f : M → ℝ) (a : ℝ)
    (hf : ContMDiff I 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞) f)
    (hreg : ∀ x : M, f x = a → ¬ IsCriticalPointAt I f x)
    (x₁ x₂ : SublevelSpace f a) (hx₁ : f x₁.1 < a) (hx₂ : f x₂.1 = a) :
    ContDiffOn ℝ (⊤ : ℕ∞)
      (morseModelWithCornersHalfSpace m ∘
        (manifoldSublevelInteriorChart I f a x₁ hx₁ hf).symm ≫ₕ
          (manifoldSublevelBoundaryChart I f a x₂ hx₂ hf hreg) ∘
        (morseModelWithCornersHalfSpace m).symm)
      ((morseModelWithCornersHalfSpace m).symm ⁻¹'
          ((manifoldSublevelInteriorChart I f a x₁ hx₁ hf).symm ≫ₕ
            (manifoldSublevelBoundaryChart I f a x₂ hx₂ hf hreg)).source ∩
        Set.range (morseModelWithCornersHalfSpace m)) := by
  classical
  let b₁ : ContDiffBump ((extChartAt I x₁.1) x₁.1) := sublevelPullbackBump I x₁.1
  let hb₁ : Metric.closedBall ((extChartAt I x₁.1) x₁.1) b₁.rOut ⊆ (extChartAt I x₁.1).target :=
    sublevelPullbackBump_closedBall_target (I := I) x₁.1
  let b₂ : ContDiffBump ((extChartAt I x₂.1) x₂.1) := sublevelPullbackBump I x₂.1
  let hb₂ : Metric.closedBall ((extChartAt I x₂.1) x₂.1) b₂.rOut ⊆ (extChartAt I x₂.1).target :=
    sublevelPullbackBump_closedBall_target (I := I) x₂.1
  let g₁ : MorseModel (m + 1) → ℝ := sublevelPullbackCutoff I f x₁.1 b₁
  let g₂ : MorseModel (m + 1) → ℝ := sublevelPullbackCutoff I f x₂.1 b₂
  let p₁ : SublevelSpace g₁ a := sublevelPullbackCutoffPoint I f a x₁ b₁
  let p₂ : SublevelSpace g₂ a := sublevelPullbackCutoffPoint I f a x₂ b₂
  let hx₁' : g₁ p₁.1 < a := sublevelPullbackCutoffPoint_value_lt I f a x₁ b₁ hx₁
  let hx₂' : g₂ p₂.1 = a := sublevelPullbackCutoffPoint_value I f a x₂ b₂ hx₂
  let hg₁ : ContDiff ℝ (⊤ : ℕ∞) g₁ := contDiff_sublevelPullbackCutoff I f hf x₁.1 b₁ hb₁
  let hg₂ : ContDiff ℝ (⊤ : ℕ∞) g₂ := contDiff_sublevelPullbackCutoff I f hf x₂.1 b₂ hb₂
  let hr₂ : fderiv ℝ g₂ p₂.1 ≠ 0 :=
    fderiv_sublevelPullbackCutoffPoint_ne_zero I f hf a hreg x₂ b₂ hx₂
  let c₁ : ℝ := sublevelInteriorShift g₁ a p₁ hx₁' hg₁
  let m₁ : OpenPartialHomeomorph (SublevelSpace g₁ a) (MorseHalfSpace m) :=
    sublevelInteriorChart g₁ a p₁ hx₁' hg₁
  let m₂ : OpenPartialHomeomorph (SublevelSpace g₂ a) (MorseHalfSpace m) :=
    sublevelBoundaryChart g₂ a p₂ hx₂' hg₂ hr₂
  let w₁ : MorseHalfSpace m → MorseModel (m + 1) :=
    fun z => morseHalfSpaceShift (-c₁) (z : MorseModel (m + 1))
  let v₂ : MorseModel (m + 1) → MorseModel (m + 1) :=
    sublevelBoundaryChartValue g₂ a p₂ hx₂' hg₂ hr₂
  let D₁ : Set (MorseModel (m + 1)) := {y : MorseModel (m + 1) | 0 ≤ y (Fin.last m)}
  have hW₁ : ContDiffOn ℝ (⊤ : ℕ∞) (fun y : MorseModel (m + 1) =>
      w₁ ((morseModelWithCornersHalfSpace m).symm y)) D₁ := by
    have hshift : ContDiffOn ℝ (⊤ : ℕ∞) (fun y : MorseModel (m + 1) =>
        morseHalfSpaceShift (-c₁) y) D₁ :=
      (contDiff_morseHalfSpaceShift (-c₁)).contDiffOn
    have hcongr : ∀ y ∈ D₁, (fun y : MorseModel (m + 1) =>
        w₁ ((morseModelWithCornersHalfSpace m).symm y)) y = morseHalfSpaceShift (-c₁) y := by
      intro y hy
      have hclamp : (morseModelWithCornersHalfSpace m).symm y = ⟨y, hy⟩ := by
        apply Subtype.ext
        exact morseHalfSpaceClamp_of_mem m hy
      dsimp [w₁]
      rw [hclamp]
    exact hshift.congr hcongr
  have hV₂ : ContDiff ℝ (⊤ : ℕ∞) v₂ :=
    contDiff_sublevelBoundaryChartValue g₂ a p₂ hx₂' hg₂ hr₂
  have hW₁val : ∀ z : MorseHalfSpace m, z ∈ m₁.target → (m₁.symm z).1 = w₁ z := by
    intro z hz
    rw [sublevelInteriorChart_symm_value g₁ a p₁ hx₁' hg₁ hz]
  have hV₂val : ∀ w : SublevelSpace g₂ a, w ∈ m₂.source → (m₂ w : MorseModel (m + 1)) = v₂ w.1 := by
    intro w hw
    exact sublevelBoundaryChart_apply_value' g₂ a p₂ hx₂' hg₂ hr₂ w
  have hD₁ : ∀ y : MorseModel (m + 1), 0 ≤ y (Fin.last m) →
      (morseModelWithCornersHalfSpace m).symm y ∈ m₁.target → y ∈ D₁ := by
    intro y hy0 hz
    exact hy0
  simpa [manifoldSublevelInteriorChart, manifoldSublevelBoundaryChart, b₁, b₂, hb₁, hb₂,
    g₁, g₂, p₁, p₂, m₁, m₂] using
    (sublevelPullbackChart_transition_contDiffOn_aux I f a x₁ x₂ b₁ hb₁ b₂ hb₂ m₁ m₂
      w₁ v₂ D₁ hW₁ hV₂ hW₁val hV₂val hD₁)

@[reducible]
noncomputable def manifoldSublevelChartedSpace [I.Boundaryless]
    [IsManifold I (⊤ : WithTop ℕ∞) M] (f : M → ℝ) (a : ℝ)
    (hf : ContMDiff I 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞) f)
    (hreg : ∀ x : M, f x = a → ¬ IsCriticalPointAt I f x) :
    ChartedSpace (MorseHalfSpace m) (SublevelSpace f a) where
  atlas := Set.range (fun x : SublevelSpace f a =>
    if hx : f x.1 = a then manifoldSublevelBoundaryChart I f a x hx hf hreg
    else manifoldSublevelInteriorChart I f a x (lt_of_le_of_ne (show f x.1 ≤ a from x.2) hx) hf)
  chartAt := fun x : SublevelSpace f a =>
    if hx : f x.1 = a then manifoldSublevelBoundaryChart I f a x hx hf hreg
    else manifoldSublevelInteriorChart I f a x (lt_of_le_of_ne (show f x.1 ≤ a from x.2) hx) hf
  mem_chart_source := by
    intro x
    by_cases hx : f x.1 = a
    · simpa [hx] using mem_manifoldSublevelBoundaryChart_source I f a x hx hf hreg
    · simpa [hx] using mem_manifoldSublevelInteriorChart_source I f a x
        (lt_of_le_of_ne (show f x.1 ≤ a from x.2) hx) hf
  chart_mem_atlas := fun x => ⟨x, rfl⟩

@[reducible]
noncomputable def manifoldSublevelHasGroupoid [I.Boundaryless]
    [IsManifold I (⊤ : WithTop ℕ∞) M] (f : M → ℝ) (a : ℝ)
    (hf : ContMDiff I 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞) f)
    (hreg : ∀ x : M, f x = a → ¬ IsCriticalPointAt I f x) :
    @HasGroupoid (MorseHalfSpace m) _ (SublevelSpace f a) _
      (manifoldSublevelChartedSpace I f a hf hreg)
      (contDiffGroupoid (⊤ : ℕ∞) (morseModelWithCornersHalfSpace m)) := by
  classical
  letI := manifoldSublevelChartedSpace I f a hf hreg
  refine hasGroupoid_of_pregroupoid (contDiffPregroupoid (⊤ : ℕ∞) (morseModelWithCornersHalfSpace m)) ?_
  intro e e' he he'
  rcases he with ⟨x₁, rfl⟩
  rcases he' with ⟨x₂, rfl⟩
  by_cases hx₁ : f x₁.1 = a
  · by_cases hx₂ : f x₂.1 = a
    · simpa [hx₁, hx₂] using
        contDiffOn_manifoldSublevelBoundary_transition I f a hf hreg x₁ x₂ hx₁ hx₂
    · simpa [hx₁, hx₂] using
        contDiffOn_manifoldSublevelBoundaryInterior_transition I f a hf hreg x₁ x₂ hx₁
          (lt_of_le_of_ne (show f x₂.1 ≤ a from x₂.2) hx₂)
  · by_cases hx₂ : f x₂.1 = a
    · simpa [hx₁, hx₂] using
        contDiffOn_manifoldSublevelInteriorBoundary_transition I f a hf hreg x₁ x₂
          (lt_of_le_of_ne (show f x₁.1 ≤ a from x₁.2) hx₁) hx₂
    · simpa [hx₁, hx₂] using
        contDiffOn_manifoldSublevelInterior_transition I f a hf x₁ x₂
          (lt_of_le_of_ne (show f x₁.1 ≤ a from x₁.2) hx₁)
          (lt_of_le_of_ne (show f x₂.1 ≤ a from x₂.2) hx₂)

@[reducible]
noncomputable def manifoldSublevelIsManifold [I.Boundaryless]
    [IsManifold I (⊤ : WithTop ℕ∞) M] (f : M → ℝ) (a : ℝ)
    (hf : ContMDiff I 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞) f)
    (hreg : ∀ x : M, f x = a → ¬ IsCriticalPointAt I f x) :
    @IsManifold ℝ _ (MorseModel (m + 1)) _ _ (MorseHalfSpace m) _
      (morseModelWithCornersHalfSpace m) (⊤ : ℕ∞) (SublevelSpace f a) _
      (manifoldSublevelChartedSpace I f a hf hreg) := by
  letI := manifoldSublevelChartedSpace I f a hf hreg
  exact { toHasGroupoid := manifoldSublevelHasGroupoid I f a hf hreg }

noncomputable def levelSetPullbackCutoffPoint (f : M → ℝ) (a : ℝ) (x : LevelSetSpace f a)
    (b : ContDiffBump ((extChartAt I x.1) x.1)) :
    LevelSetSpace (sublevelPullbackCutoff I f x.1 b) a :=
  ⟨(extChartAt I x.1) x.1, by
    have hpball : (extChartAt I x.1) x.1 ∈ Metric.ball ((extChartAt I x.1) x.1) b.rIn :=
      Metric.mem_ball_self b.rIn_pos
    rw [sublevelPullbackCutoff_eqOn I f x.1 b hpball]
    change f ((extChartAt I x.1).symm ((extChartAt I x.1) x.1)) = a
    rw [(extChartAt I x.1).left_inv (mem_extChartAt_source (I := I) x.1)]
    exact x.2⟩

theorem levelSetPullbackCutoffPoint_value (f : M → ℝ) (a : ℝ) (x : LevelSetSpace f a)
    (b : ContDiffBump ((extChartAt I x.1) x.1)) :
    (sublevelPullbackCutoff I f x.1 b) (levelSetPullbackCutoffPoint I f a x b).1 = a := by
  change (sublevelPullbackCutoff I f x.1 b) ((extChartAt I x.1) x.1) = a
  have hpball : (extChartAt I x.1) x.1 ∈ Metric.ball ((extChartAt I x.1) x.1) b.rIn :=
    Metric.mem_ball_self b.rIn_pos
  rw [sublevelPullbackCutoff_eqOn I f x.1 b hpball]
  change f ((extChartAt I x.1).symm ((extChartAt I x.1) x.1)) = a
  rw [(extChartAt I x.1).left_inv (mem_extChartAt_source (I := I) x.1)]
  exact x.2

theorem fderiv_levelSetPullbackCutoffPoint_ne_zero [I.Boundaryless]
    [IsManifold I (⊤ : WithTop ℕ∞) M] (f : M → ℝ)
    (hf : ContMDiff I 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞) f) (a : ℝ)
    (hreg : ∀ x : M, f x = a → ¬ IsCriticalPointAt I f x) (x : LevelSetSpace f a)
    (b : ContDiffBump ((extChartAt I x.1) x.1)) :
    fderiv ℝ (sublevelPullbackCutoff I f x.1 b) (levelSetPullbackCutoffPoint I f a x b).1 ≠ 0 := by
  change fderiv ℝ (sublevelPullbackCutoff I f x.1 b) ((extChartAt I x.1) x.1) ≠ 0
  apply fderiv_sublevelPullbackCutoff_ne_zero I f x.1 b
  have hx₀ : f ((extChartAt I x.1).symm ((extChartAt I x.1) x.1)) = a := by
    rw [(extChartAt I x.1).left_inv (mem_extChartAt_source (I := I) x.1)]
    exact x.2
  have hyt : (extChartAt I x.1) x.1 ∈ (extChartAt I x.1).target :=
    (extChartAt I x.1).map_source (mem_extChartAt_source (I := I) x.1)
  exact fderiv_sublevelPullback_ne_zero I f hf a hreg hx₀ hyt

noncomputable def levelSetPullbackChart (f : M → ℝ) (a : ℝ) (x : LevelSetSpace f a)
    (b : ContDiffBump ((extChartAt I x.1) x.1))
    (hb : Metric.closedBall ((extChartAt I x.1) x.1) b.rOut ⊆ (extChartAt I x.1).target) :
    OpenPartialHomeomorph (LevelSetSpace f a)
      (LevelSetSpace (sublevelPullbackCutoff I f x.1 b) a) := by
  classical
  let e : PartialEquiv M (MorseModel (m + 1)) := extChartAt I x.1
  let p : MorseModel (m + 1) := (extChartAt I x.1) x.1
  let toFun' : LevelSetSpace f a → LevelSetSpace (sublevelPullbackCutoff I f x.1 b) a :=
    fun x' =>
      if hx : x'.1 ∈ e.source ∧ e x'.1 ∈ Metric.ball p b.rIn then
        ⟨e x'.1, by
          rw [sublevelPullbackCutoff_eqOn I f x.1 b hx.2]
          change f ((extChartAt I x.1).symm (e x'.1)) = a
          rw [(extChartAt I x.1).left_inv hx.1]
          exact x'.2⟩
      else
        ⟨p, by
          have hpball : p ∈ Metric.ball p b.rIn := Metric.mem_ball_self b.rIn_pos
          rw [sublevelPullbackCutoff_eqOn I f x.1 b hpball]
          change f ((extChartAt I x.1).symm ((extChartAt I x.1) x.1)) = a
          rw [(extChartAt I x.1).left_inv (mem_extChartAt_source (I := I) x.1)]
          exact x.2⟩
  let invFun' : LevelSetSpace (sublevelPullbackCutoff I f x.1 b) a → LevelSetSpace f a :=
    fun z =>
      if hz : z.1 ∈ Metric.ball p b.rIn then
        ⟨(extChartAt I x.1).symm z.1, by
          change (sublevelPullback I f x.1 z.1) = a
          rw [← sublevelPullbackCutoff_eqOn I f x.1 b hz]
          exact z.2⟩
      else ⟨x.1, x.2⟩
  exact
    { toPartialEquiv :=
        { toFun := toFun'
          invFun := invFun'
          source := {x' : LevelSetSpace f a | x'.1 ∈ e.source ∧ e x'.1 ∈ Metric.ball p b.rIn}
          target := {z : LevelSetSpace (sublevelPullbackCutoff I f x.1 b) a |
            z.1 ∈ Metric.ball p b.rIn}
          map_source' := by
            intro x' hx'
            change x'.1 ∈ e.source ∧ e x'.1 ∈ Metric.ball p b.rIn at hx'
            change (toFun' x').1 ∈ Metric.ball p b.rIn
            simp only [toFun']
            rw [dif_pos hx']
            exact hx'.2
          map_target' := by
            intro z hz
            change z.1 ∈ Metric.ball p b.rIn at hz
            change (invFun' z).1 ∈ e.source ∧ e ((invFun' z).1) ∈ Metric.ball p b.rIn
            simp only [invFun']
            rw [dif_pos hz]
            change (extChartAt I x.1).symm z.1 ∈ e.source ∧
              e ((extChartAt I x.1).symm z.1) ∈ Metric.ball p b.rIn
            have hzt : z.1 ∈ (extChartAt I x.1).target :=
              ((Metric.ball_subset_ball (le_of_lt b.rIn_lt_rOut)).trans
                Metric.ball_subset_closedBall).trans hb hz
            constructor
            · exact (extChartAt I x.1).map_target hzt
            · rw [(extChartAt I x.1).right_inv hzt]
              exact hz
          left_inv' := by
            intro x' hx'
            change x'.1 ∈ e.source ∧ e x'.1 ∈ Metric.ball p b.rIn at hx'
            apply Subtype.ext
            change (invFun' (toFun' x')).1 = x'.1
            simp only [toFun']
            rw [dif_pos hx']
            simp only [invFun']
            rw [dif_pos (by exact hx'.2)]
            change (extChartAt I x.1).symm (e x'.1) = x'.1
            exact (extChartAt I x.1).left_inv hx'.1
          right_inv' := by
            intro z hz
            change z.1 ∈ Metric.ball p b.rIn at hz
            apply Subtype.ext
            change (toFun' (invFun' z)).1 = z.1
            simp only [invFun']
            rw [dif_pos hz]
            have hzt : z.1 ∈ (extChartAt I x.1).target :=
              ((Metric.ball_subset_ball (le_of_lt b.rIn_lt_rOut)).trans
                Metric.ball_subset_closedBall).trans hb hz
            have hsrc : (extChartAt I x.1).symm z.1 ∈ e.source :=
              (extChartAt I x.1).map_target hzt
            have hcond : (extChartAt I x.1).symm z.1 ∈ e.source ∧
                e ((extChartAt I x.1).symm z.1) ∈ Metric.ball p b.rIn := by
              constructor
              · exact hsrc
              · rw [(extChartAt I x.1).right_inv hzt]
                exact hz
            simp only [toFun']
            rw [dif_pos hcond]
            change (extChartAt I x.1) ((extChartAt I x.1).symm z.1) = z.1
            exact (extChartAt I x.1).right_inv hzt }
      open_source := by
        have hcont : Continuous (fun x' : LevelSetSpace f a => (x' : M)) := continuous_subtype_val
        have h₁ : IsOpen {x' : LevelSetSpace f a | x'.1 ∈ e.source} :=
          (isOpen_extChartAt_source (I := I) x.1).preimage hcont
        have hf : ContinuousOn (fun x' : LevelSetSpace f a => e x'.1)
            {x' : LevelSetSpace f a | x'.1 ∈ e.source} := by
          exact (continuousOn_extChartAt x.1).comp hcont.continuousOn (by intro x' hx'; exact hx')
        simpa using (hf.isOpen_inter_preimage h₁ (Metric.isOpen_ball))
      open_target := by
        have hcont : Continuous (fun z : LevelSetSpace (sublevelPullbackCutoff I f x.1 b) a =>
            (z : MorseModel (m + 1))) := continuous_subtype_val
        exact (Metric.isOpen_ball).preimage hcont
      continuousOn_toFun := by
        refine continuousOn_iff_continuous_restrict.mpr ?_
        have hcont : Continuous (fun x' : {x' : LevelSetSpace f a |
            x'.1 ∈ e.source ∧ e x'.1 ∈ Metric.ball p b.rIn} => e x'.1.1) := by
          exact continuousOn_univ.mp ((continuousOn_extChartAt x.1).comp
            (Continuous.continuousOn (continuous_subtype_val.comp continuous_subtype_val))
            (by intro x' hx'; exact x'.2.1))
        refine (Continuous.subtype_mk hcont (by
          intro x'
          rw [sublevelPullbackCutoff_eqOn I f x.1 b x'.2.2]
          change f ((extChartAt I x.1).symm (e x'.1.1)) = a
          rw [(extChartAt I x.1).left_inv x'.2.1]
          exact x'.1.2)).congr ?_
        intro x'
        simp only [Set.restrict]
        apply Subtype.ext
        change e x'.1.1 = (toFun' x'.1).1
        simp only [toFun']
        rw [dif_pos (show x'.1.1 ∈ e.source ∧ e x'.1.1 ∈ Metric.ball p b.rIn from x'.2)]
      continuousOn_invFun := by
        refine continuousOn_iff_continuous_restrict.mpr ?_
        have hcont : Continuous (fun z : {z : LevelSetSpace (sublevelPullbackCutoff I f x.1 b) a |
            z.1 ∈ Metric.ball p b.rIn} => (extChartAt I x.1).symm z.1.1) := by
          exact continuousOn_univ.mp ((continuousOn_extChartAt_symm x.1).comp
            (Continuous.continuousOn (continuous_subtype_val.comp continuous_subtype_val))
            (by intro z hz; exact ((Metric.ball_subset_ball (le_of_lt b.rIn_lt_rOut)).trans
              Metric.ball_subset_closedBall).trans hb z.2))
        refine (Continuous.subtype_mk hcont (by
          intro z
          change (sublevelPullback I f x.1 z.1.1) = a
          rw [← sublevelPullbackCutoff_eqOn I f x.1 b z.2]
          exact z.1.2)).congr ?_
        intro z
        simp only [Set.restrict]
        apply Subtype.ext
        change (extChartAt I x.1).symm z.1.1 = (invFun' z.1).1
        simp only [invFun']
        rw [dif_pos (show z.1.1 ∈ Metric.ball p b.rIn from z.2)]
      }

theorem mem_levelSetPullbackChart_source (f : M → ℝ) (a : ℝ) (x : LevelSetSpace f a)
    (b : ContDiffBump ((extChartAt I x.1) x.1))
    (hb : Metric.closedBall ((extChartAt I x.1) x.1) b.rOut ⊆ (extChartAt I x.1).target) :
    x ∈ (levelSetPullbackChart I f a x b hb).source := by
  simpa [levelSetPullbackChart] using (show x.1 ∈ (extChartAt I x.1).source ∧
    (extChartAt I x.1) x.1 ∈ Metric.ball ((extChartAt I x.1) x.1) b.rIn from by
      constructor
      · exact mem_extChartAt_source (I := I) x.1
      · exact Metric.mem_ball_self b.rIn_pos)

theorem levelSetPullbackChart_apply_of_mem (f : M → ℝ) (a : ℝ) (x : LevelSetSpace f a)
    (b : ContDiffBump ((extChartAt I x.1) x.1))
    (hb : Metric.closedBall ((extChartAt I x.1) x.1) b.rOut ⊆ (extChartAt I x.1).target)
    {x' : LevelSetSpace f a} (hx : x' ∈ (levelSetPullbackChart I f a x b hb).source) :
    (levelSetPullbackChart I f a x b hb x').1 = (extChartAt I x.1) x'.1 := by
  have hx' : x'.1 ∈ (extChartAt I x.1).source ∧
      (extChartAt I x.1) x'.1 ∈ Metric.ball ((extChartAt I x.1) x.1) b.rIn := by
    simpa [levelSetPullbackChart] using hx
  change x'.1 ∈ (chartAt H x.1).source ∩ (chartAt H x.1) ⁻¹' I.source ∧
      I ((chartAt H x.1) x'.1) ∈ Metric.ball (I ((chartAt H x.1) x.1)) b.rIn at hx'
  dsimp [levelSetPullbackChart]
  rw [dif_pos hx']

theorem levelSetPullbackChart_symm_value (f : M → ℝ) (a : ℝ) (x : LevelSetSpace f a)
    (b : ContDiffBump ((extChartAt I x.1) x.1))
    (hb : Metric.closedBall ((extChartAt I x.1) x.1) b.rOut ⊆ (extChartAt I x.1).target)
    {z : LevelSetSpace (sublevelPullbackCutoff I f x.1 b) a}
    (hz : z ∈ (levelSetPullbackChart I f a x b hb).target) :
    ((levelSetPullbackChart I f a x b hb).symm z).1 = (extChartAt I x.1).symm z.1 := by
  have hz' : z.1 ∈ Metric.ball ((extChartAt I x.1) x.1) b.rIn := by
    simpa [levelSetPullbackChart] using hz
  change z.1 ∈ Metric.ball (I ((chartAt H x.1) x.1)) b.rIn at hz'
  dsimp [levelSetPullbackChart]
  rw [dif_pos hz']

private theorem levelSetPullbackChart_transition_mem_aux
    [I.Boundaryless] [IsManifold I (⊤ : WithTop ℕ∞) M]
    (f : M → ℝ) (a : ℝ) (x₁ x₂ : LevelSetSpace f a)
    (b₁ : ContDiffBump ((extChartAt I x₁.1) x₁.1))
    (hb₁ : Metric.closedBall ((extChartAt I x₁.1) x₁.1) b₁.rOut ⊆ (extChartAt I x₁.1).target)
    (b₂ : ContDiffBump ((extChartAt I x₂.1) x₂.1))
    (hb₂ : Metric.closedBall ((extChartAt I x₂.1) x₂.1) b₂.rOut ⊆ (extChartAt I x₂.1).target)
    (m₁ : OpenPartialHomeomorph (LevelSetSpace (sublevelPullbackCutoff I f x₁.1 b₁) a)
      (MorseModel m))
    (m₂ : OpenPartialHomeomorph (LevelSetSpace (sublevelPullbackCutoff I f x₂.1 b₂) a)
      (MorseModel m))
    {y : MorseModel m}
    (hy : y ∈ ((levelSetPullbackChart I f a x₁ b₁ hb₁ ≫ₕ m₁).symm ≫ₕ
        (levelSetPullbackChart I f a x₂ b₂ hb₂ ≫ₕ m₂)).source) :
    y ∈ m₁.target ∧
    m₁.symm y ∈ (levelSetPullbackChart I f a x₁ b₁ hb₁).target ∧
    (levelSetPullbackChart I f a x₁ b₁ hb₁).symm (m₁.symm y) ∈
      (levelSetPullbackChart I f a x₂ b₂ hb₂).source ∧
    (levelSetPullbackChart I f a x₂ b₂ hb₂)
      ((levelSetPullbackChart I f a x₁ b₁ hb₁).symm (m₁.symm y)) ∈ m₂.source := by
  classical
  let e₁ : OpenPartialHomeomorph (LevelSetSpace f a)
      (LevelSetSpace (sublevelPullbackCutoff I f x₁.1 b₁) a) :=
    levelSetPullbackChart I f a x₁ b₁ hb₁
  let e₂ : OpenPartialHomeomorph (LevelSetSpace f a)
      (LevelSetSpace (sublevelPullbackCutoff I f x₂.1 b₂) a) :=
    levelSetPullbackChart I f a x₂ b₂ hb₂
  let c₁ : OpenPartialHomeomorph (LevelSetSpace f a) (MorseModel m) := e₁ ≫ₕ m₁
  let c₂ : OpenPartialHomeomorph (LevelSetSpace f a) (MorseModel m) := e₂ ≫ₕ m₂
  have hy1 : y ∈ (c₁.symm ≫ₕ c₂).source := hy
  have hz1 : y ∈ c₁.target := by
    rw [OpenPartialHomeomorph.trans_source] at hy1
    simpa using hy1.1
  have hz1c : y ∈ (e₁ ≫ₕ m₁).target := by
    simpa [c₁] using hz1
  have hm₁ : y ∈ m₁.target := by
    rw [OpenPartialHomeomorph.trans_target] at hz1c
    exact hz1c.1
  have hme₁ : m₁.symm y ∈ e₁.target := by
    rw [OpenPartialHomeomorph.trans_target] at hz1c
    exact hz1c.2
  have hc₁₂ : c₁.symm y ∈ c₂.source := by
    rw [OpenPartialHomeomorph.trans_source] at hy1
    exact hy1.2
  have hcs : c₁.symm y = e₁.symm (m₁.symm y) := by
    rw [show c₁.symm = (e₁ ≫ₕ m₁).symm from rfl]
    rw [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm]
    rfl
  have hc₁₂e₂ : e₁.symm (m₁.symm y) ∈ e₂.source := by
    simpa [hcs] using hc₁₂.1
  have hm₂ : e₂ (e₁.symm (m₁.symm y)) ∈ m₂.source := by
    rw [OpenPartialHomeomorph.trans_source] at hc₁₂
    simpa [hcs] using hc₁₂.2
  exact ⟨hm₁, hme₁, hc₁₂e₂, hm₂⟩

private theorem levelSetPullbackChart_transition_reduce_aux
    [I.Boundaryless] [IsManifold I (⊤ : WithTop ℕ∞) M]
    (f : M → ℝ) (a : ℝ) (x₁ x₂ : LevelSetSpace f a)
    (b₁ : ContDiffBump ((extChartAt I x₁.1) x₁.1))
    (hb₁ : Metric.closedBall ((extChartAt I x₁.1) x₁.1) b₁.rOut ⊆ (extChartAt I x₁.1).target)
    (b₂ : ContDiffBump ((extChartAt I x₂.1) x₂.1))
    (hb₂ : Metric.closedBall ((extChartAt I x₂.1) x₂.1) b₂.rOut ⊆ (extChartAt I x₂.1).target)
    (m₁ : OpenPartialHomeomorph (LevelSetSpace (sublevelPullbackCutoff I f x₁.1 b₁) a)
      (MorseModel m))
    (m₂ : OpenPartialHomeomorph (LevelSetSpace (sublevelPullbackCutoff I f x₂.1 b₂) a)
      (MorseModel m))
    (w₁ : MorseModel m → MorseModel (m + 1))
    (v₂ : MorseModel (m + 1) → MorseModel m)
    (hW₁val : ∀ z : MorseModel m, z ∈ m₁.target → (m₁.symm z).1 = w₁ z)
    (hV₂val : ∀ w : LevelSetSpace (sublevelPullbackCutoff I f x₂.1 b₂) a,
      w ∈ m₂.source → (m₂ w : MorseModel m) = v₂ w.1)
    {y : MorseModel m}
    (hy : y ∈ ((levelSetPullbackChart I f a x₁ b₁ hb₁ ≫ₕ m₁).symm ≫ₕ
        (levelSetPullbackChart I f a x₂ b₂ hb₂ ≫ₕ m₂)).source) :
    (((levelSetPullbackChart I f a x₁ b₁ hb₁ ≫ₕ m₁).symm ≫ₕ
        (levelSetPullbackChart I f a x₂ b₂ hb₂ ≫ₕ m₂)) y : MorseModel m) =
      v₂ (sublevelChartTransition I x₁.1 x₂.1 (w₁ y)) := by
  classical
  let e₁ : OpenPartialHomeomorph (LevelSetSpace f a)
      (LevelSetSpace (sublevelPullbackCutoff I f x₁.1 b₁) a) :=
    levelSetPullbackChart I f a x₁ b₁ hb₁
  let e₂ : OpenPartialHomeomorph (LevelSetSpace f a)
      (LevelSetSpace (sublevelPullbackCutoff I f x₂.1 b₂) a) :=
    levelSetPullbackChart I f a x₂ b₂ hb₂
  have hmems := levelSetPullbackChart_transition_mem_aux I f a x₁ x₂ b₁ hb₁ b₂ hb₂ m₁ m₂ hy
  change (m₂ (e₂ (e₁.symm (m₁.symm y))) : MorseModel m) =
    v₂ (sublevelChartTransition I x₁.1 x₂.1 (w₁ y))
  rw [hV₂val (e₂ (e₁.symm (m₁.symm y))) hmems.2.2.2]
  rw [levelSetPullbackChart_apply_of_mem I f a x₂ b₂ hb₂ hmems.2.2.1]
  rw [levelSetPullbackChart_symm_value I f a x₁ b₁ hb₁ hmems.2.1]
  rw [hW₁val y hmems.1]
  rfl

private theorem levelSetPullbackChart_transition_w₁_mem_aux
    [I.Boundaryless] [IsManifold I (⊤ : WithTop ℕ∞) M]
    (f : M → ℝ) (a : ℝ) (x₁ x₂ : LevelSetSpace f a)
    (b₁ : ContDiffBump ((extChartAt I x₁.1) x₁.1))
    (hb₁ : Metric.closedBall ((extChartAt I x₁.1) x₁.1) b₁.rOut ⊆ (extChartAt I x₁.1).target)
    (b₂ : ContDiffBump ((extChartAt I x₂.1) x₂.1))
    (hb₂ : Metric.closedBall ((extChartAt I x₂.1) x₂.1) b₂.rOut ⊆ (extChartAt I x₂.1).target)
    (m₁ : OpenPartialHomeomorph (LevelSetSpace (sublevelPullbackCutoff I f x₁.1 b₁) a)
      (MorseModel m))
    (m₂ : OpenPartialHomeomorph (LevelSetSpace (sublevelPullbackCutoff I f x₂.1 b₂) a)
      (MorseModel m))
    (w₁ : MorseModel m → MorseModel (m + 1))
    (hW₁val : ∀ z : MorseModel m, z ∈ m₁.target → (m₁.symm z).1 = w₁ z)
    {y : MorseModel m}
    (hy : y ∈ ((levelSetPullbackChart I f a x₁ b₁ hb₁ ≫ₕ m₁).symm ≫ₕ
        (levelSetPullbackChart I f a x₂ b₂ hb₂ ≫ₕ m₂)).source) :
    w₁ y ∈ sublevelChartTransitionDomain I x₁.1 x₂.1 := by
  classical
  have hmems := levelSetPullbackChart_transition_mem_aux I f a x₁ x₂ b₁ hb₁ b₂ hb₂ m₁ m₂ hy
  have hw₁y : (m₁.symm y).1 = w₁ y := hW₁val y hmems.1
  have htarget : (m₁.symm y).1 ∈ (extChartAt I x₁.1).target := by
    have hball : (m₁.symm y).1 ∈ Metric.ball ((extChartAt I x₁.1) x₁.1) b₁.rIn := by
      simpa [levelSetPullbackChart] using hmems.2.1
    exact ((Metric.ball_subset_ball (le_of_lt b₁.rIn_lt_rOut)).trans
      Metric.ball_subset_closedBall).trans hb₁ hball
  have hsrc : (extChartAt I x₁.1).symm ((m₁.symm y).1) ∈ (extChartAt I x₂.1).source := by
    have hmem₂ : (levelSetPullbackChart I f a x₁ b₁ hb₁).symm (m₁.symm y) ∈
        (levelSetPullbackChart I f a x₂ b₂ hb₂).source := hmems.2.2.1
    have hval : ((levelSetPullbackChart I f a x₁ b₁ hb₁).symm (m₁.symm y)).1 =
        (extChartAt I x₁.1).symm ((m₁.symm y).1) :=
      levelSetPullbackChart_symm_value I f a x₁ b₁ hb₁ hmems.2.1
    have hmem₂' : ((levelSetPullbackChart I f a x₁ b₁ hb₁).symm (m₁.symm y)).1 ∈
        (chartAt H x₂.1).source := by
      have hconj : ((levelSetPullbackChart I f a x₁ b₁ hb₁).symm (m₁.symm y)).1 ∈
          (extChartAt I x₂.1).source ∧
        (extChartAt I x₂.1) ((levelSetPullbackChart I f a x₁ b₁ hb₁).symm (m₁.symm y)).1 ∈
          Metric.ball ((extChartAt I x₂.1) x₂.1) b₂.rIn := hmem₂
      simpa [extChartAt_source] using hconj.1
    rw [← hval]
    simpa [extChartAt_source] using hmem₂'
  change w₁ y ∈ sublevelChartTransitionDomain I x₁.1 x₂.1
  rw [sublevelChartTransitionDomain]
  constructor
  · rwa [← hw₁y]
  · rwa [← hw₁y]

private theorem levelSetPullbackChart_transition_contDiffOn_aux
    [I.Boundaryless] [IsManifold I (⊤ : WithTop ℕ∞) M]
    (f : M → ℝ) (a : ℝ) (x₁ x₂ : LevelSetSpace f a)
    (b₁ : ContDiffBump ((extChartAt I x₁.1) x₁.1))
    (hb₁ : Metric.closedBall ((extChartAt I x₁.1) x₁.1) b₁.rOut ⊆ (extChartAt I x₁.1).target)
    (b₂ : ContDiffBump ((extChartAt I x₂.1) x₂.1))
    (hb₂ : Metric.closedBall ((extChartAt I x₂.1) x₂.1) b₂.rOut ⊆ (extChartAt I x₂.1).target)
    (m₁ : OpenPartialHomeomorph (LevelSetSpace (sublevelPullbackCutoff I f x₁.1 b₁) a)
      (MorseModel m))
    (m₂ : OpenPartialHomeomorph (LevelSetSpace (sublevelPullbackCutoff I f x₂.1 b₂) a)
      (MorseModel m))
    (w₁ : MorseModel m → MorseModel (m + 1))
    (v₂ : MorseModel (m + 1) → MorseModel m) (D₁ : Set (MorseModel m))
    (hW₁ : ContDiffOn ℝ (⊤ : ℕ∞) w₁ D₁)
    (hV₂ : ContDiff ℝ (⊤ : ℕ∞) v₂)
    (hW₁val : ∀ z : MorseModel m, z ∈ m₁.target → (m₁.symm z).1 = w₁ z)
    (hV₂val : ∀ w : LevelSetSpace (sublevelPullbackCutoff I f x₂.1 b₂) a,
      w ∈ m₂.source → (m₂ w : MorseModel m) = v₂ w.1)
    (hD₁ : ∀ y : MorseModel m, y ∈ m₁.target → y ∈ D₁) :
    ContDiffOn ℝ (⊤ : ℕ∞)
      ((levelSetPullbackChart I f a x₁ b₁ hb₁ ≫ₕ m₁).symm ≫ₕ
        (levelSetPullbackChart I f a x₂ b₂ hb₂ ≫ₕ m₂) : MorseModel m → MorseModel m)
      ((levelSetPullbackChart I f a x₁ b₁ hb₁ ≫ₕ m₁).symm ≫ₕ
        (levelSetPullbackChart I f a x₂ b₂ hb₂ ≫ₕ m₂)).source := by
  classical
  let s : Set (MorseModel m) := ((levelSetPullbackChart I f a x₁ b₁ hb₁ ≫ₕ m₁).symm ≫ₕ
    (levelSetPullbackChart I f a x₂ b₂ hb₂ ≫ₕ m₂)).source
  intro y hy
  have hw : ContDiffWithinAt ℝ (⊤ : ℕ∞) w₁ s y := by
    exact (hW₁.mono (by intro y' hy'; exact hD₁ y' (by
      have hmems' := levelSetPullbackChart_transition_mem_aux I f a x₁ x₂ b₁ hb₁ b₂ hb₂ m₁ m₂ hy'
      exact hmems'.1))) y hy
  have hwt : w₁ y ∈ sublevelChartTransitionDomain I x₁.1 x₂.1 :=
    levelSetPullbackChart_transition_w₁_mem_aux I f a x₁ x₂ b₁ hb₁ b₂ hb₂ m₁ m₂ w₁ hW₁val hy
  have hφ : ContDiffWithinAt ℝ (⊤ : ℕ∞) (sublevelChartTransition I x₁.1 x₂.1)
      (sublevelChartTransitionDomain I x₁.1 x₂.1) (w₁ y) :=
    (contDiffOn_sublevelChartTransition I x₁.1 x₂.1) _ hwt
  have hφw : ContDiffWithinAt ℝ (⊤ : ℕ∞)
      (sublevelChartTransition I x₁.1 x₂.1 ∘ w₁) s y := by
    refine hφ.comp y hw ?_
    intro y' hy'
    exact levelSetPullbackChart_transition_w₁_mem_aux I f a x₁ x₂ b₁ hb₁ b₂ hb₂ m₁ m₂ w₁ hW₁val hy'
  have hv : ContDiffWithinAt ℝ (⊤ : ℕ∞) v₂ (Set.univ)
      (sublevelChartTransition I x₁.1 x₂.1 (w₁ y)) :=
    hV₂.contDiffAt.contDiffWithinAt
  have hcd : ContDiffWithinAt ℝ (⊤ : ℕ∞)
      (v₂ ∘ sublevelChartTransition I x₁.1 x₂.1 ∘ w₁) s y := by
    refine hv.comp y hφw ?_
    intro y' hy'
    trivial
  change ContDiffWithinAt ℝ (⊤ : ℕ∞)
    (fun y' : MorseModel m => ((levelSetPullbackChart I f a x₁ b₁ hb₁ ≫ₕ m₁).symm ≫ₕ
      (levelSetPullbackChart I f a x₂ b₂ hb₂ ≫ₕ m₂)) y') s y
  refine hcd.congr_of_eventuallyEq ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with y' hy'
    simpa using (levelSetPullbackChart_transition_reduce_aux I f a x₁ x₂ b₁ hb₁ b₂ hb₂ m₁ m₂
      w₁ v₂ hW₁val hV₂val hy')
  · simpa using (levelSetPullbackChart_transition_reduce_aux I f a x₁ x₂ b₁ hb₁ b₂ hb₂ m₁ m₂
      w₁ v₂ hW₁val hV₂val hy)

noncomputable def manifoldLevelSetChart [I.Boundaryless]
    [IsManifold I (⊤ : WithTop ℕ∞) M] (f : M → ℝ) (a : ℝ)
    (hf : ContMDiff I 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞) f)
    (hreg : ∀ x : M, f x = a → ¬ IsCriticalPointAt I f x) (x : LevelSetSpace f a) :
    OpenPartialHomeomorph (LevelSetSpace f a) (MorseModel m) :=
  let b : ContDiffBump ((extChartAt I x.1) x.1) := sublevelPullbackBump I x.1
  let hb : Metric.closedBall ((extChartAt I x.1) x.1) b.rOut ⊆ (extChartAt I x.1).target :=
    sublevelPullbackBump_closedBall_target (I := I) x.1
  let g : MorseModel (m + 1) → ℝ := sublevelPullbackCutoff I f x.1 b
  let p : LevelSetSpace g a := levelSetPullbackCutoffPoint I f a x b
  levelSetPullbackChart I f a x b hb ≫ₕ
    levelSetChart g a p (contDiff_sublevelPullbackCutoff I f hf x.1 b hb)
      (fderiv_levelSetPullbackCutoffPoint_ne_zero I f hf a hreg x b)

theorem mem_manifoldLevelSetChart_source [I.Boundaryless]
    [IsManifold I (⊤ : WithTop ℕ∞) M] (f : M → ℝ) (a : ℝ)
    (hf : ContMDiff I 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞) f)
    (hreg : ∀ x : M, f x = a → ¬ IsCriticalPointAt I f x) (x : LevelSetSpace f a) :
    x ∈ (manifoldLevelSetChart I f a hf hreg x).source := by
  let b : ContDiffBump ((extChartAt I x.1) x.1) := sublevelPullbackBump I x.1
  let hb : Metric.closedBall ((extChartAt I x.1) x.1) b.rOut ⊆ (extChartAt I x.1).target :=
    sublevelPullbackBump_closedBall_target (I := I) x.1
  let g : MorseModel (m + 1) → ℝ := sublevelPullbackCutoff I f x.1 b
  let p : LevelSetSpace g a := levelSetPullbackCutoffPoint I f a x b
  dsimp [manifoldLevelSetChart]
  constructor
  · exact mem_levelSetPullbackChart_source I f a x b hb
  · change (levelSetPullbackChart I f a x b hb) x ∈
      (levelSetChart g a p (contDiff_sublevelPullbackCutoff I f hf x.1 b hb)
        (fderiv_levelSetPullbackCutoffPoint_ne_zero I f hf a hreg x b)).source
    have hpt : (levelSetPullbackChart I f a x b hb) x = levelSetPullbackCutoffPoint I f a x b := by
      apply Subtype.ext
      change ((levelSetPullbackChart I f a x b hb) x).1 =
        (levelSetPullbackCutoffPoint I f a x b).1
      rw [levelSetPullbackChart_apply_of_mem I f a x b hb
        (mem_levelSetPullbackChart_source I f a x b hb)]
      rfl
    rw [hpt]
    exact mem_levelSetChart_source g a p (contDiff_sublevelPullbackCutoff I f hf x.1 b hb)
      (fderiv_levelSetPullbackCutoffPoint_ne_zero I f hf a hreg x b)

theorem contDiffOn_manifoldLevelSet_transition [I.Boundaryless]
    [IsManifold I (⊤ : WithTop ℕ∞) M] (f : M → ℝ) (a : ℝ)
    (hf : ContMDiff I 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞) f)
    (hreg : ∀ x : M, f x = a → ¬ IsCriticalPointAt I f x)
    (x₁ x₂ : LevelSetSpace f a) :
    ContDiffOn ℝ (⊤ : ℕ∞)
      ((manifoldLevelSetChart I f a hf hreg x₁).symm ≫ₕ
        (manifoldLevelSetChart I f a hf hreg x₂) : MorseModel m → MorseModel m)
      ((manifoldLevelSetChart I f a hf hreg x₁).symm ≫ₕ
        (manifoldLevelSetChart I f a hf hreg x₂)).source := by
  classical
  let b₁ : ContDiffBump ((extChartAt I x₁.1) x₁.1) := sublevelPullbackBump I x₁.1
  let hb₁ : Metric.closedBall ((extChartAt I x₁.1) x₁.1) b₁.rOut ⊆ (extChartAt I x₁.1).target :=
    sublevelPullbackBump_closedBall_target (I := I) x₁.1
  let b₂ : ContDiffBump ((extChartAt I x₂.1) x₂.1) := sublevelPullbackBump I x₂.1
  let hb₂ : Metric.closedBall ((extChartAt I x₂.1) x₂.1) b₂.rOut ⊆ (extChartAt I x₂.1).target :=
    sublevelPullbackBump_closedBall_target (I := I) x₂.1
  let g₁ : MorseModel (m + 1) → ℝ := sublevelPullbackCutoff I f x₁.1 b₁
  let g₂ : MorseModel (m + 1) → ℝ := sublevelPullbackCutoff I f x₂.1 b₂
  let p₁ : LevelSetSpace g₁ a := levelSetPullbackCutoffPoint I f a x₁ b₁
  let p₂ : LevelSetSpace g₂ a := levelSetPullbackCutoffPoint I f a x₂ b₂
  let hg₁ : ContDiff ℝ (⊤ : ℕ∞) g₁ := contDiff_sublevelPullbackCutoff I f hf x₁.1 b₁ hb₁
  let hg₂ : ContDiff ℝ (⊤ : ℕ∞) g₂ := contDiff_sublevelPullbackCutoff I f hf x₂.1 b₂ hb₂
  let hr₁ : fderiv ℝ g₁ p₁.1 ≠ 0 :=
    fderiv_levelSetPullbackCutoffPoint_ne_zero I f hf a hreg x₁ b₁
  let hr₂ : fderiv ℝ g₂ p₂.1 ≠ 0 :=
    fderiv_levelSetPullbackCutoffPoint_ne_zero I f hf a hreg x₂ b₂
  let m₁ : OpenPartialHomeomorph (LevelSetSpace g₁ a) (MorseModel m) :=
    levelSetChart g₁ a p₁ hg₁ hr₁
  let m₂ : OpenPartialHomeomorph (LevelSetSpace g₂ a) (MorseModel m) :=
    levelSetChart g₂ a p₂ hg₂ hr₂
  let w₁ : MorseModel m → MorseModel (m + 1) := levelSetChartInvValue g₁ a p₁ hg₁ hr₁
  let v₂ : MorseModel (m + 1) → MorseModel m := levelSetChartValue g₂ a p₂ hg₂ hr₂
  let D₁ : Set (MorseModel m) := levelSetChartDomain g₁ a p₁ hg₁ hr₁
  have hW₁ : ContDiffOn ℝ (⊤ : ℕ∞) w₁ D₁ := by
    dsimp [w₁]
    exact contDiffOn_levelSetChartInvValueRaw g₁ a p₁ hg₁ hr₁
  have hV₂ : ContDiff ℝ (⊤ : ℕ∞) v₂ := by
    dsimp [v₂]
    exact contDiff_levelSetChartValue g₂ a p₂ hg₂ hr₂
  have hW₁val : ∀ z : MorseModel m, z ∈ m₁.target → (m₁.symm z).1 = w₁ z := by
    intro z hz
    rw [levelSetChart_symm_value' g₁ a p₁ hg₁ hr₁ hz]
    rfl
  have hV₂val : ∀ w : LevelSetSpace g₂ a, w ∈ m₂.source → (m₂ w : MorseModel m) = v₂ w.1 := by
    intro w hw
    exact levelSetChart_apply_value' g₂ a p₂ hg₂ hr₂ w
  have hD₁ : ∀ y : MorseModel m, y ∈ m₁.target → y ∈ D₁ := by
    intro y hy
    simpa [levelSetChartDomain] using hy
  simpa [manifoldLevelSetChart, b₁, b₂, hb₁, hb₂, g₁, g₂, p₁, p₂, m₁, m₂] using
    (levelSetPullbackChart_transition_contDiffOn_aux I f a x₁ x₂ b₁ hb₁ b₂ hb₂ m₁ m₂
      w₁ v₂ D₁ hW₁ hV₂ hW₁val hV₂val hD₁)

@[reducible]
noncomputable def manifoldLevelSetChartedSpace [I.Boundaryless]
    [IsManifold I (⊤ : WithTop ℕ∞) M] (f : M → ℝ) (a : ℝ)
    (hf : ContMDiff I 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞) f)
    (hreg : ∀ x : M, f x = a → ¬ IsCriticalPointAt I f x) :
    ChartedSpace (MorseModel m) (LevelSetSpace f a) where
  atlas := Set.range (fun x : LevelSetSpace f a => manifoldLevelSetChart I f a hf hreg x)
  chartAt := fun x : LevelSetSpace f a => manifoldLevelSetChart I f a hf hreg x
  mem_chart_source := fun x => mem_manifoldLevelSetChart_source I f a hf hreg x
  chart_mem_atlas := fun x => ⟨x, rfl⟩

@[reducible]
noncomputable def manifoldLevelSetHasGroupoid [I.Boundaryless]
    [IsManifold I (⊤ : WithTop ℕ∞) M] (f : M → ℝ) (a : ℝ)
    (hf : ContMDiff I 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞) f)
    (hreg : ∀ x : M, f x = a → ¬ IsCriticalPointAt I f x) :
    @HasGroupoid (MorseModel m) _ (LevelSetSpace f a) _
      (manifoldLevelSetChartedSpace I f a hf hreg)
      (contDiffGroupoid (⊤ : ℕ∞) (𝓘(ℝ, MorseModel m))) := by
  classical
  letI := manifoldLevelSetChartedSpace I f a hf hreg
  refine hasGroupoid_of_pregroupoid (contDiffPregroupoid (⊤ : ℕ∞) (𝓘(ℝ, MorseModel m))) ?_
  intro e e' he he'
  rcases he with ⟨x₁, rfl⟩
  rcases he' with ⟨x₂, rfl⟩
  have hfun : 𝓘(ℝ, MorseModel m) ∘
        (manifoldLevelSetChart I f a hf hreg x₁).symm ≫ₕ
          (manifoldLevelSetChart I f a hf hreg x₂) ∘ (𝓘(ℝ, MorseModel m)).symm =
      (manifoldLevelSetChart I f a hf hreg x₁).symm ≫ₕ
        (manifoldLevelSetChart I f a hf hreg x₂) := by
    ext y
    simp [modelWithCornersSelf, ModelWithCorners.ofTargetUniv]
  have hdom : (𝓘(ℝ, MorseModel m)).symm ⁻¹'
        ((manifoldLevelSetChart I f a hf hreg x₁).symm ≫ₕ
          (manifoldLevelSetChart I f a hf hreg x₂)).source ∩
      Set.range (𝓘(ℝ, MorseModel m)) =
      ((manifoldLevelSetChart I f a hf hreg x₁).symm ≫ₕ
        (manifoldLevelSetChart I f a hf hreg x₂)).source := by
    ext y
    simp [modelWithCornersSelf, ModelWithCorners.ofTargetUniv]
  change ContDiffOn ℝ (⊤ : ℕ∞) (𝓘(ℝ, MorseModel m) ∘
      ((manifoldLevelSetChart I f a hf hreg x₁).symm ≫ₕ
        (manifoldLevelSetChart I f a hf hreg x₂) : MorseModel m → MorseModel m) ∘
      (𝓘(ℝ, MorseModel m)).symm)
      ((𝓘(ℝ, MorseModel m)).symm ⁻¹'
        ((manifoldLevelSetChart I f a hf hreg x₁).symm ≫ₕ
          (manifoldLevelSetChart I f a hf hreg x₂)).source ∩
        Set.range (𝓘(ℝ, MorseModel m)))
  rw [hfun, hdom]
  exact contDiffOn_manifoldLevelSet_transition I f a hf hreg x₁ x₂

@[reducible]
noncomputable def manifoldLevelSetIsManifold [I.Boundaryless]
    [IsManifold I (⊤ : WithTop ℕ∞) M] (f : M → ℝ) (a : ℝ)
    (hf : ContMDiff I 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞) f)
    (hreg : ∀ x : M, f x = a → ¬ IsCriticalPointAt I f x) :
    @IsManifold ℝ _ (MorseModel m) _ _ (MorseModel m) _ (𝓘(ℝ, MorseModel m))
      (⊤ : ℕ∞) (LevelSetSpace f a) _ (manifoldLevelSetChartedSpace I f a hf hreg) := by
  letI := manifoldLevelSetChartedSpace I f a hf hreg
  exact { toHasGroupoid := manifoldLevelSetHasGroupoid I f a hf hreg }

theorem manifoldSublevelBoundaryChart_extend_last_zero [I.Boundaryless]
    [IsManifold I (⊤ : WithTop ℕ∞) M] (f : M → ℝ) (a : ℝ)
    (hf : ContMDiff I 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞) f)
    (hreg : ∀ x : M, f x = a → ¬ IsCriticalPointAt I f x)
    (x : SublevelSpace f a) (hx : f x.1 = a) :
    (manifoldSublevelBoundaryChart I f a x hx hf hreg x : MorseModel (m + 1)) (Fin.last m) = 0 := by
  classical
  let b : ContDiffBump ((extChartAt I x.1) x.1) := sublevelPullbackBump I x.1
  let hb : Metric.closedBall ((extChartAt I x.1) x.1) b.rOut ⊆ (extChartAt I x.1).target :=
    sublevelPullbackBump_closedBall_target (I := I) x.1
  dsimp [manifoldSublevelBoundaryChart]
  have he : (sublevelPullbackChart I f a x b hb) x = sublevelPullbackCutoffPoint I f a x b := by
    apply Subtype.ext
    change ((sublevelPullbackChart I f a x b hb) x).1 =
      (sublevelPullbackCutoffPoint I f a x b).1
    rw [sublevelPullbackChart_apply_of_mem I f a x b hb
      (mem_sublevelPullbackChart_source I f a x b hb)]
    rfl
  rw [he]
  have hzero := sublevelBoundaryChart_extend_last_zero (sublevelPullbackCutoff I f x.1 b) a
    (sublevelPullbackCutoffPoint I f a x b) (sublevelPullbackCutoffPoint_value I f a x b hx)
    (contDiff_sublevelPullbackCutoff I f hf x.1 b hb)
    (fderiv_sublevelPullbackCutoffPoint_ne_zero I f hf a hreg x b hx)
  rw [OpenPartialHomeomorph.extend_coe] at hzero
  simpa using hzero

theorem manifoldSublevelInteriorChart_extend_last_pos [I.Boundaryless]
    [IsManifold I (⊤ : WithTop ℕ∞) M] (f : M → ℝ) (a : ℝ)
    (hf : ContMDiff I 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞) f)
    (x : SublevelSpace f a) (hx : f x.1 < a) :
    0 < (manifoldSublevelInteriorChart I f a x hx hf x : MorseModel (m + 1)) (Fin.last m) := by
  classical
  let b : ContDiffBump ((extChartAt I x.1) x.1) := sublevelPullbackBump I x.1
  let hb : Metric.closedBall ((extChartAt I x.1) x.1) b.rOut ⊆ (extChartAt I x.1).target :=
    sublevelPullbackBump_closedBall_target (I := I) x.1
  let g : MorseModel (m + 1) → ℝ := sublevelPullbackCutoff I f x.1 b
  let p : SublevelSpace g a := sublevelPullbackCutoffPoint I f a x b
  let hx' : g p.1 < a := sublevelPullbackCutoffPoint_value_lt I f a x b hx
  let hg : ContDiff ℝ (⊤ : ℕ∞) g := contDiff_sublevelPullbackCutoff I f hf x.1 b hb
  dsimp [manifoldSublevelInteriorChart]
  have he : (sublevelPullbackChart I f a x b hb) x = sublevelPullbackCutoffPoint I f a x b := by
    apply Subtype.ext
    change ((sublevelPullbackChart I f a x b hb) x).1 =
      (sublevelPullbackCutoffPoint I f a x b).1
    rw [sublevelPullbackChart_apply_of_mem I f a x b hb
      (mem_sublevelPullbackChart_source I f a x b hb)]
    rfl
  rw [he]
  have hval := sublevelInteriorChart_apply_value g a p hx' hg p (by
    have hmem := mem_sublevelInteriorChart_source g a p hx' hg
    simpa [sublevelInteriorChart] using hmem)
  rw [hval]
  have hnorm : |p.1 (Fin.last m)| ≤ ‖p.1‖ := by
    have hle : ‖p.1 (Fin.last m)‖ ≤ ‖p.1‖ := by
      have h := (pi_norm_le_iff_of_nonempty (ι := Fin (m + 1)) (f := p.1) (r := ‖p.1‖))
      exact h.mp le_rfl (Fin.last m)
    simpa using hle
  have hlow : -(‖p.1‖) ≤ p.1 (Fin.last m) := (abs_le.mp hnorm).1
  have hc : 0 < sublevelInteriorShift g a p hx' hg := by
    dsimp [sublevelInteriorShift]
    have hρ : 0 < sublevelInteriorRadius g a p hx' hg := by
      dsimp [sublevelInteriorRadius]
      exact (Classical.choose_spec (Metric.mem_nhds_iff.mp
        ((isOpen_Iio.preimage hg.continuous).mem_nhds hx'))).1
    linarith [hρ, norm_nonneg p.1]
  change 0 < morseHalfSpaceShift (sublevelInteriorShift g a p hx' hg) p.1 (Fin.last m)
  rw [morseHalfSpaceShift_last]
  have hnonneg : 0 ≤ p.1 (Fin.last m) + ‖p.1‖ := by linarith [hlow]
  have hρ : 0 < sublevelInteriorRadius g a p hx' hg := by
    dsimp [sublevelInteriorRadius]
    exact (Classical.choose_spec (Metric.mem_nhds_iff.mp
      ((isOpen_Iio.preimage hg.continuous).mem_nhds hx'))).1
  have hshift : 0 < sublevelInteriorRadius g a p hx' hg + 1 := by linarith [hρ]
  dsimp [sublevelInteriorShift]
  linarith [hnonneg, hshift]

noncomputable def manifoldSublevelBoundaryEquiv (f : M → ℝ) (a : ℝ) :
    {x : SublevelSpace f a // f x.1 = a} ≃ₜ
      LevelSetSpace f a where
  toFun := fun x => ⟨x.1.1, x.2⟩
  invFun := fun y => ⟨⟨y.1, le_of_eq y.2⟩, y.2⟩
  left_inv := by
    intro x
    apply Subtype.ext
    rfl
  right_inv := by
    intro y
    apply Subtype.ext
    rfl
  continuous_toFun := by
    exact Continuous.subtype_mk (continuous_subtype_val.comp continuous_subtype_val) (fun x => x.2)
  continuous_invFun := by
    exact Continuous.subtype_mk
      (Continuous.subtype_mk continuous_subtype_val (fun y : LevelSetSpace f a => by
        change f y.1 ≤ a
        exact le_of_eq y.2))
      (fun y : LevelSetSpace f a => by
        simpa using y.2)

theorem contMDiff_levelSetInclusion [I.Boundaryless] [IsManifold I (⊤ : WithTop ℕ∞) M]
    (f : M → ℝ) (a : ℝ) (hf : ContMDiff I 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞) f)
    (hreg : ∀ x : M, f x = a → ¬ IsCriticalPointAt I f x)
    (hcs : ChartedSpace (MorseModel m) (LevelSetSpace f a) :=
      manifoldLevelSetChartedSpace I f a hf hreg)
    (hchart : ∀ x : LevelSetSpace f a, hcs.chartAt x = manifoldLevelSetChart I f a hf hreg x := by
      intro x
      rfl) :
    ContMDiff (𝓘(ℝ, MorseModel m)) I (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : LevelSetSpace f a => x.1) := by
  classical
  letI := hcs
  intro x
  rw [contMDiffAt_iff]
  constructor
  · exact continuous_subtype_val.continuousAt
  · let b : ContDiffBump ((extChartAt I x.1) x.1) := sublevelPullbackBump I x.1
    let hb : Metric.closedBall ((extChartAt I x.1) x.1) b.rOut ⊆ (extChartAt I x.1).target :=
      sublevelPullbackBump_closedBall_target (I := I) x.1
    let g : MorseModel (m + 1) → ℝ := sublevelPullbackCutoff I f x.1 b
    let p : LevelSetSpace g a := levelSetPullbackCutoffPoint I f a x b
    let hg : ContDiff ℝ (⊤ : ℕ∞) g := contDiff_sublevelPullbackCutoff I f hf x.1 b hb
    let hr : fderiv ℝ g p.1 ≠ 0 := fderiv_levelSetPullbackCutoffPoint_ne_zero I f hf a hreg x b
    let c : OpenPartialHomeomorph (LevelSetSpace f a) (MorseModel m) :=
      manifoldLevelSetChart I f a hf hreg x
    let e : OpenPartialHomeomorph (LevelSetSpace f a) (LevelSetSpace g a) :=
      levelSetPullbackChart I f a x b hb
    let mc : OpenPartialHomeomorph (LevelSetSpace g a) (MorseModel m) :=
      levelSetChart g a p hg hr
    let F : MorseModel m → MorseModel (m + 1) :=
      extChartAt I x.1 ∘ (fun y : LevelSetSpace f a => y.1) ∘
        (extChartAt (𝓘(ℝ, MorseModel m)) x).symm
    let z₀ : MorseModel m := (extChartAt (𝓘(ℝ, MorseModel m)) x) x
    have hsymm₀ : ∀ z : MorseModel m, (extChartAt (𝓘(ℝ, MorseModel m)) x).symm z = c.symm z := by
      intro z
      change (hcs.chartAt x).symm z = c.symm z
      rw [hchart x]
    have hz₀ : z₀ ∈ c.target := by
      have hval₀ : c x ∈ c.target :=
        c.map_source (mem_manifoldLevelSetChart_source I f a hf hreg x)
      dsimp [z₀]
      simpa [hchart x] using hval₀
    have hval : ∀ z ∈ c.target, F z = levelSetChartInvValueRaw g a p hg hr z := by
      intro z hz
      have hz' : z ∈ mc.target := by
        dsimp [c, manifoldLevelSetChart] at hz
        exact hz.1
      have hze : mc.symm z ∈ e.target := by
        dsimp [c, manifoldLevelSetChart] at hz
        exact hz.2
      have hsymm₁ := levelSetChart_symm_value' g a p hg hr hz'
      have hsymm₂ := levelSetPullbackChart_symm_value I f a x b hb hze
      have hzball : (mc.symm z).1 ∈ Metric.ball ((extChartAt I x.1) x.1) b.rIn := by
        simpa [e, levelSetPullbackChart] using hze
      have hzt : (mc.symm z).1 ∈ (extChartAt I x.1).target :=
        ((Metric.ball_subset_ball (le_of_lt b.rIn_lt_rOut)).trans
          Metric.ball_subset_closedBall).trans hb hzball
      change (extChartAt I x.1) ((((extChartAt (𝓘(ℝ, MorseModel m)) x).symm z) :
          LevelSetSpace f a).1) = levelSetChartInvValueRaw g a p hg hr z
      rw [hsymm₀ z]
      have hc : c.symm z = e.symm (mc.symm z) := by
        dsimp [c, e, mc, manifoldLevelSetChart]
      rw [hc]
      rw [hsymm₂]
      change (extChartAt I x.1) ((extChartAt I x.1).symm ((mc.symm z).1)) =
        levelSetChartInvValueRaw g a p hg hr z
      rw [(extChartAt I x.1).right_inv hzt]
      rw [hsymm₁]
    have hF : ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) F c.target := by
      have hraw : ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
          (levelSetChartInvValueRaw g a p hg hr) (levelSetChartDomain g a p hg hr) :=
        contDiffOn_levelSetChartInvValueRaw g a p hg hr
      have hsub : c.target ⊆ levelSetChartDomain g a p hg hr := by
        intro z hz
        have hz' : z ∈ mc.target := by
          dsimp [c, manifoldLevelSetChart] at hz
          exact hz.1
        simpa [levelSetChartDomain] using hz'
      exact (hraw.mono hsub).congr (by intro z hz; exact hval z hz)
    have hFAt : ContDiffAt ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) F z₀ :=
      hF.contDiffAt (c.open_target.mem_nhds hz₀)
    simpa [F, modelWithCornersSelf, ModelWithCorners.ofTargetUniv] using hFAt.contDiffWithinAt

noncomputable def levelSetCollarMap [I.Boundaryless] [IsManifold I (⊤ : WithTop ℕ∞) M] [T2Space M]
    (f : M → ℝ) {a b : ℝ}
    (v : (x : M) → TangentSpace I x)
    (hv : ContMDiff I (I.prod 𝓘(ℝ, MorseModel (m + 1))) (⊤ : ℕ∞)
      (fun x : M => (⟨x, v x⟩ : TangentBundle I M)))
    (hsupp : IsCompact (tsupport v)) :
    LevelSetSpace f a × Set.Icc (0 : ℝ) (b - a) → M :=
  fun p => curveAt v (exists_globalIntegralCurve_of_compactSupport v hv hsupp) p.1.1 (-(p.2 : ℝ))

theorem contMDiff_levelSetCollarMap [I.Boundaryless] [IsManifold I (⊤ : WithTop ℕ∞) M] [T2Space M]
    (f : M → ℝ) (a : ℝ) (hf : ContMDiff I 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞) f)
    (hreg : ∀ x : M, f x = a → ¬ IsCriticalPointAt I f x) {b : ℝ} [Fact (0 < b - a)]
    (v : (x : M) → TangentSpace I x)
    (hv : ContMDiff I (I.prod 𝓘(ℝ, MorseModel (m + 1))) (⊤ : ℕ∞)
      (fun x : M => (⟨x, v x⟩ : TangentBundle I M)))
    (hsupp : IsCompact (tsupport v))
    (hcs : ChartedSpace (MorseModel m) (LevelSetSpace f a) :=
      manifoldLevelSetChartedSpace I f a hf hreg)
    (hchart : ∀ x : LevelSetSpace f a, hcs.chartAt x = manifoldLevelSetChart I f a hf hreg x := by
      intro x
      rfl) :
    ContMDiff ((𝓘(ℝ, MorseModel m)).prod (𝓡∂ 1)) I (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (levelSetCollarMap I f v hv hsupp :
        LevelSetSpace f a × Set.Icc (0 : ℝ) (b - a) → M) := by
  classical
  letI := hcs
  have hflow : ContMDiff (𝓘(ℝ, ℝ).prod I) I (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ℝ × M => curveAt v (exists_globalIntegralCurve_of_compactSupport v hv hsupp) p.2 p.1) :=
    contMDiff_globalFlow_joint_of_compactSupport (E := MorseModel (m + 1)) (I := I)
      (v := v) (hv := hv) (hsupp := hsupp)
  have hinc : ContMDiff (𝓘(ℝ, MorseModel m)) I (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : LevelSetSpace f a => x.1) :=
    contMDiff_levelSetInclusion I f a hf hreg hcs hchart
  have hproj₁ : ContMDiff ((𝓘(ℝ, MorseModel m)).prod (𝓡∂ 1)) (𝓘(ℝ, MorseModel m))
      (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : LevelSetSpace f a × Set.Icc (0 : ℝ) (b - a) => p.1) :=
    contMDiff_fst (I := 𝓘(ℝ, MorseModel m)) (J := 𝓡∂ 1) (n := (↑(⊤ : ℕ∞) : WithTop ℕ∞))
  have hproj₂ : ContMDiff ((𝓘(ℝ, MorseModel m)).prod (𝓡∂ 1)) (𝓡∂ 1)
      (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : LevelSetSpace f a × Set.Icc (0 : ℝ) (b - a) => p.2) :=
    contMDiff_snd (I := 𝓘(ℝ, MorseModel m)) (J := 𝓡∂ 1) (n := (↑(⊤ : ℕ∞) : WithTop ℕ∞))
  have hcoe : ContMDiff (𝓡∂ 1) 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (fun t : Set.Icc (0 : ℝ) (b - a) => (t : ℝ)) :=
    contMDiff_subtype_coe_Icc (x := (0 : ℝ)) (y := b - a) (n := (↑(⊤ : ℕ∞) : WithTop ℕ∞))
  have hneg : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞) (fun r : ℝ => -r) := by
    exact (contDiff_neg : ContDiff ℝ (⊤ : ℕ∞) (fun r : ℝ => -r)).contMDiff
  have h₂ : ContMDiff ((𝓘(ℝ, MorseModel m)).prod (𝓡∂ 1)) 𝓘(ℝ, ℝ)
      (↑(⊤ : ℕ∞) : WithTop ℕ∞) (fun p : LevelSetSpace f a × Set.Icc (0 : ℝ) (b - a) =>
        -(p.2 : ℝ)) :=
    hneg.comp (hcoe.comp hproj₂)
  have h₁ : ContMDiff ((𝓘(ℝ, MorseModel m)).prod (𝓡∂ 1)) (𝓘(ℝ, ℝ).prod I)
      (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : LevelSetSpace f a × Set.Icc (0 : ℝ) (b - a) => (-(p.2 : ℝ), p.1.1)) :=
    h₂.prodMk (hinc.comp hproj₁)
  have hcollar : ContMDiff ((𝓘(ℝ, MorseModel m)).prod (𝓡∂ 1)) I (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : LevelSetSpace f a × Set.Icc (0 : ℝ) (b - a) =>
        curveAt v (exists_globalIntegralCurve_of_compactSupport v hv hsupp) p.1.1 (-(p.2 : ℝ))) :=
    hflow.comp h₁
  simpa [levelSetCollarMap] using hcollar

end

end DifferentialGeometry.Topology.Morse
