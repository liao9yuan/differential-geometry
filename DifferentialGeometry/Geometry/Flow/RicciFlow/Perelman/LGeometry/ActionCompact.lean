import DifferentialGeometry.Analysis.Calculus.ArzelaAscoli
import DifferentialGeometry.Geometry.Comparison.RiemannianDistContinuity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.RegAction

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open Bundle Filter Manifold MeasureTheory Set
open scoped ENNReal Manifold ContDiff Topology

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
  [InnerProductSpace Real E] [FiniteDimensional Real E]
  [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [PseudoMetricSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [CompactSpace M]
variable {D : RealTimeInterval}

omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
  [I.Boundaryless] in
/-- A uniformly action-bounded sequence of regularized L-curves on a compact manifold has a
uniformly convergent subsequence on its compact parameter interval. -/
theorem lAction_subseq
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (T t0 t1 : Real) (gRef : SmoothRiemannianMetric I M)
    (a b A : Real) (hab : a ≤ b)
    (htime : Set.Icc t0 t1 ⊆ D.carrier)
    (hback : ∀ s ∈ Set.Icc a b, T - s ^ 2 ∈ Set.Icc t0 t1)
    (alpha : Nat → Real → M)
    (halpha : ∀ n, ContMDiffOn 𝓘(Real, Real) I 1 (alpha n) (Set.Icc a b))
    (hE : ∀ n, IntegrableOn
      (fun s ↦ gRef.inner (alpha n s) (lVelocity (I := I) (alpha n) s)
        (lVelocity (I := I) (alpha n) s)) (Set.Icc a b))
    (hLag : ∀ n, IntervalIntegrable (lRegLag S T (alpha n)) volume a b)
    (hact : ∀ n, lRegAction S T (alpha n) a b ≤ A) :
    ∃ (phi : Nat → Nat) (g : C(Set.Icc a b, M)),
      StrictMono phi ∧
        TendstoUniformly
          (fun n (s : Set.Icc a b) ↦ alpha (phi n) s.1) g atTop := by
  classical
  obtain ⟨c, C, hc, hbudget⟩ :=
    lRefEnergy_bound (I := I) S hS T t0 t1 gRef a b A hab htime hback
  let B : Real := (2 / c) * (A - C * (b - a))
  have href (n : Nat) : IntervalIntegrable
      (fun s ↦ gRef.inner (alpha n s) (lVelocity (I := I) (alpha n) s)
        (lVelocity (I := I) (alpha n) s)) volume a b := by
    apply IntegrableOn.intervalIntegrable
    simpa only [Set.uIcc_of_le hab] using hE n
  have henergy (n : Nat) :
      curveEnergy (I := I) gRef (alpha n) a b ≤ B := by
    exact hbudget (alpha n) (href n) (hLag n) (hact n)
  have hriedist (n : Nat) {s t : Real}
      (has : a ≤ s) (hst : s ≤ t) (htb : t ≤ b) :
      riemannianEDistOf (I := I) gRef (alpha n s) (alpha n t) ≤
        ENNReal.ofReal (Real.sqrt (t - s) * Real.sqrt B) := by
    have hsub : Set.Icc s t ⊆ Set.Icc a b := Set.Icc_subset_Icc has htb
    have hsubE :
        curveEnergy (I := I) gRef (alpha n) s t ≤
          curveEnergy (I := I) gRef (alpha n) a b :=
      curveEnergy_mono (I := I) gRef has hst htb (by
        simpa only [lVelocity] using hE n)
    exact edistOf_le_budget (I := I) gRef hst
      ((halpha n).mono hsub)
      (by simpa only [lVelocity] using (hE n).mono_set hsub)
      (hsubE.trans (henergy n))
  let f : Nat → C(Set.Icc a b, M) := fun n ↦
    ⟨fun s ↦ alpha n s.1, (halpha n).continuousOn.restrict⟩
  have hmod : Tendsto (fun r : Real ↦ Real.sqrt r * Real.sqrt B) (𝓝 0) (𝓝 0) := by
    have hcont : Continuous (fun r : Real ↦ Real.sqrt r * Real.sqrt B) :=
      Real.continuous_sqrt.mul continuous_const
    simpa only [Real.sqrt_zero, zero_mul] using hcont.tendsto (0 : Real)
  have hunif : UniformEquicontinuous (fun n ↦ (f n : Set.Icc a b → M)) := by
    rw [Metric.uniformEquicontinuous_iff]
    intro ε hε
    letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
      ⟨gRef.toRiemannianMetric⟩
    obtain ⟨ρ, hρ, htoDist⟩ := dist_lt_of_riedist (I := I) gRef hε
    obtain ⟨δ, hδ, hmodδ⟩ := Metric.tendsto_nhds_nhds.1 hmod ρ hρ
    refine ⟨δ, hδ, ?_⟩
    intro x y hxy n
    have hsmall : Real.sqrt (dist x y) * Real.sqrt B < ρ := by
      have h := hmodδ (x := dist x y) (by simpa using hxy)
      simpa only [Real.dist_eq, sub_zero,
        abs_of_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))] using h
    have hofReal :
        ENNReal.ofReal (Real.sqrt (dist x y) * Real.sqrt B) < ENNReal.ofReal ρ :=
      (ENNReal.ofReal_lt_ofReal_iff hρ).2 hsmall
    rcases le_total x.1 y.1 with hxy' | hyx
    · have hriem := hriedist n x.2.1 hxy' y.2.2
      have hriem' := hriem.trans_lt (by
        simpa only [Subtype.dist_eq, Real.dist_eq,
          abs_of_nonpos (sub_nonpos.mpr hxy'), neg_sub] using hofReal)
      have hout := htoDist (alpha n x.1) (alpha n y.1) (by
        simpa only [riemannianEDistOf] using hriem')
      simpa only [f] using hout
    · have hriem := hriedist n y.2.1 hyx x.2.2
      have hriem' := hriem.trans_lt (by
        simpa only [Subtype.dist_eq, Real.dist_eq,
          abs_of_nonneg (sub_nonneg.mpr hyx)] using hofReal)
      have hout := htoDist (alpha n y.1) (alpha n x.1) (by
        simpa only [riemannianEDistOf] using hriem')
      simpa only [f, dist_comm] using hout
  have hequi : Equicontinuous (fun n ↦ (f n : Set.Icc a b → M)) :=
    hunif.equicontinuous
  obtain ⟨phi, g, hphi, hconv⟩ :=
    DifferentialGeometry.Analysis.arzela_subseq_cpt
      (K := Set.univ) isCompact_univ f (fun _ _ ↦ Set.mem_univ _) hequi
  refine ⟨phi, g, hphi, ?_⟩
  simpa only [f] using hconv

omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
  [I.Boundaryless] in
/-- The bounded-action compactness subsequence preserves two fixed endpoints. -/
theorem lAction_subseq_fix
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (T t0 t1 : Real) (gRef : SmoothRiemannianMetric I M)
    (a b A : Real) (hab : a ≤ b)
    (htime : Set.Icc t0 t1 ⊆ D.carrier)
    (hback : ∀ s ∈ Set.Icc a b, T - s ^ 2 ∈ Set.Icc t0 t1)
    (alpha : Nat → Real → M)
    (halpha : ∀ n, ContMDiffOn 𝓘(Real, Real) I 1 (alpha n) (Set.Icc a b))
    (hE : ∀ n, IntegrableOn
      (fun s ↦ gRef.inner (alpha n s) (lVelocity (I := I) (alpha n) s)
        (lVelocity (I := I) (alpha n) s)) (Set.Icc a b))
    (hLag : ∀ n, IntervalIntegrable (lRegLag S T (alpha n)) volume a b)
    (hact : ∀ n, lRegAction S T (alpha n) a b ≤ A)
    (x y : M) (hfixa : ∀ n, alpha n a = x)
    (hfixb : ∀ n, alpha n b = y) :
    ∃ (phi : Nat → Nat) (g : C(Set.Icc a b, M)),
      StrictMono phi ∧
        TendstoUniformly
          (fun n (s : Set.Icc a b) ↦ alpha (phi n) s.1) g atTop ∧
        g ⟨a, le_rfl, hab⟩ = x ∧ g ⟨b, hab, le_rfl⟩ = y := by
  obtain ⟨phi, g, hphi, hconv⟩ :=
    lAction_subseq (I := I) S hS T t0 t1 gRef a b A hab htime hback
      alpha halpha hE hLag hact
  refine ⟨phi, g, hphi, hconv, ?_, ?_⟩
  · have hlim := hconv.tendsto_at (⟨a, le_rfl, hab⟩ : Set.Icc a b)
    have hlim' : Tendsto (fun _ : Nat ↦ x) atTop
        (𝓝 (g ⟨a, le_rfl, hab⟩)) := by
      simpa only [hfixa] using hlim
    exact tendsto_nhds_unique hlim' tendsto_const_nhds
  · have hlim := hconv.tendsto_at (⟨b, hab, le_rfl⟩ : Set.Icc a b)
    have hlim' : Tendsto (fun _ : Nat ↦ y) atTop
        (𝓝 (g ⟨b, hab, le_rfl⟩)) := by
      simpa only [hfixb] using hlim
    exact tendsto_nhds_unique hlim' tendsto_const_nhds

end DifferentialGeometry.PDE.RicciFlow.Perelman

end
