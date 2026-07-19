import DifferentialGeometry.Geometry.Curvature.Realized.MetricFamilyContinuity

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# Initial-edge bounds for a smooth Ricci-flow family

This file starts the regularizing-edge package needed by forward uniqueness.
The first producer below extracts the purely topological part: joint chart-Gram
continuity up to the initial time gives uniform two-sided metric equivalence on
every compact initial time slab.  Spatial derivative bounds remain a separate
parabolic-regularity frontier.
-/

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle Set
open scoped Manifold ContDiff Topology
open DifferentialGeometry
open DifferentialGeometry.Integral.Connection

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
    [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [BoundarylessManifold I M]
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

/-- Joint chart-Gram regularity up to the initial time gives one metric
equivalence constant on every compact initial subinterval.  This is the
zeroth-order component of the regularizing-edge estimates used in smooth
forward uniqueness. -/
theorem ricciEdgeMetric
    (g : Real → SmoothRiemannianMetric I M) {a b c : Real}
    (hab : a < b) (hcb : c < b)
    (hcont : ∀ (x₀ : M) (i j : Fin (Module.finrank Real E)),
      ContinuousOn
        (fun p : Real × M =>
          Integral.Measure.chartGramMatrix (I := I) (g p.1) x₀ p.2 i j)
        (Set.Ico a b ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet)) :
    ∃ Λ : Real, 1 ≤ Λ ∧
      ∀ t ∈ Set.Icc a c, ∀ x : M, ∀ v : TangentSpace I x,
        Λ⁻¹ * (g a).inner x v v ≤ (g t).inner x v v ∧
          (g t).inner x v v ≤ Λ * (g a).inner x v v := by
  have hG : Tensor0SFamilyContinuousOnSet (I := I) (M := M) 2
      (Set.Ico a b)
      (fun t x => Tensor0SBundle.metricTensorField (I := I) (g t) x) := by
    apply metricTensorCont_of_chartGram (K := Set.Ico a b) g
    intro x₀ i j
    have hincl : Continuous
        (fun q : {t : Real // t ∈ Set.Ico a b} × M => ((q.1 : Real), q.2)) :=
      (continuous_subtype_val.comp continuous_fst).prodMk continuous_snd
    have hcomp : ContinuousOn
        ((fun p : Real × M =>
            Integral.Measure.chartGramMatrix (I := I) (g p.1) x₀ p.2 i j) ∘
          (fun q : {t : Real // t ∈ Set.Ico a b} × M => ((q.1 : Real), q.2)))
        {q : {t : Real // t ∈ Set.Ico a b} × M |
          q.2 ∈ (trivializationAt E (TangentSpace I) x₀).baseSet} :=
      (hcont x₀ i j).comp hincl.continuousOn (fun q hq => ⟨q.1.2, hq⟩)
    simpa only [Function.comp_apply] using hcomp
  have hK : Set.Icc a c ⊆ Set.Ico a b := by
    intro t ht
    exact ⟨ht.1, lt_of_le_of_lt ht.2 hcb⟩
  have hGt : Tensor0SFamilyContinuousOnSet (I := I) (M := M) 2
      (Set.Icc a c)
      (fun t x => Tensor0SBundle.metricTensorField (I := I) (g t) x) := by
    exact Tensor0SFamilyContinuousOnSet.mono (I := I) (M := M) hG hK
  have haD : a ∈ Set.Ico a b := ⟨le_rfl, hab⟩
  have hGa : Tensor0SFamilyContinuousOnSet (I := I) (M := M) 2
      (Set.Icc a c)
      (fun _ x => Tensor0SBundle.metricTensorField (I := I) (g a) x) := by
    exact Tensor0SFamilyContinuousOnSet.comp_time (I := I) (M := M)
      (K := Set.Icc a c) (L := Set.Ico a b) hG
      (continuous_const : Continuous (fun _ : Real => a))
      (fun _ _ => haD)
  have hquadT : Continuous
      (metricTimeBundleQuad (I := I) (M := M) g (Set.Icc a c)) := by
    have hq := tensor0SFamily_quadCont (I := I) (M := M) hGt
    simpa [metricTimeBundleQuad, quad02,
      Tensor0SBundle.metricTensorField_apply] using hq
  have hquadA : Continuous
      (metricTimeBundleQuad (I := I) (M := M) (fun _ => g a) (Set.Icc a c)) := by
    have hq := tensor0SFamily_quadCont (I := I) (M := M) hGa
    simpa [metricTimeBundleQuad, quad02,
      Tensor0SBundle.metricTensorField_apply] using hq
  have hcompactT := metricUnitTimeSlab_icc_compact_of_bundle
    (I := I) (M := M) g a c (g a) hquadT
  have hcompactA := metricUnitTimeSlab_icc_compact_of_bundle
    (I := I) (M := M) (fun _ => g a) a c (g a) hquadA
  have htotalT := Tensor0SFamilyContinuousOnSet.tangentBundle
    (I := I) (M := M) hGt
  have htotalA := Tensor0SFamilyContinuousOnSet.tangentBundle
    (I := I) (M := M) hGa
  have habsT := timeSlabAbsQuadCont (I := I) (M := M)
    (G := fun _ => g a)
    (A := fun t x => Tensor0SBundle.metricTensorField (I := I) (g t) x)
    (Set.Icc a c) htotalT
  have habsA := timeSlabAbsQuadCont (I := I) (M := M)
    (G := g)
    (A := fun _ x => Tensor0SBundle.metricTensorField (I := I) (g a) x)
    (Set.Icc a c) htotalA
  obtain ⟨C₁, hC₁, hupper⟩ := compactUnitTimeSlab_absBound
    (I := I) (M := M) (fun _ => g a)
    (fun t x => Tensor0SBundle.metricTensorField (I := I) (g t) x)
    (Set.Icc a c) hcompactA habsT
  obtain ⟨C₂, hC₂, hlower⟩ := compactUnitTimeSlab_absBound
    (I := I) (M := M) g
    (fun _ x => Tensor0SBundle.metricTensorField (I := I) (g a) x)
    (Set.Icc a c) hcompactT habsA
  let Λ : Real := max 1 (max C₁ C₂)
  have hΛ : 1 ≤ Λ := le_max_left _ _
  have hΛpos : 0 < Λ := lt_of_lt_of_le zero_lt_one hΛ
  refine ⟨Λ, hΛ, ?_⟩
  intro t ht x v
  have hq₀ : 0 ≤ (g a).inner x v v := by
    rcases eq_or_ne v 0 with rfl | hv
    · simp
    · exact ((g a).pos x v hv).le
  have hqt : 0 ≤ (g t).inner x v v := by
    rcases eq_or_ne v 0 with rfl | hv
    · simp
    · exact ((g t).pos x v hv).le
  have huAbs := hupper t ht x v
  have hlAbs := hlower t ht x v
  simp only [quad02, Tensor0SBundle.metricTensorField_apply] at huAbs hlAbs
  have hu : (g t).inner x v v ≤ C₁ * (g a).inner x v v :=
    (le_abs_self _).trans huAbs
  have hl : (g a).inner x v v ≤ C₂ * (g t).inner x v v :=
    (le_abs_self _).trans hlAbs
  have hC₁Λ : C₁ ≤ Λ := le_trans (le_max_left C₁ C₂) (le_max_right 1 _)
  have hC₂Λ : C₂ ≤ Λ := le_trans (le_max_right C₁ C₂) (le_max_right 1 _)
  have hlΛ : (g a).inner x v v ≤ Λ * (g t).inner x v v :=
    hl.trans (mul_le_mul_of_nonneg_right hC₂Λ hqt)
  constructor
  · calc
      Λ⁻¹ * (g a).inner x v v ≤ Λ⁻¹ * (Λ * (g t).inner x v v) :=
        mul_le_mul_of_nonneg_left hlΛ (inv_nonneg.mpr hΛpos.le)
      _ = (g t).inner x v v := by simp [hΛpos.ne']
  · exact hu.trans (mul_le_mul_of_nonneg_right hC₁Λ hq₀)

end DifferentialGeometry.PDE.RicciFlow
