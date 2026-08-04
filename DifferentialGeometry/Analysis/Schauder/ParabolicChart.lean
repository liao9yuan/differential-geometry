import DifferentialGeometry.Analysis.Schauder.Composition
import DifferentialGeometry.Analysis.Schauder.Localization
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Geometry.Manifold.IsManifold.ExtChartAt

noncomputable section

open Set
open scoped ENNReal NNReal

namespace DifferentialGeometry.Analysis.Schauder

variable {E F H M : Type*}
  [NormedAddCommGroup E] [NormedSpace Real E]
  [NormedAddCommGroup F] [NormedSpace Real F]
  [TopologicalSpace H] {I : ModelWithCorners Real E H}
  [TopologicalSpace M] [ChartedSpace H M]

def parabolicExtChartRepresentation
    (I : ModelWithCorners Real E H) (x₀ : M) (u : Real → M → F) :
    Real → E → F :=
  fun t y ↦ u t ((extChartAt I x₀).symm y)

def parabolicEuclideanChartRepresentation
    [FiniteDimensional Real E]
    (I : ModelWithCorners Real E H) (x₀ : M) (u : Real → M → F) :
    Real → EuclideanSpace Real (Fin (Module.finrank Real E)) → F :=
  fun t y ↦ u t ((extChartAt I x₀).symm ((toEuclidean (E := E)).symm y))

omit [NormedAddCommGroup F] [NormedSpace Real F] in
@[simp]
theorem parabolicExtChartRepresentation_apply
    (I : ModelWithCorners Real E H) (x₀ : M) (u : Real → M → F)
    (t : Real) (y : E) :
    parabolicExtChartRepresentation I x₀ u t y =
      u t ((extChartAt I x₀).symm y) := by
  rfl

omit [NormedAddCommGroup F] [NormedSpace Real F] in
@[simp]
theorem parabolicEuclideanChartRepresentation_apply
    [FiniteDimensional Real E]
    (I : ModelWithCorners Real E H) (x₀ : M) (u : Real → M → F)
    (t : Real) (y : EuclideanSpace Real (Fin (Module.finrank Real E))) :
    parabolicEuclideanChartRepresentation I x₀ u t y =
      u t ((extChartAt I x₀).symm ((toEuclidean (E := E)).symm y)) := by
  rfl

def eParabolicC2HolderGaugeInExtChartOn
    (alpha : NNReal) (I : ModelWithCorners Real E H) (x₀ : M)
    (Q : Set (ParabolicPoint E)) (u : Real → M → F) : ENNReal :=
  eParabolicC2HolderGaugeOn alpha Q
    (parabolicExtChartRepresentation I x₀ u)

def eParabolicC2HolderGaugeInEuclideanChartOn
    [FiniteDimensional Real E]
    (alpha : NNReal) (I : ModelWithCorners Real E H) (x₀ : M)
    (Q : Set (ParabolicPoint
      (EuclideanSpace Real (Fin (Module.finrank Real E)))))
    (u : Real → M → F) : ENNReal :=
  eParabolicC2HolderGaugeOn alpha Q
    (parabolicEuclideanChartRepresentation I x₀ u)

theorem eParabolicC2HolderGaugeInExtChartOn_mono
    {Q R : Set (ParabolicPoint E)} (hQR : Q ⊆ R)
    (alpha : NNReal) (I : ModelWithCorners Real E H) (x₀ : M)
    (u : Real → M → F) :
    eParabolicC2HolderGaugeInExtChartOn alpha I x₀ Q u ≤
      eParabolicC2HolderGaugeInExtChartOn alpha I x₀ R u := by
  exact eParabolicC2HolderGaugeOn_mono hQR alpha _

theorem eParabolicC2HolderGaugeInEuclideanChartOn_mono
    [FiniteDimensional Real E]
    {Q R : Set (ParabolicPoint
      (EuclideanSpace Real (Fin (Module.finrank Real E))))}
    (hQR : Q ⊆ R) (alpha : NNReal)
    (I : ModelWithCorners Real E H) (x₀ : M) (u : Real → M → F) :
    eParabolicC2HolderGaugeInEuclideanChartOn alpha I x₀ Q u ≤
      eParabolicC2HolderGaugeInEuclideanChartOn alpha I x₀ R u := by
  exact eParabolicC2HolderGaugeOn_mono hQR alpha _

theorem eParabolicC2HolderGaugeInExtChartOn_eq_of_coordinate_representation
    [I.Boundaryless]
    {x₀ : M} {J : Set Real} (hJ : IsOpen J) {Q : Set (ParabolicPoint E)}
    (hQ : Q ⊆ parabolicCylinder J (extChartAt I x₀).target)
    (alpha : NNReal) (u : Real → M → F) (v : Real → E → F)
    (hv : ∀ t ∈ J, ∀ y ∈ (extChartAt I x₀).target,
      v t y = u t ((extChartAt I x₀).symm y)) :
    eParabolicC2HolderGaugeInExtChartOn alpha I x₀ Q u =
      eParabolicC2HolderGaugeOn alpha Q v := by
  unfold eParabolicC2HolderGaugeInExtChartOn
  apply eParabolicC2HolderGaugeOn_congr_of_eqOn_open
    (isOpen_parabolicCylinder hJ (isOpen_extChartAt_target (I := I) x₀)) hQ
  intro p hp
  exact (hv p.time hp.1 p.space hp.2).symm

def eParabolicC2HolderGaugeInExtChartsOn
    {A : Type*} (alpha : NNReal) (I : ModelWithCorners Real E H)
    (center : A → M) (Q : A → Set (ParabolicPoint E))
    (u : Real → M → F) : ENNReal :=
  ⨆ i, eParabolicC2HolderGaugeInExtChartOn alpha I (center i) (Q i) u

def eParabolicC2HolderGaugeInEuclideanChartsOn
    [FiniteDimensional Real E]
    {A : Type*} (alpha : NNReal) (I : ModelWithCorners Real E H)
    (center : A → M)
    (Q : A → Set (ParabolicPoint
      (EuclideanSpace Real (Fin (Module.finrank Real E)))))
    (u : Real → M → F) : ENNReal :=
  ⨆ i, eParabolicC2HolderGaugeInEuclideanChartOn alpha I (center i) (Q i) u

theorem eParabolicC2HolderGaugeInExtChartOn_le_extCharts
    {A : Type*} (alpha : NNReal) (I : ModelWithCorners Real E H)
    (center : A → M) (Q : A → Set (ParabolicPoint E))
    (u : Real → M → F) (i : A) :
    eParabolicC2HolderGaugeInExtChartOn alpha I (center i) (Q i) u ≤
      eParabolicC2HolderGaugeInExtChartsOn alpha I center Q u := by
  exact le_iSup (fun j ↦
    eParabolicC2HolderGaugeInExtChartOn alpha I (center j) (Q j) u) i

theorem eParabolicC2HolderGaugeInEuclideanChartOn_le_euclideanCharts
    [FiniteDimensional Real E]
    {A : Type*} (alpha : NNReal) (I : ModelWithCorners Real E H)
    (center : A → M)
    (Q : A → Set (ParabolicPoint
      (EuclideanSpace Real (Fin (Module.finrank Real E)))))
    (u : Real → M → F) (i : A) :
    eParabolicC2HolderGaugeInEuclideanChartOn alpha I (center i) (Q i) u ≤
      eParabolicC2HolderGaugeInEuclideanChartsOn alpha I center Q u := by
  exact le_iSup (fun j ↦
    eParabolicC2HolderGaugeInEuclideanChartOn alpha I (center j) (Q j) u) i

theorem eParabolicC2HolderGaugeInExtChartsOn_le_iff
    {A : Type*} (alpha : NNReal) (I : ModelWithCorners Real E H)
    (center : A → M) (Q : A → Set (ParabolicPoint E))
    (u : Real → M → F) (C : ENNReal) :
    eParabolicC2HolderGaugeInExtChartsOn alpha I center Q u ≤ C ↔
      ∀ i, eParabolicC2HolderGaugeInExtChartOn alpha I (center i) (Q i) u ≤ C := by
  exact iSup_le_iff

theorem eParabolicC2HolderGaugeInEuclideanChartsOn_le_iff
    [FiniteDimensional Real E]
    {A : Type*} (alpha : NNReal) (I : ModelWithCorners Real E H)
    (center : A → M)
    (Q : A → Set (ParabolicPoint
      (EuclideanSpace Real (Fin (Module.finrank Real E)))))
    (u : Real → M → F) (C : ENNReal) :
    eParabolicC2HolderGaugeInEuclideanChartsOn alpha I center Q u ≤ C ↔
      ∀ i, eParabolicC2HolderGaugeInEuclideanChartOn
        alpha I (center i) (Q i) u ≤ C := by
  exact iSup_le_iff

theorem eParabolicC2HolderGaugeInEuclideanChartsOn_le_iSup
    [FiniteDimensional Real E]
    {A : Type*} (alpha : NNReal) (I : ModelWithCorners Real E H)
    (center : A → M)
    (Q : A → Set (ParabolicPoint
      (EuclideanSpace Real (Fin (Module.finrank Real E)))))
    (u : Real → M → F) (C : A → ENNReal)
    (h : ∀ i, eParabolicC2HolderGaugeInEuclideanChartOn
      alpha I (center i) (Q i) u ≤ C i) :
    eParabolicC2HolderGaugeInEuclideanChartsOn alpha I center Q u ≤
      ⨆ i, C i := by
  apply iSup_mono
  exact h

theorem eParabolicC2HolderGaugeInEuclideanChartsOn_le_sum_of_finite
    [FiniteDimensional Real E]
    {A : Type*} [Fintype A]
    (alpha : NNReal) (I : ModelWithCorners Real E H)
    (center : A → M)
    (Q : A → Set (ParabolicPoint
      (EuclideanSpace Real (Fin (Module.finrank Real E)))))
    (u : Real → M → F) (C : A → NNReal)
    (h : ∀ i, eParabolicC2HolderGaugeInEuclideanChartOn
      alpha I (center i) (Q i) u ≤ C i) :
    eParabolicC2HolderGaugeInEuclideanChartsOn alpha I center Q u ≤
      ∑ i, C i := by
  classical
  unfold eParabolicC2HolderGaugeInEuclideanChartsOn
  apply iSup_le
  intro i
  exact (h i).trans
    (ENNReal.coe_le_coe.mpr
      (Finset.single_le_sum (fun j _ ↦ zero_le (C j)) (Finset.mem_univ i)))

end DifferentialGeometry.Analysis.Schauder

end
