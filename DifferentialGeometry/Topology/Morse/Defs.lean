import Mathlib.Geometry.Manifold.MFDeriv.Basic
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.LinearAlgebra.QuadraticForm.Signature

namespace DifferentialGeometry.Topology.Morse

open Manifold

noncomputable section

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M]

def sublevel (f : M → ℝ) (a : ℝ) : Set M :=
  f ⁻¹' Set.Iic a

def superlevel (f : M → ℝ) (a : ℝ) : Set M :=
  f ⁻¹' Set.Ici a

def sublevelStrip (f : M → ℝ) (a b : ℝ) : Set M :=
  f ⁻¹' Set.Icc a b

abbrev SublevelSpace (f : M → ℝ) (a : ℝ) : Type :=
  {x : M // x ∈ sublevel f a}

def IsCriticalPointAt (I : ModelWithCorners ℝ E H) (f : M → ℝ) (x : M) : Prop :=
  mfderiv I 𝓘(ℝ, ℝ) f x = 0

def chartHessianBilinAt (g : E → ℝ) (y : E) : LinearMap.BilinForm ℝ E :=
  { toFun := fun x => (fderiv ℝ (fderiv ℝ g) y x).toLinearMap
    map_add' := by
      intro x y
      ext z
      simp
    map_smul' := by
      intro a x
      ext z
      simp }

def chartHessianAt (g : E → ℝ) (y : E) : QuadraticForm ℝ E :=
  (chartHessianBilinAt g y).toQuadraticMap

def chartHessian (g : E → ℝ) : QuadraticForm ℝ E :=
  chartHessianAt g 0

def IsNondegenerateCriticalPointAt (I : ModelWithCorners ℝ E H) (f : M → ℝ) (x : M) : Prop :=
  IsCriticalPointAt I f x ∧
    (QuadraticMap.associated (R := ℝ)
      (chartHessianAt (g := fun y => f ((extChartAt I x).symm y))
        (extChartAt I x x))).SeparatingLeft

end
end DifferentialGeometry.Topology.Morse
