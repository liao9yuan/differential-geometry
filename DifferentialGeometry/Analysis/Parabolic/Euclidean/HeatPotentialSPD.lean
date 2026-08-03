import DifferentialGeometry.Analysis.Parabolic.Euclidean.FrozenDuhamelSPD
import DifferentialGeometry.Analysis.Parabolic.Euclidean.HeatPotentialEstimate
import DifferentialGeometry.Analysis.Schauder.Scaling

noncomputable section

open Matrix Real Set
open scoped Interval NNReal RealInnerProductSpace Topology

namespace DifferentialGeometry.Analysis.Parabolic.Euclidean

open DifferentialGeometry.Analysis.Schauder

private abbrev Euc (n : Type*) := EuclideanSpace Real n

variable {n F : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
  [NormedAddCommGroup F] [NormedSpace Real F] [CompleteSpace F]

def spdHeatSource (A : Matrix n n Real) (hA : A.PosDef)
    (f : Real → BoundedContinuousFunction (Euc n) F) :
    Real → BoundedContinuousFunction (Euc n) F :=
  fun t => linPullBcf (spdSqrtEquiv A hA) (f t)

def spdSourceHolderConst (A : Matrix n n Real) (hA : A.PosDef)
    (alpha K : NNReal) : NNReal :=
  K * (max 1 ‖(spdSqrtEquiv A hA : Euc n →L[Real] Euc n)‖₊) ^
    (alpha : Real)

def spdHeatDuh (A : Matrix n n Real) (hA : A.PosDef) (t : Real)
    (f : Real → BoundedContinuousFunction (Euc n) F) (x : Euc n) : F :=
  heatDuh t (spdHeatSource A hA f) ((spdSqrtEquiv A hA).symm x)

def eSpdParabolicC2HolderGaugeOn
    (A : Matrix n n Real) (hA : A.PosDef) (alpha : NNReal)
    (Q : Set (ParabolicPoint (Euc n))) (u : Real → Euc n → F) : ENNReal :=
  eParabolicC2HolderGaugeOn alpha Q
    (fun t y => u t (spdSqrtEquiv A hA y))

omit [Nonempty n] [NormedSpace Real F] [CompleteSpace F] in
theorem spdHeatSource_norm (A : Matrix n n Real) (hA : A.PosDef)
    (f : Real → BoundedContinuousFunction (Euc n) F) (t : Real) :
    ‖spdHeatSource A hA f t‖ = ‖f t‖ := by
  exact norm_linPullBcf (spdSqrtEquiv A hA) (f t)

omit [Nonempty n] [NormedSpace Real F] [CompleteSpace F] in
theorem spdHeatSource_parabolic_holder
    {alpha K : NNReal} {S : Real}
    (A : Matrix n n Real) (hA : A.PosDef)
    (f : Real → BoundedContinuousFunction (Euc n) F)
    (hsource : HolderWith K alpha
      ((parabolicCylinder (Icc (0 : Real) S) Set.univ).restrict
        (fun p => f p.time p.space))) :
    HolderWith (spdSourceHolderConst A hA alpha K) alpha
      ((parabolicCylinder (Icc (0 : Real) S) Set.univ).restrict
        (fun p => spdHeatSource A hA f p.time p.space)) := by
  have h := parabolicHolder_linearMap
    (spdSqrtEquiv A hA : Euc n →L[Real] Euc n) hsource
  simpa only [spdSourceHolderConst,
    parabolicLinearPreimage_cylinder_univ, spdHeatSource,
    linPullBcf_apply, Function.comp_apply, parabolicLinearMap_time,
    parabolicLinearMap_space] using h

theorem spdHeatDuh_schauder_estimate
    {alpha K B : NNReal}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    {S T : Real} (hT : 0 ≤ T) (hTS : T < S)
    (A : Matrix n n Real) (hA : A.PosDef)
    (f : Real → BoundedContinuousFunction (Euc n) F)
    (hbound : ∀ r ∈ Icc (0 : Real) S, ‖f r‖ ≤ B)
    (hsource : HolderWith K alpha
      ((parabolicCylinder (Icc (0 : Real) S) Set.univ).restrict
        (fun p => f p.time p.space))) :
    eSpdParabolicC2HolderGaugeOn A hA alpha
      (parabolicCylinder (Ioc (0 : Real) T) Set.univ)
      (fun t x => spdHeatDuh A hA t f x) ≤
      heatPotentialSchauderConst (V := Euc n) alpha
        (spdSourceHolderConst A hA alpha K) B
        (spdSourceHolderConst A hA alpha K) T := by
  have hbound' : ∀ r ∈ Icc (0 : Real) S,
      ‖spdHeatSource A hA f r‖ ≤ B := by
    intro r hr
    rw [spdHeatSource_norm]
    exact hbound r hr
  have h := heatDuh_schauder_estimate_of_parabolic_holder
    halpha0 halpha1 hT hTS (spdHeatSource A hA f) hbound'
      (spdHeatSource_parabolic_holder A hA f hsource)
  unfold eSpdParabolicC2HolderGaugeOn spdHeatDuh
  simpa only [ContinuousLinearEquiv.symm_apply_apply] using h

end DifferentialGeometry.Analysis.Parabolic.Euclidean

end
