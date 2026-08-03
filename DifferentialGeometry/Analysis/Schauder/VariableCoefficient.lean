import DifferentialGeometry.Analysis.Schauder.ConstantCoefficientElliptic
import DifferentialGeometry.Analysis.Schauder.CutoffProduct
import Mathlib.Topology.ContinuousMap.Bounded.Normed

noncomputable section

open Real
open scoped BoundedContinuousFunction NNReal RealInnerProductSpace

namespace DifferentialGeometry.Analysis.Schauder

open DifferentialGeometry.Analysis.Parabolic.Euclidean

private abbrev Euc (n : Type*) := EuclideanSpace Real n

variable {n F : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
  [NormedAddCommGroup F] [NormedSpace Real F]

def hessianComponentBcf
    (d2u : BoundedContinuousFunction (Euc n)
      (Euc n →L[Real] Euc n →L[Real] F)) (i j : n) :
    BoundedContinuousFunction (Euc n) F :=
  (ContinuousLinearMap.apply Real F (EuclideanSpace.basisFun n Real j))
    |>.compLeftContinuousBounded (Euc n)
      ((ContinuousLinearMap.apply Real (Euc n →L[Real] F)
        (EuclideanSpace.basisFun n Real i))
        |>.compLeftContinuousBounded (Euc n) d2u)

omit [DecidableEq n] [Nonempty n] in
@[simp]
theorem hessianComponentBcf_apply
    (d2u : BoundedContinuousFunction (Euc n)
      (Euc n →L[Real] Euc n →L[Real] F)) (i j : n) (x : Euc n) :
    hessianComponentBcf d2u i j x =
      d2u x (EuclideanSpace.basisFun n Real i)
        (EuclideanSpace.basisFun n Real j) := rfl

def variableMatrixLap
    (a : n → n → BoundedContinuousFunction (Euc n) Real)
    (d2u : BoundedContinuousFunction (Euc n)
      (Euc n →L[Real] Euc n →L[Real] F)) :
    BoundedContinuousFunction (Euc n) F :=
  ∑ i, ∑ j, a i j • hessianComponentBcf d2u i j

omit [DecidableEq n] [Nonempty n] in
@[simp]
theorem variableMatrixLap_apply
    (a : n → n → BoundedContinuousFunction (Euc n) Real)
    (d2u : BoundedContinuousFunction (Euc n)
      (Euc n →L[Real] Euc n →L[Real] F)) (x : Euc n) :
    variableMatrixLap a d2u x =
      matrixLap (fun i j ↦ a i j x) (d2u x) := by
  simp only [variableMatrixLap, matrixLap,
    BoundedContinuousFunction.sum_apply]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rfl

def frozenMatrixLap
    (a : n → n → BoundedContinuousFunction (Euc n) Real) (x0 : Euc n)
    (d2u : BoundedContinuousFunction (Euc n)
      (Euc n →L[Real] Euc n →L[Real] F)) :
    BoundedContinuousFunction (Euc n) F :=
  ∑ i, ∑ j, (a i j x0) • hessianComponentBcf d2u i j

omit [DecidableEq n] [Nonempty n] in
@[simp]
theorem frozenMatrixLap_apply
    (a : n → n → BoundedContinuousFunction (Euc n) Real) (x0 : Euc n)
    (d2u : BoundedContinuousFunction (Euc n)
      (Euc n →L[Real] Euc n →L[Real] F)) (x : Euc n) :
    frozenMatrixLap a x0 d2u x =
      matrixLap (fun i j ↦ a i j x0) (d2u x) := by
  simp only [frozenMatrixLap, matrixLap,
    BoundedContinuousFunction.sum_apply,
    BoundedContinuousFunction.smul_apply, hessianComponentBcf_apply]

def matrixLapFreezeDefect
    (a : n → n → BoundedContinuousFunction (Euc n) Real) (x0 : Euc n)
    (d2u : BoundedContinuousFunction (Euc n)
      (Euc n →L[Real] Euc n →L[Real] F)) :
    BoundedContinuousFunction (Euc n) F :=
  ∑ i, ∑ j,
    ((a i j x0) • hessianComponentBcf d2u i j -
      a i j • hessianComponentBcf d2u i j)

omit [DecidableEq n] [Nonempty n] in
@[simp]
theorem matrixLapFreezeDefect_apply
    (a : n → n → BoundedContinuousFunction (Euc n) Real) (x0 : Euc n)
    (d2u : BoundedContinuousFunction (Euc n)
      (Euc n →L[Real] Euc n →L[Real] F)) (x : Euc n) :
    matrixLapFreezeDefect a x0 d2u x =
      ∑ i, ∑ j, (a i j x0 - a i j x) •
        d2u x (EuclideanSpace.basisFun n Real i)
          (EuclideanSpace.basisFun n Real j) := by
  simp only [matrixLapFreezeDefect,
    BoundedContinuousFunction.sum_apply]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  change (a i j x0) •
      d2u x (EuclideanSpace.basisFun n Real i)
        (EuclideanSpace.basisFun n Real j) -
    a i j x • d2u x (EuclideanSpace.basisFun n Real i)
      (EuclideanSpace.basisFun n Real j) = _
  rw [sub_smul]

omit [DecidableEq n] [Nonempty n] in
theorem frozenMatrixLap_eq_variableMatrixLap_add_defect
    (a : n → n → BoundedContinuousFunction (Euc n) Real) (x0 : Euc n)
    (d2u : BoundedContinuousFunction (Euc n)
      (Euc n →L[Real] Euc n →L[Real] F)) :
    frozenMatrixLap a x0 d2u =
      variableMatrixLap a d2u + matrixLapFreezeDefect a x0 d2u := by
  ext x
  simp only [frozenMatrixLap_apply, BoundedContinuousFunction.add_apply,
    variableMatrixLap_apply, matrixLapFreezeDefect_apply, matrixLap]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  module

omit [DecidableEq n] [Nonempty n] in
theorem norm_apply_euclideanBasis_le_one
    {G : Type*} [NormedAddCommGroup G] [NormedSpace Real G] (i : n) :
    ‖ContinuousLinearMap.apply Real G
      (EuclideanSpace.basisFun n Real i)‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one ?_
  intro A
  change ‖A (EuclideanSpace.basisFun n Real i)‖ ≤ 1 * ‖A‖
  simpa only [(EuclideanSpace.basisFun n Real).orthonormal.norm_eq_one i,
    mul_one, one_mul] using A.le_opNorm (EuclideanSpace.basisFun n Real i)

omit [DecidableEq n] [Nonempty n] in
theorem norm_hessianComponentBcf_apply_le
    (d2u : BoundedContinuousFunction (Euc n)
      (Euc n →L[Real] Euc n →L[Real] F)) (i j : n) (x : Euc n) :
    ‖hessianComponentBcf d2u i j x‖ ≤ ‖d2u x‖ := by
  calc
    ‖d2u x (EuclideanSpace.basisFun n Real i)
        (EuclideanSpace.basisFun n Real j)‖ ≤
        ‖d2u x (EuclideanSpace.basisFun n Real i)‖ *
          ‖EuclideanSpace.basisFun n Real j‖ :=
      (d2u x (EuclideanSpace.basisFun n Real i)).le_opNorm _
    _ ≤ (‖d2u x‖ * ‖EuclideanSpace.basisFun n Real i‖) *
          ‖EuclideanSpace.basisFun n Real j‖ := by
      gcongr
      exact (d2u x).le_opNorm _
    _ = ‖d2u x‖ := by
      rw [(EuclideanSpace.basisFun n Real).orthonormal.norm_eq_one i,
        (EuclideanSpace.basisFun n Real).orthonormal.norm_eq_one j,
        mul_one, mul_one]

omit [DecidableEq n] [Nonempty n] in
theorem hessianComponentBcf_holderWith
    {alpha K : NNReal}
    (d2u : BoundedContinuousFunction (Euc n)
      (Euc n →L[Real] Euc n →L[Real] F))
    (hd2u : HolderWith K alpha
      (d2u : Euc n → Euc n →L[Real] Euc n →L[Real] F))
    (i j : n) :
    HolderWith K alpha (hessianComponentBcf d2u i j : Euc n → F) := by
  intro x y
  have hreal : dist (hessianComponentBcf d2u i j x)
      (hessianComponentBcf d2u i j y) ≤
      (K : Real) * dist x y ^ (alpha : Real) := by
    rw [dist_eq_norm]
    change ‖d2u x (EuclideanSpace.basisFun n Real i)
        (EuclideanSpace.basisFun n Real j) -
      d2u y (EuclideanSpace.basisFun n Real i)
        (EuclideanSpace.basisFun n Real j)‖ ≤ _
    rw [← ContinuousLinearMap.sub_apply, ← ContinuousLinearMap.sub_apply]
    calc
      ‖(d2u x - d2u y) (EuclideanSpace.basisFun n Real i)
          (EuclideanSpace.basisFun n Real j)‖ ≤ ‖d2u x - d2u y‖ := by
        calc
          _ ≤ ‖(d2u x - d2u y) (EuclideanSpace.basisFun n Real i)‖ *
              ‖EuclideanSpace.basisFun n Real j‖ :=
            ((d2u x - d2u y) (EuclideanSpace.basisFun n Real i)).le_opNorm _
          _ ≤ (‖d2u x - d2u y‖ *
                ‖EuclideanSpace.basisFun n Real i‖) *
              ‖EuclideanSpace.basisFun n Real j‖ := by
            gcongr
            exact (d2u x - d2u y).le_opNorm _
          _ = ‖d2u x - d2u y‖ := by
            rw [(EuclideanSpace.basisFun n Real).orthonormal.norm_eq_one i,
              (EuclideanSpace.basisFun n Real).orthonormal.norm_eq_one j,
              mul_one, mul_one]
      _ = dist (d2u x) (d2u y) :=
        (dist_eq_norm (d2u x) (d2u y)).symm
      _ ≤ (K : Real) * dist x y ^ (alpha : Real) := hd2u.dist_le x y
  rw [edist_dist, edist_dist]
  calc
    ENNReal.ofReal (dist (hessianComponentBcf d2u i j x)
        (hessianComponentBcf d2u i j y)) ≤
        ENNReal.ofReal ((K : Real) * dist x y ^ (alpha : Real)) :=
      ENNReal.ofReal_le_ofReal hreal
    _ = (K : ENNReal) * ENNReal.ofReal (dist x y ^ (alpha : Real)) := by
      rw [ENNReal.ofReal_mul K.coe_nonneg]
      congr 1
      exact ENNReal.ofReal_coe_nnreal
    _ = (K : ENNReal) * ENNReal.ofReal (dist x y) ^ (alpha : Real) := by
      rw [ENNReal.ofReal_rpow_of_nonneg (dist_nonneg) alpha.coe_nonneg]

omit [DecidableEq n] [Nonempty n] in
theorem norm_matrixLapFreezeDefect_le
    (a : n → n → BoundedContinuousFunction (Euc n) Real) (x0 : Euc n)
    (d2u : BoundedContinuousFunction (Euc n)
      (Euc n →L[Real] Euc n →L[Real] F))
    (omega : n → n → NNReal) (M : NNReal)
    (homega : ∀ i j x, ‖a i j x0 - a i j x‖ ≤ omega i j)
    (hd2unorm : ∀ x, ‖d2u x‖ ≤ M) :
    ‖matrixLapFreezeDefect a x0 d2u‖ ≤
      ∑ i, ∑ j, (omega i j : Real) * M := by
  rw [BoundedContinuousFunction.norm_le (by positivity)]
  intro x
  rw [matrixLapFreezeDefect_apply]
  calc
    ‖∑ i, ∑ j, (a i j x0 - a i j x) •
        d2u x (EuclideanSpace.basisFun n Real i)
          (EuclideanSpace.basisFun n Real j)‖ ≤
        ∑ i, ∑ j, ‖(a i j x0 - a i j x) •
          d2u x (EuclideanSpace.basisFun n Real i)
            (EuclideanSpace.basisFun n Real j)‖ :=
      (norm_sum_le _ _).trans
        (Finset.sum_le_sum fun i _ ↦ norm_sum_le _ _)
    _ ≤ ∑ i, ∑ j, (omega i j : Real) * M := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      rw [norm_smul]
      exact mul_le_mul (homega i j x)
        ((norm_hessianComponentBcf_apply_le d2u i j x).trans
          (hd2unorm x))
        (norm_nonneg _) (by positivity)

omit [DecidableEq n] [Nonempty n] in
theorem matrixLapFreezeDefect_holderWith
    {alpha Kd2u : NNReal}
    (a : n → n → BoundedContinuousFunction (Euc n) Real) (x0 : Euc n)
    (d2u : BoundedContinuousFunction (Euc n)
      (Euc n →L[Real] Euc n →L[Real] F))
    (Ka omega : n → n → NNReal) (M : NNReal)
    (ha : ∀ i j, HolderWith (Ka i j) alpha (a i j : Euc n → Real))
    (homega : ∀ i j x, ‖a i j x0 - a i j x‖ ≤ omega i j)
    (hd2unorm : ∀ x, ‖d2u x‖ ≤ M)
    (hd2u : HolderWith Kd2u alpha
      (d2u : Euc n → Euc n →L[Real] Euc n →L[Real] F)) :
    HolderWith
      (∑ i, ∑ j, (omega i j * Kd2u + M * Ka i j)) alpha
      (matrixLapFreezeDefect a x0 d2u : Euc n → F) := by
  classical
  let C : n → n → NNReal :=
    fun i j ↦ omega i j * Kd2u + M * Ka i j
  have hcomponent : ∀ i j,
      HolderWith (C i j) alpha (fun x ↦
        (a i j x0 - a i j x) •
          d2u x (EuclideanSpace.basisFun n Real i)
            (EuclideanSpace.basisFun n Real j)) := by
    intro i j
    have hcoeff : HolderWith (Ka i j) alpha
        (fun x : Euc n ↦ a i j x0 - a i j x) := by
      intro x y
      rw [show edist (a i j x0 - a i j x) (a i j x0 - a i j y) =
          edist (a i j x) (a i j y) by
        simp only [edist_dist, Real.dist_eq]
        rw [show a i j x0 - a i j x - (a i j x0 - a i j y) =
          -(a i j x - a i j y) by ring, abs_neg]]
      exact ha i j x y
    have hhess := hessianComponentBcf_holderWith d2u hd2u i j
    apply holderWith_smul_of_norm_le hcoeff hhess
    · exact homega i j
    · intro x
      exact (norm_hessianComponentBcf_apply_le d2u i j x).trans
        (hd2unorm x)
  have hinner : ∀ i,
      HolderWith (∑ j, C i j) alpha (fun x ↦
        ∑ j, (a i j x0 - a i j x) •
          d2u x (EuclideanSpace.basisFun n Real i)
            (EuclideanSpace.basisFun n Real j)) := by
    intro i
    exact holderWith_finset_sum Finset.univ
      (fun j _ ↦ hcomponent i j)
  have hall := holderWith_finset_sum Finset.univ
    (K := fun i ↦ ∑ j, C i j)
    (f := fun i x ↦ ∑ j, (a i j x0 - a i j x) •
      d2u x (EuclideanSpace.basisFun n Real i)
        (EuclideanSpace.basisFun n Real j))
    (fun i _ ↦ hinner i)
  have heq : (matrixLapFreezeDefect a x0 d2u : Euc n → F) =
      fun x ↦ ∑ i, ∑ j, (a i j x0 - a i j x) •
        d2u x (EuclideanSpace.basisFun n Real i)
          (EuclideanSpace.basisFun n Real j) := by
    funext x
    exact matrixLapFreezeDefect_apply a x0 d2u x
  rw [heq]
  simpa only [C] using hall

end DifferentialGeometry.Analysis.Schauder

end
