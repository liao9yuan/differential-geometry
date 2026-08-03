import DifferentialGeometry.Analysis.Schauder.ConstantCoefficientElliptic
import DifferentialGeometry.Analysis.Schauder.CutoffProduct
import DifferentialGeometry.Analysis.Schauder.Absorption
import Mathlib.Topology.ContinuousMap.Bounded.Normed

noncomputable section

open Real
open scoped BoundedContinuousFunction NNReal RealInnerProductSpace

namespace DifferentialGeometry.Analysis.Schauder

open DifferentialGeometry.Analysis.Parabolic.Euclidean

private abbrev Euc (n : Type*) := EuclideanSpace Real n

private def hessianCurryEquiv
    (E F : Type*) [NormedAddCommGroup E] [NormedSpace Real E]
    [NormedAddCommGroup F] [NormedSpace Real F] :
    (E [×2]→L[Real] F) ≃ₗᵢ[Real] E →L[Real] E →L[Real] F :=
  (continuousMultilinearCurryRightEquiv' Real 1 E F).trans
    (continuousMultilinearCurryFin1 Real E (E →L[Real] F))

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

section Estimates

variable [CompleteSpace F]

omit [DecidableEq n] [Nonempty n] [CompleteSpace F] in
private theorem hessianCurryEquiv_iteratedFDeriv_two
    (u : BoundedContinuousFunction (Euc n) F)
    (du : BoundedContinuousFunction (Euc n) (Euc n →L[Real] F))
    (d2u : BoundedContinuousFunction (Euc n)
      (Euc n →L[Real] Euc n →L[Real] F))
    (hu : ∀ x, HasFDerivAt (u : Euc n → F) (du x) x)
    (hdu : ∀ x,
      HasFDerivAt (du : Euc n → Euc n →L[Real] F) (d2u x) x)
    (x : Euc n) :
    hessianCurryEquiv (Euc n) F
        (iteratedFDeriv Real 2 (u : Euc n → F) x) = d2u x := by
  have hfd : fderiv Real (u : Euc n → F) =
      (du : Euc n → Euc n →L[Real] F) := by
    funext y
    exact (hu y).fderiv
  ext v w
  simp only [hessianCurryEquiv, LinearIsometryEquiv.trans_apply,
    continuousMultilinearCurryFin1_apply,
    continuousMultilinearCurryRightEquiv_apply', iteratedFDeriv_two_apply]
  rw [hfd, (hdu x).fderiv]
  rfl

theorem frozen_matrix_laplacian_schauder_estimate
    {alpha K B : NNReal}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (a : n → n → BoundedContinuousFunction (Euc n) Real) (x0 : Euc n)
    (hA : Matrix.PosDef (fun i j ↦ a i j x0))
    (u : BoundedContinuousFunction (Euc n) F)
    (du : BoundedContinuousFunction (Euc n) (Euc n →L[Real] F))
    (d2u : BoundedContinuousFunction (Euc n)
      (Euc n →L[Real] Euc n →L[Real] F))
    (hu : ∀ x, HasFDerivAt (u : Euc n → F) (du x) x)
    (hdu : ∀ x,
      HasFDerivAt (du : Euc n → Euc n →L[Real] F) (d2u x) x)
    (hbound : ‖frozenMatrixLap a x0 d2u‖ ≤ B)
    (hholder : HolderWith K alpha (frozenMatrixLap a x0 d2u)) :
    eContDiffHolderGaugeOn 2 alpha Set.univ (u : Euc n → F) ≤
      spdLaplacianSchauderConst (fun i j ↦ a i j x0) hA alpha K B u := by
  let A : Matrix n n Real := fun i j ↦ a i j x0
  have heq : spdMatrixLap A hA d2u = frozenMatrixLap a x0 d2u := by
    ext x
    simp only [spdMatrixLap_apply, frozenMatrixLap_apply, A]
  apply spd_laplacian_schauder_estimate halpha0 halpha1 A hA
    u du d2u hu hdu
  · rw [heq]
    exact hbound
  · rw [heq]
    exact hholder

theorem variable_coefficient_schauder_estimate_of_freeze_defect
    {alpha Kf Kdefect Bf Bdefect : NNReal}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (a : n → n → BoundedContinuousFunction (Euc n) Real) (x0 : Euc n)
    (hA : Matrix.PosDef (fun i j ↦ a i j x0))
    (u : BoundedContinuousFunction (Euc n) F)
    (du : BoundedContinuousFunction (Euc n) (Euc n →L[Real] F))
    (d2u : BoundedContinuousFunction (Euc n)
      (Euc n →L[Real] Euc n →L[Real] F))
    (hu : ∀ x, HasFDerivAt (u : Euc n → F) (du x) x)
    (hdu : ∀ x,
      HasFDerivAt (du : Euc n → Euc n →L[Real] F) (d2u x) x)
    (hfBound : ‖variableMatrixLap a d2u‖ ≤ Bf)
    (hdefectBound : ‖matrixLapFreezeDefect a x0 d2u‖ ≤ Bdefect)
    (hfHolder : HolderWith Kf alpha (variableMatrixLap a d2u))
    (hdefectHolder : HolderWith Kdefect alpha
      (matrixLapFreezeDefect a x0 d2u)) :
    eContDiffHolderGaugeOn 2 alpha Set.univ (u : Euc n → F) ≤
      spdLaplacianSchauderConst (fun i j ↦ a i j x0) hA alpha
        (Kf + Kdefect) (Bf + Bdefect) u := by
  have hbound : ‖frozenMatrixLap a x0 d2u‖ ≤ Bf + Bdefect := by
    rw [frozenMatrixLap_eq_variableMatrixLap_add_defect]
    exact (norm_add_le _ _).trans (add_le_add hfBound hdefectBound)
  have hholder : HolderWith (Kf + Kdefect) alpha
      (frozenMatrixLap a x0 d2u) := by
    rw [frozenMatrixLap_eq_variableMatrixLap_add_defect]
    exact hfHolder.add hdefectHolder
  exact frozen_matrix_laplacian_schauder_estimate halpha0 halpha1
    a x0 hA u du d2u hu hdu hbound hholder

theorem variable_coefficient_schauder_estimate_of_coefficient_oscillation
    {alpha Kf Kd2u Bf : NNReal}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (a : n → n → BoundedContinuousFunction (Euc n) Real) (x0 : Euc n)
    (hA : Matrix.PosDef (fun i j ↦ a i j x0))
    (u : BoundedContinuousFunction (Euc n) F)
    (du : BoundedContinuousFunction (Euc n) (Euc n →L[Real] F))
    (d2u : BoundedContinuousFunction (Euc n)
      (Euc n →L[Real] Euc n →L[Real] F))
    (hu : ∀ x, HasFDerivAt (u : Euc n → F) (du x) x)
    (hdu : ∀ x,
      HasFDerivAt (du : Euc n → Euc n →L[Real] F) (d2u x) x)
    (hfBound : ‖variableMatrixLap a d2u‖ ≤ Bf)
    (hfHolder : HolderWith Kf alpha (variableMatrixLap a d2u))
    (Ka omega : n → n → NNReal) (M : NNReal)
    (ha : ∀ i j, HolderWith (Ka i j) alpha (a i j : Euc n → Real))
    (homega : ∀ i j x, ‖a i j x0 - a i j x‖ ≤ omega i j)
    (hd2unorm : ∀ x, ‖d2u x‖ ≤ M)
    (hd2uHolder : HolderWith Kd2u alpha
      (d2u : Euc n → Euc n →L[Real] Euc n →L[Real] F)) :
    eContDiffHolderGaugeOn 2 alpha Set.univ (u : Euc n → F) ≤
      spdLaplacianSchauderConst (fun i j ↦ a i j x0) hA alpha
        (Kf + ∑ i, ∑ j, (omega i j * Kd2u + M * Ka i j))
        (Bf + ∑ i, ∑ j, omega i j * M) u := by
  let Kdefect : NNReal :=
    ∑ i, ∑ j, (omega i j * Kd2u + M * Ka i j)
  let Bdefect : NNReal := ∑ i, ∑ j, omega i j * M
  have hdefectBound : ‖matrixLapFreezeDefect a x0 d2u‖ ≤ Bdefect := by
    have hraw := norm_matrixLapFreezeDefect_le a x0 d2u omega M
      homega hd2unorm
    exact_mod_cast hraw
  have hdefectHolder : HolderWith Kdefect alpha
      (matrixLapFreezeDefect a x0 d2u) :=
    matrixLapFreezeDefect_holderWith a x0 d2u Ka omega M
      ha homega hd2unorm hd2uHolder
  exact variable_coefficient_schauder_estimate_of_freeze_defect
    halpha0 halpha1 a x0 hA u du d2u hu hdu hfBound hdefectBound
    hfHolder hdefectHolder

theorem variable_coefficient_schauder_estimate_of_small_oscillation_of_hessian_control
    {alpha Kf Bf X : NNReal}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (a : n → n → BoundedContinuousFunction (Euc n) Real) (x0 : Euc n)
    (hA : Matrix.PosDef (fun i j ↦ a i j x0))
    (u : BoundedContinuousFunction (Euc n) F)
    (du : BoundedContinuousFunction (Euc n) (Euc n →L[Real] F))
    (d2u : BoundedContinuousFunction (Euc n)
      (Euc n →L[Real] Euc n →L[Real] F))
    (hu : ∀ x, HasFDerivAt (u : Euc n → F) (du x) x)
    (hdu : ∀ x,
      HasFDerivAt (du : Euc n → Euc n →L[Real] F) (d2u x) x)
    (hfBound : ‖variableMatrixLap a d2u‖ ≤ Bf)
    (hfHolder : HolderWith Kf alpha (variableMatrixLap a d2u))
    (Ka omega : n → n → NNReal)
    (ha : ∀ i j, HolderWith (Ka i j) alpha (a i j : Euc n → Real))
    (homega : ∀ i j x, ‖a i j x0 - a i j x‖ ≤ omega i j)
    (hd2unorm : ∀ x, ‖d2u x‖ ≤ X)
    (hd2uHolder : HolderWith X alpha
      (d2u : Euc n → Euc n →L[Real] Euc n →L[Real] F))
    (hX : (X : ENNReal) ≤
      eContDiffHolderGaugeOn 2 alpha Set.univ (u : Euc n → F))
    (hsmall : spdLaplacianSchauderDefectConst
      (fun i j ↦ a i j x0) hA alpha
        (∑ i, ∑ j, (omega i j + Ka i j))
        (∑ i, ∑ j, omega i j) < 1) :
    eContDiffHolderGaugeOn 2 alpha Set.univ (u : Euc n → F) ≤
      ((spdLaplacianSchauderConst (fun i j ↦ a i j x0) hA
        alpha Kf Bf u) /
        (1 - spdLaplacianSchauderDefectConst
          (fun i j ↦ a i j x0) hA alpha
            (∑ i, ∑ j, (omega i j + Ka i j))
            (∑ i, ∑ j, omega i j)) : NNReal) := by
  let Kosc : NNReal := ∑ i, ∑ j, (omega i j + Ka i j)
  let Bosc : NNReal := ∑ i, ∑ j, omega i j
  let epsilon : NNReal := spdLaplacianSchauderDefectConst
    (fun i j ↦ a i j x0) hA alpha Kosc Bosc
  let C : NNReal := spdLaplacianSchauderConst
    (fun i j ↦ a i j x0) hA alpha Kf Bf u
  have hK : (∑ i, ∑ j, (omega i j * X + X * Ka i j)) = X * Kosc := by
    simp only [Kosc, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    ring
  have hB : (∑ i, ∑ j, omega i j * X) = X * Bosc := by
    simp only [Bosc, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    ring
  have hraw := variable_coefficient_schauder_estimate_of_coefficient_oscillation
    halpha0 halpha1 a x0 hA u du d2u hu hdu hfBound hfHolder
    Ka omega X ha homega hd2unorm hd2uHolder
  rw [hK, hB,
    spdLaplacianSchauderConst_add_source halpha1
      (fun i j ↦ a i j x0) hA Kf (X * Kosc) Bf (X * Bosc) u,
    spdLaplacianSchauderDefectConst_nnreal_mul
      (fun i j ↦ a i j x0) hA alpha X Kosc Bosc] at hraw
  have hraw' :
      eContDiffHolderGaugeOn 2 alpha Set.univ (u : Euc n → F) ≤
        (C : ENNReal) + (epsilon : ENNReal) * X := by
    simpa only [C, epsilon, ENNReal.coe_add, ENNReal.coe_mul,
      mul_comm] using hraw
  have hself :
      eContDiffHolderGaugeOn 2 alpha Set.univ (u : Euc n → F) ≤
        (C : ENNReal) + (epsilon : ENNReal) *
          eContDiffHolderGaugeOn 2 alpha Set.univ (u : Euc n → F) :=
    hraw'.trans (by gcongr)
  have hfinite :
      eContDiffHolderGaugeOn 2 alpha Set.univ (u : Euc n → F) ≠ ⊤ :=
    ne_of_lt (hraw'.trans_lt (ENNReal.add_lt_top.mpr
      ⟨ENNReal.coe_lt_top,
        ENNReal.mul_lt_top ENNReal.coe_lt_top ENNReal.coe_lt_top⟩))
  have habsorb := ennreal_le_coe_div_one_sub_of_le_add_mul
    hfinite (show epsilon < 1 by simpa only [epsilon, Kosc, Bosc] using hsmall)
    hself
  simpa only [C, epsilon, Kosc, Bosc] using habsorb

theorem variable_coefficient_schauder_estimate_of_small_oscillation
    {alpha Kf Kd2u Bf M : NNReal}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (a : n → n → BoundedContinuousFunction (Euc n) Real) (x0 : Euc n)
    (hA : Matrix.PosDef (fun i j ↦ a i j x0))
    (u : BoundedContinuousFunction (Euc n) F)
    (du : BoundedContinuousFunction (Euc n) (Euc n →L[Real] F))
    (d2u : BoundedContinuousFunction (Euc n)
      (Euc n →L[Real] Euc n →L[Real] F))
    (hu : ∀ x, HasFDerivAt (u : Euc n → F) (du x) x)
    (hdu : ∀ x,
      HasFDerivAt (du : Euc n → Euc n →L[Real] F) (d2u x) x)
    (hfBound : ‖variableMatrixLap a d2u‖ ≤ Bf)
    (hfHolder : HolderWith Kf alpha (variableMatrixLap a d2u))
    (Ka omega : n → n → NNReal)
    (ha : ∀ i j, HolderWith (Ka i j) alpha (a i j : Euc n → Real))
    (homega : ∀ i j x, ‖a i j x0 - a i j x‖ ≤ omega i j)
    (hd2unorm0 : ∀ x, ‖d2u x‖ ≤ M)
    (hd2uHolder : HolderWith Kd2u alpha
      (d2u : Euc n → Euc n →L[Real] Euc n →L[Real] F))
    (hsmall : spdLaplacianSchauderDefectConst
      (fun i j ↦ a i j x0) hA alpha
        (∑ i, ∑ j, (omega i j + Ka i j))
        (∑ i, ∑ j, omega i j) < 1) :
    eContDiffHolderGaugeOn 2 alpha Set.univ (u : Euc n → F) ≤
      ((spdLaplacianSchauderConst (fun i j ↦ a i j x0) hA
        alpha Kf Bf u) /
        (1 - spdLaplacianSchauderDefectConst
          (fun i j ↦ a i j x0) hA alpha
            (∑ i, ∑ j, (omega i j + Ka i j))
            (∑ i, ∑ j, omega i j)) : NNReal) := by
  let e := hessianCurryEquiv (Euc n) F
  have heq : ∀ x, e (iteratedFDeriv Real 2 (u : Euc n → F) x) = d2u x :=
    hessianCurryEquiv_iteratedFDeriv_two u du d2u hu hdu
  let Cspatial : Nat → NNReal
    | 0 => ‖u‖₊
    | 1 => ‖du‖₊
    | _ => M
  have hspatial : ∀ j ≤ 2, ∀ x ∈ (Set.univ : Set (Euc n)),
      ‖iteratedFDeriv Real j (u : Euc n → F) x‖ ≤ Cspatial j := by
    intro j hj x hx
    interval_cases j
    · rw [norm_iteratedFDeriv_zero]
      simpa only [Cspatial] using u.norm_coe_le_norm x
    · rw [norm_iteratedFDeriv_one, (hu x).fderiv]
      simpa only [Cspatial] using du.norm_coe_le_norm x
    · rw [← e.norm_map (iteratedFDeriv Real 2 (u : Euc n → F) x), heq]
      simpa only [Cspatial] using hd2unorm0 x
  have hiterHolder : HolderWith Kd2u alpha
      (iteratedFDeriv Real 2 (u : Euc n → F)) := by
    have hcomp := e.symm.lipschitz.holderWith.comp hd2uHolder
    have hfun : e.symm ∘ (d2u : Euc n → Euc n →L[Real] Euc n →L[Real] F) =
        iteratedFDeriv Real 2 (u : Euc n → F) := by
      funext x
      rw [Function.comp_apply, ← heq x, e.symm_apply_apply]
    rw [hfun] at hcomp
    simpa using hcomp
  have hgaugeBound := eContDiffHolderGaugeOn_le
    Cspatial Kd2u hspatial
      ((hiterHolder.holderOnWith Set.univ).holderWith)
  have hgaugeFinite :
      eContDiffHolderGaugeOn 2 alpha Set.univ (u : Euc n → F) ≠ ⊤ :=
    ne_of_lt (hgaugeBound.trans_lt (by simp))
  let X : NNReal :=
    (eContDiffHolderGaugeOn 2 alpha Set.univ (u : Euc n → F)).toNNReal
  have hcoeX : (X : ENNReal) =
      eContDiffHolderGaugeOn 2 alpha Set.univ (u : Euc n → F) := by
    exact ENNReal.coe_toNNReal hgaugeFinite
  have hgaugeLeX :
      eContDiffHolderGaugeOn 2 alpha Set.univ (u : Euc n → F) ≤ X :=
    hcoeX.ge
  have hd2unorm : ∀ x, ‖d2u x‖ ≤ X := by
    intro x
    calc
      ‖d2u x‖ = ‖e (iteratedFDeriv Real 2 (u : Euc n → F) x)‖ :=
        congrArg norm (heq x).symm
      _ = ‖iteratedFDeriv Real 2 (u : Euc n → F) x‖ := e.norm_map _
      _ ≤ X := spatialJet_norm_le hgaugeLeX le_rfl (Set.mem_univ x)
  have hiterRestrict := topSpatialJet_holderWith_restrict hgaugeLeX
  have hd2uRestrict : HolderWith X alpha
      ((Set.univ : Set (Euc n)).restrict
        (d2u : Euc n → Euc n →L[Real] Euc n →L[Real] F)) := by
    have hcomp := e.lipschitz.holderWith.comp hiterRestrict
    have hfun : e ∘ ((Set.univ : Set (Euc n)).restrict
        (iteratedFDeriv Real 2 (u : Euc n → F))) =
      (Set.univ : Set (Euc n)).restrict
        (d2u : Euc n → Euc n →L[Real] Euc n →L[Real] F) := by
      funext x
      exact heq x
    rw [hfun] at hcomp
    simpa using hcomp
  have hd2uHolderX : HolderWith X alpha
      (d2u : Euc n → Euc n →L[Real] Euc n →L[Real] F) := by
    intro x y
    simpa using hd2uRestrict
      (⟨x, Set.mem_univ x⟩ : Set.univ)
      (⟨y, Set.mem_univ y⟩ : Set.univ)
  exact variable_coefficient_schauder_estimate_of_small_oscillation_of_hessian_control
    halpha0 halpha1 a x0 hA u du d2u hu hdu hfBound hfHolder
    Ka omega ha homega hd2unorm hd2uHolderX hcoeX.le hsmall

end Estimates

end DifferentialGeometry.Analysis.Schauder

end
