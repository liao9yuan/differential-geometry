import DifferentialGeometry.Analysis.Schauder.VariableCoefficient

noncomputable section

open Real
open scoped BoundedContinuousFunction NNReal RealInnerProductSpace

namespace DifferentialGeometry.Analysis.Schauder

open DifferentialGeometry.Analysis.Parabolic.Euclidean

private abbrev Euc (n : Type*) := EuclideanSpace Real n

variable {n F : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
  [NormedAddCommGroup F] [NormedSpace Real F] [CompleteSpace F]

def gradientComponentBcf
    (du : BoundedContinuousFunction (Euc n) (Euc n →L[Real] F))
    (i : n) : BoundedContinuousFunction (Euc n) F :=
  (ContinuousLinearMap.apply Real F (EuclideanSpace.basisFun n Real i))
    |>.compLeftContinuousBounded (Euc n) du

omit [DecidableEq n] [Nonempty n] [CompleteSpace F] in
@[simp]
theorem gradientComponentBcf_apply
    (du : BoundedContinuousFunction (Euc n) (Euc n →L[Real] F))
    (i : n) (x : Euc n) :
    gradientComponentBcf du i x =
      du x (EuclideanSpace.basisFun n Real i) := rfl

def driftTerm
    (b : n → BoundedContinuousFunction (Euc n) Real)
    (du : BoundedContinuousFunction (Euc n) (Euc n →L[Real] F)) :
    BoundedContinuousFunction (Euc n) F :=
  ∑ i, b i • gradientComponentBcf du i

omit [DecidableEq n] [Nonempty n] [CompleteSpace F] in
@[simp]
theorem driftTerm_apply
    (b : n → BoundedContinuousFunction (Euc n) Real)
    (du : BoundedContinuousFunction (Euc n) (Euc n →L[Real] F))
    (x : Euc n) :
    driftTerm b du x =
      ∑ i, b i x • du x (EuclideanSpace.basisFun n Real i) := by
  simp only [driftTerm, BoundedContinuousFunction.sum_apply]
  apply Finset.sum_congr rfl
  intro i hi
  rfl

def potentialTerm
    (c : BoundedContinuousFunction (Euc n) Real)
    (u : BoundedContinuousFunction (Euc n) F) :
    BoundedContinuousFunction (Euc n) F :=
  c • u

omit [Fintype n] [DecidableEq n] [Nonempty n] [CompleteSpace F] in
@[simp]
theorem potentialTerm_apply
    (c : BoundedContinuousFunction (Euc n) Real)
    (u : BoundedContinuousFunction (Euc n) F) (x : Euc n) :
    potentialTerm c u x = c x • u x := rfl

def lowerOrderTerm
    (b : n → BoundedContinuousFunction (Euc n) Real)
    (c : BoundedContinuousFunction (Euc n) Real)
    (u : BoundedContinuousFunction (Euc n) F)
    (du : BoundedContinuousFunction (Euc n) (Euc n →L[Real] F)) :
    BoundedContinuousFunction (Euc n) F :=
  driftTerm b du + potentialTerm c u

omit [DecidableEq n] [Nonempty n] [CompleteSpace F] in
@[simp]
theorem lowerOrderTerm_apply
    (b : n → BoundedContinuousFunction (Euc n) Real)
    (c : BoundedContinuousFunction (Euc n) Real)
    (u : BoundedContinuousFunction (Euc n) F)
    (du : BoundedContinuousFunction (Euc n) (Euc n →L[Real] F))
    (x : Euc n) :
    lowerOrderTerm b c u du x =
      ∑ i, b i x • du x (EuclideanSpace.basisFun n Real i) +
        c x • u x := by
  rw [lowerOrderTerm, BoundedContinuousFunction.add_apply,
    driftTerm_apply, potentialTerm_apply]

def nondivergenceOperator
    (a : n → n → BoundedContinuousFunction (Euc n) Real)
    (b : n → BoundedContinuousFunction (Euc n) Real)
    (c : BoundedContinuousFunction (Euc n) Real)
    (u : BoundedContinuousFunction (Euc n) F)
    (du : BoundedContinuousFunction (Euc n) (Euc n →L[Real] F))
    (d2u : BoundedContinuousFunction (Euc n)
      (Euc n →L[Real] Euc n →L[Real] F)) :
    BoundedContinuousFunction (Euc n) F :=
  variableMatrixLap a d2u + lowerOrderTerm b c u du

omit [DecidableEq n] [Nonempty n] [CompleteSpace F] in
@[simp]
theorem nondivergenceOperator_apply
    (a : n → n → BoundedContinuousFunction (Euc n) Real)
    (b : n → BoundedContinuousFunction (Euc n) Real)
    (c : BoundedContinuousFunction (Euc n) Real)
    (u : BoundedContinuousFunction (Euc n) F)
    (du : BoundedContinuousFunction (Euc n) (Euc n →L[Real] F))
    (d2u : BoundedContinuousFunction (Euc n)
      (Euc n →L[Real] Euc n →L[Real] F))
    (x : Euc n) :
    nondivergenceOperator a b c u du d2u x =
      matrixLap (fun i j ↦ a i j x) (d2u x) +
        (∑ i, b i x • du x (EuclideanSpace.basisFun n Real i) +
          c x • u x) := by
  simp only [nondivergenceOperator, BoundedContinuousFunction.add_apply,
    variableMatrixLap_apply, lowerOrderTerm_apply]

omit [DecidableEq n] [Nonempty n] [CompleteSpace F] in
theorem variableMatrixLap_eq_nondivergenceOperator_sub_lowerOrderTerm
    (a : n → n → BoundedContinuousFunction (Euc n) Real)
    (b : n → BoundedContinuousFunction (Euc n) Real)
    (c : BoundedContinuousFunction (Euc n) Real)
    (u : BoundedContinuousFunction (Euc n) F)
    (du : BoundedContinuousFunction (Euc n) (Euc n →L[Real] F))
    (d2u : BoundedContinuousFunction (Euc n)
      (Euc n →L[Real] Euc n →L[Real] F)) :
    variableMatrixLap a d2u =
      nondivergenceOperator a b c u du d2u - lowerOrderTerm b c u du := by
  unfold nondivergenceOperator
  abel

omit [DecidableEq n] [Nonempty n] [CompleteSpace F] in
theorem norm_driftTerm_le
    (b : n → BoundedContinuousFunction (Euc n) Real)
    (du : BoundedContinuousFunction (Euc n) (Euc n →L[Real] F))
    (Bb : n → NNReal) (Mdu : NNReal)
    (hb : ∀ i x, ‖b i x‖ ≤ Bb i)
    (hdu : ∀ x, ‖du x‖ ≤ Mdu) :
    ‖driftTerm b du‖ ≤ ∑ i, (Bb i : Real) * Mdu := by
  rw [BoundedContinuousFunction.norm_le (by positivity)]
  intro x
  rw [driftTerm_apply]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i hi ↦ ?_)
  rw [norm_smul, Real.norm_eq_abs]
  exact mul_le_mul (by simpa only [Real.norm_eq_abs] using hb i x)
    ((du x).le_opNorm _ |>.trans (by
      rw [(EuclideanSpace.basisFun n Real).orthonormal.norm_eq_one i]
      simpa using hdu x)) (norm_nonneg _) (by positivity)

omit [DecidableEq n] [Nonempty n] [CompleteSpace F] in
theorem driftTerm_holderWith
    {alpha Kdu : NNReal}
    (b : n → BoundedContinuousFunction (Euc n) Real)
    (du : BoundedContinuousFunction (Euc n) (Euc n →L[Real] F))
    (Kb Bb : n → NNReal) (Mdu : NNReal)
    (hb : ∀ i, HolderWith (Kb i) alpha (b i : Euc n → Real))
    (hbNorm : ∀ i x, ‖b i x‖ ≤ Bb i)
    (hdu : HolderWith Kdu alpha
      (du : Euc n → Euc n →L[Real] F))
    (hduNorm : ∀ x, ‖du x‖ ≤ Mdu) :
    HolderWith (∑ i, (Bb i * Kdu + Mdu * Kb i)) alpha
      (driftTerm b du : Euc n → F) := by
  have hcomponent : ∀ i, HolderWith (Bb i * Kdu + Mdu * Kb i) alpha
      (fun x ↦ b i x • du x (EuclideanSpace.basisFun n Real i)) := by
    intro i
    have hdui : HolderWith Kdu alpha
        (fun x ↦ du x (EuclideanSpace.basisFun n Real i)) :=
      holderWith_comp_continuousLinearMap_of_norm_le_one
        (ContinuousLinearMap.apply Real F
          (EuclideanSpace.basisFun n Real i))
        (norm_apply_euclideanBasis_le_one i) hdu
    apply holderWith_smul_of_norm_le (hb i) hdui (hbNorm i)
    intro x
    exact (du x).le_opNorm _ |>.trans (by
      rw [(EuclideanSpace.basisFun n Real).orthonormal.norm_eq_one i]
      simpa using hduNorm x)
  have hsum := holderWith_finset_sum
    (Finset.univ : Finset n)
    (K := fun i ↦ Bb i * Kdu + Mdu * Kb i)
    (f := fun i x ↦ b i x • du x (EuclideanSpace.basisFun n Real i))
    (fun i hi ↦ hcomponent i)
  rw [show (driftTerm b du : Euc n → F) =
    fun x ↦ ∑ i, b i x • du x (EuclideanSpace.basisFun n Real i) from
      funext fun x ↦ driftTerm_apply b du x]
  simpa only [Finset.sum_filter, Finset.mem_univ, implies_true] using hsum

omit [Fintype n] [DecidableEq n] [Nonempty n] [CompleteSpace F] in
theorem norm_potentialTerm_le
    (c : BoundedContinuousFunction (Euc n) Real)
    (u : BoundedContinuousFunction (Euc n) F)
    (Bc Mu : NNReal)
    (hc : ∀ x, ‖c x‖ ≤ Bc) (hu : ∀ x, ‖u x‖ ≤ Mu) :
    ‖potentialTerm c u‖ ≤ (Bc : Real) * Mu := by
  rw [BoundedContinuousFunction.norm_le (by positivity)]
  intro x
  rw [potentialTerm_apply, norm_smul, Real.norm_eq_abs]
  exact mul_le_mul (by simpa only [Real.norm_eq_abs] using hc x)
    (hu x) (norm_nonneg _) (by positivity)

omit [DecidableEq n] [Nonempty n] [CompleteSpace F] in
theorem potentialTerm_holderWith
    {alpha Kc Ku Bc Mu : NNReal}
    (c : BoundedContinuousFunction (Euc n) Real)
    (u : BoundedContinuousFunction (Euc n) F)
    (hc : HolderWith Kc alpha (c : Euc n → Real))
    (hu : HolderWith Ku alpha (u : Euc n → F))
    (hcNorm : ∀ x, ‖c x‖ ≤ Bc) (huNorm : ∀ x, ‖u x‖ ≤ Mu) :
    HolderWith (Bc * Ku + Mu * Kc) alpha
      (potentialTerm c u : Euc n → F) := by
  simpa only [potentialTerm_apply] using
    holderWith_smul_of_norm_le hc hu hcNorm huNorm

def lowerOrderSupConst
    (Bb : n → NNReal) (Bc Mdu Mu : NNReal) : NNReal :=
  (∑ i, Bb i * Mdu) + Bc * Mu

def lowerOrderHolderConst
    (Kb Bb : n → NNReal) (Kc Kdu Ku Mdu Bc Mu : NNReal) : NNReal :=
  (∑ i, (Bb i * Kdu + Mdu * Kb i)) + (Bc * Ku + Mu * Kc)

omit [DecidableEq n] [Nonempty n] [CompleteSpace F] in
theorem norm_lowerOrderTerm_le
    (b : n → BoundedContinuousFunction (Euc n) Real)
    (c : BoundedContinuousFunction (Euc n) Real)
    (u : BoundedContinuousFunction (Euc n) F)
    (du : BoundedContinuousFunction (Euc n) (Euc n →L[Real] F))
    (Bb : n → NNReal) (Bc Mdu Mu : NNReal)
    (hb : ∀ i x, ‖b i x‖ ≤ Bb i)
    (hc : ∀ x, ‖c x‖ ≤ Bc)
    (hdu : ∀ x, ‖du x‖ ≤ Mdu) (hu : ∀ x, ‖u x‖ ≤ Mu) :
    ‖lowerOrderTerm b c u du‖ ≤ lowerOrderSupConst Bb Bc Mdu Mu := by
  rw [lowerOrderTerm]
  refine (norm_add_le _ _).trans ?_
  have hb' := norm_driftTerm_le b du Bb Mdu hb hdu
  have hc' := norm_potentialTerm_le c u Bc Mu hc hu
  exact_mod_cast add_le_add hb' hc'

omit [DecidableEq n] [Nonempty n] [CompleteSpace F] in
theorem lowerOrderTerm_holderWith
    {alpha Kc Kdu Ku : NNReal}
    (b : n → BoundedContinuousFunction (Euc n) Real)
    (c : BoundedContinuousFunction (Euc n) Real)
    (u : BoundedContinuousFunction (Euc n) F)
    (du : BoundedContinuousFunction (Euc n) (Euc n →L[Real] F))
    (Kb Bb : n → NNReal) (Mdu Bc Mu : NNReal)
    (hb : ∀ i, HolderWith (Kb i) alpha (b i : Euc n → Real))
    (hc : HolderWith Kc alpha (c : Euc n → Real))
    (hdu : HolderWith Kdu alpha
      (du : Euc n → Euc n →L[Real] F))
    (hu : HolderWith Ku alpha (u : Euc n → F))
    (hbNorm : ∀ i x, ‖b i x‖ ≤ Bb i)
    (hcNorm : ∀ x, ‖c x‖ ≤ Bc)
    (hduNorm : ∀ x, ‖du x‖ ≤ Mdu)
    (huNorm : ∀ x, ‖u x‖ ≤ Mu) :
    HolderWith (lowerOrderHolderConst Kb Bb Kc Kdu Ku Mdu Bc Mu) alpha
      (lowerOrderTerm b c u du : Euc n → F) := by
  exact (driftTerm_holderWith b du Kb Bb Mdu hb hbNorm hdu hduNorm).add
    (potentialTerm_holderWith c u hc hu hcNorm huNorm)

theorem variable_coefficient_schauder_estimate_of_lower_order_source
    {alpha KL Klo BL Blo M Kd2u : NNReal}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (a : n → n → BoundedContinuousFunction (Euc n) Real) (x0 : Euc n)
    (hA : Matrix.PosDef (fun i j ↦ a i j x0))
    (b : n → BoundedContinuousFunction (Euc n) Real)
    (c : BoundedContinuousFunction (Euc n) Real)
    (u : BoundedContinuousFunction (Euc n) F)
    (du : BoundedContinuousFunction (Euc n) (Euc n →L[Real] F))
    (d2u : BoundedContinuousFunction (Euc n)
      (Euc n →L[Real] Euc n →L[Real] F))
    (hu : ∀ x, HasFDerivAt (u : Euc n → F) (du x) x)
    (hdu : ∀ x,
      HasFDerivAt (du : Euc n → Euc n →L[Real] F) (d2u x) x)
    (hLBound : ‖nondivergenceOperator a b c u du d2u‖ ≤ BL)
    (hLHolder : HolderWith KL alpha
      (nondivergenceOperator a b c u du d2u))
    (hloBound : ‖lowerOrderTerm b c u du‖ ≤ Blo)
    (hloHolder : HolderWith Klo alpha (lowerOrderTerm b c u du))
    (Ka omega : n → n → NNReal)
    (ha : ∀ i j, HolderWith (Ka i j) alpha (a i j : Euc n → Real))
    (homega : ∀ i j x, ‖a i j x0 - a i j x‖ ≤ omega i j)
    (hd2unorm : ∀ x, ‖d2u x‖ ≤ M)
    (hd2uHolder : HolderWith Kd2u alpha
      (d2u : Euc n → Euc n →L[Real] Euc n →L[Real] F))
    (hsmall : spdLaplacianSchauderDefectConst
      (fun i j ↦ a i j x0) hA alpha
        (∑ i, ∑ j, (omega i j + Ka i j))
        (∑ i, ∑ j, omega i j) < 1) :
    eContDiffHolderGaugeOn 2 alpha Set.univ (u : Euc n → F) ≤
      ((spdLaplacianSchauderConst (fun i j ↦ a i j x0) hA
        alpha (KL + Klo) (BL + Blo) u) /
        (1 - spdLaplacianSchauderDefectConst
          (fun i j ↦ a i j x0) hA alpha
            (∑ i, ∑ j, (omega i j + Ka i j))
            (∑ i, ∑ j, omega i j)) : NNReal) := by
  have hprincipalBound :
      ‖variableMatrixLap a d2u‖ ≤ ((BL + Blo : NNReal) : Real) := by
    rw [variableMatrixLap_eq_nondivergenceOperator_sub_lowerOrderTerm]
    exact (norm_sub_le _ _).trans (add_le_add hLBound hloBound)
  have hprincipalHolder : HolderWith (KL + Klo) alpha
      (variableMatrixLap a d2u) := by
    rw [variableMatrixLap_eq_nondivergenceOperator_sub_lowerOrderTerm]
    exact holderWith_sub hLHolder hloHolder
  exact variable_coefficient_schauder_estimate_of_small_oscillation
    (Kf := KL + Klo) (Bf := BL + Blo) (M := M) (Kd2u := Kd2u)
    halpha0 halpha1 a x0 hA u du d2u hu hdu
    hprincipalBound hprincipalHolder Ka omega ha homega
    hd2unorm hd2uHolder hsmall

theorem nondivergence_schauder_estimate_of_small_oscillation
    {alpha KL BL Kc Kdu Ku Mdu Bc Mu M Kd2u : NNReal}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (a : n → n → BoundedContinuousFunction (Euc n) Real) (x0 : Euc n)
    (hA : Matrix.PosDef (fun i j ↦ a i j x0))
    (b : n → BoundedContinuousFunction (Euc n) Real)
    (c : BoundedContinuousFunction (Euc n) Real)
    (u : BoundedContinuousFunction (Euc n) F)
    (du : BoundedContinuousFunction (Euc n) (Euc n →L[Real] F))
    (d2u : BoundedContinuousFunction (Euc n)
      (Euc n →L[Real] Euc n →L[Real] F))
    (huDeriv : ∀ x, HasFDerivAt (u : Euc n → F) (du x) x)
    (hduDeriv : ∀ x,
      HasFDerivAt (du : Euc n → Euc n →L[Real] F) (d2u x) x)
    (hLBound : ‖nondivergenceOperator a b c u du d2u‖ ≤ BL)
    (hLHolder : HolderWith KL alpha
      (nondivergenceOperator a b c u du d2u))
    (Kb Bb : n → NNReal) (Ka omega : n → n → NNReal)
    (hb : ∀ i, HolderWith (Kb i) alpha (b i : Euc n → Real))
    (ha : ∀ i j, HolderWith (Ka i j) alpha (a i j : Euc n → Real))
    (hc : HolderWith Kc alpha (c : Euc n → Real))
    (hduHolder : HolderWith Kdu alpha
      (du : Euc n → Euc n →L[Real] F))
    (huHolder : HolderWith Ku alpha (u : Euc n → F))
    (hbNorm : ∀ i x, ‖b i x‖ ≤ Bb i)
    (hcNorm : ∀ x, ‖c x‖ ≤ Bc)
    (hduNorm : ∀ x, ‖du x‖ ≤ Mdu)
    (huNorm : ∀ x, ‖u x‖ ≤ Mu)
    (homega : ∀ i j x, ‖a i j x0 - a i j x‖ ≤ omega i j)
    (hd2unorm : ∀ x, ‖d2u x‖ ≤ M)
    (hd2uHolder : HolderWith Kd2u alpha
      (d2u : Euc n → Euc n →L[Real] Euc n →L[Real] F))
    (hsmall : spdLaplacianSchauderDefectConst
      (fun i j ↦ a i j x0) hA alpha
        (∑ i, ∑ j, (omega i j + Ka i j))
        (∑ i, ∑ j, omega i j) < 1) :
    eContDiffHolderGaugeOn 2 alpha Set.univ (u : Euc n → F) ≤
      ((spdLaplacianSchauderConst (fun i j ↦ a i j x0) hA alpha
        (KL + lowerOrderHolderConst
          Kb Bb Kc Kdu Ku Mdu Bc Mu)
        (BL + lowerOrderSupConst Bb Bc Mdu Mu) u) /
        (1 - spdLaplacianSchauderDefectConst
          (fun i j ↦ a i j x0) hA alpha
            (∑ i, ∑ j, (omega i j + Ka i j))
            (∑ i, ∑ j, omega i j)) : NNReal) := by
  exact variable_coefficient_schauder_estimate_of_lower_order_source
    (Klo := lowerOrderHolderConst Kb Bb Kc Kdu Ku Mdu Bc Mu)
    (Blo := lowerOrderSupConst Bb Bc Mdu Mu)
    halpha0 halpha1 a x0 hA b c u du d2u huDeriv hduDeriv
    hLBound hLHolder
    (norm_lowerOrderTerm_le b c u du Bb Bc Mdu Mu
      hbNorm hcNorm hduNorm huNorm)
    (lowerOrderTerm_holderWith b c u du Kb Bb Mdu Bc Mu
      hb hc hduHolder huHolder hbNorm hcNorm hduNorm huNorm)
    Ka omega ha homega hd2unorm hd2uHolder hsmall

end DifferentialGeometry.Analysis.Schauder

end
