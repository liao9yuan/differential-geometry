import DifferentialGeometry.Analysis.Parabolic.Euclidean.Cutoff
import DifferentialGeometry.Analysis.Schauder.VariableCoefficient

noncomputable section

open Matrix Real Set
open scoped NNReal RealInnerProductSpace

namespace DifferentialGeometry.Analysis.Parabolic.Euclidean

open DifferentialGeometry.Analysis.Schauder

private abbrev Euc (n : Type*) := EuclideanSpace Real n

variable {n F : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
  [NormedAddCommGroup F] [NormedSpace Real F]

def parabolicMatrixCutoffCommutatorSupConst
    (A : n → n → NNReal) (Mdchi Mdu Md2chi Mu : NNReal) : NNReal :=
  (∑ i, ∑ j, 2 * (A i j * Mdchi * Mdu)) +
    ∑ i, ∑ j, A i j * Md2chi * Mu

def parabolicMatrixCutoffCommutatorHolderConst
    (A Ka : n → n → NNReal)
    (Kdchi Kdu Kd2chi Ku Mdchi Mdu Md2chi Mu : NNReal) : NNReal :=
  ∑ i, ∑ j,
    (2 * ((A i j * Mdchi) * Kdu +
      Mdu * (A i j * Kdchi + Mdchi * Ka i j)) +
    (A i j * Md2chi) * Ku +
      Mu * (A i j * Kd2chi + Md2chi * Ka i j))

omit [DecidableEq n] [Nonempty n] in
theorem norm_parabolicMatrixCutoffCommutator_le
    {Q : Set (ParabolicPoint (Euc n))}
    (a : n → n → ParabolicPoint (Euc n) → Real)
    (dchi : ParabolicPoint (Euc n) → Euc n →L[Real] Real)
    (d2chi : ParabolicPoint (Euc n) →
      Euc n →L[Real] Euc n →L[Real] Real)
    (u : Real → Euc n → F)
    (du : ParabolicPoint (Euc n) → Euc n →L[Real] F)
    (A : n → n → NNReal) (Mdchi Mdu Md2chi Mu : NNReal)
    (haNorm : ∀ i j p, p ∈ Q → ‖a i j p‖ ≤ A i j)
    (hdchiNorm : ∀ p, p ∈ Q → ‖dchi p‖ ≤ Mdchi)
    (hduNorm : ∀ p, p ∈ Q → ‖du p‖ ≤ Mdu)
    (hd2chiNorm : ∀ p, p ∈ Q → ‖d2chi p‖ ≤ Md2chi)
    (huNorm : ∀ p, p ∈ Q → ‖u p.time p.space‖ ≤ Mu)
    (p : ParabolicPoint (Euc n)) (hp : p ∈ Q) :
    ‖parabolicMatrixCutoffCommutator a dchi d2chi u du p‖ ≤
      parabolicMatrixCutoffCommutatorSupConst A Mdchi Mdu Md2chi Mu := by
  unfold parabolicMatrixCutoffCommutator
  refine (norm_sum_le _ _).trans ?_
  rw [parabolicMatrixCutoffCommutatorSupConst, NNReal.coe_add]
  push_cast
  calc
    ∑ i, ‖∑ j,
        ((a i j p * dchi p (EuclideanSpace.basisFun n Real i)) •
            du p (EuclideanSpace.basisFun n Real j) +
          (a i j p * dchi p (EuclideanSpace.basisFun n Real j)) •
            du p (EuclideanSpace.basisFun n Real i) +
          (a i j p * d2chi p (EuclideanSpace.basisFun n Real i)
            (EuclideanSpace.basisFun n Real j)) • u p.time p.space)‖ ≤
        ∑ i, ∑ j,
          (2 * ((A i j : Real) * Mdchi * Mdu) +
            (A i j : Real) * Md2chi * Mu) := by
      apply Finset.sum_le_sum
      intro i _hi
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _hj ↦ ?_)
      refine (norm_add_le _ _).trans ?_
      refine add_le_add ((norm_add_le _ _).trans ?_) ?_
      · have hai : |a i j p| ≤ A i j := by
          simpa only [Real.norm_eq_abs] using haNorm i j p hp
        have hdchii :
            |dchi p (EuclideanSpace.basisFun n Real i)| ≤ Mdchi := by
          rw [← Real.norm_eq_abs]
          exact (dchi p).le_opNorm _ |>.trans (by
            rw [(EuclideanSpace.basisFun n Real).orthonormal.norm_eq_one i]
            simpa using hdchiNorm p hp)
        have hdchij :
            |dchi p (EuclideanSpace.basisFun n Real j)| ≤ Mdchi := by
          rw [← Real.norm_eq_abs]
          exact (dchi p).le_opNorm _ |>.trans (by
            rw [(EuclideanSpace.basisFun n Real).orthonormal.norm_eq_one j]
            simpa using hdchiNorm p hp)
        have hdui :
            ‖du p (EuclideanSpace.basisFun n Real i)‖ ≤ Mdu :=
          (du p).le_opNorm _ |>.trans (by
            rw [(EuclideanSpace.basisFun n Real).orthonormal.norm_eq_one i]
            simpa using hduNorm p hp)
        have hduj :
            ‖du p (EuclideanSpace.basisFun n Real j)‖ ≤ Mdu :=
          (du p).le_opNorm _ |>.trans (by
            rw [(EuclideanSpace.basisFun n Real).orthonormal.norm_eq_one j]
            simpa using hduNorm p hp)
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
          abs_mul, abs_mul]
        have hi : |a i j p| *
            |dchi p (EuclideanSpace.basisFun n Real i)| *
              ‖du p (EuclideanSpace.basisFun n Real j)‖ ≤
            (A i j : Real) * Mdchi * Mdu := by
          gcongr
        have hj : |a i j p| *
            |dchi p (EuclideanSpace.basisFun n Real j)| *
              ‖du p (EuclideanSpace.basisFun n Real i)‖ ≤
            (A i j : Real) * Mdchi * Mdu := by
          gcongr
        linarith
      · rw [norm_smul, Real.norm_eq_abs, abs_mul]
        have hai : |a i j p| ≤ A i j := by
          simpa only [Real.norm_eq_abs] using haNorm i j p hp
        have hd2chiij : |d2chi p
            (EuclideanSpace.basisFun n Real i)
            (EuclideanSpace.basisFun n Real j)| ≤ Md2chi := by
          rw [← Real.norm_eq_abs]
          calc
            ‖d2chi p (EuclideanSpace.basisFun n Real i)
                (EuclideanSpace.basisFun n Real j)‖ ≤
                ‖d2chi p (EuclideanSpace.basisFun n Real i)‖ := by
              simpa only
                [(EuclideanSpace.basisFun n Real).orthonormal.norm_eq_one j,
                  mul_one] using
                (d2chi p (EuclideanSpace.basisFun n Real i)).le_opNorm
                  (EuclideanSpace.basisFun n Real j)
            _ ≤ ‖d2chi p‖ := by
              simpa only
                [(EuclideanSpace.basisFun n Real).orthonormal.norm_eq_one i,
                  mul_one] using
                (d2chi p).le_opNorm (EuclideanSpace.basisFun n Real i)
            _ ≤ Md2chi := hd2chiNorm p hp
        exact mul_le_mul
          (mul_le_mul hai hd2chiij (abs_nonneg _) (A i j).coe_nonneg)
          (huNorm p hp) (norm_nonneg _) (by positivity)
    _ = (∑ i, ∑ j, 2 * ((A i j : Real) * Mdchi * Mdu)) +
          ∑ i, ∑ j, (A i j : Real) * Md2chi * Mu := by
      simp only [Finset.sum_add_distrib]

omit [DecidableEq n] [Nonempty n] in
theorem eSupNormOn_parabolicMatrixCutoffCommutator_le
    {Q : Set (ParabolicPoint (Euc n))}
    (a : n → n → ParabolicPoint (Euc n) → Real)
    (dchi : ParabolicPoint (Euc n) → Euc n →L[Real] Real)
    (d2chi : ParabolicPoint (Euc n) →
      Euc n →L[Real] Euc n →L[Real] Real)
    (u : Real → Euc n → F)
    (du : ParabolicPoint (Euc n) → Euc n →L[Real] F)
    (A : n → n → NNReal) (Mdchi Mdu Md2chi Mu : NNReal)
    (haNorm : ∀ i j p, p ∈ Q → ‖a i j p‖ ≤ A i j)
    (hdchiNorm : ∀ p, p ∈ Q → ‖dchi p‖ ≤ Mdchi)
    (hduNorm : ∀ p, p ∈ Q → ‖du p‖ ≤ Mdu)
    (hd2chiNorm : ∀ p, p ∈ Q → ‖d2chi p‖ ≤ Md2chi)
    (huNorm : ∀ p, p ∈ Q → ‖u p.time p.space‖ ≤ Mu) :
    eSupNormOn Q (parabolicMatrixCutoffCommutator a dchi d2chi u du) ≤
      parabolicMatrixCutoffCommutatorSupConst A Mdchi Mdu Md2chi Mu := by
  rw [eSupNormOn_le]
  intro p hp
  rw [ENNReal.ofReal_le_coe]
  exact norm_parabolicMatrixCutoffCommutator_le a dchi d2chi u du
    A Mdchi Mdu Md2chi Mu haNorm hdchiNorm hduNorm hd2chiNorm huNorm p hp

omit [DecidableEq n] [Nonempty n] in
theorem parabolicMatrixCutoffCommutator_holderWith_restrict
    {Q : Set (ParabolicPoint (Euc n))}
    {alpha Kdchi Kdu Kd2chi Ku : NNReal}
    (a : n → n → ParabolicPoint (Euc n) → Real)
    (dchi : ParabolicPoint (Euc n) → Euc n →L[Real] Real)
    (d2chi : ParabolicPoint (Euc n) →
      Euc n →L[Real] Euc n →L[Real] Real)
    (u : Real → Euc n → F)
    (du : ParabolicPoint (Euc n) → Euc n →L[Real] F)
    (A Ka : n → n → NNReal) (Mdchi Mdu Md2chi Mu : NNReal)
    (ha : ∀ i j, HolderWith (Ka i j) alpha (Q.restrict (a i j)))
    (hdchi : HolderWith Kdchi alpha (Q.restrict dchi))
    (hdu : HolderWith Kdu alpha (Q.restrict du))
    (hd2chi : HolderWith Kd2chi alpha (Q.restrict d2chi))
    (hu : HolderWith Ku alpha
      (Q.restrict (fun p ↦ u p.time p.space)))
    (haNorm : ∀ i j p, p ∈ Q → ‖a i j p‖ ≤ A i j)
    (hdchiNorm : ∀ p, p ∈ Q → ‖dchi p‖ ≤ Mdchi)
    (hduNorm : ∀ p, p ∈ Q → ‖du p‖ ≤ Mdu)
    (hd2chiNorm : ∀ p, p ∈ Q → ‖d2chi p‖ ≤ Md2chi)
    (huNorm : ∀ p, p ∈ Q → ‖u p.time p.space‖ ≤ Mu) :
    HolderWith (parabolicMatrixCutoffCommutatorHolderConst A Ka
      Kdchi Kdu Kd2chi Ku Mdchi Mdu Md2chi Mu) alpha
      (Q.restrict (parabolicMatrixCutoffCommutator a dchi d2chi u du)) := by
  classical
  let C : n → n → NNReal := fun i j ↦
    (A i j * Mdchi) * Kdu +
      Mdu * (A i j * Kdchi + Mdchi * Ka i j)
  let D : n → n → NNReal := fun i j ↦
    (A i j * Md2chi) * Ku +
      Mu * (A i j * Kd2chi + Md2chi * Ka i j)
  have hcomponent : ∀ i j, HolderWith (C i j + C i j + D i j) alpha
      (fun p : Q ↦
        (a i j p.1 * dchi p.1 (EuclideanSpace.basisFun n Real i)) •
            du p.1 (EuclideanSpace.basisFun n Real j) +
          (a i j p.1 * dchi p.1 (EuclideanSpace.basisFun n Real j)) •
            du p.1 (EuclideanSpace.basisFun n Real i) +
          (a i j p.1 * d2chi p.1 (EuclideanSpace.basisFun n Real i)
            (EuclideanSpace.basisFun n Real j)) •
              u p.1.time p.1.space) := by
    intro i j
    have hdchii : HolderWith Kdchi alpha
        (fun p : Q ↦ dchi p.1 (EuclideanSpace.basisFun n Real i)) :=
      holderWith_comp_continuousLinearMap_of_norm_le_one
        (ContinuousLinearMap.apply Real Real
          (EuclideanSpace.basisFun n Real i))
        (norm_apply_euclideanBasis_le_one i) hdchi
    have hdchij : HolderWith Kdchi alpha
        (fun p : Q ↦ dchi p.1 (EuclideanSpace.basisFun n Real j)) :=
      holderWith_comp_continuousLinearMap_of_norm_le_one
        (ContinuousLinearMap.apply Real Real
          (EuclideanSpace.basisFun n Real j))
        (norm_apply_euclideanBasis_le_one j) hdchi
    have hdui : HolderWith Kdu alpha
        (fun p : Q ↦ du p.1 (EuclideanSpace.basisFun n Real i)) :=
      holderWith_comp_continuousLinearMap_of_norm_le_one
        (ContinuousLinearMap.apply Real F
          (EuclideanSpace.basisFun n Real i))
        (norm_apply_euclideanBasis_le_one i) hdu
    have hduj : HolderWith Kdu alpha
        (fun p : Q ↦ du p.1 (EuclideanSpace.basisFun n Real j)) :=
      holderWith_comp_continuousLinearMap_of_norm_le_one
        (ContinuousLinearMap.apply Real F
          (EuclideanSpace.basisFun n Real j))
        (norm_apply_euclideanBasis_le_one j) hdu
    have hd2chii : HolderWith Kd2chi alpha
        (fun p : Q ↦ d2chi p.1 (EuclideanSpace.basisFun n Real i)) :=
      holderWith_comp_continuousLinearMap_of_norm_le_one
        (ContinuousLinearMap.apply Real (Euc n →L[Real] Real)
          (EuclideanSpace.basisFun n Real i))
        (norm_apply_euclideanBasis_le_one i) hd2chi
    have hd2chiij : HolderWith Kd2chi alpha
        (fun p : Q ↦ d2chi p.1 (EuclideanSpace.basisFun n Real i)
          (EuclideanSpace.basisFun n Real j)) :=
      holderWith_comp_continuousLinearMap_of_norm_le_one
        (ContinuousLinearMap.apply Real Real
          (EuclideanSpace.basisFun n Real j))
        (norm_apply_euclideanBasis_le_one j) hd2chii
    have hadchii : HolderWith
        (A i j * Kdchi + Mdchi * Ka i j) alpha
        (fun p : Q ↦ a i j p.1 *
          dchi p.1 (EuclideanSpace.basisFun n Real i)) := by
      simpa only [smul_eq_mul, Set.restrict_apply] using
        holderWith_smul_of_norm_le (ha i j) hdchii
          (fun p ↦ haNorm i j p.1 p.2)
          (fun p ↦ (by
            calc
              ‖dchi p.1 (EuclideanSpace.basisFun n Real i)‖ ≤
                  ‖dchi p.1‖ := by
                simpa only
                  [(EuclideanSpace.basisFun n Real).orthonormal.norm_eq_one i,
                    mul_one] using
                  (dchi p.1).le_opNorm (EuclideanSpace.basisFun n Real i)
              _ ≤ Mdchi := hdchiNorm p.1 p.2))
    have hadchij : HolderWith
        (A i j * Kdchi + Mdchi * Ka i j) alpha
        (fun p : Q ↦ a i j p.1 *
          dchi p.1 (EuclideanSpace.basisFun n Real j)) := by
      simpa only [smul_eq_mul, Set.restrict_apply] using
        holderWith_smul_of_norm_le (ha i j) hdchij
          (fun p ↦ haNorm i j p.1 p.2)
          (fun p ↦ (by
            calc
              ‖dchi p.1 (EuclideanSpace.basisFun n Real j)‖ ≤
                  ‖dchi p.1‖ := by
                simpa only
                  [(EuclideanSpace.basisFun n Real).orthonormal.norm_eq_one j,
                    mul_one] using
                  (dchi p.1).le_opNorm (EuclideanSpace.basisFun n Real j)
              _ ≤ Mdchi := hdchiNorm p.1 p.2))
    have had2chi : HolderWith
        (A i j * Kd2chi + Md2chi * Ka i j) alpha
        (fun p : Q ↦ a i j p.1 *
          d2chi p.1 (EuclideanSpace.basisFun n Real i)
            (EuclideanSpace.basisFun n Real j)) := by
      simpa only [smul_eq_mul, Set.restrict_apply] using
        holderWith_smul_of_norm_le (ha i j) hd2chiij
          (fun p ↦ haNorm i j p.1 p.2)
          (fun p ↦ (by
            calc
              ‖d2chi p.1 (EuclideanSpace.basisFun n Real i)
                  (EuclideanSpace.basisFun n Real j)‖ ≤
                  ‖d2chi p.1 (EuclideanSpace.basisFun n Real i)‖ := by
                simpa only
                  [(EuclideanSpace.basisFun n Real).orthonormal.norm_eq_one j,
                    mul_one] using
                  (d2chi p.1 (EuclideanSpace.basisFun n Real i)).le_opNorm
                    (EuclideanSpace.basisFun n Real j)
              _ ≤ ‖d2chi p.1‖ := by
                simpa only
                  [(EuclideanSpace.basisFun n Real).orthonormal.norm_eq_one i,
                    mul_one] using
                  (d2chi p.1).le_opNorm (EuclideanSpace.basisFun n Real i)
              _ ≤ Md2chi := hd2chiNorm p.1 p.2))
    have hadchiNorm : ∀ k (p : Q),
        ‖a i j p.1 * dchi p.1 (EuclideanSpace.basisFun n Real k)‖ ≤
          A i j * Mdchi := by
      intro k p
      rw [Real.norm_eq_abs, abs_mul]
      exact_mod_cast mul_le_mul
        (by simpa only [Real.norm_eq_abs] using haNorm i j p.1 p.2)
        (by rw [← Real.norm_eq_abs]
            calc
              ‖dchi p.1 (EuclideanSpace.basisFun n Real k)‖ ≤
                  ‖dchi p.1‖ := by
                simpa only
                  [(EuclideanSpace.basisFun n Real).orthonormal.norm_eq_one k,
                    mul_one] using
                  (dchi p.1).le_opNorm (EuclideanSpace.basisFun n Real k)
              _ ≤ Mdchi := hdchiNorm p.1 p.2)
        (abs_nonneg _) (A i j).coe_nonneg
    have had2chiNorm : ∀ p : Q,
        ‖a i j p.1 * d2chi p.1 (EuclideanSpace.basisFun n Real i)
          (EuclideanSpace.basisFun n Real j)‖ ≤ A i j * Md2chi := by
      intro p
      rw [Real.norm_eq_abs, abs_mul]
      exact_mod_cast mul_le_mul
        (by simpa only [Real.norm_eq_abs] using haNorm i j p.1 p.2)
        (by rw [← Real.norm_eq_abs]
            calc
              ‖d2chi p.1 (EuclideanSpace.basisFun n Real i)
                  (EuclideanSpace.basisFun n Real j)‖ ≤
                  ‖d2chi p.1 (EuclideanSpace.basisFun n Real i)‖ := by
                simpa only
                  [(EuclideanSpace.basisFun n Real).orthonormal.norm_eq_one j,
                    mul_one] using
                  (d2chi p.1 (EuclideanSpace.basisFun n Real i)).le_opNorm
                    (EuclideanSpace.basisFun n Real j)
              _ ≤ ‖d2chi p.1‖ := by
                simpa only
                  [(EuclideanSpace.basisFun n Real).orthonormal.norm_eq_one i,
                    mul_one] using
                  (d2chi p.1).le_opNorm (EuclideanSpace.basisFun n Real i)
              _ ≤ Md2chi := hd2chiNorm p.1 p.2)
        (abs_nonneg _) (A i j).coe_nonneg
    have hcrossi : HolderWith (C i j) alpha
        (fun p : Q ↦
          (a i j p.1 * dchi p.1 (EuclideanSpace.basisFun n Real i)) •
            du p.1 (EuclideanSpace.basisFun n Real j)) := by
      exact holderWith_smul_of_norm_le hadchii hduj (hadchiNorm i)
        (fun p ↦ (du p.1).le_opNorm _ |>.trans (by
          simpa only
            [(EuclideanSpace.basisFun n Real).orthonormal.norm_eq_one j,
              mul_one] using hduNorm p.1 p.2))
    have hcrossj : HolderWith (C i j) alpha
        (fun p : Q ↦
          (a i j p.1 * dchi p.1 (EuclideanSpace.basisFun n Real j)) •
            du p.1 (EuclideanSpace.basisFun n Real i)) := by
      exact holderWith_smul_of_norm_le hadchij hdui (hadchiNorm j)
        (fun p ↦ (du p.1).le_opNorm _ |>.trans (by
          simpa only
            [(EuclideanSpace.basisFun n Real).orthonormal.norm_eq_one i,
              mul_one] using hduNorm p.1 p.2))
    have hhessian : HolderWith (D i j) alpha
        (fun p : Q ↦
          (a i j p.1 * d2chi p.1 (EuclideanSpace.basisFun n Real i)
            (EuclideanSpace.basisFun n Real j)) •
              u p.1.time p.1.space) := by
      exact holderWith_smul_of_norm_le had2chi hu had2chiNorm
        (fun p ↦ huNorm p.1 p.2)
    exact hcrossi.add hcrossj |>.add hhessian
  have hinner : ∀ i, HolderWith (∑ j, (C i j + C i j + D i j)) alpha
      (fun p : Q ↦ ∑ j,
        ((a i j p.1 * dchi p.1 (EuclideanSpace.basisFun n Real i)) •
            du p.1 (EuclideanSpace.basisFun n Real j) +
          (a i j p.1 * dchi p.1 (EuclideanSpace.basisFun n Real j)) •
            du p.1 (EuclideanSpace.basisFun n Real i) +
          (a i j p.1 * d2chi p.1 (EuclideanSpace.basisFun n Real i)
            (EuclideanSpace.basisFun n Real j)) •
              u p.1.time p.1.space)) := by
    intro i
    exact holderWith_finset_sum Finset.univ (fun j _hj ↦ hcomponent i j)
  have hall := holderWith_finset_sum Finset.univ
    (K := fun i ↦ ∑ j, (C i j + C i j + D i j))
    (f := fun i (p : Q) ↦ ∑ j,
      ((a i j p.1 * dchi p.1 (EuclideanSpace.basisFun n Real i)) •
          du p.1 (EuclideanSpace.basisFun n Real j) +
        (a i j p.1 * dchi p.1 (EuclideanSpace.basisFun n Real j)) •
          du p.1 (EuclideanSpace.basisFun n Real i) +
        (a i j p.1 * d2chi p.1 (EuclideanSpace.basisFun n Real i)
          (EuclideanSpace.basisFun n Real j)) •
            u p.1.time p.1.space))
    (fun i _hi ↦ hinner i)
  convert hall using 1
  · simp only [parabolicMatrixCutoffCommutatorHolderConst, C, D, two_mul,
      add_assoc]

end DifferentialGeometry.Analysis.Parabolic.Euclidean

end
