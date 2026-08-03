import DifferentialGeometry.Analysis.Parabolic.Euclidean.FrozenDuhamel
import DifferentialGeometry.Analysis.Parabolic.Euclidean.FrozenDuhamelSPD
import DifferentialGeometry.Analysis.Parabolic.Euclidean.HeatPotentialEstimate
import DifferentialGeometry.Analysis.Parabolic.Euclidean.HeatSemigroupSchauder
import DifferentialGeometry.Analysis.Schauder.Scaling

noncomputable section

open Matrix MeasureTheory Real Set
open scoped NNReal RealInnerProductSpace

namespace DifferentialGeometry.Analysis.Schauder

open DifferentialGeometry.Analysis.Parabolic.Euclidean

variable {V F : Type*}
  [NormedAddCommGroup V] [InnerProductSpace Real V] [FiniteDimensional Real V]
  [MeasurableSpace V] [BorelSpace V] [Nontrivial V]
  [NormedAddCommGroup F] [NormedSpace Real F] [CompleteSpace F]

private abbrev Euc (n : Type*) := EuclideanSpace Real n

def laplacianSchauderConst
    (alpha K B : NNReal) (u : BoundedContinuousFunction V F) : NNReal :=
  heatSupSchauderConst (V := V) 1 u +
    heatDuhConstSchauderConst (V := V) alpha K B 1

theorem laplacian_schauder_estimate
    {alpha K B : NNReal}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (u : BoundedContinuousFunction V F)
    (du : BoundedContinuousFunction V (V →L[Real] F))
    (d2u : BoundedContinuousFunction V (V →L[Real] V →L[Real] F))
    (hu : ∀ x : V, HasFDerivAt (u : V → F) (du x) x)
    (hdu : ∀ x : V, HasFDerivAt (du : V → V →L[Real] F) (d2u x) x)
    (hbound : ‖coreLap d2u‖ ≤ B)
    (hholder : HolderWith K alpha (coreLap d2u)) :
    eContDiffHolderGaugeOn 2 alpha Set.univ (u : V → F) ≤
      laplacianSchauderConst (V := V) alpha K B u := by
  have hulip : LipschitzWith ‖du‖₊ (u : V → F) := by
    apply lipschitzWith_of_nnnorm_fderiv_le (𝕜 := Real)
    · exact fun x ↦ (hu x).differentiableAt
    · intro x
      rw [(hu x).fderiv]
      exact_mod_cast du.norm_coe_le_norm x
  have huzero : HolderWith (2 * ‖u‖₊) 0 (u : V → F) := by
    apply holderWith_zero_of_norm_le
    exact u.norm_coe_le_norm
  have huhalf : HolderWith (max (2 * ‖u‖₊) ‖du‖₊) (1 / 2 : NNReal)
      (u : V → F) :=
    huzero.of_le_of_le hulip.holderWith (by positivity) (by norm_num)
  have hrep : (u : V → F) =
      (fun x ↦ heatSup 1 u x) - heatDuh 1 (fun _ ↦ coreLap d2u) := by
    funext x
    rw [Pi.sub_apply, heatDuh_const_eq_integral_heatSup]
    have hprim := heatSup_primitive (t := 1) one_pos u du d2u hu hdu huhalf x
    rw [hprim]
    abel
  have hduC1 : ContDiff Real 1 (du : V → V →L[Real] F) :=
    contDiff_one_iff_hasFDerivAt.mpr ⟨d2u, d2u.continuous, hdu⟩
  have huC2 : ContDiff Real 2 (u : V → F) :=
    (contDiff_succ_iff_hasFDerivAt (n := 1)).mpr ⟨du, hduC1, hu⟩
  have hheatC2 : ContDiff Real 2 (fun x : V ↦ heatSup 1 u x) :=
    heatSup_contDiff_two one_pos u
  have hduhEq : heatDuh 1 (fun _ ↦ coreLap d2u) =
      (fun x ↦ heatSup 1 u x) - (u : V → F) := by
    rw [hrep]
    abel
  have hduhC2 : ContDiff Real 2 (heatDuh 1 (fun _ ↦ coreLap d2u)) := by
    rw [hduhEq]
    exact hheatC2.sub huC2
  rw [hrep]
  refine (eContDiffHolderGaugeOn_sub_le 2 alpha Set.univ _ _
    hheatC2 hduhC2).trans ?_
  have hheat := heatSup_schauder_estimate halpha1.le one_pos u
  have hduh := heatDuh_const_schauder_estimate
    halpha0 halpha1 (T := 1) (S := 2) one_pos (by norm_num)
    (coreLap d2u) hbound hholder
  exact (add_le_add hheat hduh).trans_eq (by
    simp only [laplacianSchauderConst, ENNReal.coe_add])

section PositiveDefinite

variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]

def spdMatrixLap (A : Matrix n n Real) (hA : A.PosDef)
    (d2u : BoundedContinuousFunction (Euc n)
      (Euc n →L[Real] Euc n →L[Real] F)) :
    BoundedContinuousFunction (Euc n) F :=
  linPullBcf (spdSqrtEquiv A hA).symm
    (coreLap (pullJet2 (spdSqrtEquiv A hA) d2u))

omit [Nonempty n] [CompleteSpace F] in
@[simp]
theorem spdMatrixLap_apply (A : Matrix n n Real) (hA : A.PosDef)
    (d2u : BoundedContinuousFunction (Euc n)
      (Euc n →L[Real] Euc n →L[Real] F)) (x : Euc n) :
    spdMatrixLap A hA d2u x = matrixLap A (d2u x) := by
  let L := spdSqrtEquiv A hA
  change coreLap (pullJet2 L d2u) (L.symm x) = matrixLap A (d2u x)
  calc
    coreLap (pullJet2 L d2u) (L.symm x) =
        lapEval (pullJet2 L d2u (L.symm x)) := rfl
    _ = ∑ i : n, (pullJet2 L d2u (L.symm x))
        (EuclideanSpace.basisFun n Real i)
        (EuclideanSpace.basisFun n Real i) :=
      lapEval_basis (EuclideanSpace.basisFun n Real) _
    _ = factorLap L (d2u x) := by
      unfold factorLap
      simp only [pullJet2_apply, ContinuousLinearEquiv.apply_symm_apply]
    _ = matrixLap A (d2u x) := spd_factorLap A hA (d2u x)

def spdLaplacianSchauderConst
    (A : Matrix n n Real) (hA : A.PosDef)
    (alpha K B : NNReal) (u : BoundedContinuousFunction (Euc n) F) : NNReal :=
  let L := spdSqrtEquiv A hA
  let K' := K * ‖(L : Euc n →L[Real] Euc n)‖₊ ^ (alpha : Real)
  contDiffHolderLinearEquivConst L alpha
    (laplacianSchauderConst alpha K' B (linPullBcf L u))

theorem spd_laplacian_schauder_estimate
    {alpha K B : NNReal}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (A : Matrix n n Real) (hA : A.PosDef)
    (u : BoundedContinuousFunction (Euc n) F)
    (du : BoundedContinuousFunction (Euc n) (Euc n →L[Real] F))
    (d2u : BoundedContinuousFunction (Euc n)
      (Euc n →L[Real] Euc n →L[Real] F))
    (hu : ∀ x : Euc n, HasFDerivAt (u : Euc n → F) (du x) x)
    (hdu : ∀ x : Euc n,
      HasFDerivAt (du : Euc n → Euc n →L[Real] F) (d2u x) x)
    (hbound : ‖spdMatrixLap A hA d2u‖ ≤ B)
    (hholder : HolderWith K alpha (spdMatrixLap A hA d2u)) :
    eContDiffHolderGaugeOn 2 alpha Set.univ (u : Euc n → F) ≤
      spdLaplacianSchauderConst A hA alpha K B u := by
  let L := spdSqrtEquiv A hA
  let up := linPullBcf L u
  let dup := pullJet1 L du
  let d2up := pullJet2 L d2u
  let fp := coreLap d2up
  let K' := K * ‖(L : Euc n →L[Real] Euc n)‖₊ ^ (alpha : Real)
  have hfp : fp = linPullBcf L (spdMatrixLap A hA d2u) := by
    apply BoundedContinuousFunction.ext
    intro x
    simp only [fp, d2up, linPullBcf_apply]
    change coreLap (pullJet2 L d2u) x =
      coreLap (pullJet2 L d2u) (L.symm (L x))
    rw [L.symm_apply_apply]
  have hbound' : ‖fp‖ ≤ B := by
    rw [hfp, norm_linPullBcf]
    exact hbound
  have hholder' : HolderWith K' alpha fp := by
    rw [hfp]
    have hraw := hholder.comp L.lipschitz.holderWith
    simpa only [K', NNReal.coe_one, NNReal.rpow_one, one_mul, mul_one,
      linPullBcf_apply, Function.comp_apply] using hraw
  have hup : ∀ x : Euc n,
      HasFDerivAt (up : Euc n → F) (dup x) x :=
    fun x ↦ linPull_fderiv L u du hu x
  have hdup : ∀ x : Euc n,
      HasFDerivAt (dup : Euc n → Euc n →L[Real] F) (d2up x) x :=
    fun x ↦ pullJet1_fderiv L du d2u hdu x
  have hpull := laplacian_schauder_estimate halpha0 halpha1
    up dup d2up hup hdup hbound' hholder'
  apply eContDiffHolderGaugeOn_linearEquiv_le L alpha
    (laplacianSchauderConst alpha K' B up) (u : Euc n → F)
  simpa only [up, linPullBcf_apply] using hpull

end PositiveDefinite

end DifferentialGeometry.Analysis.Schauder

end
