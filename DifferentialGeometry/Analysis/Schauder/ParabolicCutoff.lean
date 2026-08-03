import DifferentialGeometry.Analysis.Schauder.BallCutoffHessian
import DifferentialGeometry.Analysis.Schauder.CutoffProduct

noncomputable section

open Real Set
open scoped BoundedContinuousFunction NNReal RealInnerProductSpace

namespace DifferentialGeometry.Analysis.Schauder

def timeCutoffBcf
    (center : Real) {r R : Real} (hr : 0 ≤ r) (hrR : r < R) :
    BoundedContinuousFunction Real Real :=
  ballCutoffBcf center hr hrR

def timeCutoffDerivBcf
    (center : Real) {r R : Real} (hr : 0 ≤ r) (hrR : r < R) :
    BoundedContinuousFunction Real Real :=
  (ContinuousLinearMap.apply Real Real (1 : Real))
    |>.compLeftContinuousBounded Real
      (ballCutoffFDerivBcf center hr hrR)

@[simp]
theorem timeCutoffBcf_apply
    (center : Real) {r R : Real} (hr : 0 ≤ r) (hrR : r < R) (t : Real) :
    timeCutoffBcf center hr hrR t = ballCutoff center r R t := rfl

@[simp]
theorem timeCutoffDerivBcf_apply
    (center : Real) {r R : Real} (hr : 0 ≤ r) (hrR : r < R) (t : Real) :
    timeCutoffDerivBcf center hr hrR t =
      ballCutoffFDeriv center r R t 1 := rfl

theorem timeCutoffBcf_hasDerivAt
    (center : Real) {r R : Real} (hr : 0 ≤ r) (hrR : r < R) (t : Real) :
    HasDerivAt (timeCutoffBcf center hr hrR : Real → Real)
      (timeCutoffDerivBcf center hr hrR t) t := by
  simpa only [timeCutoffBcf_apply, timeCutoffDerivBcf_apply] using
    (hasFDerivAt_ballCutoff center r R t).hasDerivAt

def timeCutoffDerivHolderConst (r R : Real) : NNReal :=
  ballCutoffFDerivHolderConst r R

theorem timeCutoffBcf_holderWith
    (center : Real) {r R : Real} (hr : 0 ≤ r) (hrR : r < R)
    {beta : NNReal} (hbeta1 : beta ≤ 1) :
    HolderWith (ballCutoffHolderConst r R) beta
      (timeCutoffBcf center hr hrR : Real → Real) := by
  simpa only [timeCutoffBcf_apply] using
    ballCutoff_holderWith (V := Real) hr hrR (zero_le beta) hbeta1

theorem timeCutoffDerivBcf_holderWith
    (center : Real) {r R : Real} (hr : 0 ≤ r) (hrR : r < R)
    {beta : NNReal} (hbeta1 : beta ≤ 1) :
    HolderWith (timeCutoffDerivHolderConst r R) beta
      (timeCutoffDerivBcf center hr hrR : Real → Real) := by
  let L := ContinuousLinearMap.apply Real Real (1 : Real)
  have hbase := ballCutoffFDeriv_holderWith (V := Real) (center := center)
    hr hrR (zero_le beta) hbeta1
  have hL : LipschitzWith 1 L := by
    apply LipschitzWith.of_dist_le_mul
    intro A B
    rw [dist_eq_norm, ← map_sub]
    calc
      ‖L (A - B)‖ ≤ ‖A - B‖ * ‖(1 : Real)‖ := (A - B).le_opNorm 1
      _ = (1 : Real) * dist A B := by simp only [norm_one, mul_one, one_mul,
        dist_eq_norm]
  have hcomp := hL.holderWith.comp hbase
  change HolderWith (timeCutoffDerivHolderConst r R) beta
    (fun t ↦ ballCutoffFDeriv center r R t 1)
  simpa only [timeCutoffDerivHolderConst, L, Function.comp_apply,
    NNReal.coe_one, NNReal.rpow_one, mul_one, one_mul] using hcomp

theorem timeCutoffBcf_parabolic_holderWith
    {V : Type*} [PseudoMetricSpace V]
    (center : Real) {r R : Real} (hr : 0 ≤ r) (hrR : r < R)
    {alpha : NNReal} (halpha1 : alpha ≤ 1) :
    HolderWith (ballCutoffHolderConst r R) alpha
      (fun p : ParabolicPoint V ↦ timeCutoffBcf center hr hrR p.time) := by
  apply holderWith_parabolic_const_space
  apply timeCutoffBcf_holderWith center hr hrR
  exact (div_le_iff₀ (by norm_num : (0 : NNReal) < 2)).2
    (by simpa using halpha1.trans (show (1 : NNReal) ≤ 2 by norm_num))

theorem timeCutoffDerivBcf_parabolic_holderWith
    {V : Type*} [PseudoMetricSpace V]
    (center : Real) {r R : Real} (hr : 0 ≤ r) (hrR : r < R)
    {alpha : NNReal} (halpha1 : alpha ≤ 1) :
    HolderWith (timeCutoffDerivHolderConst r R) alpha
      (fun p : ParabolicPoint V ↦
        timeCutoffDerivBcf center hr hrR p.time) := by
  apply holderWith_parabolic_const_space
  apply timeCutoffDerivBcf_holderWith center hr hrR
  exact (div_le_iff₀ (by norm_num : (0 : NNReal) < 2)).2
    (by simpa using halpha1.trans (show (1 : NNReal) ≤ 2 by norm_num))

section Separable

variable {V F : Type*} [TopologicalSpace V]
  [NormedAddCommGroup F] [NormedSpace Real F]

def separableBcfPath
    (eta : BoundedContinuousFunction Real Real)
    (v : BoundedContinuousFunction V F) :
    Real → BoundedContinuousFunction V F :=
  fun t ↦ eta t • v

@[simp]
theorem separableBcfPath_apply
    (eta : BoundedContinuousFunction Real Real)
    (v : BoundedContinuousFunction V F) (t : Real) (x : V) :
    separableBcfPath eta v t x = eta t • v x := rfl

theorem separableBcfPath_hasDerivAt
    (eta deta : BoundedContinuousFunction Real Real)
    (v : BoundedContinuousFunction V F) (t : Real)
    (heta : HasDerivAt (eta : Real → Real) (deta t) t) :
    HasDerivAt (separableBcfPath eta v) (deta t • v) t := by
  simpa only [separableBcfPath] using heta.smul_const v

end Separable

section Spatial

variable {V F : Type*}
  [NormedAddCommGroup V] [NormedSpace Real V]
  [NormedAddCommGroup F] [NormedSpace Real F]

theorem separableBcfPath_hasFDerivAt
    (eta : BoundedContinuousFunction Real Real)
    (v : BoundedContinuousFunction V F)
    (dv : BoundedContinuousFunction V (V →L[Real] F))
    (hv : ∀ x, HasFDerivAt (v : V → F) (dv x) x)
    (t : Real) (x : V) :
    HasFDerivAt (separableBcfPath eta v t : V → F)
      (eta t • dv x) x := by
  simpa only [separableBcfPath_apply] using (hv x).const_smul (eta t)

theorem separableBcfPath_fderiv_hasFDerivAt
    (eta : BoundedContinuousFunction Real Real)
    (dv : BoundedContinuousFunction V (V →L[Real] F))
    (d2v : BoundedContinuousFunction V (V →L[Real] V →L[Real] F))
    (hdv : ∀ x, HasFDerivAt (dv : V → V →L[Real] F) (d2v x) x)
    (t : Real) (x : V) :
    HasFDerivAt (separableBcfPath eta dv t : V → V →L[Real] F)
      (eta t • d2v x) x := by
  simpa only [separableBcfPath_apply] using (hdv x).const_smul (eta t)

omit [NormedSpace Real V] in
theorem separableBcfPath_holderWith_restrict
    {alpha Keta Kv Meta Mv : NNReal} {J : Set Real}
    (eta : BoundedContinuousFunction Real Real)
    (v : BoundedContinuousFunction V F)
    (heta : HolderWith Keta (alpha / 2) (eta : Real → Real))
    (hv : HolderWith Kv alpha (v : V → F))
    (hetaNorm : ∀ t, ‖eta t‖ ≤ Meta)
    (hvNorm : ∀ x, ‖v x‖ ≤ Mv) :
    HolderWith (Meta * Kv + Mv * Keta) alpha
      ((parabolicCylinder J Set.univ).restrict
        (fun p ↦ separableBcfPath eta v p.time p.space)) := by
  let Q := parabolicCylinder J (Set.univ : Set V)
  have hetaFull : HolderWith Keta alpha
      (fun p : ParabolicPoint V ↦ eta p.time) :=
    holderWith_parabolic_const_space heta
  have hetaQ : HolderWith Keta alpha
      (Q.restrict (fun p : ParabolicPoint V ↦ eta p.time)) :=
    (hetaFull.holderOnWith Q).holderWith
  have hvQ : HolderWith Kv alpha
      (Q.restrict (fun p : ParabolicPoint V ↦ v p.space)) :=
    holderWith_parabolic_const_time (v : V → F) hv J
  have hproduct := holderWith_smul_of_norm_le hetaQ hvQ
    (fun p ↦ hetaNorm p.1.time) (fun p ↦ hvNorm p.1.space)
  simpa only [Q, Set.restrict_apply, separableBcfPath_apply] using hproduct

end Spatial

end DifferentialGeometry.Analysis.Schauder

end
