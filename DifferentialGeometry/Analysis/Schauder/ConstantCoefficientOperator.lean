import DifferentialGeometry.Analysis.Parabolic.Euclidean.FrozenDuhamel
import DifferentialGeometry.Analysis.Schauder.HolderOperator

noncomputable section

open scoped NNReal RealInnerProductSpace

namespace DifferentialGeometry.Analysis.Schauder

variable {V F : Type*}
  [NormedAddCommGroup V] [InnerProductSpace Real V]
  [FiniteDimensional Real V]
  [NormedAddCommGroup F] [NormedSpace Real F]

def laplacianEval : (V [×2]→L[Real] F) →L[Real] F :=
  DifferentialGeometry.Analysis.Parabolic.Euclidean.lapEval.comp
    (hessianCurryEquiv V F).toContinuousLinearEquiv.toContinuousLinearMap

@[simp]
theorem laplacianEval_apply (A : V [×2]→L[Real] F) :
    laplacianEval A =
      DifferentialGeometry.Analysis.Parabolic.Euclidean.lapEval
        (hessianCurryEquiv V F A) :=
  rfl

theorem norm_laplacianEval_le :
    ‖laplacianEval (V := V) (F := F)‖ ≤ Module.finrank Real V := by
  apply ContinuousLinearMap.opNorm_le_bound _ (Nat.cast_nonneg _)
  intro A
  have h := DifferentialGeometry.Analysis.Parabolic.Euclidean.lapEval_dist_le
    (V := V) (F := F) (hessianCurryEquiv V F A) 0
  simpa only [laplacianEval_apply, map_zero, dist_zero_right,
    LinearIsometryEquiv.norm_map] using h

def contDiffHolderSpaceLaplacian (alpha : NNReal) :
    ContDiffHolderSpace (V := V) (F := F) 2 alpha →L[Real]
      BoundedHolderSpace (X := V) (F := F) alpha :=
  (boundedHolderSpaceMap alpha (laplacianEval (V := V) (F := F))).comp
    (contDiffHolderSpaceTopJet 2 alpha)

@[simp]
theorem contDiffHolderSpaceLaplacian_apply
    (alpha : NNReal)
    (f : ContDiffHolderSpace (V := V) (F := F) 2 alpha) (x : V) :
    contDiffHolderSpaceLaplacian alpha f x =
      laplacianEval
        (iteratedFDeriv Real 2 (contDiffHolderSpaceFun f) x) :=
  rfl

theorem norm_contDiffHolderSpaceLaplacian_le (alpha : NNReal) :
    ‖contDiffHolderSpaceLaplacian (V := V) (F := F) alpha‖ ≤
      Module.finrank Real V := by
  calc
    ‖contDiffHolderSpaceLaplacian (V := V) (F := F) alpha‖ ≤
        ‖boundedHolderSpaceMap alpha
          (laplacianEval (V := V) (F := F))‖ *
        ‖contDiffHolderSpaceTopJet (V := V) (F := F) 2 alpha‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖laplacianEval (V := V) (F := F)‖ * 1 := by
      gcongr
      · exact norm_boundedHolderSpaceMap_le alpha
          (laplacianEval (V := V) (F := F))
      · exact norm_contDiffHolderSpaceTopJet_le
          (V := V) (F := F) 2 alpha
    _ ≤ Module.finrank Real V := by
      simpa only [mul_one] using norm_laplacianEval_le (V := V) (F := F)

def parabolicC2HolderSpaceLaplacian (alpha : NNReal) :
    ParabolicC2HolderSpace (V := V) (F := F) alpha →L[Real]
      ParabolicHolderSpace (V := V) (F := F) alpha :=
  (boundedHolderSpaceMap alpha (laplacianEval (V := V) (F := F))).comp
    (parabolicC2HolderSpaceSpatialHessian alpha)

@[simp]
theorem parabolicC2HolderSpaceLaplacian_apply
    (alpha : NNReal)
    (u : ParabolicC2HolderSpace (V := V) (F := F) alpha)
    (p : ParabolicPoint V) :
    parabolicC2HolderSpaceLaplacian alpha u p =
      laplacianEval
        (parabolicSpatialJet 2 (parabolicC2HolderSpaceFun u) p) :=
  rfl

theorem norm_parabolicC2HolderSpaceLaplacian_le (alpha : NNReal) :
    ‖parabolicC2HolderSpaceLaplacian (V := V) (F := F) alpha‖ ≤
      Module.finrank Real V := by
  calc
    ‖parabolicC2HolderSpaceLaplacian (V := V) (F := F) alpha‖ ≤
        ‖boundedHolderSpaceMap alpha
          (laplacianEval (V := V) (F := F))‖ *
        ‖parabolicC2HolderSpaceSpatialHessian
          (V := V) (F := F) alpha‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖laplacianEval (V := V) (F := F)‖ * 1 := by
      gcongr
      · exact norm_boundedHolderSpaceMap_le alpha
          (laplacianEval (V := V) (F := F))
      · exact norm_parabolicC2HolderSpaceSpatialHessian_le
          (V := V) (F := F) alpha
    _ ≤ Module.finrank Real V := by
      simpa only [mul_one] using norm_laplacianEval_le (V := V) (F := F)

def parabolicHeatOperator (alpha : NNReal) :
    ParabolicC2HolderSpace (V := V) (F := F) alpha →L[Real]
      ParabolicHolderSpace (V := V) (F := F) alpha :=
  parabolicC2HolderSpaceTimeDerivative alpha -
    parabolicC2HolderSpaceLaplacian alpha

@[simp]
theorem parabolicHeatOperator_apply
    (alpha : NNReal)
    (u : ParabolicC2HolderSpace (V := V) (F := F) alpha)
    (p : ParabolicPoint V) :
    parabolicHeatOperator alpha u p =
      parabolicTimeDerivative (parabolicC2HolderSpaceFun u) p -
        laplacianEval
          (parabolicSpatialJet 2 (parabolicC2HolderSpaceFun u) p) :=
  rfl

theorem norm_parabolicHeatOperator_le (alpha : NNReal) :
    ‖parabolicHeatOperator (V := V) (F := F) alpha‖ ≤
      1 + Module.finrank Real V := by
  calc
    ‖parabolicHeatOperator (V := V) (F := F) alpha‖ ≤
        ‖parabolicC2HolderSpaceTimeDerivative
          (V := V) (F := F) alpha‖ +
        ‖parabolicC2HolderSpaceLaplacian
          (V := V) (F := F) alpha‖ := norm_sub_le _ _
    _ ≤ 1 + Module.finrank Real V :=
      add_le_add
        (norm_parabolicC2HolderSpaceTimeDerivative_le
          (V := V) (F := F) alpha)
        (norm_parabolicC2HolderSpaceLaplacian_le
          (V := V) (F := F) alpha)

end DifferentialGeometry.Analysis.Schauder
