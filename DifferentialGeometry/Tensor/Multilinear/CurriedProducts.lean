import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Topology.Algebra.Module.FiniteDimension

noncomputable section

namespace ContinuousLinearMap

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]

private local instance : NormedAddCommGroup (E →L[𝕜] 𝕜) :=
  ContinuousLinearMap.toNormedAddCommGroup

private local instance : NormedSpace 𝕜 (E →L[𝕜] 𝕜) :=
  ContinuousLinearMap.toNormedSpace

private local instance : NormedAddCommGroup (E →L[𝕜] E →L[𝕜] 𝕜) :=
  ContinuousLinearMap.toNormedAddCommGroup

private local instance : NormedSpace 𝕜 (E →L[𝕜] E →L[𝕜] 𝕜) :=
  ContinuousLinearMap.toNormedSpace

private local instance : NormedAddCommGroup (E →L[𝕜] E →L[𝕜] E →L[𝕜] 𝕜) :=
  ContinuousLinearMap.toNormedAddCommGroup

private local instance : NormedSpace 𝕜 (E →L[𝕜] E →L[𝕜] E →L[𝕜] 𝕜) :=
  ContinuousLinearMap.toNormedSpace

private local instance :
    NormedAddCommGroup (E →L[𝕜] E →L[𝕜] E →L[𝕜] E →L[𝕜] 𝕜) :=
  ContinuousLinearMap.toNormedAddCommGroup

private local instance :
    NormedSpace 𝕜 (E →L[𝕜] E →L[𝕜] E →L[𝕜] E →L[𝕜] 𝕜) :=
  ContinuousLinearMap.toNormedSpace

def evalCurriedFourLastTwo
    (F : E →L[𝕜] E →L[𝕜] E →L[𝕜] E →L[𝕜] 𝕜) (u w : E) :
    E →L[𝕜] E →L[𝕜] 𝕜 :=
  (ContinuousLinearMap.compL 𝕜 E (E →L[𝕜] E →L[𝕜] 𝕜) 𝕜
    ((ContinuousLinearMap.apply 𝕜 𝕜 w).comp
      (ContinuousLinearMap.apply 𝕜 (E →L[𝕜] 𝕜) u))).comp F

def curriedBilinearMul (A B : E →L[𝕜] E →L[𝕜] 𝕜) :
    E →L[𝕜] E →L[𝕜] E →L[𝕜] E →L[𝕜] 𝕜 :=
  LinearMap.toContinuousLinearMap
    { toFun := fun c => LinearMap.toContinuousLinearMap
        { toFun := fun v => LinearMap.toContinuousLinearMap
            { toFun := fun c' => LinearMap.toContinuousLinearMap
                { toFun := fun v' => A c c' * B v v'
                  map_add' := fun v₁ v₂ => by
                    simp [map_add, mul_add]
                  map_smul' := fun r v' => by
                    simp [map_smul, smul_eq_mul]
                    ring }
              map_add' := fun c₁ c₂ => by
                ext v'
                simp [LinearMap.toContinuousLinearMap, map_add,
                  ContinuousLinearMap.add_apply, add_mul]
              map_smul' := fun r c' => by
                ext v'
                simp [LinearMap.toContinuousLinearMap, map_smul,
                  ContinuousLinearMap.smul_apply, smul_eq_mul]
                ring }
          map_add' := fun v₁ v₂ => by
            ext c' v'
            simp [LinearMap.toContinuousLinearMap, map_add,
              ContinuousLinearMap.add_apply, mul_add]
          map_smul' := fun r v => by
            ext c' v'
            simp [LinearMap.toContinuousLinearMap, map_smul,
              ContinuousLinearMap.smul_apply, smul_eq_mul]
            ring }
      map_add' := fun c₁ c₂ => by
        ext v c' v'
        simp [LinearMap.toContinuousLinearMap, map_add,
          ContinuousLinearMap.add_apply, add_mul]
      map_smul' := fun r c => by
        ext v c' v'
        simp [LinearMap.toContinuousLinearMap, map_smul,
          ContinuousLinearMap.smul_apply, smul_eq_mul]
        ring }

@[simp]
theorem curriedBilinearMul_apply
    (A B : E →L[𝕜] E →L[𝕜] 𝕜) (c v c' v' : E) :
    curriedBilinearMul A B c v c' v' = A c c' * B v v' := rfl

def evalCurriedThreeLast
    (f : E →L[𝕜] E →L[𝕜] E →L[𝕜] 𝕜) (e : E) :
    E →L[𝕜] E →L[𝕜] 𝕜 :=
  LinearMap.toContinuousLinearMap
    { toFun := fun c => LinearMap.toContinuousLinearMap
        { toFun := fun v => f c v e
          map_add' := fun v₁ v₂ => by
            simp [map_add, ContinuousLinearMap.add_apply]
          map_smul' := fun r v => by
            simp [map_smul, ContinuousLinearMap.smul_apply] }
      map_add' := fun c₁ c₂ => by
        ext v
        change f (c₁ + c₂) v e = f c₁ v e + f c₂ v e
        rw [f.map_add]
        rfl
      map_smul' := fun r c => by
        ext v
        change f (r • c) v e = r • f c v e
        rw [f.map_smul]
        rfl }

end ContinuousLinearMap

end
