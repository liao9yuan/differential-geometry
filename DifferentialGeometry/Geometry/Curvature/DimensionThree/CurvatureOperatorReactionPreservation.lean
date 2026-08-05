import DifferentialGeometry.Geometry.Curvature.DimensionThree.CurvatureOperatorReactionTensor
import DifferentialGeometry.Geometry.Curvature.DimensionThree.RicciControlsRm

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.Integral.Connection

open Bundle Tensor0SBundle
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M]
variable {x : M}

theorem ricciFromSectional3_secRic3
    (l1 l2 l3 : Real) (i j : Fin 3) :
    DifferentialGeometry.Dim3Reaction.ricciFromSectional3
        (sec12Ric3 l1 l2 l3) (sec13Ric3 l1 l2 l3)
        (sec23Ric3 l1 l2 l3) i j =
      ricciDiag3 l1 l2 l3 i j := by
  fin_cases i <;> fin_cases j <;>
    simp [DifferentialGeometry.Dim3Reaction.ricciFromSectional3,
      sec12Ric3, sec13Ric3, sec23Ric3, ricciDiag3] <;> ring

theorem stdRmDiag3_neg_eq_rm_ricciFromSectional3
    (l1 l2 l3 : Real) (i j k l : Fin 3) :
    stdRmDiag3 (-l1) (-l2) (-l3) i j k l =
      DifferentialGeometry.Dim3Reaction.rm
        (DifferentialGeometry.Dim3Reaction.ricciFromSectional3
          (sec12Ric3 l1 l2 l3) (sec13Ric3 l1 l2 l3)
          (sec23Ric3 l1 l2 l3)) i j k l := by
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    simp [stdRmDiag3, ricciDiag3, ricciEigenScalar3, delta3,
      DifferentialGeometry.Dim3Reaction.rm,
      DifferentialGeometry.Dim3Reaction.ricciFromSectional3,
      DifferentialGeometry.Dim3Reaction.sc, DifferentialGeometry.Dim3Reaction.kd,
      sec12Ric3, sec13Ric3, sec23Ric3] <;> ring

theorem algebraicCurvatureOperatorNonnegative_normalForm3
    (g : SmoothRiemannianMetric I M)
    (Ric : Tensor02At (I := I) (M := M) x)
    (scalar : Real)
    (A : algebraicCurvatureTensorSubmodule (I := I) (M := M) x)
    (hdim : Module.finrank Real (TangentSpace I x) = 3)
    (hsymm : RicciSymAt (I := I) Ric)
    (htrace : ∀ basis : Module.Basis (Fin 3) Real (TangentSpace I x),
      OrthonormalBasisAt (I := I) g x basis →
        RiemannFromRicci3DTraceDataAt (I := I) g (-Ric) (-scalar)
          (A : Tensor04At (I := I) (M := M) x) basis)
    (hA : A ∈ algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M)) :
    ∃ (basis : Module.Basis (Fin 3) Real (TangentSpace I x))
        (K12 K13 K23 : Real),
      OrthonormalBasisAt (I := I) g x basis ∧
        0 ≤ K12 ∧ 0 ≤ K13 ∧ 0 ≤ K23 ∧
        (∀ i j,
          ricciCompAt (I := I) basis Ric i j =
            DifferentialGeometry.Dim3Reaction.ricciFromSectional3 K12 K13 K23 i j) ∧
        ∀ a b c d,
          tensor04StdAt (I := I) (M := M)
            (A : Tensor04At (I := I) (M := M) x)
            (basis a) (basis b) (basis c) (basis d) =
              DifferentialGeometry.Dim3Reaction.rm
                (DifferentialGeometry.Dim3Reaction.ricciFromSectional3 K12 K13 K23)
                a b c d := by
  obtain ⟨basis, l1, l2, l3, horth, hdiag⟩ :=
    ricciEigen3 (I := I) g Ric hdim hsymm
  let K12 := sec12Ric3 l1 l2 l3
  let K13 := sec13Ric3 l1 l2 l3
  let K23 := sec23Ric3 l1 l2 l3
  have htraceBasis := htrace basis horth
  have h00 :
      stdRicci3 (standardRmCompAt (I := I) basis
        (A : Tensor04At (I := I) (M := M) x)) 0 0 = -l1 := by
    rw [← htraceBasis.ricci_trace 0 0]
    rw [ricciCompAt_apply]
    change -(Ric (vec2 (I := I) (basis 0) (basis 0))) = -l1
    have h := hdiag.2 0 0
    rw [ricciCompAt_apply] at h
    simpa [ricciDiag3] using congrArg Neg.neg h
  have h11 :
      stdRicci3 (standardRmCompAt (I := I) basis
        (A : Tensor04At (I := I) (M := M) x)) 1 1 = -l2 := by
    rw [← htraceBasis.ricci_trace 1 1]
    rw [ricciCompAt_apply]
    change -(Ric (vec2 (I := I) (basis 1) (basis 1))) = -l2
    have h := hdiag.2 1 1
    rw [ricciCompAt_apply] at h
    simpa [ricciDiag3] using congrArg Neg.neg h
  have h22 :
      stdRicci3 (standardRmCompAt (I := I) basis
        (A : Tensor04At (I := I) (M := M) x)) 2 2 = -l3 := by
    rw [← htraceBasis.ricci_trace 2 2]
    rw [ricciCompAt_apply]
    change -(Ric (vec2 (I := I) (basis 2) (basis 2))) = -l3
    have h := hdiag.2 2 2
    rw [ricciCompAt_apply] at h
    simpa [ricciDiag3] using congrArg Neg.neg h
  have hscalar : scalar = ricciEigenScalar3 l1 l2 l3 := by
    have hs := htraceBasis.scalar_trace
    unfold stdScalar3 at hs
    simp [h00, h11, h22] at hs
    unfold ricciEigenScalar3
    linarith
  have hdiagNeg :
      RicciDiagAt (I := I) (-Ric) (-scalar) (-l1) (-l2) (-l3) basis := by
    constructor
    · unfold ricciEigenScalar3 at hscalar ⊢
      linarith
    · intro i j
      have hij := hdiag.2 i j
      rw [ricciCompAt_apply] at hij ⊢
      change -(Ric (vec2 (I := I) (basis i) (basis j))) =
        ricciDiag3 (-l1) (-l2) (-l3) i j
      rw [hij]
      fin_cases i <;> fin_cases j <;> simp [ricciDiag3]
  have hcompStd := stdRmComp_eq_diag (I := I) htraceBasis hdiagNeg
  have hcomp : ∀ a b c d,
      tensor04StdAt (I := I) (M := M)
        (A : Tensor04At (I := I) (M := M) x)
        (basis a) (basis b) (basis c) (basis d) =
          DifferentialGeometry.Dim3Reaction.rm
            (DifferentialGeometry.Dim3Reaction.ricciFromSectional3 K12 K13 K23)
            a b c d := by
    intro a b c d
    unfold tensor04StdAt
    rw [← rm04CompAt_apply]
    change standardRmCompAt (I := I) basis
      (A : Tensor04At (I := I) (M := M) x) a b c d = _
    rw [hcompStd a b c d]
    exact stdRmDiag3_neg_eq_rm_ricciFromSectional3 l1 l2 l3 a b c d
  have hsectional :
      A ∈ algebraicSectionalNonnegativeCone (I := I) (M := M) :=
    algebraicCurvatureOperatorNonnegativeCone_le_sectionalNonnegativeCone hA
  have h12 := mem_algebraicSectionalNonnegativeCone.mp hsectional (basis 0) (basis 1)
  have h13 := mem_algebraicSectionalNonnegativeCone.mp hsectional (basis 0) (basis 2)
  have h23 := mem_algebraicSectionalNonnegativeCone.mp hsectional (basis 1) (basis 2)
  change 0 ≤ tensor04StdAt (I := I) (M := M)
    (A : Tensor04At (I := I) (M := M) x) (basis 0) (basis 1) (basis 1) (basis 0) at h12
  change 0 ≤ tensor04StdAt (I := I) (M := M)
    (A : Tensor04At (I := I) (M := M) x) (basis 0) (basis 2) (basis 2) (basis 0) at h13
  change 0 ≤ tensor04StdAt (I := I) (M := M)
    (A : Tensor04At (I := I) (M := M) x) (basis 1) (basis 2) (basis 2) (basis 1) at h23
  rw [hcomp 0 1 1 0] at h12
  rw [hcomp 0 2 2 0] at h13
  rw [hcomp 1 2 2 1] at h23
  have hK12 : 0 ≤ K12 := by
    simp [DifferentialGeometry.Dim3Reaction.rm,
      DifferentialGeometry.Dim3Reaction.ricciFromSectional3,
      DifferentialGeometry.Dim3Reaction.sc, DifferentialGeometry.Dim3Reaction.kd] at h12
    linarith
  have hK13 : 0 ≤ K13 := by
    simp [DifferentialGeometry.Dim3Reaction.rm,
      DifferentialGeometry.Dim3Reaction.ricciFromSectional3,
      DifferentialGeometry.Dim3Reaction.sc, DifferentialGeometry.Dim3Reaction.kd] at h13
    linarith
  have hK23 : 0 ≤ K23 := by
    simp [DifferentialGeometry.Dim3Reaction.rm,
      DifferentialGeometry.Dim3Reaction.ricciFromSectional3,
      DifferentialGeometry.Dim3Reaction.sc, DifferentialGeometry.Dim3Reaction.kd] at h23
    linarith
  refine ⟨basis, K12, K13, K23, horth, hK12, hK13, hK23, ?_, hcomp⟩
  intro i j
  rw [hdiag.2 i j]
  exact (ricciFromSectional3_secRic3 l1 l2 l3 i j).symm

theorem algebraicCurvatureOperatorReaction_nonnegative3
    (g : SmoothRiemannianMetric I M)
    (Ric : Tensor02At (I := I) (M := M) x)
    (scalar : Real)
    (A Q : algebraicCurvatureTensorSubmodule (I := I) (M := M) x)
    (hdim : Module.finrank Real (TangentSpace I x) = 3)
    (hsymm : RicciSymAt (I := I) Ric)
    (htrace : ∀ basis : Module.Basis (Fin 3) Real (TangentSpace I x),
      OrthonormalBasisAt (I := I) g x basis →
        RiemannFromRicci3DTraceDataAt (I := I) g (-Ric) (-scalar)
          (A : Tensor04At (I := I) (M := M) x) basis)
    (hA : A ∈ algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M))
    (hreaction : ∀ (basis : Module.Basis (Fin 3) Real (TangentSpace I x)),
      OrthonormalBasisAt (I := I) g x basis → ∀ a b c d,
        tensor04StdAt (I := I) (M := M)
          (Q : Tensor04At (I := I) (M := M) x)
          (basis a) (basis b) (basis c) (basis d) =
            -2 * DifferentialGeometry.Dim3Reaction.Bsharp
              (fun i j ↦ ricciCompAt (I := I) basis Ric i j) a b c d) :
    Q ∈ algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M) := by
  obtain ⟨basis, K12, K13, K23, horth, h12, h13, h23, hRic, _⟩ :=
    algebraicCurvatureOperatorNonnegative_normalForm3
      (I := I) g Ric scalar A hdim hsymm htrace hA
  apply algebraicCurvatureOperatorNonnegative_of_components_eq_reaction
    basis Q K12 K13 K23 h12 h13 h23
  intro a b c d
  rw [hreaction basis horth a b c d]
  unfold DifferentialGeometry.Dim3Reaction.curvatureTensorReaction3
  congr 2
  funext i j
  exact hRic i j

end DifferentialGeometry.Integral.Connection
