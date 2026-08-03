import DifferentialGeometry.Analysis.Parabolic.Euclidean.HeatPotentialSPD
import DifferentialGeometry.Analysis.Parabolic.Euclidean.HeatSemigroupSchauder
import DifferentialGeometry.Analysis.Schauder.BilinearHolder

noncomputable section

open Matrix Real Set
open scoped NNReal RealInnerProductSpace

namespace DifferentialGeometry.Analysis.Parabolic.Euclidean

open DifferentialGeometry.Analysis.Schauder

private abbrev Euc (n : Type*) := EuclideanSpace Real n

variable {n F : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
  [NormedAddCommGroup F] [NormedSpace Real F]

def parabolicHessianComponent
    (u : Real → Euc n → F) (i j : n) : ParabolicPoint (Euc n) → F :=
  fun p ↦
    hessianCurryEquiv (Euc n) F (parabolicSpatialJet 2 u p)
      (EuclideanSpace.basisFun n Real i)
      (EuclideanSpace.basisFun n Real j)

def parabolicVariableMatrixLap
    (a : n → n → ParabolicPoint (Euc n) → Real)
    (u : Real → Euc n → F) : ParabolicPoint (Euc n) → F :=
  fun p ↦ matrixLap (fun i j ↦ a i j p)
    (hessianCurryEquiv (Euc n) F (parabolicSpatialJet 2 u p))

def parabolicFrozenMatrixLap
    (A : Matrix n n Real) (u : Real → Euc n → F) :
    ParabolicPoint (Euc n) → F :=
  fun p ↦ matrixLap A
    (hessianCurryEquiv (Euc n) F (parabolicSpatialJet 2 u p))

def parabolicVariableMatrixOperator
    (a : n → n → ParabolicPoint (Euc n) → Real)
    (u : Real → Euc n → F) : ParabolicPoint (Euc n) → F :=
  fun p ↦ parabolicTimeDerivative u p - parabolicVariableMatrixLap a u p

def parabolicFrozenMatrixOperator
    (A : Matrix n n Real) (u : Real → Euc n → F) :
    ParabolicPoint (Euc n) → F :=
  fun p ↦ parabolicTimeDerivative u p - parabolicFrozenMatrixLap A u p

def parabolicMatrixLapFreezeDefect
    (a : n → n → ParabolicPoint (Euc n) → Real)
    (p0 : ParabolicPoint (Euc n)) (u : Real → Euc n → F) :
    ParabolicPoint (Euc n) → F :=
  fun p ↦ ∑ i, ∑ j, (a i j p0 - a i j p) • parabolicHessianComponent u i j p

omit [DecidableEq n] [Nonempty n] in
@[simp]
theorem parabolicVariableMatrixLap_apply
    (a : n → n → ParabolicPoint (Euc n) → Real)
    (u : Real → Euc n → F) (p : ParabolicPoint (Euc n)) :
    parabolicVariableMatrixLap a u p =
      ∑ i, ∑ j, a i j p • parabolicHessianComponent u i j p := by
  rfl

omit [DecidableEq n] [Nonempty n] in
@[simp]
theorem parabolicFrozenMatrixLap_apply
    (A : Matrix n n Real) (u : Real → Euc n → F)
    (p : ParabolicPoint (Euc n)) :
    parabolicFrozenMatrixLap A u p =
      ∑ i, ∑ j, A i j • parabolicHessianComponent u i j p := by
  rfl

omit [DecidableEq n] [Nonempty n] in
theorem parabolicFrozenMatrixLap_eq_variable_add_defect
    (a : n → n → ParabolicPoint (Euc n) → Real)
    (p0 : ParabolicPoint (Euc n)) (u : Real → Euc n → F)
    (p : ParabolicPoint (Euc n)) :
    parabolicFrozenMatrixLap (fun i j ↦ a i j p0) u p =
      parabolicVariableMatrixLap a u p +
        parabolicMatrixLapFreezeDefect a p0 u p := by
  simp only [parabolicFrozenMatrixLap_apply,
    parabolicVariableMatrixLap_apply, parabolicMatrixLapFreezeDefect]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _hj
  module

omit [DecidableEq n] [Nonempty n] in
theorem parabolicTimeDerivative_sub_frozenMatrixLap
    (a : n → n → ParabolicPoint (Euc n) → Real)
    (p0 : ParabolicPoint (Euc n)) (u : Real → Euc n → F)
    (p : ParabolicPoint (Euc n)) :
    parabolicTimeDerivative u p -
        parabolicFrozenMatrixLap (fun i j ↦ a i j p0) u p =
      (parabolicTimeDerivative u p - parabolicVariableMatrixLap a u p) -
        parabolicMatrixLapFreezeDefect a p0 u p := by
  rw [parabolicFrozenMatrixLap_eq_variable_add_defect]
  abel

omit [DecidableEq n] [Nonempty n] in
theorem parabolicFrozenMatrixOperator_eq_variable_sub_defect
    (a : n → n → ParabolicPoint (Euc n) → Real)
    (p0 : ParabolicPoint (Euc n)) (u : Real → Euc n → F)
    (p : ParabolicPoint (Euc n)) :
    parabolicFrozenMatrixOperator (fun i j ↦ a i j p0) u p =
      parabolicVariableMatrixOperator a u p -
        parabolicMatrixLapFreezeDefect a p0 u p := by
  exact parabolicTimeDerivative_sub_frozenMatrixLap a p0 u p

omit [DecidableEq n] [Nonempty n] in
theorem parabolicHessianComponent_norm_le
    (u : Real → Euc n → F) (i j : n) (p : ParabolicPoint (Euc n)) :
    ‖parabolicHessianComponent u i j p‖ ≤ ‖parabolicSpatialJet 2 u p‖ := by
  let H := hessianCurryEquiv (Euc n) F (parabolicSpatialJet 2 u p)
  calc
    ‖parabolicHessianComponent u i j p‖ =
        ‖H (EuclideanSpace.basisFun n Real i)
          (EuclideanSpace.basisFun n Real j)‖ := rfl
    _ ≤ ‖H (EuclideanSpace.basisFun n Real i)‖ *
        ‖EuclideanSpace.basisFun n Real j‖ :=
      (H (EuclideanSpace.basisFun n Real i)).le_opNorm _
    _ ≤ (‖H‖ * ‖EuclideanSpace.basisFun n Real i‖) *
        ‖EuclideanSpace.basisFun n Real j‖ := by
      gcongr
      exact H.le_opNorm _
    _ = ‖H‖ := by
      rw [(EuclideanSpace.basisFun n Real).orthonormal.norm_eq_one i,
        (EuclideanSpace.basisFun n Real).orthonormal.norm_eq_one j,
        mul_one, mul_one]
    _ = ‖parabolicSpatialJet 2 u p‖ :=
      (hessianCurryEquiv (Euc n) F).norm_map _

omit [DecidableEq n] [Nonempty n] in
theorem parabolicHessianComponent_holderWith_restrict
    {alpha X : NNReal} {Q : Set (ParabolicPoint (Euc n))}
    {u : Real → Euc n → F}
    (h : eParabolicC2HolderGaugeOn alpha Q u ≤ X) (i j : n) :
    HolderWith X alpha (Q.restrict (parabolicHessianComponent u i j)) := by
  have hjet := parabolicSpatialJet_holderWith_restrict h
  intro p q
  rw [edist_dist, edist_dist]
  have hreal :
      dist (parabolicHessianComponent u i j p.1)
          (parabolicHessianComponent u i j q.1) ≤
        (X : Real) * dist p q ^ (alpha : Real) := by
    rw [dist_eq_norm]
    change ‖hessianCurryEquiv (Euc n) F (parabolicSpatialJet 2 u p.1)
          (EuclideanSpace.basisFun n Real i)
          (EuclideanSpace.basisFun n Real j) -
        hessianCurryEquiv (Euc n) F (parabolicSpatialJet 2 u q.1)
          (EuclideanSpace.basisFun n Real i)
          (EuclideanSpace.basisFun n Real j)‖ ≤ _
    rw [← ContinuousLinearMap.sub_apply, ← ContinuousLinearMap.sub_apply,
      ← map_sub]
    calc
      ‖hessianCurryEquiv (Euc n) F
          (parabolicSpatialJet 2 u p.1 - parabolicSpatialJet 2 u q.1)
          (EuclideanSpace.basisFun n Real i)
          (EuclideanSpace.basisFun n Real j)‖ ≤
          ‖hessianCurryEquiv (Euc n) F
            (parabolicSpatialJet 2 u p.1 - parabolicSpatialJet 2 u q.1)‖ := by
        let H := hessianCurryEquiv (Euc n) F
          (parabolicSpatialJet 2 u p.1 - parabolicSpatialJet 2 u q.1)
        calc
          ‖H (EuclideanSpace.basisFun n Real i)
              (EuclideanSpace.basisFun n Real j)‖ ≤
              ‖H (EuclideanSpace.basisFun n Real i)‖ *
                ‖EuclideanSpace.basisFun n Real j‖ :=
            (H (EuclideanSpace.basisFun n Real i)).le_opNorm _
          _ ≤ (‖H‖ * ‖EuclideanSpace.basisFun n Real i‖) *
                ‖EuclideanSpace.basisFun n Real j‖ := by
            gcongr
            exact H.le_opNorm _
          _ = ‖H‖ := by
            rw [(EuclideanSpace.basisFun n Real).orthonormal.norm_eq_one i,
              (EuclideanSpace.basisFun n Real).orthonormal.norm_eq_one j,
              mul_one, mul_one]
      _ = ‖parabolicSpatialJet 2 u p.1 - parabolicSpatialJet 2 u q.1‖ :=
        (hessianCurryEquiv (Euc n) F).norm_map _
      _ = dist (parabolicSpatialJet 2 u p.1)
          (parabolicSpatialJet 2 u q.1) :=
        (dist_eq_norm _ _).symm
      _ ≤ (X : Real) * dist p q ^ (alpha : Real) := hjet.dist_le p q
  calc
    ENNReal.ofReal
        (dist (parabolicHessianComponent u i j p.1)
          (parabolicHessianComponent u i j q.1)) ≤
        ENNReal.ofReal ((X : Real) * dist p q ^ (alpha : Real)) :=
      ENNReal.ofReal_le_ofReal hreal
    _ = (X : ENNReal) * ENNReal.ofReal (dist p q ^ (alpha : Real)) := by
      rw [ENNReal.ofReal_mul X.coe_nonneg]
      congr 1
      exact ENNReal.ofReal_coe_nnreal
    _ = (X : ENNReal) * ENNReal.ofReal (dist p q) ^ (alpha : Real) := by
      rw [ENNReal.ofReal_rpow_of_nonneg dist_nonneg alpha.coe_nonneg]

omit [DecidableEq n] [Nonempty n] in
theorem norm_parabolicMatrixLapFreezeDefect_le
    {alpha X : NNReal} {Q : Set (ParabolicPoint (Euc n))}
    (a : n → n → ParabolicPoint (Euc n) → Real)
    (p0 : ParabolicPoint (Euc n)) (u : Real → Euc n → F)
    (omega : n → n → NNReal)
    (homega : ∀ i j p, p ∈ Q → ‖a i j p0 - a i j p‖ ≤ omega i j)
    (hu : eParabolicC2HolderGaugeOn alpha Q u ≤ X)
    (p : ParabolicPoint (Euc n)) (hp : p ∈ Q) :
    ‖parabolicMatrixLapFreezeDefect a p0 u p‖ ≤
      (∑ i, ∑ j, omega i j * X : NNReal) := by
  unfold parabolicMatrixLapFreezeDefect
  calc
    ‖∑ i, ∑ j, (a i j p0 - a i j p) •
        parabolicHessianComponent u i j p‖ ≤
        ∑ i, ∑ j, ‖(a i j p0 - a i j p) •
          parabolicHessianComponent u i j p‖ :=
      (norm_sum_le _ _).trans
        (Finset.sum_le_sum fun i _ ↦ norm_sum_le _ _)
    _ ≤ ∑ i, ∑ j, (omega i j : Real) * X := by
      apply Finset.sum_le_sum
      intro i _hi
      apply Finset.sum_le_sum
      intro j _hj
      rw [norm_smul]
      exact mul_le_mul (homega i j p hp)
        ((parabolicHessianComponent_norm_le u i j p).trans
          (parabolicSpatialJet_norm_le hu le_rfl hp))
        (norm_nonneg _) (by positivity)
    _ = (∑ i, ∑ j, omega i j * X : NNReal) := by
      push_cast
      rfl

omit [DecidableEq n] [Nonempty n] in
theorem eSupNormOn_parabolicMatrixLapFreezeDefect_le
    {alpha X : NNReal} {Q : Set (ParabolicPoint (Euc n))}
    (a : n → n → ParabolicPoint (Euc n) → Real)
    (p0 : ParabolicPoint (Euc n)) (u : Real → Euc n → F)
    (omega : n → n → NNReal)
    (homega : ∀ i j p, p ∈ Q → ‖a i j p0 - a i j p‖ ≤ omega i j)
    (hu : eParabolicC2HolderGaugeOn alpha Q u ≤ X) :
    eSupNormOn Q (parabolicMatrixLapFreezeDefect a p0 u) ≤
      (∑ i, ∑ j, omega i j * X : NNReal) := by
  rw [eSupNormOn_le]
  intro p hp
  rw [ENNReal.ofReal_le_coe]
  exact norm_parabolicMatrixLapFreezeDefect_le
    a p0 u omega homega hu p hp

omit [DecidableEq n] [Nonempty n] in
theorem parabolicMatrixLapFreezeDefect_holderWith_restrict
    {alpha X : NNReal} {Q : Set (ParabolicPoint (Euc n))}
    (a : n → n → ParabolicPoint (Euc n) → Real)
    (p0 : ParabolicPoint (Euc n)) (u : Real → Euc n → F)
    (Ka omega : n → n → NNReal)
    (ha : ∀ i j, HolderWith (Ka i j) alpha (Q.restrict (a i j)))
    (homega : ∀ i j p, p ∈ Q → ‖a i j p0 - a i j p‖ ≤ omega i j)
    (hu : eParabolicC2HolderGaugeOn alpha Q u ≤ X) :
    HolderWith
      (∑ i, ∑ j, (omega i j * X + X * Ka i j)) alpha
      (Q.restrict (parabolicMatrixLapFreezeDefect a p0 u)) := by
  classical
  let C : n → n → NNReal :=
    fun i j ↦ omega i j * X + X * Ka i j
  have hcomponent : ∀ i j, HolderWith (C i j) alpha
      (fun p : Q ↦ (a i j p0 - a i j p.1) •
        parabolicHessianComponent u i j p.1) := by
    intro i j
    have hcoeff : HolderWith (Ka i j) alpha
        (fun p : Q ↦ a i j p0 - a i j p.1) := by
      intro p q
      change edist (a i j p0 - a i j p.1) (a i j p0 - a i j q.1) ≤ _
      rw [show edist (a i j p0 - a i j p.1)
          (a i j p0 - a i j q.1) = edist (a i j p.1) (a i j q.1) by
        simp only [edist_dist, Real.dist_eq]
        rw [show a i j p0 - a i j p.1 - (a i j p0 - a i j q.1) =
          -(a i j p.1 - a i j q.1) by ring, abs_neg]]
      exact ha i j p q
    have hhess := parabolicHessianComponent_holderWith_restrict hu i j
    apply holderWith_smul_of_norm_le hcoeff hhess
    · exact fun p ↦ homega i j p.1 p.2
    · intro p
      exact (parabolicHessianComponent_norm_le u i j p.1).trans
        (parabolicSpatialJet_norm_le hu le_rfl p.2)
  have hinner : ∀ i, HolderWith (∑ j, C i j) alpha
      (fun p : Q ↦ ∑ j, (a i j p0 - a i j p.1) •
        parabolicHessianComponent u i j p.1) := by
    intro i
    exact holderWith_finset_sum Finset.univ
      (fun j _ ↦ hcomponent i j)
  have hall := holderWith_finset_sum Finset.univ
    (K := fun i ↦ ∑ j, C i j)
    (f := fun (i : n) (p : Q) ↦ ∑ j, (a i j p0 - a i j p.1) •
      parabolicHessianComponent u i j p.1)
    (fun i _ ↦ hinner i)
  simpa only [C, parabolicMatrixLapFreezeDefect, Set.restrict_apply] using hall

omit [DecidableEq n] [Nonempty n] in
theorem parabolicFrozenMatrixOperator_source_estimate
    {alpha Kf Bf X : NNReal} {Q : Set (ParabolicPoint (Euc n))}
    (a : n → n → ParabolicPoint (Euc n) → Real)
    (p0 : ParabolicPoint (Euc n)) (u : Real → Euc n → F)
    (Ka omega : n → n → NNReal)
    (hsourceBound :
      eSupNormOn Q (parabolicVariableMatrixOperator a u) ≤ Bf)
    (hsourceHolder : HolderWith Kf alpha
      (Q.restrict (parabolicVariableMatrixOperator a u)))
    (ha : ∀ i j, HolderWith (Ka i j) alpha (Q.restrict (a i j)))
    (homega : ∀ i j p, p ∈ Q → ‖a i j p0 - a i j p‖ ≤ omega i j)
    (hu : eParabolicC2HolderGaugeOn alpha Q u ≤ X) :
    eSupNormOn Q
        (parabolicFrozenMatrixOperator (fun i j ↦ a i j p0) u) ≤
        Bf + ∑ i, ∑ j, omega i j * X ∧
      HolderWith
        (Kf + ∑ i, ∑ j, (omega i j * X + X * Ka i j)) alpha
        (Q.restrict
          (parabolicFrozenMatrixOperator (fun i j ↦ a i j p0) u)) := by
  have heq :
      parabolicFrozenMatrixOperator (fun i j ↦ a i j p0) u =
        parabolicVariableMatrixOperator a u -
          parabolicMatrixLapFreezeDefect a p0 u := by
    funext p
    exact parabolicFrozenMatrixOperator_eq_variable_sub_defect a p0 u p
  rw [heq]
  constructor
  · exact (eSupNormOn_sub_le Q _ _).trans
      (add_le_add hsourceBound
        (eSupNormOn_parabolicMatrixLapFreezeDefect_le
          a p0 u omega homega hu))
  · exact holderWith_sub hsourceHolder
      (parabolicMatrixLapFreezeDefect_holderWith_restrict
        a p0 u Ka omega ha homega hu)

end DifferentialGeometry.Analysis.Parabolic.Euclidean

end
