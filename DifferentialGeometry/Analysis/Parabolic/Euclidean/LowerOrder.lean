import DifferentialGeometry.Analysis.Parabolic.Euclidean.VariableCoefficient

noncomputable section

open Matrix Real Set
open scoped NNReal RealInnerProductSpace

namespace DifferentialGeometry.Analysis.Parabolic.Euclidean

open DifferentialGeometry.Analysis.Schauder

private abbrev Euc (n : Type*) := EuclideanSpace Real n

variable {n F : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
  [NormedAddCommGroup F] [NormedSpace Real F]

def parabolicGradientComponent
    (u : Real → Euc n → F) (i : n) : ParabolicPoint (Euc n) → F :=
  fun p ↦ continuousMultilinearCurryFin1 Real (Euc n) F
    (parabolicSpatialJet 1 u p) (EuclideanSpace.basisFun n Real i)

def parabolicDriftTerm
    (b : n → ParabolicPoint (Euc n) → Real)
    (u : Real → Euc n → F) : ParabolicPoint (Euc n) → F :=
  fun p ↦ ∑ i, b i p • parabolicGradientComponent u i p

def parabolicPotentialTerm
    (c : ParabolicPoint (Euc n) → Real)
    (u : Real → Euc n → F) : ParabolicPoint (Euc n) → F :=
  fun p ↦ c p • u p.time p.space

def parabolicLowerOrderTerm
    (b : n → ParabolicPoint (Euc n) → Real)
    (c : ParabolicPoint (Euc n) → Real)
    (u : Real → Euc n → F) : ParabolicPoint (Euc n) → F :=
  parabolicDriftTerm b u + parabolicPotentialTerm c u

def parabolicNondivergenceOperator
    (a : n → n → ParabolicPoint (Euc n) → Real)
    (b : n → ParabolicPoint (Euc n) → Real)
    (c : ParabolicPoint (Euc n) → Real)
    (u : Real → Euc n → F) : ParabolicPoint (Euc n) → F :=
  parabolicVariableMatrixOperator a u - parabolicLowerOrderTerm b c u

omit [DecidableEq n] [Nonempty n] in
@[simp]
theorem parabolicGradientComponent_apply
    (u : Real → Euc n → F) (i : n) (p : ParabolicPoint (Euc n)) :
    parabolicGradientComponent u i p =
      continuousMultilinearCurryFin1 Real (Euc n) F
        (parabolicSpatialJet 1 u p)
          (EuclideanSpace.basisFun n Real i) := rfl

omit [Fintype n] [DecidableEq n] [Nonempty n] in
@[simp]
theorem parabolicPotentialTerm_apply
    (c : ParabolicPoint (Euc n) → Real)
    (u : Real → Euc n → F) (p : ParabolicPoint (Euc n)) :
    parabolicPotentialTerm c u p = c p • u p.time p.space := rfl

omit [DecidableEq n] [Nonempty n] in
@[simp]
theorem parabolicLowerOrderTerm_apply
    (b : n → ParabolicPoint (Euc n) → Real)
    (c : ParabolicPoint (Euc n) → Real)
    (u : Real → Euc n → F) (p : ParabolicPoint (Euc n)) :
    parabolicLowerOrderTerm b c u p =
      (∑ i, b i p • parabolicGradientComponent u i p) +
        c p • u p.time p.space := by
  rfl

omit [DecidableEq n] [Nonempty n] in
theorem parabolicVariableMatrixOperator_eq_nondivergenceOperator_add_lowerOrderTerm
    (a : n → n → ParabolicPoint (Euc n) → Real)
    (b : n → ParabolicPoint (Euc n) → Real)
    (c : ParabolicPoint (Euc n) → Real)
    (u : Real → Euc n → F) :
    parabolicVariableMatrixOperator a u =
      parabolicNondivergenceOperator a b c u +
        parabolicLowerOrderTerm b c u := by
  unfold parabolicNondivergenceOperator
  abel

omit [DecidableEq n] [Nonempty n] in
theorem parabolicNondivergenceOperator_congr_of_eqOn_open
    {U : Set (ParabolicPoint (Euc n))} (hU : IsOpen U)
    (a : n → n → ParabolicPoint (Euc n) → Real)
    (b : n → ParabolicPoint (Euc n) → Real)
    (c : ParabolicPoint (Euc n) → Real)
    (u v : Real → Euc n → F) {p : ParabolicPoint (Euc n)} (hp : p ∈ U)
    (huv : Set.EqOn (fun q ↦ u q.time q.space)
      (fun q ↦ v q.time q.space) U) :
    parabolicNondivergenceOperator a b c u p =
      parabolicNondivergenceOperator a b c v p := by
  classical
  have hspaceMap : ContinuousAt
      (fun x ↦ parabolicPoint p.time x) p.space := by
    unfold parabolicPoint
    exact (continuous_const.prodMk continuous_id).continuousAt
  have hspace : u p.time =ᶠ[nhds p.space] v p.time := by
    filter_upwards [hspaceMap (hU.mem_nhds hp)] with x hx
    exact huv hx
  have htimeMap : ContinuousAt
      (fun t ↦ parabolicPoint t p.space) p.time := by
    unfold parabolicPoint
    exact (Metric.Snowflaking.continuous_toSnowflaking.prodMk
      continuous_const).continuousAt
  have htime : (fun t ↦ u t p.space) =ᶠ[nhds p.time]
      fun t ↦ v t p.space := by
    filter_upwards [htimeMap (hU.mem_nhds hp)] with t ht
    exact huv ht
  have hjetOne : parabolicSpatialJet 1 u p =
      parabolicSpatialJet 1 v p := by
    unfold parabolicSpatialJet
    exact (Filter.EventuallyEq.iteratedFDeriv Real hspace 1).eq_of_nhds
  have hjetTwo : parabolicSpatialJet 2 u p =
      parabolicSpatialJet 2 v p := by
    unfold parabolicSpatialJet
    exact (Filter.EventuallyEq.iteratedFDeriv Real hspace 2).eq_of_nhds
  have htimeDeriv : parabolicTimeDerivative u p =
      parabolicTimeDerivative v p := by
    unfold parabolicTimeDerivative
    exact congrArg (fun L : Real →L[Real] F ↦ L 1) htime.fderiv_eq
  have hvalue : u p.time p.space = v p.time p.space := huv hp
  unfold parabolicNondivergenceOperator parabolicVariableMatrixOperator
    parabolicVariableMatrixLap parabolicLowerOrderTerm parabolicDriftTerm
    parabolicGradientComponent parabolicPotentialTerm
  simp only [Pi.sub_apply, Pi.add_apply]
  rw [htimeDeriv, hjetTwo]
  simp_rw [hjetOne, hvalue]

omit [DecidableEq n] [Nonempty n] in
theorem parabolicGradientComponent_norm_le
    (u : Real → Euc n → F) (i : n) (p : ParabolicPoint (Euc n)) :
    ‖parabolicGradientComponent u i p‖ ≤ ‖parabolicSpatialJet 1 u p‖ := by
  rw [parabolicGradientComponent_apply]
  calc
    ‖continuousMultilinearCurryFin1 Real (Euc n) F
        (parabolicSpatialJet 1 u p) (EuclideanSpace.basisFun n Real i)‖ ≤
        ‖continuousMultilinearCurryFin1 Real (Euc n) F
          (parabolicSpatialJet 1 u p)‖ := by
      exact (continuousMultilinearCurryFin1 Real (Euc n) F
        (parabolicSpatialJet 1 u p)).le_opNorm _ |>.trans (by
          rw [(EuclideanSpace.basisFun n Real).orthonormal.norm_eq_one i,
            mul_one])
    _ = ‖parabolicSpatialJet 1 u p‖ :=
      (continuousMultilinearCurryFin1 Real (Euc n) F).norm_map _

omit [DecidableEq n] [Nonempty n] in
theorem parabolicGradientComponent_holderWith_restrict
    {alpha Kdu : NNReal} {Q : Set (ParabolicPoint (Euc n))}
    {u : Real → Euc n → F}
    (hdu : HolderWith Kdu alpha
      (Q.restrict (parabolicSpatialJet 1 u))) (i : n) :
    HolderWith Kdu alpha
      (Q.restrict (parabolicGradientComponent u i)) := by
  intro p q
  rw [edist_dist, edist_dist]
  have hreal : dist (parabolicGradientComponent u i p.1)
      (parabolicGradientComponent u i q.1) ≤
        (Kdu : Real) * dist p q ^ (alpha : Real) := by
    rw [dist_eq_norm]
    change ‖continuousMultilinearCurryFin1 Real (Euc n) F
          (parabolicSpatialJet 1 u p.1)
            (EuclideanSpace.basisFun n Real i) -
        continuousMultilinearCurryFin1 Real (Euc n) F
          (parabolicSpatialJet 1 u q.1)
            (EuclideanSpace.basisFun n Real i)‖ ≤ _
    rw [← ContinuousLinearMap.sub_apply, ← map_sub]
    calc
      ‖continuousMultilinearCurryFin1 Real (Euc n) F
          (parabolicSpatialJet 1 u p.1 - parabolicSpatialJet 1 u q.1)
            (EuclideanSpace.basisFun n Real i)‖ ≤
          ‖continuousMultilinearCurryFin1 Real (Euc n) F
            (parabolicSpatialJet 1 u p.1 -
              parabolicSpatialJet 1 u q.1)‖ := by
        exact (continuousMultilinearCurryFin1 Real (Euc n) F
          (parabolicSpatialJet 1 u p.1 -
            parabolicSpatialJet 1 u q.1)).le_opNorm _ |>.trans (by
              rw [(EuclideanSpace.basisFun n Real).orthonormal.norm_eq_one i,
                mul_one])
      _ = ‖parabolicSpatialJet 1 u p.1 -
          parabolicSpatialJet 1 u q.1‖ :=
        (continuousMultilinearCurryFin1 Real (Euc n) F).norm_map _
      _ = dist (parabolicSpatialJet 1 u p.1)
          (parabolicSpatialJet 1 u q.1) := (dist_eq_norm _ _).symm
      _ ≤ (Kdu : Real) * dist p q ^ (alpha : Real) := hdu.dist_le p q
  exact ENNReal.ofReal_le_ofReal hreal |>.trans_eq (by
    rw [ENNReal.ofReal_mul Kdu.coe_nonneg, ENNReal.ofReal_coe_nnreal,
      ENNReal.ofReal_rpow_of_nonneg dist_nonneg alpha.coe_nonneg])

def parabolicLowerOrderSupConst
    (Bb : n → NNReal) (Bc Mdu Mu : NNReal) : NNReal :=
  (∑ i, Bb i * Mdu) + Bc * Mu

def parabolicLowerOrderHolderConst
    (Kb Bb : n → NNReal) (Kc Kdu Ku Mdu Bc Mu : NNReal) : NNReal :=
  (∑ i, (Bb i * Kdu + Mdu * Kb i)) + (Bc * Ku + Mu * Kc)

omit [DecidableEq n] [Nonempty n] in
theorem norm_parabolicDriftTerm_le
    {Q : Set (ParabolicPoint (Euc n))}
    (b : n → ParabolicPoint (Euc n) → Real)
    (u : Real → Euc n → F) (Bb : n → NNReal) (Mdu : NNReal)
    (hb : ∀ i p, p ∈ Q → ‖b i p‖ ≤ Bb i)
    (hdu : ∀ p, p ∈ Q → ‖parabolicSpatialJet 1 u p‖ ≤ Mdu)
    (p : ParabolicPoint (Euc n)) (hp : p ∈ Q) :
    ‖parabolicDriftTerm b u p‖ ≤ ∑ i, Bb i * Mdu := by
  unfold parabolicDriftTerm
  calc
    ‖∑ i, b i p • parabolicGradientComponent u i p‖ ≤
        ∑ i, ‖b i p • parabolicGradientComponent u i p‖ :=
      norm_sum_le _ _
    _ ≤ ∑ i, (Bb i : Real) * Mdu := by
      apply Finset.sum_le_sum
      intro i _hi
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul (by simpa only [Real.norm_eq_abs] using hb i p hp)
        ((parabolicGradientComponent_norm_le u i p).trans (hdu p hp))
        (norm_nonneg _) (by positivity)
    _ = (∑ i, Bb i * Mdu : NNReal) := by push_cast; rfl

omit [DecidableEq n] [Nonempty n] in
theorem parabolicDriftTerm_holderWith_restrict
    {alpha Kdu : NNReal} {Q : Set (ParabolicPoint (Euc n))}
    (b : n → ParabolicPoint (Euc n) → Real)
    (u : Real → Euc n → F) (Kb Bb : n → NNReal) (Mdu : NNReal)
    (hb : ∀ i, HolderWith (Kb i) alpha (Q.restrict (b i)))
    (hbNorm : ∀ i p, p ∈ Q → ‖b i p‖ ≤ Bb i)
    (hdu : HolderWith Kdu alpha
      (Q.restrict (parabolicSpatialJet 1 u)))
    (hduNorm : ∀ p, p ∈ Q → ‖parabolicSpatialJet 1 u p‖ ≤ Mdu) :
    HolderWith (∑ i, (Bb i * Kdu + Mdu * Kb i)) alpha
      (Q.restrict (parabolicDriftTerm b u)) := by
  have hcomponent : ∀ i,
      HolderWith (Bb i * Kdu + Mdu * Kb i) alpha
        (fun p : Q ↦ b i p.1 • parabolicGradientComponent u i p.1) := by
    intro i
    apply holderWith_smul_of_norm_le (hb i)
      (parabolicGradientComponent_holderWith_restrict hdu i)
    · exact fun p ↦ hbNorm i p.1 p.2
    · intro p
      exact (parabolicGradientComponent_norm_le u i p.1).trans
        (hduNorm p.1 p.2)
  have hsum := holderWith_finset_sum (Finset.univ : Finset n)
    (K := fun i ↦ Bb i * Kdu + Mdu * Kb i)
    (f := fun i (p : Q) ↦ b i p.1 • parabolicGradientComponent u i p.1)
    (fun i _hi ↦ hcomponent i)
  simpa only [parabolicDriftTerm, Set.restrict_apply] using hsum

omit [Fintype n] [DecidableEq n] [Nonempty n] in
theorem norm_parabolicPotentialTerm_le
    {Q : Set (ParabolicPoint (Euc n))}
    (c : ParabolicPoint (Euc n) → Real)
    (u : Real → Euc n → F) (Bc Mu : NNReal)
    (hc : ∀ p, p ∈ Q → ‖c p‖ ≤ Bc)
    (hu : ∀ p, p ∈ Q → ‖u p.time p.space‖ ≤ Mu)
    (p : ParabolicPoint (Euc n)) (hp : p ∈ Q) :
    ‖parabolicPotentialTerm c u p‖ ≤ Bc * Mu := by
  rw [parabolicPotentialTerm_apply, norm_smul, Real.norm_eq_abs]
  exact mul_le_mul (by simpa only [Real.norm_eq_abs] using hc p hp)
    (hu p hp) (norm_nonneg _) (by positivity)

omit [DecidableEq n] [Nonempty n] in
theorem parabolicPotentialTerm_holderWith_restrict
    {alpha Kc Ku Bc Mu : NNReal} {Q : Set (ParabolicPoint (Euc n))}
    (c : ParabolicPoint (Euc n) → Real)
    (u : Real → Euc n → F)
    (hc : HolderWith Kc alpha (Q.restrict c))
    (hu : HolderWith Ku alpha
      (Q.restrict (fun p ↦ u p.time p.space)))
    (hcNorm : ∀ p, p ∈ Q → ‖c p‖ ≤ Bc)
    (huNorm : ∀ p, p ∈ Q → ‖u p.time p.space‖ ≤ Mu) :
    HolderWith (Bc * Ku + Mu * Kc) alpha
      (Q.restrict (parabolicPotentialTerm c u)) := by
  simpa only [Set.restrict_apply, parabolicPotentialTerm_apply] using
    holderWith_smul_of_norm_le hc hu
      (fun p ↦ hcNorm p.1 p.2) (fun p ↦ huNorm p.1 p.2)

omit [DecidableEq n] [Nonempty n] in
theorem norm_parabolicLowerOrderTerm_le
    {Q : Set (ParabolicPoint (Euc n))}
    (b : n → ParabolicPoint (Euc n) → Real)
    (c : ParabolicPoint (Euc n) → Real)
    (u : Real → Euc n → F) (Bb : n → NNReal) (Bc Mdu Mu : NNReal)
    (hb : ∀ i p, p ∈ Q → ‖b i p‖ ≤ Bb i)
    (hc : ∀ p, p ∈ Q → ‖c p‖ ≤ Bc)
    (hdu : ∀ p, p ∈ Q → ‖parabolicSpatialJet 1 u p‖ ≤ Mdu)
    (hu : ∀ p, p ∈ Q → ‖u p.time p.space‖ ≤ Mu)
    (p : ParabolicPoint (Euc n)) (hp : p ∈ Q) :
    ‖parabolicLowerOrderTerm b c u p‖ ≤
      parabolicLowerOrderSupConst Bb Bc Mdu Mu := by
  rw [parabolicLowerOrderTerm_apply, parabolicLowerOrderSupConst,
    NNReal.coe_add]
  exact (norm_add_le _ _).trans (add_le_add
    (norm_parabolicDriftTerm_le b u Bb Mdu hb hdu p hp)
    (norm_parabolicPotentialTerm_le c u Bc Mu hc hu p hp))

omit [DecidableEq n] [Nonempty n] in
theorem eSupNormOn_parabolicLowerOrderTerm_le
    {Q : Set (ParabolicPoint (Euc n))}
    (b : n → ParabolicPoint (Euc n) → Real)
    (c : ParabolicPoint (Euc n) → Real)
    (u : Real → Euc n → F) (Bb : n → NNReal) (Bc Mdu Mu : NNReal)
    (hb : ∀ i p, p ∈ Q → ‖b i p‖ ≤ Bb i)
    (hc : ∀ p, p ∈ Q → ‖c p‖ ≤ Bc)
    (hdu : ∀ p, p ∈ Q → ‖parabolicSpatialJet 1 u p‖ ≤ Mdu)
    (hu : ∀ p, p ∈ Q → ‖u p.time p.space‖ ≤ Mu) :
    eSupNormOn Q (parabolicLowerOrderTerm b c u) ≤
      parabolicLowerOrderSupConst Bb Bc Mdu Mu := by
  rw [eSupNormOn_le]
  intro p hp
  rw [ENNReal.ofReal_le_coe]
  exact norm_parabolicLowerOrderTerm_le b c u Bb Bc Mdu Mu
    hb hc hdu hu p hp

omit [DecidableEq n] [Nonempty n] in
theorem parabolicLowerOrderTerm_holderWith_restrict
    {alpha Kc Kdu Ku : NNReal} {Q : Set (ParabolicPoint (Euc n))}
    (b : n → ParabolicPoint (Euc n) → Real)
    (c : ParabolicPoint (Euc n) → Real)
    (u : Real → Euc n → F) (Kb Bb : n → NNReal) (Mdu Bc Mu : NNReal)
    (hb : ∀ i, HolderWith (Kb i) alpha (Q.restrict (b i)))
    (hc : HolderWith Kc alpha (Q.restrict c))
    (hdu : HolderWith Kdu alpha
      (Q.restrict (parabolicSpatialJet 1 u)))
    (hu : HolderWith Ku alpha
      (Q.restrict (fun p ↦ u p.time p.space)))
    (hbNorm : ∀ i p, p ∈ Q → ‖b i p‖ ≤ Bb i)
    (hcNorm : ∀ p, p ∈ Q → ‖c p‖ ≤ Bc)
    (hduNorm : ∀ p, p ∈ Q → ‖parabolicSpatialJet 1 u p‖ ≤ Mdu)
    (huNorm : ∀ p, p ∈ Q → ‖u p.time p.space‖ ≤ Mu) :
    HolderWith (parabolicLowerOrderHolderConst
      Kb Bb Kc Kdu Ku Mdu Bc Mu) alpha
      (Q.restrict (parabolicLowerOrderTerm b c u)) := by
  exact (parabolicDriftTerm_holderWith_restrict
    b u Kb Bb Mdu hb hbNorm hdu hduNorm).add
    (parabolicPotentialTerm_holderWith_restrict
      c u hc hu hcNorm huNorm)

section Schauder

variable [CompleteSpace F]

theorem parabolic_variable_coefficient_schauder_estimate_of_lower_order_source
    {alpha KL BL Klo Blo X : NNReal}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    {S T : Real} (hT : 0 ≤ T) (hTS : T < S)
    (a : n → n → ParabolicPoint (Euc n) → Real)
    (p0 : ParabolicPoint (Euc n))
    (hA : Matrix.PosDef (fun i j ↦ a i j p0))
    (b : n → ParabolicPoint (Euc n) → Real)
    (c : ParabolicPoint (Euc n) → Real)
    (u : Real → Euc n → F)
    (g : Real → BoundedContinuousFunction (Euc n) F)
    (hrep : u = fun t x ↦
      spdHeatDuh (fun i j ↦ a i j p0) hA t g x)
    (hgfrozen : Set.EqOn (fun p ↦ g p.time p.space)
      (parabolicFrozenMatrixOperator (fun i j ↦ a i j p0) u)
      (parabolicCylinder (Icc (0 : Real) S) Set.univ))
    (hsourceBound : eSupNormOn
      (parabolicCylinder (Icc (0 : Real) S) Set.univ)
      (parabolicNondivergenceOperator a b c u) ≤ BL)
    (hsourceHolder : HolderWith KL alpha
      ((parabolicCylinder (Icc (0 : Real) S) Set.univ).restrict
        (parabolicNondivergenceOperator a b c u)))
    (hloBound : eSupNormOn
      (parabolicCylinder (Icc (0 : Real) S) Set.univ)
      (parabolicLowerOrderTerm b c u) ≤ Blo)
    (hloHolder : HolderWith Klo alpha
      ((parabolicCylinder (Icc (0 : Real) S) Set.univ).restrict
        (parabolicLowerOrderTerm b c u)))
    (Ka omega : n → n → NNReal)
    (ha : ∀ i j, HolderWith (Ka i j) alpha
      ((parabolicCylinder (Icc (0 : Real) S) Set.univ).restrict (a i j)))
    (homega : ∀ i j p,
      p ∈ parabolicCylinder (Icc (0 : Real) S) Set.univ →
        ‖a i j p0 - a i j p‖ ≤ omega i j)
    (hu : eParabolicC2HolderGaugeOn alpha
      (parabolicCylinder (Icc (0 : Real) S) Set.univ) u ≤ X) :
    eParabolicC2HolderGaugeOn alpha
        (parabolicCylinder (Ioc (0 : Real) T) Set.univ) u ≤
      spdHeatPotentialSchauderConst (fun i j ↦ a i j p0) hA alpha
        ((KL + Klo) + X * parabolicMatrixFreezeHolderConst Ka omega)
        ((BL + Blo) + X * parabolicMatrixFreezeSupConst omega) T := by
  let Q : Set (ParabolicPoint (Euc n)) :=
    parabolicCylinder (Icc (0 : Real) S) Set.univ
  have hprincipalBound : eSupNormOn Q
      (parabolicVariableMatrixOperator a u) ≤ BL + Blo := by
    rw [parabolicVariableMatrixOperator_eq_nondivergenceOperator_add_lowerOrderTerm]
    exact (eSupNormOn_add_le Q
      (parabolicNondivergenceOperator a b c u)
      (parabolicLowerOrderTerm b c u)).trans
        (add_le_add hsourceBound hloBound)
  have hprincipalHolder : HolderWith (KL + Klo) alpha
      (Q.restrict (parabolicVariableMatrixOperator a u)) := by
    rw [parabolicVariableMatrixOperator_eq_nondivergenceOperator_add_lowerOrderTerm]
    exact hsourceHolder.add hloHolder
  exact parabolic_variable_coefficient_schauder_estimate_of_frozen_representation
    halpha0 halpha1 hT hTS a p0 hA u g hrep hgfrozen
    hprincipalBound hprincipalHolder Ka omega ha homega hu

theorem parabolic_nondivergence_schauder_estimate_of_frozen_representation
    {alpha KL BL Kc Kdu Ku Bc X : NNReal}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    {S T : Real} (hT : 0 ≤ T) (hTS : T < S)
    (a : n → n → ParabolicPoint (Euc n) → Real)
    (p0 : ParabolicPoint (Euc n))
    (hA : Matrix.PosDef (fun i j ↦ a i j p0))
    (b : n → ParabolicPoint (Euc n) → Real)
    (c : ParabolicPoint (Euc n) → Real)
    (u : Real → Euc n → F)
    (g : Real → BoundedContinuousFunction (Euc n) F)
    (hrep : u = fun t x ↦
      spdHeatDuh (fun i j ↦ a i j p0) hA t g x)
    (hgfrozen : Set.EqOn (fun p ↦ g p.time p.space)
      (parabolicFrozenMatrixOperator (fun i j ↦ a i j p0) u)
      (parabolicCylinder (Icc (0 : Real) S) Set.univ))
    (hsourceBound : eSupNormOn
      (parabolicCylinder (Icc (0 : Real) S) Set.univ)
      (parabolicNondivergenceOperator a b c u) ≤ BL)
    (hsourceHolder : HolderWith KL alpha
      ((parabolicCylinder (Icc (0 : Real) S) Set.univ).restrict
        (parabolicNondivergenceOperator a b c u)))
    (Kb Bb : n → NNReal) (Ka omega : n → n → NNReal)
    (hb : ∀ i, HolderWith (Kb i) alpha
      ((parabolicCylinder (Icc (0 : Real) S) Set.univ).restrict (b i)))
    (ha : ∀ i j, HolderWith (Ka i j) alpha
      ((parabolicCylinder (Icc (0 : Real) S) Set.univ).restrict (a i j)))
    (hc : HolderWith Kc alpha
      ((parabolicCylinder (Icc (0 : Real) S) Set.univ).restrict c))
    (hdu : HolderWith Kdu alpha
      ((parabolicCylinder (Icc (0 : Real) S) Set.univ).restrict
        (parabolicSpatialJet 1 u)))
    (huHolder : HolderWith Ku alpha
      ((parabolicCylinder (Icc (0 : Real) S) Set.univ).restrict
        (fun p ↦ u p.time p.space)))
    (hbNorm : ∀ i p,
      p ∈ parabolicCylinder (Icc (0 : Real) S) Set.univ →
        ‖b i p‖ ≤ Bb i)
    (hcNorm : ∀ p,
      p ∈ parabolicCylinder (Icc (0 : Real) S) Set.univ → ‖c p‖ ≤ Bc)
    (homega : ∀ i j p,
      p ∈ parabolicCylinder (Icc (0 : Real) S) Set.univ →
        ‖a i j p0 - a i j p‖ ≤ omega i j)
    (hu : eParabolicC2HolderGaugeOn alpha
      (parabolicCylinder (Icc (0 : Real) S) Set.univ) u ≤ X) :
    eParabolicC2HolderGaugeOn alpha
        (parabolicCylinder (Ioc (0 : Real) T) Set.univ) u ≤
      spdHeatPotentialSchauderConst (fun i j ↦ a i j p0) hA alpha
        ((KL + parabolicLowerOrderHolderConst
          Kb Bb Kc Kdu Ku X Bc X) +
            X * parabolicMatrixFreezeHolderConst Ka omega)
        ((BL + parabolicLowerOrderSupConst Bb Bc X X) +
          X * parabolicMatrixFreezeSupConst omega) T := by
  let Q : Set (ParabolicPoint (Euc n)) :=
    parabolicCylinder (Icc (0 : Real) S) Set.univ
  have hduNorm : ∀ p, p ∈ Q → ‖parabolicSpatialJet 1 u p‖ ≤ X :=
    fun p hp ↦ parabolicSpatialJet_norm_le hu (by omega) hp
  have huNorm : ∀ p, p ∈ Q → ‖u p.time p.space‖ ≤ X := by
    intro p hp
    have hzero := parabolicSpatialJet_norm_le hu (j := 0) (by omega) hp
    simpa only [parabolicSpatialJet, norm_iteratedFDeriv_zero] using hzero
  exact parabolic_variable_coefficient_schauder_estimate_of_lower_order_source
    (Klo := parabolicLowerOrderHolderConst Kb Bb Kc Kdu Ku X Bc X)
    (Blo := parabolicLowerOrderSupConst Bb Bc X X)
    halpha0 halpha1 hT hTS a p0 hA b c u g hrep hgfrozen
    hsourceBound hsourceHolder
    (eSupNormOn_parabolicLowerOrderTerm_le b c u Bb Bc X X
      hbNorm hcNorm hduNorm huNorm)
    (parabolicLowerOrderTerm_holderWith_restrict
      b c u Kb Bb X Bc X hb hc hdu huHolder
      hbNorm hcNorm hduNorm huNorm)
    Ka omega ha homega hu

theorem parabolic_nondivergence_schauder_estimate_of_small_freeze_defect
    {alpha KL BL Kc Kdu Ku Bc X : NNReal}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    {S T : Real} (hT : 0 ≤ T) (hTS : T < S)
    (a : n → n → ParabolicPoint (Euc n) → Real)
    (p0 : ParabolicPoint (Euc n))
    (hA : Matrix.PosDef (fun i j ↦ a i j p0))
    (b : n → ParabolicPoint (Euc n) → Real)
    (c : ParabolicPoint (Euc n) → Real)
    (u : Real → Euc n → F)
    (g : Real → BoundedContinuousFunction (Euc n) F)
    (hrep : u = fun t x ↦
      spdHeatDuh (fun i j ↦ a i j p0) hA t g x)
    (hgfrozen : Set.EqOn (fun p ↦ g p.time p.space)
      (parabolicFrozenMatrixOperator (fun i j ↦ a i j p0) u)
      (parabolicCylinder (Icc (0 : Real) S) Set.univ))
    (hsourceBound : eSupNormOn
      (parabolicCylinder (Icc (0 : Real) S) Set.univ)
      (parabolicNondivergenceOperator a b c u) ≤ BL)
    (hsourceHolder : HolderWith KL alpha
      ((parabolicCylinder (Icc (0 : Real) S) Set.univ).restrict
        (parabolicNondivergenceOperator a b c u)))
    (Kb Bb : n → NNReal) (Ka omega : n → n → NNReal)
    (hb : ∀ i, HolderWith (Kb i) alpha
      ((parabolicCylinder (Icc (0 : Real) S) Set.univ).restrict (b i)))
    (ha : ∀ i j, HolderWith (Ka i j) alpha
      ((parabolicCylinder (Icc (0 : Real) S) Set.univ).restrict (a i j)))
    (hc : HolderWith Kc alpha
      ((parabolicCylinder (Icc (0 : Real) S) Set.univ).restrict c))
    (hdu : HolderWith Kdu alpha
      ((parabolicCylinder (Icc (0 : Real) S) Set.univ).restrict
        (parabolicSpatialJet 1 u)))
    (huHolder : HolderWith Ku alpha
      ((parabolicCylinder (Icc (0 : Real) S) Set.univ).restrict
        (fun p ↦ u p.time p.space)))
    (hbNorm : ∀ i p,
      p ∈ parabolicCylinder (Icc (0 : Real) S) Set.univ →
        ‖b i p‖ ≤ Bb i)
    (hcNorm : ∀ p,
      p ∈ parabolicCylinder (Icc (0 : Real) S) Set.univ → ‖c p‖ ≤ Bc)
    (homega : ∀ i j p,
      p ∈ parabolicCylinder (Icc (0 : Real) S) Set.univ →
        ‖a i j p0 - a i j p‖ ≤ omega i j)
    (hu : eParabolicC2HolderGaugeOn alpha
      (parabolicCylinder (Icc (0 : Real) S) Set.univ) u ≤ X)
    (hX : (X : ENNReal) ≤ eParabolicC2HolderGaugeOn alpha
      (parabolicCylinder (Ioc (0 : Real) T) Set.univ) u)
    (hsmall : spdParabolicSchauderDefectConst
      (fun i j ↦ a i j p0) hA alpha Ka omega T < 1) :
    eParabolicC2HolderGaugeOn alpha
        (parabolicCylinder (Ioc (0 : Real) T) Set.univ) u ≤
      (spdHeatPotentialSchauderConst (fun i j ↦ a i j p0) hA alpha
        (KL + parabolicLowerOrderHolderConst
          Kb Bb Kc Kdu Ku X Bc X)
        (BL + parabolicLowerOrderSupConst Bb Bc X X) T /
        (1 - spdParabolicSchauderDefectConst
          (fun i j ↦ a i j p0) hA alpha Ka omega T) : NNReal) := by
  have hraw := parabolic_nondivergence_schauder_estimate_of_frozen_representation
    halpha0 halpha1 hT hTS a p0 hA b c u g hrep hgfrozen
    hsourceBound hsourceHolder Kb Bb Ka omega hb ha hc hdu huHolder
    hbNorm hcNorm homega hu
  exact parabolic_schauder_estimate_of_small_freeze_defect
    halpha1 hT (fun i j ↦ a i j p0) hA Ka omega u hraw hX hsmall

end Schauder

end DifferentialGeometry.Analysis.Parabolic.Euclidean

end
