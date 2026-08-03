import DifferentialGeometry.Analysis.Parabolic.Euclidean.ClassicalSchauder
import DifferentialGeometry.Analysis.Schauder.VariableCoefficient

noncomputable section

open Matrix Real Set
open scoped NNReal RealInnerProductSpace

namespace DifferentialGeometry.Analysis.Parabolic.Euclidean

open DifferentialGeometry.Analysis.Schauder

private abbrev Euc (n : Type*) := EuclideanSpace Real n

variable {n F : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
  [NormedAddCommGroup F] [NormedSpace Real F] [CompleteSpace F]

def parabolicCutoffFrozenSource
    (A : Matrix n n Real)
    (chi dtimeChi : Real → BoundedContinuousFunction (Euc n) Real)
    (dchi : Real →
      BoundedContinuousFunction (Euc n) (Euc n →L[Real] Real))
    (d2chi : Real → BoundedContinuousFunction (Euc n)
      (Euc n →L[Real] Euc n →L[Real] Real))
    (u dtimeU : Real → BoundedContinuousFunction (Euc n) F)
    (du : Real →
      BoundedContinuousFunction (Euc n) (Euc n →L[Real] F))
    (d2u : Real → BoundedContinuousFunction (Euc n)
      (Euc n →L[Real] Euc n →L[Real] F)) :
    Real → BoundedContinuousFunction (Euc n) F :=
  fun t ↦ cutoffTimeJet chi dtimeChi u dtimeU t -
    matrixLapBcf A (cutoffJet2 (chi t) (dchi t) (d2chi t)
      (u t) (du t) (d2u t))

omit [DecidableEq n] [Nonempty n] [CompleteSpace F] in
@[simp]
theorem parabolicCutoffFrozenSource_apply
    (A : Matrix n n Real)
    (chi dtimeChi : Real → BoundedContinuousFunction (Euc n) Real)
    (dchi : Real →
      BoundedContinuousFunction (Euc n) (Euc n →L[Real] Real))
    (d2chi : Real → BoundedContinuousFunction (Euc n)
      (Euc n →L[Real] Euc n →L[Real] Real))
    (u dtimeU : Real → BoundedContinuousFunction (Euc n) F)
    (du : Real →
      BoundedContinuousFunction (Euc n) (Euc n →L[Real] F))
    (d2u : Real → BoundedContinuousFunction (Euc n)
      (Euc n →L[Real] Euc n →L[Real] F))
    (t : Real) (x : Euc n) :
    parabolicCutoffFrozenSource A chi dtimeChi dchi d2chi
        u dtimeU du d2u t x =
      cutoffTimeJet chi dtimeChi u dtimeU t x -
        matrixLap A (cutoffJet2 (chi t) (dchi t) (d2chi t)
          (u t) (du t) (d2u t) x) := by
  simp only [parabolicCutoffFrozenSource,
    BoundedContinuousFunction.sub_apply, matrixLapBcf_apply]

theorem parabolic_variable_coefficient_schauder_estimate_of_cutoff_classical_solution
    {alpha Kf Bf X : NNReal}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    {S T : Real} (hT : 0 ≤ T) (hTS : T < S)
    (a : n → n → ParabolicPoint (Euc n) → Real)
    (p0 : ParabolicPoint (Euc n))
    (hA : Matrix.PosDef (fun i j ↦ a i j p0))
    (chi dtimeChi : Real → BoundedContinuousFunction (Euc n) Real)
    (dchi : Real →
      BoundedContinuousFunction (Euc n) (Euc n →L[Real] Real))
    (d2chi : Real → BoundedContinuousFunction (Euc n)
      (Euc n →L[Real] Euc n →L[Real] Real))
    (u dtimeU : Real → BoundedContinuousFunction (Euc n) F)
    (du : Real →
      BoundedContinuousFunction (Euc n) (Euc n →L[Real] F))
    (d2u : Real → BoundedContinuousFunction (Euc n)
      (Euc n →L[Real] Euc n →L[Real] F))
    (hchiTime : ∀ s ∈ Icc (0 : Real) S,
      HasDerivAt chi (dtimeChi s) s)
    (huTime : ∀ s ∈ Icc (0 : Real) S,
      HasDerivAt u (dtimeU s) s)
    (hchi : ∀ s ∈ Icc (0 : Real) S, ∀ x,
      HasFDerivAt (chi s : Euc n → Real) (dchi s x) x)
    (hdchi : ∀ s ∈ Icc (0 : Real) S, ∀ x,
      HasFDerivAt (dchi s : Euc n → Euc n →L[Real] Real)
        (d2chi s x) x)
    (hu : ∀ s ∈ Icc (0 : Real) S, ∀ x,
      HasFDerivAt (u s : Euc n → F) (du s x) x)
    (hdu : ∀ s ∈ Icc (0 : Real) S, ∀ x,
      HasFDerivAt (du s : Euc n → Euc n →L[Real] F) (d2u s x) x)
    (hchiCont : Continuous chi) (huCont : Continuous u)
    (hchi0 : chi 0 = 0)
    (hsourceBound : eSupNormOn
      (parabolicCylinder (Icc (0 : Real) S) Set.univ)
      (parabolicVariableMatrixOperator a
        (fun t x ↦ cutoffValue (chi t) (u t) x)) ≤ Bf)
    (hsourceHolder : HolderWith Kf alpha
      ((parabolicCylinder (Icc (0 : Real) S) Set.univ).restrict
        (parabolicVariableMatrixOperator a
          (fun t x ↦ cutoffValue (chi t) (u t) x))))
    (Ka omega : n → n → NNReal)
    (ha : ∀ i j, HolderWith (Ka i j) alpha
      ((parabolicCylinder (Icc (0 : Real) S) Set.univ).restrict (a i j)))
    (homega : ∀ i j p,
      p ∈ parabolicCylinder (Icc (0 : Real) S) Set.univ →
        ‖a i j p0 - a i j p‖ ≤ omega i j)
    (hcutoffGauge : eParabolicC2HolderGaugeOn alpha
      (parabolicCylinder (Icc (0 : Real) S) Set.univ)
      (fun t x ↦ cutoffValue (chi t) (u t) x) ≤ X) :
    eParabolicC2HolderGaugeOn alpha
        (parabolicCylinder (Ioc (0 : Real) T) Set.univ)
        (fun t x ↦ cutoffValue (chi t) (u t) x) ≤
      spdHeatPotentialSchauderConst (fun i j ↦ a i j p0) hA alpha
        (Kf + X * parabolicMatrixFreezeHolderConst Ka omega)
        (Bf + X * parabolicMatrixFreezeSupConst omega) T := by
  let w : Real → BoundedContinuousFunction (Euc n) F :=
    fun t ↦ cutoffValue (chi t) (u t)
  let dtimeW : Real → BoundedContinuousFunction (Euc n) F :=
    cutoffTimeJet chi dtimeChi u dtimeU
  let dw : Real →
      BoundedContinuousFunction (Euc n) (Euc n →L[Real] F) :=
    fun t ↦ cutoffJet1 (chi t) (dchi t) (u t) (du t)
  let d2w : Real → BoundedContinuousFunction (Euc n)
      (Euc n →L[Real] Euc n →L[Real] F) :=
    fun t ↦ cutoffJet2 (chi t) (dchi t) (d2chi t)
      (u t) (du t) (d2u t)
  let g := parabolicCutoffFrozenSource (fun i j ↦ a i j p0)
    chi dtimeChi dchi d2chi u dtimeU du d2u
  apply parabolic_variable_coefficient_schauder_estimate_of_classical_solution
    halpha0 halpha1 hT hTS a p0 hA w dtimeW g dw d2w
  · intro s hs
    exact cutoffValue_hasDerivAt chi dtimeChi u dtimeU s
      (hchiTime s hs) (huTime s hs)
  · intro s hs x
    exact cutoffValue_hasFDerivAt (chi s) (dchi s) (u s) (du s)
      (hchi s hs) (hu s hs) x
  · intro s hs x
    exact cutoffJet1_hasFDerivAt (chi s) (dchi s) (d2chi s)
      (u s) (du s) (d2u s) (hchi s hs) (hdchi s hs)
        (hu s hs) (hdu s hs) x
  · intro s x
    simp only [g, dtimeW, d2w, parabolicCutoffFrozenSource_apply]
  · exact hchiCont.smul huCont
  · ext x
    change chi 0 x • u 0 x = 0
    rw [hchi0]
    change (0 : Real) • u 0 x = (0 : F)
    exact zero_smul Real (u 0 x)
  · exact hsourceBound
  · exact hsourceHolder
  · exact ha
  · exact homega
  · exact hcutoffGauge

end DifferentialGeometry.Analysis.Parabolic.Euclidean

end
