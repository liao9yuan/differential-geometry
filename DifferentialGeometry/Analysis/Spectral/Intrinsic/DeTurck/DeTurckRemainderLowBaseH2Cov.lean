import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderLowBaseH2VB

/-!
# The `H²` covariant-arm class of the second-order low-base telescope

**Class 2** of the five-class capstone `selfLow_pair_h2`: the DeTurck--Lie
covariant-derivative edge against its refolded pair-trace partner.

The public residual identity `lieCov_residual`
(`RiemannCoefficientPalatiniRefold`) turns that edge into a *single* product

```
(-1) • app₂₆₂( lieCovPair gm , X ),
X = rsPerm(lieCovSigma)( Ext²( lieCovR4 T ) ),
```

so the whole class reduces to the `H²` jet of the fourth-covariant normal form
`lieCovR4 = -(s/2)·CurvF(T) - QuadF(gm)` and of its two-state difference.  The
`lieCovPair` factor is already public at `H²` (`LowBaseInternal.pairTrace_pair_h2`
/ `pairTrace_bdd_h2`, both `A`-free), so the new content is the `X` slot.

The `X` slot is built here in two layers.

* `armBddH2` / `armPairH2` for the connection arm (via the `s = 0` endo/section
  identity `bdConnDiffSection_eq_armSlotEndoCc_zero` and the public
  `connSec_self_h2` / `connSec_sub_tame`), `hatBddH2` / `hatPairH2` for the
  moving lowering correction (the public `lieOmega_bdd_h2` / `lieOmega_pair_h2`
  restated on `lrOmegaHat`), `curvBddH2` for the curvature head (linear in the
  state against the frozen kernels `lrRiemW1`, `lrRiemW2`), and `quadBddH2` /
  `quadPairH2` for the six permuted `arm ⊗ hat` blocks of `lrQuadF`.
* `r4BddH2` / `r4PairH2`, then `covXBddH2` / `covXPairH2` after the two slot
  extensions and the output-slot permutation.

The `X` slot carries an `A²` passenger (arm ~ `A` against hat ~ `A`), which is
inadmissible against a difference.  As in classes 3 and 4 the `A`-carrying
producers are therefore re-read at the interpolated third-jet size
`a = √(Cip·R·A4)` (`jetInterp3`), after which `(1+a)⁴ ≤ 8(1 + (Cip R A4)²)`
puts the whole excess into the single `A4`-linear arm (`amixScalar`).  The two
connection-difference pair moduli are fed with `D2 := D3`, legitimate since
`J2 (T-U) ≤ J3 (T-U)`.

Split out of `DeTurckRemainderLowBaseH2VB` to keep every file below the
source-size limit; the shared `H²` jet algebra lives there and is imported.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open Bundle Manifold Tensor0SBundle
open scoped BigOperators Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.PDE.DeTurck.RicciLinearization
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurckCoefficients
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
      [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

/-! ### The `lieCovR4` covariant arm at the `H²` level

Class 2 of the second-order telescope.  The public residual identity
`lieCov_residual` (Palatini) turns the DeTurck--Lie covariant-derivative edge
against its refolded pair-trace partner into the single product
`app₂₆₂(lieCovPair gm, X)` with `X = rsPerm(lieCovSigma)(Ext²(lieCovR4 T))`, so
the whole class reduces to the `H²` jet of `lieCovR4` and of its two-state
difference.  `lieCovR4 = -(s/2)·CurvF(T) - QuadF(gm)` is linear in `T` in its
curvature head and a product `arm ⊗ hat` in its quadratic head.

The `H¹` siblings of the transfer helpers below are `private` to
`DeTurckRemainderLowBaseLip`; they are re-established here at `H²`. -/

/-- Input-slot permutation is an `H²` jet isometry on `(0,s)` tensors. -/
theorem domH2
    (g : SmoothRiemannianMetric I M) {s : ℕ}
    (σ : Equiv.Perm (Fin s)) (S : SmoothCcTensor g 0 s) :
    lowJetSq (I := I) (M := M) g 2
        (domDomCongrSection (I := I) g σ S) =
      lowJetSq (I := I) (M := M) g 2 S := by
  unfold lowJetSq
  apply Finset.sum_congr rfl
  intro q _
  rw [SmoothCcTensor.norm_def,
    tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs,
    SmoothCcTensor.norm_def,
    tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs]
  apply MeasureTheory.integral_congr_ae
  exact Filter.Eventually.of_forall fun x =>
    riemannianFiberNormSq_iteratedCovGrad_domDomCongrSection
      (I := I) (M := M) g σ S q x

set_option linter.unusedVariables false in
/-- Input-slot permutation is additive. -/
theorem domSub
    (g : SmoothRiemannianMetric I M) {s : ℕ}
    (σ : Equiv.Perm (Fin s)) (A B : SmoothCcTensor g 0 s) :
    domDomCongrSection (I := I) g σ (A - B) =
      domDomCongrSection (I := I) g σ A -
        domDomCongrSection (I := I) g σ B := by
  apply smoothCcTensor_ext_of_unitModel (I := I) (M := M) g
  intro x
  have hsub : ∀ (P Q : SmoothCcTensor g 0 s),
      unitModel (I := I) (M := M) g s (P - Q) x =
        unitModel (I := I) (M := M) g s P x -
          unitModel (I := I) (M := M) g s Q x := by
    intro P Q
    simp only [unitModel]
    rw [SmoothCcTensor.toSection_sub]
    rfl
  rw [domDomCongrSection_unitModel, hsub A B]
  rw [hsub
    (domDomCongrSection (I := I) g σ A)
    (domDomCongrSection (I := I) g σ B)]
  rw [domDomCongrSection_unitModel, domDomCongrSection_unitModel]
  apply ContinuousMultilinearMap.ext
  intro v
  simp only [ContinuousMultilinearMap.sub_apply,
    ContinuousMultilinearMap.domDomCongr_apply]

/-- One step of the connection-arm slot tower: raising the arm index by one is a
slot extension composed with two index permutations. -/
theorem armSuccEq
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (A : ContMDiffSection I (E →L[ℝ] (E →L[ℝ] E)) ∞
      (fun x : M => TangentSpace I x →L[ℝ]
        (TangentSpace I x →L[ℝ] TangentSpace I x))) :
    armSlotEndoCc (I := I) (M := M) g (s + 1) A =
      reindexCoeffGen (I := I) (M := M) g (s + 1 + 1) (s + 1 + 1 + 1)
        (rsDomDomCongrSection (I := I) (M := M) g
          (s + 1 + 1) (s + 1 + 1 + 1)
          ((Equiv.swap (0 : Fin (s + 1 + 1 + 1)) 1).trans
            (Equiv.swap (1 : Fin (s + 1 + 1 + 1)) 2))
          (slotExtend (I := I) (M := M) g (s + 1) (s + 1 + 1)
            (armSlotEndoCc (I := I) (M := M) g s A)))
        (Equiv.swap (0 : Fin (s + 1 + 1)) 1) := by
  classical
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply ContinuousLinearMap.ext
  intro D
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro m
  dsimp only
  rw [armSlotEndoCc_toSection]
  rw [show (TensorRSSpace.ofCLM
      (armSlotFib (I := I) (M := M) (s + 1) x (A x)) :
        Tensor0SSpace (s + 1 + 1) I x →L[ℝ]
          Tensor0SSpace (s + 1 + 1 + 1) I x) D =
    armSlotFib (I := I) (M := M) (s + 1) x (A x) D from rfl]
  rw [armSlotFib_apply_eval]
  rw [reindexCoeffGen_toSection, reindexCoeffFibGen_apply,
    rsDomDomCongrSection_toSection, toModel_rsDomDomCongr_apply,
    ContinuousMultilinearMap.domDomCongr_apply, slotExtend_toSection]
  rw [show (fun k : Fin (s + 1 + 1 + 1) =>
      m (((Equiv.swap (0 : Fin (s + 1 + 1 + 1)) 1).trans
        (Equiv.swap (1 : Fin (s + 1 + 1 + 1)) 2)) k)) =
      Fin.cons (m (((Equiv.swap (0 : Fin (s + 1 + 1 + 1)) 1).trans
          (Equiv.swap (1 : Fin (s + 1 + 1 + 1)) 2)) 0))
        (fun j : Fin (s + 1 + 1) =>
          m (((Equiv.swap (0 : Fin (s + 1 + 1 + 1)) 1).trans
            (Equiv.swap (1 : Fin (s + 1 + 1 + 1)) 2)) (Fin.succ j))) from by
    funext k
    refine Fin.cases ?_ (fun j => ?_) k
    · simp only [Fin.cons_zero]
    · simp only [Fin.cons_succ]]
  rw [slotExtendFib_apply_eval]
  rw [armSlotEndoCc_toSection]
  rw [show (TensorRSSpace.ofCLM
      (armSlotFib (I := I) (M := M) s x (A x)) :
        Tensor0SSpace (s + 1) I x →L[ℝ]
          Tensor0SSpace (s + 1 + 1) I x)
      ((tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) (s + 1) x)
        (Tensor0SSpace.ofModel
          (ContinuousMultilinearMap.domDomCongr
            (Equiv.swap (0 : Fin (s + 1 + 1)) 1)
            (Tensor0SSpace.toModel D)))
        (m (((Equiv.swap (0 : Fin (s + 1 + 1 + 1)) 1).trans
          (Equiv.swap (1 : Fin (s + 1 + 1 + 1)) 2)) 0))) =
    armSlotFib (I := I) (M := M) s x (A x)
      ((tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) (s + 1) x)
        (Tensor0SSpace.ofModel
          (ContinuousMultilinearMap.domDomCongr
            (Equiv.swap (0 : Fin (s + 1 + 1)) 1)
            (Tensor0SSpace.toModel D)))
        (m (((Equiv.swap (0 : Fin (s + 1 + 1 + 1)) 1).trans
          (Equiv.swap (1 : Fin (s + 1 + 1 + 1)) 2)) 0))) from rfl]
  rw [armSlotFib_apply_eval]
  rw [slotInsertEndoFib_apply_eval, slotInsertEndoFib_apply_eval]
  simp only [TensorMultilinear.tensor0S_curry_apply_eval,
    Tensor0SSpace.toModel_ofModel, ContinuousMultilinearMap.domDomCongr_apply]
  congr 1
  funext k
  refine Fin.cases ?_ (fun k₁ => Fin.cases ?_ (fun k₂ => ?_) k₁) k
  · rfl
  · rfl
  · rfl

set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 1600000 in
/-- The connection-arm slot extension is additive. -/
theorem armSub
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (A B : ContMDiffSection I (E →L[ℝ] (E →L[ℝ] E)) ∞
      (fun x : M => TangentSpace I x →L[ℝ]
        (TangentSpace I x →L[ℝ] TangentSpace I x))) :
    armSlotEndoCc (I := I) (M := M) g s (A - B) =
      armSlotEndoCc (I := I) (M := M) g s A -
        armSlotEndoCc (I := I) (M := M) g s B := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply ContinuousLinearMap.ext
  intro D
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro m
  have hRHS : (show Tensor0SSpace (s + 1) I x →L[ℝ]
        Tensor0SSpace (s + 1 + 1) I x from
        (armSlotEndoCc (I := I) (M := M) g s A -
          armSlotEndoCc (I := I) (M := M) g s B).toSection x) D =
      armSlotFib (I := I) (M := M) s x (A x) D -
        armSlotFib (I := I) (M := M) s x (B x) D := by
    rw [show ((armSlotEndoCc (I := I) (M := M) g s A -
          armSlotEndoCc (I := I) (M := M) g s B).toSection x) =
        (armSlotEndoCc (I := I) (M := M) g s A).toSection x -
          (armSlotEndoCc (I := I) (M := M) g s B).toSection x from rfl]
    rfl
  have hLHS : (show Tensor0SSpace (s + 1) I x →L[ℝ]
        Tensor0SSpace (s + 1 + 1) I x from
        (armSlotEndoCc (I := I) (M := M) g s (A - B)).toSection x) D =
      armSlotFib (I := I) (M := M) s x ((A - B) x) D := rfl
  have hfib : armSlotFib (I := I) (M := M) s x (A x - B x) D =
      armSlotFib (I := I) (M := M) s x (A x) D -
        armSlotFib (I := I) (M := M) s x (B x) D := by
    apply Tensor0SSpace.toModel_injective
    apply ContinuousMultilinearMap.ext
    intro v
    dsimp only
    rw [Tensor0SSpace.toModel_sub, ContinuousMultilinearMap.sub_apply,
      armSlotFib_apply_eval, armSlotFib_apply_eval, armSlotFib_apply_eval,
      ContinuousLinearMap.sub_apply,
      slotInsertEndoFib_sub_left (I := I) (M := M) (s + 1) 0 x
        (A x (v 0)) (B x (v 0)),
      ContinuousLinearMap.sub_apply, Tensor0SSpace.toModel_sub,
      ContinuousMultilinearMap.sub_apply]
  rw [hLHS, hRHS, show ((A - B) x) = A x - B x from rfl, hfib]

/-- Raising the connection-arm index by one costs a single factor of the fibre
dimension in the `H²` jet. -/
theorem armSuccH2
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (A : ContMDiffSection I (E →L[ℝ] (E →L[ℝ] E)) ∞
      (fun x : M => TangentSpace I x →L[ℝ]
        (TangentSpace I x →L[ℝ] TangentSpace I x))) :
    lowJetSq (I := I) (M := M) g 2
        (armSlotEndoCc (I := I) (M := M) g (s + 1) A) ≤
      (Module.finrank ℝ E : ℝ) *
        lowJetSq (I := I) (M := M) g 2
          (armSlotEndoCc (I := I) (M := M) g s A) := by
  rw [armSuccEq (I := I) (M := M) g s A, reindexJet, rspermH2]
  exact slotH2 (I := I) (M := M) g (s + 1) (s + 1 + 1) _

/-- The second connection arm costs two factors of the fibre dimension. -/
theorem arm2H2
    (g : SmoothRiemannianMetric I M)
    (A : ContMDiffSection I (E →L[ℝ] (E →L[ℝ] E)) ∞
      (fun x : M => TangentSpace I x →L[ℝ]
        (TangentSpace I x →L[ℝ] TangentSpace I x))) :
    lowJetSq (I := I) (M := M) g 2
        (armSlotEndoCc (I := I) (M := M) g 2 A) ≤
      (Module.finrank ℝ E : ℝ) ^ 2 *
        lowJetSq (I := I) (M := M) g 2
          (armSlotEndoCc (I := I) (M := M) g 0 A) := by
  have hfr : (0 : ℝ) ≤ (Module.finrank ℝ E : ℝ) := Nat.cast_nonneg _
  calc
    lowJetSq (I := I) (M := M) g 2
        (armSlotEndoCc (I := I) (M := M) g 2 A) ≤
      (Module.finrank ℝ E : ℝ) *
        lowJetSq (I := I) (M := M) g 2
          (armSlotEndoCc (I := I) (M := M) g 1 A) :=
      armSuccH2 (I := I) (M := M) g 1 A
    _ ≤ (Module.finrank ℝ E : ℝ) *
        ((Module.finrank ℝ E : ℝ) *
          lowJetSq (I := I) (M := M) g 2
            (armSlotEndoCc (I := I) (M := M) g 0 A)) :=
      mul_le_mul_of_nonneg_left (armSuccH2 (I := I) (M := M) g 0 A) hfr
    _ = (Module.finrank ℝ E : ℝ) ^ 2 *
        lowJetSq (I := I) (M := M) g 2
          (armSlotEndoCc (I := I) (M := M) g 0 A) := by ring

set_option linter.unusedVariables false in
/-- **Single-state `H²` bound for the moving lowering correction.**  Restates
the public `lieOmega_bdd_h2` on `lrOmegaHat`, which is the same section under a
different (public) name. -/
theorem hatBddH2
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ B : ℝ → ℝ,
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B R) ∧
      ∀ (gT : SmoothRiemannianMetric I M)
        (T : SmoothCcTensor g 0 2)
        (hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        (hTtie : ∀ (x : M) (u v : TangentSpace I x),
          gT.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g T x u v)
        {δ : ℝ} (hδ_le : δ ≤ 1 / 3) (hδ0 : 0 ≤ δ)
        (hδT : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ)
        (R A : ℝ), 0 ≤ R → 0 ≤ A →
        lowJetSq (I := I) (M := M) g 2 T ≤ R ^ 2 →
        lowJetSq (I := I) (M := M) g 3 T ≤ A ^ 2 →
      lowJetSq (I := I) (M := M) g 2
          (lrOmegaHat (I := I) (M := M) g gT) ≤
        (B R * A) ^ 2 := by
  obtain ⟨B, hB, hbdd⟩ := lieOmega_bdd_h2 (I := I) (M := M) hDim g
  exact ⟨B, hB, fun gT T hT hTtie δ hδ_le hδ0 hδT hδZ R A hR hA hT2 hT3 =>
    hbdd gT T hT hTtie hδ_le hδ0 hδT hδZ R A hR hA hT2 hT3⟩

set_option linter.unusedVariables false in
/-- **Two-state `H²` modulus for the moving lowering correction.**  Restates the
public `lieOmega_pair_h2` on `lrOmegaHat`. -/
theorem hatPairH2
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ B0 B1 : ℝ → ℝ,
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B0 R) ∧
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B1 R) ∧
      ∀ (gT gU : SmoothRiemannianMetric I M)
        (T U : SmoothCcTensor g 0 2)
        (hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        (hU : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g U x u v =
            ccTensorBilin (I := I) g U x v u)
        (hTtie : ∀ (x : M) (u v : TangentSpace I x),
          gT.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g T x u v)
        (hUtie : ∀ (x : M) (u v : TangentSpace I x),
          gU.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g U x u v)
        {δ : ℝ} (hδ_le : δ ≤ 1 / 3) (hδ0 : 0 ≤ δ)
        (hδT : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (hδU : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g U) δ)
        (hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ)
        (R A D2 D3 : ℝ), 0 ≤ R → 0 ≤ A → 0 ≤ D2 → 0 ≤ D3 →
        lowJetSq (I := I) (M := M) g 2 T ≤ R ^ 2 →
        lowJetSq (I := I) (M := M) g 2 U ≤ R ^ 2 →
        lowJetSq (I := I) (M := M) g 3 T ≤ A ^ 2 →
        lowJetSq (I := I) (M := M) g 2 (T - U) ≤ D2 ^ 2 →
        lowJetSq (I := I) (M := M) g 3 (T - U) ≤ D3 ^ 2 →
      lowJetSq (I := I) (M := M) g 2
          (lrOmegaHat (I := I) (M := M) g gT -
            lrOmegaHat (I := I) (M := M) g gU) ≤
        (B0 R * D3 + B1 R * D2 + B1 R * A * D2) ^ 2 := by
  obtain ⟨B0, B1, hB0, hB1, hpair⟩ := lieOmega_pair_h2 (I := I) (M := M) hDim g
  exact ⟨B0, B1, hB0, hB1,
    fun gT gU T U hT hU hTtie hUtie δ hδ_le hδ0 hδT hδU hδZ
      R A D2 D3 hR hA hD2 hD3 hT2 hU2 hT3 hTU2 hTU3 =>
      hpair gT gU T U hT hU hTtie hUtie hδ_le hδ0 hδT hδU hδZ
        R A D2 D3 hR hA hD2 hD3 hT2 hU2 hT3 hTU2 hTU3⟩

omit [BoundarylessManifold I M] in
/-- Six-term jet splitting, hoisted so that the `lrQuadF` block bookkeeping
never reaches `linarith` with tensor-sized monomials. -/
theorem jetSix
    (g : SmoothRiemannianMetric I M) {r s : ℕ} (m : ℕ)
    (t1 t2 t3 t4 t5 t6 : SmoothCcTensor g r s) {K : ℝ}
    (h1 : lowJetSq (I := I) (M := M) g m t1 ≤ K)
    (h2 : lowJetSq (I := I) (M := M) g m t2 ≤ K)
    (h3 : lowJetSq (I := I) (M := M) g m t3 ≤ K)
    (h4 : lowJetSq (I := I) (M := M) g m t4 ≤ K)
    (h5 : lowJetSq (I := I) (M := M) g m t5 ≤ K)
    (h6 : lowJetSq (I := I) (M := M) g m t6 ≤ K) :
    lowJetSq (I := I) (M := M) g m (t1 + t2 + t3 + t4 + t5 + t6) ≤
      94 * K := by
  have a1 := jetAdd (I := I) (M := M) g m t1 t2
  have a2 := jetAdd (I := I) (M := M) g m (t1 + t2) t3
  have a3 := jetAdd (I := I) (M := M) g m (t1 + t2 + t3) t4
  have a4 := jetAdd (I := I) (M := M) g m (t1 + t2 + t3 + t4) t5
  have a5 := jetAdd (I := I) (M := M) g m (t1 + t2 + t3 + t4 + t5) t6
  linarith

omit [BoundarylessManifold I M] in
/-- `A²` sits inside the quartic envelope. -/
theorem envSq {A : ℝ} (hA : 0 ≤ A) : A ^ 2 ≤ (1 + A) ^ 4 := by
  have h1 : A ^ 2 ≤ (1 + A) ^ 2 := pow_le_pow_left₀ hA (by linarith) 2
  have h2 : (1 : ℝ) ≤ (1 + A) ^ 2 := by nlinarith
  calc A ^ 2 ≤ (1 + A) ^ 2 := h1
    _ = 1 * (1 + A) ^ 2 := (one_mul _).symm
    _ ≤ (1 + A) ^ 2 * (1 + A) ^ 2 :=
      mul_le_mul_of_nonneg_right h2 (sq_nonneg _)
    _ = (1 + A) ^ 4 := by ring

omit [BoundarylessManifold I M] in
/-- `A⁴` sits inside the quartic envelope. -/
theorem envQuart {A : ℝ} (hA : 0 ≤ A) : A ^ 4 ≤ (1 + A) ^ 4 :=
  pow_le_pow_left₀ hA (by linarith) 4

set_option linter.unusedVariables false in
/-- **Single-state `H²` bound for the second DeTurck connection arm.**  The arm
is `A`-sized (not `(1+A)`-sized): it is a pure connection difference, so the
sharp `wXi` bound applies through the `s = 0` endo/section identity. -/
theorem armBddH2
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ B : ℝ → ℝ,
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B R) ∧
      ∀ (gT : SmoothRiemannianMetric I M)
        (T : SmoothCcTensor g 0 2)
        (hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        (hTtie : ∀ (x : M) (u v : TangentSpace I x),
          gT.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g T x u v)
        {δ : ℝ} (hδ_le : δ ≤ 1 / 3) (hδ0 : 0 ≤ δ)
        (hδT : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ)
        (R A : ℝ), 0 ≤ R → 0 ≤ A →
        lowJetSq (I := I) (M := M) g 2 T ≤ R ^ 2 →
        lowJetSq (I := I) (M := M) g 3 T ≤ A ^ 2 →
      lowJetSq (I := I) (M := M) g 2
          (armSlotEndoCc (I := I) (M := M) g 2
            (bdConnPair (I := I) (M := M) g gT)) ≤
        ((Module.finrank ℝ E : ℝ) * B R * A) ^ 2 := by
  obtain ⟨Bs, hBs, hwSelf⟩ := wXiSelfTame (I := I) (M := M) hDim g
  refine ⟨Bs, hBs, ?_⟩
  intro gT T hT hTtie δ hδ_le hδ0 hδT hδZ R A hR hA hT2 hT3
  have hbase : armSlotEndoCc (I := I) (M := M) g 0
      (bdConnPair (I := I) (M := M) g gT) =
      connDiffSection (I := I) gT g :=
    (bdConnDiffSection_eq_armSlotEndoCc_zero
      (I := I) (M := M) g gT).symm
  have h0 : lowJetSq (I := I) (M := M) g 2
      (armSlotEndoCc (I := I) (M := M) g 0
        (bdConnPair (I := I) (M := M) g gT)) ≤
      (Bs R * A) ^ 2 := by
    rw [hbase, connSec_self_h2 (I := I) (M := M) g gT]
    exact hwSelf gT T hT hTtie hδ_le hδ0 hδT hδZ R A hR hA hT2 hT3
  calc
    lowJetSq (I := I) (M := M) g 2
        (armSlotEndoCc (I := I) (M := M) g 2
          (bdConnPair (I := I) (M := M) g gT)) ≤
      (Module.finrank ℝ E : ℝ) ^ 2 *
        lowJetSq (I := I) (M := M) g 2
          (armSlotEndoCc (I := I) (M := M) g 0
            (bdConnPair (I := I) (M := M) g gT)) :=
      arm2H2 (I := I) (M := M) g (bdConnPair (I := I) (M := M) g gT)
    _ ≤ (Module.finrank ℝ E : ℝ) ^ 2 * (Bs R * A) ^ 2 :=
      mul_le_mul_of_nonneg_left h0 (pow_nonneg (Nat.cast_nonneg _) 2)
    _ = ((Module.finrank ℝ E : ℝ) * Bs R * A) ^ 2 := by ring

set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 1600000 in
set_option linter.unusedVariables false in
/-- **Two-state `H²` modulus for the second DeTurck connection arm.**  Inherited
from the public `connSec_sub_tame` through the `s = 0` endo/section identity and
two slot extensions. -/
theorem armPairH2
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ B0 B1 : ℝ → ℝ,
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B0 R) ∧
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B1 R) ∧
      ∀ (gT gU : SmoothRiemannianMetric I M)
        (T U : SmoothCcTensor g 0 2)
        (hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        (hU : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g U x u v =
            ccTensorBilin (I := I) g U x v u)
        (hTtie : ∀ (x : M) (u v : TangentSpace I x),
          gT.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g T x u v)
        (hUtie : ∀ (x : M) (u v : TangentSpace I x),
          gU.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g U x u v)
        {δ : ℝ} (hδ_le : δ ≤ 1 / 3) (hδ0 : 0 ≤ δ)
        (hδT : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (hδU : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g U) δ)
        (R A D2 D3 : ℝ), 0 ≤ R → 0 ≤ A → 0 ≤ D2 → 0 ≤ D3 →
        lowJetSq (I := I) (M := M) g 2 U ≤ R ^ 2 →
        lowJetSq (I := I) (M := M) g 3 T ≤ A ^ 2 →
        lowJetSq (I := I) (M := M) g 2 (T - U) ≤ D2 ^ 2 →
        lowJetSq (I := I) (M := M) g 3 (T - U) ≤ D3 ^ 2 →
      lowJetSq (I := I) (M := M) g 2
          (armSlotEndoCc (I := I) (M := M) g 2
              (bdConnPair (I := I) (M := M) g gT) -
            armSlotEndoCc (I := I) (M := M) g 2
              (bdConnPair (I := I) (M := M) g gU)) ≤
        ((Module.finrank ℝ E : ℝ) * B0 R * D3 +
          (Module.finrank ℝ E : ℝ) * B1 R * D2 +
          (Module.finrank ℝ E : ℝ) * B1 R * A * D2) ^ 2 := by
  obtain ⟨B0, B1, hB0, hB1, hpair⟩ :=
    connSec_sub_tame (I := I) (M := M) hDim g
      (δ₀ := (1 : ℝ) / 3) (by norm_num) (by norm_num)
  refine ⟨B0, B1, hB0, hB1, ?_⟩
  intro gT gU T U hT hU hTtie hUtie δ hδ_le hδ0 hδT hδU
    R A D2 D3 hR hA hD2 hD3 hU2 hT3 hTU2 hTU3
  have hbT : armSlotEndoCc (I := I) (M := M) g 0
      (bdConnPair (I := I) (M := M) g gT) =
      connDiffSection (I := I) gT g :=
    (bdConnDiffSection_eq_armSlotEndoCc_zero
      (I := I) (M := M) g gT).symm
  have hbU : armSlotEndoCc (I := I) (M := M) g 0
      (bdConnPair (I := I) (M := M) g gU) =
      connDiffSection (I := I) gU g :=
    (bdConnDiffSection_eq_armSlotEndoCc_zero
      (I := I) (M := M) g gU).symm
  have h0 : lowJetSq (I := I) (M := M) g 2
      (armSlotEndoCc (I := I) (M := M) g 0
          (bdConnPair (I := I) (M := M) g gT) -
        armSlotEndoCc (I := I) (M := M) g 0
          (bdConnPair (I := I) (M := M) g gU)) ≤
      (B0 R * D3 + B1 R * D2 + B1 R * A * D2) ^ 2 := by
    rw [hbT, hbU]
    exact hpair gT gU T U hT hU hTtie hUtie
      hδ_le hδ0 hδT hδ_le hδ0 hδU
      R A D2 D3 hR hA hD2 hD3 hU2 hT3 hTU2 hTU3
  calc
    lowJetSq (I := I) (M := M) g 2
        (armSlotEndoCc (I := I) (M := M) g 2
            (bdConnPair (I := I) (M := M) g gT) -
          armSlotEndoCc (I := I) (M := M) g 2
            (bdConnPair (I := I) (M := M) g gU)) =
      lowJetSq (I := I) (M := M) g 2
        (armSlotEndoCc (I := I) (M := M) g 2
          (bdConnPair (I := I) (M := M) g gT -
            bdConnPair (I := I) (M := M) g gU)) := by
      rw [armSub]
    _ ≤ (Module.finrank ℝ E : ℝ) ^ 2 *
        lowJetSq (I := I) (M := M) g 2
          (armSlotEndoCc (I := I) (M := M) g 0
            (bdConnPair (I := I) (M := M) g gT -
              bdConnPair (I := I) (M := M) g gU)) :=
      arm2H2 (I := I) (M := M) g _
    _ = (Module.finrank ℝ E : ℝ) ^ 2 *
        lowJetSq (I := I) (M := M) g 2
          (armSlotEndoCc (I := I) (M := M) g 0
              (bdConnPair (I := I) (M := M) g gT) -
            armSlotEndoCc (I := I) (M := M) g 0
              (bdConnPair (I := I) (M := M) g gU)) := by
      rw [armSub]
    _ ≤ (Module.finrank ℝ E : ℝ) ^ 2 *
        (B0 R * D3 + B1 R * D2 + B1 R * A * D2) ^ 2 :=
      mul_le_mul_of_nonneg_left h0 (pow_nonneg (Nat.cast_nonneg _) 2)
    _ = ((Module.finrank ℝ E : ℝ) * B0 R * D3 +
        (Module.finrank ℝ E : ℝ) * B1 R * D2 +
        (Module.finrank ℝ E : ℝ) * B1 R * A * D2) ^ 2 := by ring

/-- The curvature head of `lieCovR4` is linear in the state. -/
theorem curvSub
    (g : SmoothRiemannianMetric I M) (T U : SmoothCcTensor g 0 2) :
    lrCurvF (I := I) (M := M) g T - lrCurvF (I := I) (M := M) g U =
      lrCurvF (I := I) (M := M) g (T - U) := by
  rw [lrCurvF, lrCurvF, lrCurvF, appCcRS_sub_right, appCcRS_sub_right]
  module

/-- **`H²` bound for the curvature head.**  `lrCurvF` contracts the state
against two frozen background curvature kernels, so its `H²` jet is controlled
by the state's `H²` jet with an `A`-free constant. -/
theorem curvBddH2
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (T : SmoothCcTensor g 0 2),
        lowJetSq (I := I) (M := M) g 2
            (lrCurvF (I := I) (M := M) g T) ≤
          C * lowJetSq (I := I) (M := M) g 2 T := by
  obtain ⟨C₀, hC₀, happ⟩ := appH2 (I := I) (M := M) hDim g 0 2 4
  refine ⟨2 * (C₀ * lowJetSq (I := I) (M := M) g 2
        (lrRiemW1 (I := I) (M := M) g) +
      C₀ * lowJetSq (I := I) (M := M) g 2
        (lrRiemW2 (I := I) (M := M) g)), ?_, ?_⟩
  · have h1 : 0 ≤ C₀ * lowJetSq (I := I) (M := M) g 2
        (lrRiemW1 (I := I) (M := M) g) :=
      mul_nonneg hC₀ (jetNn (I := I) (M := M) g _)
    have h2 : 0 ≤ C₀ * lowJetSq (I := I) (M := M) g 2
        (lrRiemW2 (I := I) (M := M) g) :=
      mul_nonneg hC₀ (jetNn (I := I) (M := M) g _)
    linarith
  intro T
  rw [lrCurvF]
  calc
    lowJetSq (I := I) (M := M) g 2
        (appCcRS (I := I) (M := M) g 0 2 4
            (lrRiemW1 (I := I) (M := M) g) T +
          appCcRS (I := I) (M := M) g 0 2 4
            (lrRiemW2 (I := I) (M := M) g) T) ≤
      2 * (lowJetSq (I := I) (M := M) g 2
          (appCcRS (I := I) (M := M) g 0 2 4
            (lrRiemW1 (I := I) (M := M) g) T) +
        lowJetSq (I := I) (M := M) g 2
          (appCcRS (I := I) (M := M) g 0 2 4
            (lrRiemW2 (I := I) (M := M) g) T)) :=
      jetAdd (I := I) (M := M) g 2 _ _
    _ ≤ 2 * (C₀ * lowJetSq (I := I) (M := M) g 2
            (lrRiemW1 (I := I) (M := M) g) *
          lowJetSq (I := I) (M := M) g 2 T +
        C₀ * lowJetSq (I := I) (M := M) g 2
            (lrRiemW2 (I := I) (M := M) g) *
          lowJetSq (I := I) (M := M) g 2 T) :=
      mul_le_mul_of_nonneg_left
        (add_le_add (happ _ T) (happ _ T)) (by norm_num)
    _ = 2 * (C₀ * lowJetSq (I := I) (M := M) g 2
          (lrRiemW1 (I := I) (M := M) g) +
        C₀ * lowJetSq (I := I) (M := M) g 2
          (lrRiemW2 (I := I) (M := M) g)) *
        lowJetSq (I := I) (M := M) g 2 T := by ring

/-- The six permuted blocks of `lrQuadF` obey a common jet bound. -/
theorem quadSixH2
    (g : SmoothRiemannianMetric I M)
    (X Y : SmoothCcTensor g 0 4) {K : ℝ}
    (hX : lowJetSq (I := I) (M := M) g 2 X ≤ K)
    (hY : lowJetSq (I := I) (M := M) g 2 Y ≤ K) :
    lowJetSq (I := I) (M := M) g 2
        (domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 4) 1) X + X +
          domDomCongrSection (I := I) g lrPermA Y +
          domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 4) 2) Y +
          domDomCongrSection (I := I) g lrPermB Y +
          domDomCongrSection (I := I) g lrPermC Y) ≤ 94 * K :=
  jetSix (I := I) (M := M) g 2 _ _ _ _ _ _
    (by rw [domH2]; exact hX) hX
    (by rw [domH2]; exact hY) (by rw [domH2]; exact hY)
    (by rw [domH2]; exact hY) (by rw [domH2]; exact hY)

/-- **`H²` bound for the quadratic head.**  `lrQuadF` is six permuted copies of
the product `arm ⊗ hat`. -/
theorem quadBddH2
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (gm : SmoothRiemannianMetric I M),
        lowJetSq (I := I) (M := M) g 2
            (lrQuadF (I := I) (M := M) g gm) ≤
          C * (lowJetSq (I := I) (M := M) g 2
                (armSlotEndoCc (I := I) (M := M) g 2
                  (bdConnPair (I := I) (M := M) g gm)) *
              lowJetSq (I := I) (M := M) g 2
                (lrOmegaHat (I := I) (M := M) g gm)) := by
  obtain ⟨Ca, hCa, happ⟩ := appH2 (I := I) (M := M) hDim g 0 3 4
  refine ⟨94 * Ca, by positivity, ?_⟩
  intro gm
  have hQB : lowJetSq (I := I) (M := M) g 2
      (lrQB (I := I) (M := M) g gm) ≤
      Ca * (lowJetSq (I := I) (M := M) g 2
            (armSlotEndoCc (I := I) (M := M) g 2
              (bdConnPair (I := I) (M := M) g gm)) *
          lowJetSq (I := I) (M := M) g 2
            (lrOmegaHat (I := I) (M := M) g gm)) := by
    rw [lrQB]
    refine (happ _ _).trans (le_of_eq ?_)
    ring
  have hQA : lowJetSq (I := I) (M := M) g 2
      (lrQA (I := I) (M := M) g gm) ≤
      Ca * (lowJetSq (I := I) (M := M) g 2
            (armSlotEndoCc (I := I) (M := M) g 2
              (bdConnPair (I := I) (M := M) g gm)) *
          lowJetSq (I := I) (M := M) g 2
            (lrOmegaHat (I := I) (M := M) g gm)) := by
    rw [lrQA]
    refine (happ _ _).trans (le_of_eq ?_)
    rw [domH2]
    ring
  rw [lrQuadF]
  refine (quadSixH2 (I := I) (M := M) g _ _ hQB hQA).trans (le_of_eq ?_)
  ring

/-- Telescoping of the `lrQB` block. -/
theorem quadTelB
    (g gT gU : SmoothRiemannianMetric I M) :
    lrQB (I := I) (M := M) g gT - lrQB (I := I) (M := M) g gU =
      appCcRS (I := I) (M := M) g 0 3 4
          (armSlotEndoCc (I := I) (M := M) g 2
            (bdConnPair (I := I) (M := M) g gU))
          (lrOmegaHat (I := I) (M := M) g gT -
            lrOmegaHat (I := I) (M := M) g gU) +
        appCcRS (I := I) (M := M) g 0 3 4
          (armSlotEndoCc (I := I) (M := M) g 2
              (bdConnPair (I := I) (M := M) g gT) -
            armSlotEndoCc (I := I) (M := M) g 2
              (bdConnPair (I := I) (M := M) g gU))
          (lrOmegaHat (I := I) (M := M) g gT) := by
  rw [lrQB, lrQB, appCcRS_sub_right, appCcRS_sub_left]
  module

/-- Telescoping of the `lrQA` block. -/
theorem quadTelA
    (g gT gU : SmoothRiemannianMetric I M) :
    lrQA (I := I) (M := M) g gT - lrQA (I := I) (M := M) g gU =
      appCcRS (I := I) (M := M) g 0 3 4
          (armSlotEndoCc (I := I) (M := M) g 2
            (bdConnPair (I := I) (M := M) g gU))
          (domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 3) 1)
            (lrOmegaHat (I := I) (M := M) g gT -
              lrOmegaHat (I := I) (M := M) g gU)) +
        appCcRS (I := I) (M := M) g 0 3 4
          (armSlotEndoCc (I := I) (M := M) g 2
              (bdConnPair (I := I) (M := M) g gT) -
            armSlotEndoCc (I := I) (M := M) g 2
              (bdConnPair (I := I) (M := M) g gU))
          (domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 3) 1)
            (lrOmegaHat (I := I) (M := M) g gT)) := by
  rw [lrQA, lrQA, domSub, appCcRS_sub_right, appCcRS_sub_left]
  module

set_option maxHeartbeats 1600000 in
/-- **Two-state `H²` modulus for the quadratic head.**  Both factors telescope,
so the difference is bounded by the two mixed products. -/
theorem quadPairH2
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (gT gU : SmoothRiemannianMetric I M),
        lowJetSq (I := I) (M := M) g 2
            (lrQuadF (I := I) (M := M) g gT -
              lrQuadF (I := I) (M := M) g gU) ≤
          C * (lowJetSq (I := I) (M := M) g 2
                  (armSlotEndoCc (I := I) (M := M) g 2
                    (bdConnPair (I := I) (M := M) g gU)) *
                lowJetSq (I := I) (M := M) g 2
                  (lrOmegaHat (I := I) (M := M) g gT -
                    lrOmegaHat (I := I) (M := M) g gU) +
              lowJetSq (I := I) (M := M) g 2
                  (armSlotEndoCc (I := I) (M := M) g 2
                      (bdConnPair (I := I) (M := M) g gT) -
                    armSlotEndoCc (I := I) (M := M) g 2
                      (bdConnPair (I := I) (M := M) g gU)) *
                lowJetSq (I := I) (M := M) g 2
                  (lrOmegaHat (I := I) (M := M) g gT)) := by
  obtain ⟨Ca, hCa, happ⟩ := appH2 (I := I) (M := M) hDim g 0 3 4
  refine ⟨188 * Ca, by positivity, ?_⟩
  intro gT gU
  have hQBd : lowJetSq (I := I) (M := M) g 2
      (lrQB (I := I) (M := M) g gT - lrQB (I := I) (M := M) g gU) ≤
      2 * Ca * (lowJetSq (I := I) (M := M) g 2
              (armSlotEndoCc (I := I) (M := M) g 2
                (bdConnPair (I := I) (M := M) g gU)) *
            lowJetSq (I := I) (M := M) g 2
              (lrOmegaHat (I := I) (M := M) g gT -
                lrOmegaHat (I := I) (M := M) g gU) +
          lowJetSq (I := I) (M := M) g 2
              (armSlotEndoCc (I := I) (M := M) g 2
                  (bdConnPair (I := I) (M := M) g gT) -
                armSlotEndoCc (I := I) (M := M) g 2
                  (bdConnPair (I := I) (M := M) g gU)) *
            lowJetSq (I := I) (M := M) g 2
              (lrOmegaHat (I := I) (M := M) g gT)) := by
    rw [quadTelB]
    refine (jetAdd (I := I) (M := M) g 2 _ _).trans ?_
    have e1 := happ
      (armSlotEndoCc (I := I) (M := M) g 2
        (bdConnPair (I := I) (M := M) g gU))
      (lrOmegaHat (I := I) (M := M) g gT -
        lrOmegaHat (I := I) (M := M) g gU)
    have e2 := happ
      (armSlotEndoCc (I := I) (M := M) g 2
          (bdConnPair (I := I) (M := M) g gT) -
        armSlotEndoCc (I := I) (M := M) g 2
          (bdConnPair (I := I) (M := M) g gU))
      (lrOmegaHat (I := I) (M := M) g gT)
    linarith
  have hQAd : lowJetSq (I := I) (M := M) g 2
      (lrQA (I := I) (M := M) g gT - lrQA (I := I) (M := M) g gU) ≤
      2 * Ca * (lowJetSq (I := I) (M := M) g 2
              (armSlotEndoCc (I := I) (M := M) g 2
                (bdConnPair (I := I) (M := M) g gU)) *
            lowJetSq (I := I) (M := M) g 2
              (lrOmegaHat (I := I) (M := M) g gT -
                lrOmegaHat (I := I) (M := M) g gU) +
          lowJetSq (I := I) (M := M) g 2
              (armSlotEndoCc (I := I) (M := M) g 2
                  (bdConnPair (I := I) (M := M) g gT) -
                armSlotEndoCc (I := I) (M := M) g 2
                  (bdConnPair (I := I) (M := M) g gU)) *
            lowJetSq (I := I) (M := M) g 2
              (lrOmegaHat (I := I) (M := M) g gT)) := by
    rw [quadTelA]
    refine (jetAdd (I := I) (M := M) g 2 _ _).trans ?_
    have e1 := happ
      (armSlotEndoCc (I := I) (M := M) g 2
        (bdConnPair (I := I) (M := M) g gU))
      (domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 3) 1)
        (lrOmegaHat (I := I) (M := M) g gT -
          lrOmegaHat (I := I) (M := M) g gU))
    have e2 := happ
      (armSlotEndoCc (I := I) (M := M) g 2
          (bdConnPair (I := I) (M := M) g gT) -
        armSlotEndoCc (I := I) (M := M) g 2
          (bdConnPair (I := I) (M := M) g gU))
      (domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 3) 1)
        (lrOmegaHat (I := I) (M := M) g gT))
    rw [domH2] at e1
    rw [domH2] at e2
    linarith
  have hsplit : lrQuadF (I := I) (M := M) g gT -
      lrQuadF (I := I) (M := M) g gU =
      domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 4) 1)
          (lrQB (I := I) (M := M) g gT - lrQB (I := I) (M := M) g gU) +
        (lrQB (I := I) (M := M) g gT - lrQB (I := I) (M := M) g gU) +
        domDomCongrSection (I := I) g lrPermA
          (lrQA (I := I) (M := M) g gT - lrQA (I := I) (M := M) g gU) +
        domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 4) 2)
          (lrQA (I := I) (M := M) g gT - lrQA (I := I) (M := M) g gU) +
        domDomCongrSection (I := I) g lrPermB
          (lrQA (I := I) (M := M) g gT - lrQA (I := I) (M := M) g gU) +
        domDomCongrSection (I := I) g lrPermC
          (lrQA (I := I) (M := M) g gT - lrQA (I := I) (M := M) g gU) := by
    simp only [lrQuadF, domSub]
    abel
  rw [hsplit]
  refine (quadSixH2 (I := I) (M := M) g _ _ hQBd hQAd).trans (le_of_eq ?_)
  ring

omit [BoundarylessManifold I M] in
/-- The quartic envelope dominates `1`. -/
theorem envOne {A : ℝ} (hA : 0 ≤ A) : (1 : ℝ) ≤ (1 + A) ^ 4 := by
  have h2 : (1 : ℝ) ≤ (1 + A) ^ 2 := by nlinarith
  calc (1 : ℝ) = 1 * 1 := (one_mul 1).symm
    _ ≤ (1 + A) ^ 2 * (1 + A) ^ 2 :=
      mul_le_mul h2 h2 zero_le_one (by positivity)
    _ = (1 + A) ^ 4 := by ring

set_option maxHeartbeats 1600000 in
set_option linter.unusedVariables false in
/-- **Single-state `H²` bound for the fourth-covariant normal form.**  Its
curvature head is `A`-linear and its quadratic head is `A²`-sized, so the whole
jet sits inside the quartic envelope. -/
theorem r4BddH2
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ D : ℝ → ℝ,
      (∀ R : ℝ, 0 ≤ R → 0 ≤ D R) ∧
      ∀ (T : SmoothCcTensor g 0 2)
        (hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        {δ : ℝ} (hδ_le : δ ≤ 1 / 3) (hδ0 : 0 ≤ δ)
        (hδT : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ)
        (R A : ℝ), 0 ≤ R → 0 ≤ A →
        lowJetSq (I := I) (M := M) g 2 T ≤ R ^ 2 →
        lowJetSq (I := I) (M := M) g 3 T ≤ A ^ 2 →
        ∀ {s : ℝ}, s ∈ Set.Icc (0 : ℝ) 1 →
      lowJetSq (I := I) (M := M) g 2
          (lieCovR4 (I := I) (M := M) g T hδT hδZ s) ≤
        D R * (1 + A) ^ 4 := by
  obtain ⟨Cc, hCc, hcurv⟩ := curvBddH2 (I := I) (M := M) hDim g
  obtain ⟨Cq, hCq, hquad⟩ := quadBddH2 (I := I) (M := M) hDim g
  obtain ⟨Bs, hBs, harmb⟩ := armBddH2 (I := I) (M := M) hDim g
  obtain ⟨Bt, hBt, hhatb⟩ := hatBddH2 (I := I) (M := M) hDim g
  set fr : ℝ := (Module.finrank ℝ E : ℝ) with hfrdef
  let D : ℝ → ℝ := fun R =>
    2 * Cc + 2 * Cq * ((fr * Bs R) ^ 2 * (Bt R) ^ 2)
  refine ⟨D, ?_, ?_⟩
  · intro R hR
    have h1 : (0 : ℝ) ≤ 2 * Cq * ((fr * Bs R) ^ 2 * (Bt R) ^ 2) :=
      mul_nonneg (by linarith) (by positivity)
    simp only [D]
    linarith
  intro T hT δ hδ_le hδ0 hδT hδZ R A hR hA hT2 hT3 s hs
  have hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le (by norm_num)
  set gm : SmoothRiemannianMetric I M :=
    realizedFam (I := I) g T 0 hδT hδZ s with hgm
  set P : SmoothCcTensor g 0 2 := s • T with hcP
  have hs_mem : s ∈ realizedSmallSet (δ := δ) (δ' := δ) :=
    Icc_subset_realizedSmallSet hδ_lt hδ_lt hs
  have hs2 : s ^ 2 ≤ (1 : ℝ) := by nlinarith [hs.1, hs.2]
  have hPsymm : ∀ (x : M) (u v : TangentSpace I x),
      ccTensorBilin (I := I) g P x u v =
        ccTensorBilin (I := I) g P x v u := by
    intro x u v
    simp only [hcP, ccTensorBilin_apply, ccTensorModel_smul,
      ContinuousMultilinearMap.smul_apply, smul_eq_mul]
    apply congrArg (fun z : ℝ => s * z)
    simpa only [ccTensorBilin_apply] using hT x u v
  have hPtie : ∀ (x : M) (u v : TangentSpace I x),
      gm.inner x u v =
        g.inner x u v + ccTensorBilinSymm (I := I) g P x u v := by
    intro x u v
    simpa only [hgm, hcP, convexPerturbation, smul_zero, zero_add] using
      realizedFam_inner_of_mem (I := I) g T 0 hδT hδZ hs_mem x u v
  have hδP : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g P) δ := by
    intro x u v
    have hraw := convexPerturbation_gFibreOpBound_abs
      (I := I) g T 0 hδT hδZ s x u v
    have heq : |1 - s| * δ + |s| * δ = δ := by
      rw [abs_of_nonneg (by linarith [hs.2] : (0 : ℝ) ≤ 1 - s),
        abs_of_nonneg hs.1]
      ring
    simpa only [hcP, convexPerturbation, smul_zero, zero_add, heq] using hraw
  have hP2 : lowJetSq (I := I) (M := M) g 2 P ≤ R ^ 2 := by
    rw [hcP, jetSmul]
    exact (mul_le_of_le_one_left
      (jetNn (I := I) (M := M) (m := 2) g T) hs2).trans hT2
  have hP3 : lowJetSq (I := I) (M := M) g 3 P ≤ A ^ 2 := by
    rw [hcP, jetSmul]
    exact (mul_le_of_le_one_left
      (jetNn (I := I) (M := M) (m := 3) g T) hs2).trans hT3
  have hCF : lowJetSq (I := I) (M := M) g 2
      (lrCurvF (I := I) (M := M) g T) ≤ Cc * A ^ 2 :=
    (hcurv T).trans (mul_le_mul_of_nonneg_left
      ((jetMono (I := I) (M := M) g (by norm_num : (2 : ℕ) ≤ 3) T).trans hT3)
      hCc)
  have harm : lowJetSq (I := I) (M := M) g 2
      (armSlotEndoCc (I := I) (M := M) g 2
        (bdConnPair (I := I) (M := M) g gm)) ≤ (fr * Bs R * A) ^ 2 :=
    harmb gm P hPsymm hPtie hδ_le hδ0 hδP hδZ R A hR hA hP2 hP3
  have hhat : lowJetSq (I := I) (M := M) g 2
      (lrOmegaHat (I := I) (M := M) g gm) ≤ (Bt R * A) ^ 2 :=
    hhatb gm P hPsymm hPtie hδ_le hδ0 hδP hδZ R A hR hA hP2 hP3
  have hQF : lowJetSq (I := I) (M := M) g 2
      (lrQuadF (I := I) (M := M) g gm) ≤
      Cq * ((fr * Bs R * A) ^ 2 * (Bt R * A) ^ 2) :=
    (hquad gm).trans (mul_le_mul_of_nonneg_left
      (mul_le_mul harm hhat (jetNn (I := I) (M := M) (m := 2) g _)
        (sq_nonneg _)) hCq)
  have hdecomp : lieCovR4 (I := I) (M := M) g T hδT hδZ s =
      (-(s / 2) : ℝ) • lrCurvF (I := I) (M := M) g T +
        (-1 : ℝ) • lrQuadF (I := I) (M := M) g gm := by
    rw [hgm, lieCovR4_eq (I := I) (M := M) g T hδT hδZ s]
    module
  have hs22 : (s / 2) ^ 2 ≤ 1 := by nlinarith [hs.1, hs.2]
  have hu0 : 0 ≤ lowJetSq (I := I) (M := M) g 2
      (lrCurvF (I := I) (M := M) g T) := jetNn (I := I) (M := M) g _
  have hfin : 2 * (Cc * A ^ 2 +
      Cq * ((fr * Bs R * A) ^ 2 * (Bt R * A) ^ 2)) ≤ D R * (1 + A) ^ 4 := by
    have e1 : Cc * A ^ 2 ≤ Cc * (1 + A) ^ 4 :=
      mul_le_mul_of_nonneg_left (envSq hA) hCc
    have e2 : Cq * ((fr * Bs R * A) ^ 2 * (Bt R * A) ^ 2) ≤
        Cq * ((fr * Bs R) ^ 2 * (Bt R) ^ 2 * (1 + A) ^ 4) := by
      refine mul_le_mul_of_nonneg_left ?_ hCq
      have hre : (fr * Bs R * A) ^ 2 * (Bt R * A) ^ 2 =
          (fr * Bs R) ^ 2 * (Bt R) ^ 2 * A ^ 4 := by ring
      rw [hre]
      exact mul_le_mul_of_nonneg_left (envQuart hA)
        (by positivity)
    have heq : D R * (1 + A) ^ 4 =
        2 * (Cc * (1 + A) ^ 4) +
          2 * (Cq * ((fr * Bs R) ^ 2 * (Bt R) ^ 2 * (1 + A) ^ 4)) := by
      simp only [D]
      ring
    rw [heq]
    linarith
  calc
    lowJetSq (I := I) (M := M) g 2
        (lieCovR4 (I := I) (M := M) g T hδT hδZ s) =
      lowJetSq (I := I) (M := M) g 2
        ((-(s / 2) : ℝ) • lrCurvF (I := I) (M := M) g T +
          (-1 : ℝ) • lrQuadF (I := I) (M := M) g gm) := by
      rw [hdecomp]
    _ ≤ 2 * (lowJetSq (I := I) (M := M) g 2
          ((-(s / 2) : ℝ) • lrCurvF (I := I) (M := M) g T) +
        lowJetSq (I := I) (M := M) g 2
          ((-1 : ℝ) • lrQuadF (I := I) (M := M) g gm)) :=
      jetAdd (I := I) (M := M) g 2 _ _
    _ = 2 * ((-(s / 2)) ^ 2 * lowJetSq (I := I) (M := M) g 2
          (lrCurvF (I := I) (M := M) g T) +
        (-1 : ℝ) ^ 2 * lowJetSq (I := I) (M := M) g 2
          (lrQuadF (I := I) (M := M) g gm)) := by
      rw [jetSmul, jetSmul]
    _ ≤ 2 * (Cc * A ^ 2 +
        Cq * ((fr * Bs R * A) ^ 2 * (Bt R * A) ^ 2)) := by
      have h1 : (-(s / 2)) ^ 2 * lowJetSq (I := I) (M := M) g 2
          (lrCurvF (I := I) (M := M) g T) ≤ Cc * A ^ 2 := by
        have hle : (-(s / 2)) ^ 2 * lowJetSq (I := I) (M := M) g 2
            (lrCurvF (I := I) (M := M) g T) ≤
            1 * lowJetSq (I := I) (M := M) g 2
              (lrCurvF (I := I) (M := M) g T) := by
          have hss : (-(s / 2)) ^ 2 = (s / 2) ^ 2 := by ring
          rw [hss]
          exact mul_le_mul_of_nonneg_right hs22 hu0
        rw [one_mul] at hle
        exact hle.trans hCF
      have h2 : (-1 : ℝ) ^ 2 * lowJetSq (I := I) (M := M) g 2
          (lrQuadF (I := I) (M := M) g gm) ≤
          Cq * ((fr * Bs R * A) ^ 2 * (Bt R * A) ^ 2) := by
        have hvv : ((-1 : ℝ) ^ 2 * lowJetSq (I := I) (M := M) g 2
            (lrQuadF (I := I) (M := M) g gm)) =
            lowJetSq (I := I) (M := M) g 2
              (lrQuadF (I := I) (M := M) g gm) := by ring
        rw [hvv]
        exact hQF
      linarith
    _ ≤ D R * (1 + A) ^ 4 := hfin

set_option maxHeartbeats 3200000 in
set_option linter.unusedVariables false in
/-- **Two-state `H²` modulus for the fourth-covariant normal form.**  The
curvature head is linear, hence contributes only the third-jet difference; the
quadratic head telescopes into `arm ⊗ Δhat` and `Δarm ⊗ hat`, both of which fold
through `pairFold3` into the quartic envelope times `D3²`. -/
theorem r4PairH2
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ C : ℝ → ℝ,
      (∀ R : ℝ, 0 ≤ R → 0 ≤ C R) ∧
      ∀ (T U : SmoothCcTensor g 0 2)
        (hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        (hU : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g U x u v =
            ccTensorBilin (I := I) g U x v u)
        {δ : ℝ} (hδ_le : δ ≤ 1 / 3) (hδ0 : 0 ≤ δ)
        (hδT : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (hδU : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g U) δ)
        (hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ)
        (R A D3 : ℝ), 0 ≤ R → 0 ≤ A → 0 ≤ D3 →
        lowJetSq (I := I) (M := M) g 2 T ≤ R ^ 2 →
        lowJetSq (I := I) (M := M) g 2 U ≤ R ^ 2 →
        lowJetSq (I := I) (M := M) g 3 T ≤ A ^ 2 →
        lowJetSq (I := I) (M := M) g 3 U ≤ A ^ 2 →
        lowJetSq (I := I) (M := M) g 3 (T - U) ≤ D3 ^ 2 →
        ∀ {s : ℝ}, s ∈ Set.Icc (0 : ℝ) 1 →
      lowJetSq (I := I) (M := M) g 2
          (lieCovR4 (I := I) (M := M) g T hδT hδZ s -
            lieCovR4 (I := I) (M := M) g U hδU hδZ s) ≤
        C R * ((1 + A) ^ 4 * D3 ^ 2) := by
  obtain ⟨Cc, hCc, hcurv⟩ := curvBddH2 (I := I) (M := M) hDim g
  obtain ⟨Cq, hCq, hquadp⟩ := quadPairH2 (I := I) (M := M) hDim g
  obtain ⟨Bs, hBs, harmb⟩ := armBddH2 (I := I) (M := M) hDim g
  obtain ⟨Bt, hBt, hhatb⟩ := hatBddH2 (I := I) (M := M) hDim g
  obtain ⟨A0, A1, hA0, hA1, harmp⟩ := armPairH2 (I := I) (M := M) hDim g
  obtain ⟨W0, W1, hW0, hW1, hhatp⟩ := hatPairH2 (I := I) (M := M) hDim g
  set fr : ℝ := (Module.finrank ℝ E : ℝ) with hfrdef
  have hfr : 0 ≤ fr := Nat.cast_nonneg _
  let Mh : ℝ → ℝ := fun R => 2 * (W0 R + W1 R) ^ 2 + 2 * (W1 R) ^ 2
  let Ma : ℝ → ℝ := fun R =>
    2 * (fr * A0 R + fr * A1 R) ^ 2 + 2 * (fr * A1 R) ^ 2
  let Kq : ℝ → ℝ := fun R =>
    (fr * Bs R) ^ 2 * Mh R + Ma R * (Bt R) ^ 2
  let C : ℝ → ℝ := fun R => 2 * Cc + 2 * (Cq * Kq R)
  have hMh : ∀ R : ℝ, 0 ≤ R → 0 ≤ Mh R := fun R hR => by
    simp only [Mh]
    positivity
  have hMa : ∀ R : ℝ, 0 ≤ R → 0 ≤ Ma R := fun R hR => by
    simp only [Ma]
    positivity
  have hKq : ∀ R : ℝ, 0 ≤ R → 0 ≤ Kq R := fun R hR => by
    have h1 : (0 : ℝ) ≤ (fr * Bs R) ^ 2 * Mh R :=
      mul_nonneg (sq_nonneg _) (hMh R hR)
    have h2 : (0 : ℝ) ≤ Ma R * (Bt R) ^ 2 :=
      mul_nonneg (hMa R hR) (sq_nonneg _)
    simp only [Kq]
    linarith
  refine ⟨C, ?_, ?_⟩
  · intro R hR
    have h1 : (0 : ℝ) ≤ Cq * Kq R := mul_nonneg hCq (hKq R hR)
    simp only [C]
    linarith
  intro T U hT hU δ hδ_le hδ0 hδT hδU hδZ R A D3 hR hA hD3
    hT2 hU2 hT3 hU3 hTU3 s hs
  have hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le (by norm_num)
  set gmT : SmoothRiemannianMetric I M :=
    realizedFam (I := I) g T 0 hδT hδZ s with hgmT
  set gmU : SmoothRiemannianMetric I M :=
    realizedFam (I := I) g U 0 hδU hδZ s with hgmU
  set P : SmoothCcTensor g 0 2 := s • T with hcP
  set Q : SmoothCcTensor g 0 2 := s • U with hcQ
  have hs_mem : s ∈ realizedSmallSet (δ := δ) (δ' := δ) :=
    Icc_subset_realizedSmallSet hδ_lt hδ_lt hs
  have hs2 : s ^ 2 ≤ (1 : ℝ) := by nlinarith [hs.1, hs.2]
  have hPsymm : ∀ (x : M) (u v : TangentSpace I x),
      ccTensorBilin (I := I) g P x u v =
        ccTensorBilin (I := I) g P x v u := by
    intro x u v
    simp only [hcP, ccTensorBilin_apply, ccTensorModel_smul,
      ContinuousMultilinearMap.smul_apply, smul_eq_mul]
    apply congrArg (fun z : ℝ => s * z)
    simpa only [ccTensorBilin_apply] using hT x u v
  have hQsymm : ∀ (x : M) (u v : TangentSpace I x),
      ccTensorBilin (I := I) g Q x u v =
        ccTensorBilin (I := I) g Q x v u := by
    intro x u v
    simp only [hcQ, ccTensorBilin_apply, ccTensorModel_smul,
      ContinuousMultilinearMap.smul_apply, smul_eq_mul]
    apply congrArg (fun z : ℝ => s * z)
    simpa only [ccTensorBilin_apply] using hU x u v
  have hPtie : ∀ (x : M) (u v : TangentSpace I x),
      gmT.inner x u v =
        g.inner x u v + ccTensorBilinSymm (I := I) g P x u v := by
    intro x u v
    simpa only [hgmT, hcP, convexPerturbation, smul_zero, zero_add] using
      realizedFam_inner_of_mem (I := I) g T 0 hδT hδZ hs_mem x u v
  have hQtie : ∀ (x : M) (u v : TangentSpace I x),
      gmU.inner x u v =
        g.inner x u v + ccTensorBilinSymm (I := I) g Q x u v := by
    intro x u v
    simpa only [hgmU, hcQ, convexPerturbation, smul_zero, zero_add] using
      realizedFam_inner_of_mem (I := I) g U 0 hδU hδZ hs_mem x u v
  have hδP : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g P) δ := by
    intro x u v
    have hraw := convexPerturbation_gFibreOpBound_abs
      (I := I) g T 0 hδT hδZ s x u v
    have heq : |1 - s| * δ + |s| * δ = δ := by
      rw [abs_of_nonneg (by linarith [hs.2] : (0 : ℝ) ≤ 1 - s),
        abs_of_nonneg hs.1]
      ring
    simpa only [hcP, convexPerturbation, smul_zero, zero_add, heq] using hraw
  have hδQ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g Q) δ := by
    intro x u v
    have hraw := convexPerturbation_gFibreOpBound_abs
      (I := I) g U 0 hδU hδZ s x u v
    have heq : |1 - s| * δ + |s| * δ = δ := by
      rw [abs_of_nonneg (by linarith [hs.2] : (0 : ℝ) ≤ 1 - s),
        abs_of_nonneg hs.1]
      ring
    simpa only [hcQ, convexPerturbation, smul_zero, zero_add, heq] using hraw
  have hP2 : lowJetSq (I := I) (M := M) g 2 P ≤ R ^ 2 := by
    rw [hcP, jetSmul]
    exact (mul_le_of_le_one_left
      (jetNn (I := I) (M := M) (m := 2) g T) hs2).trans hT2
  have hQ2 : lowJetSq (I := I) (M := M) g 2 Q ≤ R ^ 2 := by
    rw [hcQ, jetSmul]
    exact (mul_le_of_le_one_left
      (jetNn (I := I) (M := M) (m := 2) g U) hs2).trans hU2
  have hP3 : lowJetSq (I := I) (M := M) g 3 P ≤ A ^ 2 := by
    rw [hcP, jetSmul]
    exact (mul_le_of_le_one_left
      (jetNn (I := I) (M := M) (m := 3) g T) hs2).trans hT3
  have hQ3 : lowJetSq (I := I) (M := M) g 3 Q ≤ A ^ 2 := by
    rw [hcQ, jetSmul]
    exact (mul_le_of_le_one_left
      (jetNn (I := I) (M := M) (m := 3) g U) hs2).trans hU3
  have hPQ3 : lowJetSq (I := I) (M := M) g 3 (P - Q) ≤ D3 ^ 2 := by
    have hPQ : P - Q = s • (T - U) := by rw [hcP, hcQ, smul_sub]
    rw [hPQ, jetSmul]
    exact (mul_le_of_le_one_left
      (jetNn (I := I) (M := M) (m := 3) g (T - U)) hs2).trans hTU3
  have hPQ2 : lowJetSq (I := I) (M := M) g 2 (P - Q) ≤ D3 ^ 2 :=
    (jetMono (I := I) (M := M) g (by norm_num : (2 : ℕ) ≤ 3) (P - Q)).trans hPQ3
  have hTU2 : lowJetSq (I := I) (M := M) g 2 (T - U) ≤ D3 ^ 2 :=
    (jetMono (I := I) (M := M) g (by norm_num : (2 : ℕ) ≤ 3) (T - U)).trans hTU3
  -- the envelope and the difference budget
  set pl2 : ℝ := (1 + A) ^ 2 with hpl2
  have hpl21 : (1 : ℝ) ≤ pl2 := by
    rw [hpl2]
    nlinarith
  have hpl20 : 0 ≤ pl2 := le_trans zero_le_one hpl21
  have hplA2 : A ^ 2 ≤ pl2 := by
    rw [hpl2]
    nlinarith
  have hd0 : (0 : ℝ) ≤ D3 ^ 2 := sq_nonneg _
  have hquart : pl2 * (pl2 * D3 ^ 2) = (1 + A) ^ 4 * D3 ^ 2 := by
    rw [hpl2]
    ring
  -- the four factor moduli
  have hCFd : lowJetSq (I := I) (M := M) g 2
      (lrCurvF (I := I) (M := M) g T -
        lrCurvF (I := I) (M := M) g U) ≤ Cc * D3 ^ 2 := by
    rw [curvSub]
    exact (hcurv (T - U)).trans (mul_le_mul_of_nonneg_left hTU2 hCc)
  have harmU : lowJetSq (I := I) (M := M) g 2
      (armSlotEndoCc (I := I) (M := M) g 2
        (bdConnPair (I := I) (M := M) g gmU)) ≤ (fr * Bs R * A) ^ 2 :=
    harmb gmU Q hQsymm hQtie hδ_le hδ0 hδQ hδZ R A hR hA hQ2 hQ3
  have hhatT : lowJetSq (I := I) (M := M) g 2
      (lrOmegaHat (I := I) (M := M) g gmT) ≤ (Bt R * A) ^ 2 :=
    hhatb gmT P hPsymm hPtie hδ_le hδ0 hδP hδZ R A hR hA hP2 hP3
  have hhatD : lowJetSq (I := I) (M := M) g 2
      (lrOmegaHat (I := I) (M := M) g gmT -
        lrOmegaHat (I := I) (M := M) g gmU) ≤ Mh R * (pl2 * D3 ^ 2) := by
    refine (hhatp gmT gmU P Q hPsymm hQsymm hPtie hQtie
      hδ_le hδ0 hδP hδQ hδZ R A D3 D3 hR hA hD3 hD3
      hP2 hQ2 hP3 hPQ2 hPQ3).trans ?_
    exact pairFold3 hpl21 hplA2 hd0 le_rfl
  have harmD : lowJetSq (I := I) (M := M) g 2
      (armSlotEndoCc (I := I) (M := M) g 2
          (bdConnPair (I := I) (M := M) g gmT) -
        armSlotEndoCc (I := I) (M := M) g 2
          (bdConnPair (I := I) (M := M) g gmU)) ≤
      Ma R * (pl2 * D3 ^ 2) := by
    refine (harmp gmT gmU P Q hPsymm hQsymm hPtie hQtie
      hδ_le hδ0 hδP hδQ R A D3 D3 hR hA hD3 hD3
      hQ2 hP3 hPQ2 hPQ3).trans ?_
    exact pairFold3 hpl21 hplA2 hd0 le_rfl
  -- the quadratic head
  have hQFd : lowJetSq (I := I) (M := M) g 2
      (lrQuadF (I := I) (M := M) g gmT -
        lrQuadF (I := I) (M := M) g gmU) ≤
      Cq * Kq R * ((1 + A) ^ 4 * D3 ^ 2) := by
    refine (hquadp gmT gmU).trans ?_
    have e1 : lowJetSq (I := I) (M := M) g 2
        (armSlotEndoCc (I := I) (M := M) g 2
          (bdConnPair (I := I) (M := M) g gmU)) *
        lowJetSq (I := I) (M := M) g 2
          (lrOmegaHat (I := I) (M := M) g gmT -
            lrOmegaHat (I := I) (M := M) g gmU) ≤
        (fr * Bs R) ^ 2 * Mh R * ((1 + A) ^ 4 * D3 ^ 2) := by
      have hstep := mul_le_mul harmU hhatD
        (jetNn (I := I) (M := M) (m := 2) g _) (sq_nonneg _)
      refine hstep.trans ?_
      have hre : (fr * Bs R * A) ^ 2 * (Mh R * (pl2 * D3 ^ 2)) =
          (fr * Bs R) ^ 2 * Mh R * (A ^ 2 * (pl2 * D3 ^ 2)) := by ring
      rw [hre]
      refine mul_le_mul_of_nonneg_left ?_
        (mul_nonneg (sq_nonneg _) (hMh R hR))
      rw [← hquart]
      exact mul_le_mul_of_nonneg_right hplA2
        (mul_nonneg hpl20 hd0)
    have e2 : lowJetSq (I := I) (M := M) g 2
        (armSlotEndoCc (I := I) (M := M) g 2
            (bdConnPair (I := I) (M := M) g gmT) -
          armSlotEndoCc (I := I) (M := M) g 2
            (bdConnPair (I := I) (M := M) g gmU)) *
        lowJetSq (I := I) (M := M) g 2
          (lrOmegaHat (I := I) (M := M) g gmT) ≤
        Ma R * (Bt R) ^ 2 * ((1 + A) ^ 4 * D3 ^ 2) := by
      have hstep := mul_le_mul harmD hhatT
        (jetNn (I := I) (M := M) (m := 2) g _)
        (mul_nonneg (hMa R hR) (mul_nonneg hpl20 hd0))
      refine hstep.trans ?_
      have hre : Ma R * (pl2 * D3 ^ 2) * (Bt R * A) ^ 2 =
          Ma R * (Bt R) ^ 2 * (A ^ 2 * (pl2 * D3 ^ 2)) := by ring
      rw [hre]
      refine mul_le_mul_of_nonneg_left ?_
        (mul_nonneg (hMa R hR) (sq_nonneg _))
      rw [← hquart]
      exact mul_le_mul_of_nonneg_right hplA2
        (mul_nonneg hpl20 hd0)
    have hsum : Cq * ((fr * Bs R) ^ 2 * Mh R * ((1 + A) ^ 4 * D3 ^ 2) +
        Ma R * (Bt R) ^ 2 * ((1 + A) ^ 4 * D3 ^ 2)) =
        Cq * Kq R * ((1 + A) ^ 4 * D3 ^ 2) := by
      simp only [Kq]
      ring
    calc
      Cq * (_ + _) ≤ Cq * ((fr * Bs R) ^ 2 * Mh R * ((1 + A) ^ 4 * D3 ^ 2) +
          Ma R * (Bt R) ^ 2 * ((1 + A) ^ 4 * D3 ^ 2)) :=
        mul_le_mul_of_nonneg_left (add_le_add e1 e2) hCq
      _ = Cq * Kq R * ((1 + A) ^ 4 * D3 ^ 2) := hsum
  -- assembly
  have hdecomp : lieCovR4 (I := I) (M := M) g T hδT hδZ s -
      lieCovR4 (I := I) (M := M) g U hδU hδZ s =
      (-(s / 2) : ℝ) • (lrCurvF (I := I) (M := M) g T -
          lrCurvF (I := I) (M := M) g U) +
        (-1 : ℝ) • (lrQuadF (I := I) (M := M) g gmT -
          lrQuadF (I := I) (M := M) g gmU) := by
    rw [hgmT, hgmU, lieCovR4_eq (I := I) (M := M) g T hδT hδZ s,
      lieCovR4_eq (I := I) (M := M) g U hδU hδZ s]
    module
  have hs22 : (s / 2) ^ 2 ≤ 1 := by nlinarith [hs.1, hs.2]
  have hcf0 : 0 ≤ lowJetSq (I := I) (M := M) g 2
      (lrCurvF (I := I) (M := M) g T -
        lrCurvF (I := I) (M := M) g U) := jetNn (I := I) (M := M) g _
  have hDenv : D3 ^ 2 ≤ (1 + A) ^ 4 * D3 ^ 2 := by
    calc D3 ^ 2 = 1 * D3 ^ 2 := (one_mul _).symm
      _ ≤ (1 + A) ^ 4 * D3 ^ 2 :=
        mul_le_mul_of_nonneg_right (envOne hA) hd0
  calc
    lowJetSq (I := I) (M := M) g 2
        (lieCovR4 (I := I) (M := M) g T hδT hδZ s -
          lieCovR4 (I := I) (M := M) g U hδU hδZ s) =
      lowJetSq (I := I) (M := M) g 2
        ((-(s / 2) : ℝ) • (lrCurvF (I := I) (M := M) g T -
            lrCurvF (I := I) (M := M) g U) +
          (-1 : ℝ) • (lrQuadF (I := I) (M := M) g gmT -
            lrQuadF (I := I) (M := M) g gmU)) := by
      rw [hdecomp]
    _ ≤ 2 * (lowJetSq (I := I) (M := M) g 2
          ((-(s / 2) : ℝ) • (lrCurvF (I := I) (M := M) g T -
            lrCurvF (I := I) (M := M) g U)) +
        lowJetSq (I := I) (M := M) g 2
          ((-1 : ℝ) • (lrQuadF (I := I) (M := M) g gmT -
            lrQuadF (I := I) (M := M) g gmU))) :=
      jetAdd (I := I) (M := M) g 2 _ _
    _ = 2 * ((-(s / 2)) ^ 2 * lowJetSq (I := I) (M := M) g 2
          (lrCurvF (I := I) (M := M) g T -
            lrCurvF (I := I) (M := M) g U) +
        (-1 : ℝ) ^ 2 * lowJetSq (I := I) (M := M) g 2
          (lrQuadF (I := I) (M := M) g gmT -
            lrQuadF (I := I) (M := M) g gmU)) := by
      rw [jetSmul, jetSmul]
    _ ≤ 2 * (Cc * D3 ^ 2 + Cq * Kq R * ((1 + A) ^ 4 * D3 ^ 2)) := by
      have h1 : (-(s / 2)) ^ 2 * lowJetSq (I := I) (M := M) g 2
          (lrCurvF (I := I) (M := M) g T -
            lrCurvF (I := I) (M := M) g U) ≤ Cc * D3 ^ 2 := by
        have hle : (-(s / 2)) ^ 2 * lowJetSq (I := I) (M := M) g 2
            (lrCurvF (I := I) (M := M) g T -
              lrCurvF (I := I) (M := M) g U) ≤
            1 * lowJetSq (I := I) (M := M) g 2
              (lrCurvF (I := I) (M := M) g T -
                lrCurvF (I := I) (M := M) g U) := by
          have hss : (-(s / 2)) ^ 2 = (s / 2) ^ 2 := by ring
          rw [hss]
          exact mul_le_mul_of_nonneg_right hs22 hcf0
        rw [one_mul] at hle
        exact hle.trans hCFd
      have h2 : (-1 : ℝ) ^ 2 * lowJetSq (I := I) (M := M) g 2
          (lrQuadF (I := I) (M := M) g gmT -
            lrQuadF (I := I) (M := M) g gmU) ≤
          Cq * Kq R * ((1 + A) ^ 4 * D3 ^ 2) := by
        have hvv : ((-1 : ℝ) ^ 2 * lowJetSq (I := I) (M := M) g 2
            (lrQuadF (I := I) (M := M) g gmT -
              lrQuadF (I := I) (M := M) g gmU)) =
            lowJetSq (I := I) (M := M) g 2
              (lrQuadF (I := I) (M := M) g gmT -
                lrQuadF (I := I) (M := M) g gmU) := by ring
        rw [hvv]
        exact hQFd
      linarith
    _ ≤ C R * ((1 + A) ^ 4 * D3 ^ 2) := by
      have e1 : Cc * D3 ^ 2 ≤ Cc * ((1 + A) ^ 4 * D3 ^ 2) :=
        mul_le_mul_of_nonneg_left hDenv hCc
      have heq : C R * ((1 + A) ^ 4 * D3 ^ 2) =
          2 * (Cc * ((1 + A) ^ 4 * D3 ^ 2)) +
            2 * (Cq * Kq R * ((1 + A) ^ 4 * D3 ^ 2)) := by
        simp only [C]
        ring
      rw [heq]
      linarith

set_option linter.unusedVariables false in
/-- **The `X`-slot of class 2, single state.**  The `lieCovR4` normal form is
extended into two extra slot pairs and its output slots are permuted; both
operations are `H²` jet transfers. -/
theorem covXBddH2
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ D : ℝ → ℝ,
      (∀ R : ℝ, 0 ≤ R → 0 ≤ D R) ∧
      ∀ (T : SmoothCcTensor g 0 2)
        (hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        {δ : ℝ} (hδ_le : δ ≤ 1 / 3) (hδ0 : 0 ≤ δ)
        (hδT : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ)
        (R A : ℝ), 0 ≤ R → 0 ≤ A →
        lowJetSq (I := I) (M := M) g 2 T ≤ R ^ 2 →
        lowJetSq (I := I) (M := M) g 3 T ≤ A ^ 2 →
        ∀ {s : ℝ}, s ∈ Set.Icc (0 : ℝ) 1 →
      lowJetSq (I := I) (M := M) g 2
          (rsDomDomCongrSection (I := I) (M := M) g 2 6 lieCovSigma
            (slotExtendIter (I := I) (M := M) g 0 4 2
              (lieCovR4 (I := I) (M := M) g T hδT hδZ s))) ≤
        D R * (1 + A) ^ 4 := by
  obtain ⟨Dr, hDr, hr4⟩ := r4BddH2 (I := I) (M := M) hDim g
  set fr : ℝ := (Module.finrank ℝ E : ℝ) with hfrdef
  have hfr : 0 ≤ fr := Nat.cast_nonneg _
  refine ⟨fun R => fr ^ 2 * Dr R, fun R hR => mul_nonneg (sq_nonneg _)
    (hDr R hR), ?_⟩
  intro T hT δ hδ_le hδ0 hδT hδZ R A hR hA hT2 hT3 s hs
  have hIter : slotExtendIter (I := I) (M := M) g 0 4 2
      (lieCovR4 (I := I) (M := M) g T hδT hδZ s) =
      slotExtend (I := I) (M := M) g 1 5
        (slotExtend (I := I) (M := M) g 0 4
          (lieCovR4 (I := I) (M := M) g T hδT hδZ s)) := rfl
  have hbase := hr4 T hT hδ_le hδ0 hδT hδZ R A hR hA hT2 hT3 hs
  calc
    lowJetSq (I := I) (M := M) g 2
        (rsDomDomCongrSection (I := I) (M := M) g 2 6 lieCovSigma
          (slotExtendIter (I := I) (M := M) g 0 4 2
            (lieCovR4 (I := I) (M := M) g T hδT hδZ s))) =
      lowJetSq (I := I) (M := M) g 2
        (slotExtend (I := I) (M := M) g 1 5
          (slotExtend (I := I) (M := M) g 0 4
            (lieCovR4 (I := I) (M := M) g T hδT hδZ s))) := by
      rw [hIter, rspermH2]
    _ ≤ fr * lowJetSq (I := I) (M := M) g 2
        (slotExtend (I := I) (M := M) g 0 4
          (lieCovR4 (I := I) (M := M) g T hδT hδZ s)) :=
      slotH2 (I := I) (M := M) g 1 5 _
    _ ≤ fr * (fr * lowJetSq (I := I) (M := M) g 2
        (lieCovR4 (I := I) (M := M) g T hδT hδZ s)) :=
      mul_le_mul_of_nonneg_left (slotH2 (I := I) (M := M) g 0 4 _) hfr
    _ ≤ fr * (fr * (Dr R * (1 + A) ^ 4)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hbase hfr) hfr
    _ = fr ^ 2 * Dr R * (1 + A) ^ 4 := by ring

set_option maxHeartbeats 1600000 in
set_option linter.unusedVariables false in
/-- **The `X`-slot of class 2, two states.**  Both transfers are additive, so
the difference reduces to the `lieCovR4` two-state modulus. -/
theorem covXPairH2
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ C : ℝ → ℝ,
      (∀ R : ℝ, 0 ≤ R → 0 ≤ C R) ∧
      ∀ (T U : SmoothCcTensor g 0 2)
        (hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        (hU : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g U x u v =
            ccTensorBilin (I := I) g U x v u)
        {δ : ℝ} (hδ_le : δ ≤ 1 / 3) (hδ0 : 0 ≤ δ)
        (hδT : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (hδU : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g U) δ)
        (hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ)
        (R A D3 : ℝ), 0 ≤ R → 0 ≤ A → 0 ≤ D3 →
        lowJetSq (I := I) (M := M) g 2 T ≤ R ^ 2 →
        lowJetSq (I := I) (M := M) g 2 U ≤ R ^ 2 →
        lowJetSq (I := I) (M := M) g 3 T ≤ A ^ 2 →
        lowJetSq (I := I) (M := M) g 3 U ≤ A ^ 2 →
        lowJetSq (I := I) (M := M) g 3 (T - U) ≤ D3 ^ 2 →
        ∀ {s : ℝ}, s ∈ Set.Icc (0 : ℝ) 1 →
      lowJetSq (I := I) (M := M) g 2
          (rsDomDomCongrSection (I := I) (M := M) g 2 6 lieCovSigma
              (slotExtendIter (I := I) (M := M) g 0 4 2
                (lieCovR4 (I := I) (M := M) g T hδT hδZ s)) -
            rsDomDomCongrSection (I := I) (M := M) g 2 6 lieCovSigma
              (slotExtendIter (I := I) (M := M) g 0 4 2
                (lieCovR4 (I := I) (M := M) g U hδU hδZ s))) ≤
        C R * ((1 + A) ^ 4 * D3 ^ 2) := by
  obtain ⟨Cr, hCr, hr4p⟩ := r4PairH2 (I := I) (M := M) hDim g
  set fr : ℝ := (Module.finrank ℝ E : ℝ) with hfrdef
  have hfr : 0 ≤ fr := Nat.cast_nonneg _
  refine ⟨fun R => fr ^ 2 * Cr R, fun R hR => mul_nonneg (sq_nonneg _)
    (hCr R hR), ?_⟩
  intro T U hT hU δ hδ_le hδ0 hδT hδU hδZ R A D3 hR hA hD3
    hT2 hU2 hT3 hU3 hTU3 s hs
  have hXsub :
      rsDomDomCongrSection (I := I) (M := M) g 2 6 lieCovSigma
          (slotExtendIter (I := I) (M := M) g 0 4 2
            (lieCovR4 (I := I) (M := M) g T hδT hδZ s)) -
        rsDomDomCongrSection (I := I) (M := M) g 2 6 lieCovSigma
          (slotExtendIter (I := I) (M := M) g 0 4 2
            (lieCovR4 (I := I) (M := M) g U hδU hδZ s)) =
      rsDomDomCongrSection (I := I) (M := M) g 2 6 lieCovSigma
        (slotExtend (I := I) (M := M) g 1 5
          (slotExtend (I := I) (M := M) g 0 4
            (lieCovR4 (I := I) (M := M) g T hδT hδZ s -
              lieCovR4 (I := I) (M := M) g U hδU hδZ s))) := by
    rw [← rspermSub, slotExtend_sub, slotExtend_sub]
    rfl
  have hbase := hr4p T U hT hU hδ_le hδ0 hδT hδU hδZ R A D3 hR hA hD3
    hT2 hU2 hT3 hU3 hTU3 hs
  rw [hXsub, rspermH2]
  calc
    lowJetSq (I := I) (M := M) g 2
        (slotExtend (I := I) (M := M) g 1 5
          (slotExtend (I := I) (M := M) g 0 4
            (lieCovR4 (I := I) (M := M) g T hδT hδZ s -
              lieCovR4 (I := I) (M := M) g U hδU hδZ s))) ≤
      fr * lowJetSq (I := I) (M := M) g 2
        (slotExtend (I := I) (M := M) g 0 4
          (lieCovR4 (I := I) (M := M) g T hδT hδZ s -
            lieCovR4 (I := I) (M := M) g U hδU hδZ s)) :=
      slotH2 (I := I) (M := M) g 1 5 _
    _ ≤ fr * (fr * lowJetSq (I := I) (M := M) g 2
        (lieCovR4 (I := I) (M := M) g T hδT hδZ s -
          lieCovR4 (I := I) (M := M) g U hδU hδZ s)) :=
      mul_le_mul_of_nonneg_left (slotH2 (I := I) (M := M) g 0 4 _) hfr
    _ ≤ fr * (fr * (Cr R * ((1 + A) ^ 4 * D3 ^ 2))) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hbase hfr) hfr
    _ = fr ^ 2 * Cr R * ((1 + A) ^ 4 * D3 ^ 2) := by ring

/-- The refolded pair-trace partner of the Lie covariant-derivative edge, in the
fixed-permutation normal form consumed by `lieCov_residual`. -/
theorem edgeEq
    (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    {δ : ℝ}
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) δ)
    (s : ℝ) :
    edgeLiePairFam (I := I) (M := M) g T hδ hδZ
        lieRefoldQ lieRefoldEps s =
      deTurckLieCovDerivRefoldPairTraceFamily (I := I) (M := M)
        g T hδ hδZ
          ![Equiv.swap (0 : Fin 4) 1 * Equiv.swap (0 : Fin 4) 2,
            Equiv.swap (2 : Fin 4) 3 * Equiv.swap (1 : Fin 4) 2 *
              Equiv.swap (0 : Fin 4) 1,
            Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3]
          ![(-1 : ℝ), -1, 1] s := rfl

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1000000 in
set_option linter.unusedVariables false in
/-- **Class 2 of the second-order five-class telescope** — the DeTurck--Lie
covariant-derivative edge against its refolded pair-trace partner obeys the
admissible modulus
`(B0 R · (1+A) · (D4 + D3 + D2 + N) + B1 R · A4 · (D3 + N))²`.

By `lieCov_residual` the edge is the single product
`(-1) • app₂₆₂(lieCovPair gm, X)` with `X = rsPerm(Ext²(lieCovR4 T))`.  The
`lieCovPair` factor is `A`-free at `H²` (`pairTrace_bdd_h2`) and its difference
is purely spectral (`pairTrace_pair_h2`); the `X` factor is `A²`-sized
(`covXBddH2`) and its difference is `(1+A)⁴·D3²`-sized (`covXPairH2`).  The
`A²` passenger is inadmissible against a difference, so — exactly as in classes
3 and 4 — both states are re-read at the interpolated third-jet size
`a = √(Cip·R·A4)` (`jetInterp3`), and `amixScalar` collapses `(1+a)⁴` into the
single `A4`-linear arm. -/
theorem lieCovH2Pair
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ ρ : ℝ, ∃ B0 B1 : ℝ → ℝ,
      0 < ρ ∧ (∀ R : ℝ, 0 ≤ R → 0 ≤ B0 R) ∧
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B1 R) ∧
      ∀ (T U : SmoothCcTensor g 0 2)
        (hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        (hU : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g U x u v =
            ccTensorBilin (I := I) g U x v u)
        {δ : ℝ} (hδ_le : δ ≤ 1 / 3) (hδ0 : 0 ≤ δ)
        (hδT : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (hδU : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g U) δ)
        (hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ)
        (R A A4 D2 D3 D4 N : ℝ),
        0 ≤ R → 0 ≤ A → 0 ≤ A4 → 0 ≤ D2 → 0 ≤ D3 → 0 ≤ D4 → 0 ≤ N →
        lowJetSq (I := I) (M := M) g 2 T ≤ R ^ 2 →
        lowJetSq (I := I) (M := M) g 2 U ≤ R ^ 2 →
        lowJetSq (I := I) (M := M) g 3 T ≤ A ^ 2 →
        lowJetSq (I := I) (M := M) g 3 U ≤ A ^ 2 →
        lowJetSq (I := I) (M := M) g 4 T ≤ A4 ^ 2 →
        lowJetSq (I := I) (M := M) g 4 U ≤ A4 ^ 2 →
        lowJetSq (I := I) (M := M) g 2 (T - U) ≤ D2 ^ 2 →
        lowJetSq (I := I) (M := M) g 3 (T - U) ≤ D3 ^ 2 →
        lowJetSq (I := I) (M := M) g 4 (T - U) ≤ D4 ^ 2 →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ ρ →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ ≤ ρ →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (T - U)‖ ≤ N →
        ∀ {s : ℝ}, s ∈ Set.Icc (0 : ℝ) 1 →
      lowJetSq (I := I) (M := M) g 2
          ((deTurckLieCovDerivArmField (I := I) (M := M) g
              (realizedFam (I := I) g T 0 hδT hδZ s) g -
            edgeLiePairFam (I := I) (M := M) g T hδT hδZ
              lieRefoldQ lieRefoldEps s) -
          (deTurckLieCovDerivArmField (I := I) (M := M) g
              (realizedFam (I := I) g U 0 hδU hδZ s) g -
            edgeLiePairFam (I := I) (M := M) g U hδU hδZ
              lieRefoldQ lieRefoldEps s)) ≤
        (B0 R * (1 + A) * (D4 + D3 + D2 + N) +
          B1 R * A4 * (D3 + N)) ^ 2 := by
  obtain ⟨Ca, hCa, happ⟩ := appH2 (I := I) (M := M) hDim g 2 6 2
  obtain ⟨ρp, Cp, hρp, hCp, hlcvp⟩ :=
    LowBaseInternal.pairTrace_pair_h2 (I := I) (M := M) hDim g
  obtain ⟨ρb, Bp, hρb, hBp, hlcvb⟩ :=
    LowBaseInternal.pairTrace_bdd_h2 (I := I) (M := M) hDim g
  obtain ⟨Dx, hDx, hcovb⟩ := covXBddH2 (I := I) (M := M) hDim g
  obtain ⟨Cx, hCx, hcovp⟩ := covXPairH2 (I := I) (M := M) hDim g
  obtain ⟨Cip, hCip, hinterp⟩ := jetInterp3 (I := I) (M := M) g 2
  let Bh : ℝ → ℝ := fun R => 2 * (Ca * Cp ^ 2 * Dx R + Ca * Bp ^ 2 * Cx R)
  let B0 : ℝ → ℝ := fun R => Real.sqrt (8 * Bh R)
  let B1 : ℝ → ℝ := fun R => Real.sqrt (8 * Bh R) * Cip * R
  have hBhnn : ∀ R : ℝ, 0 ≤ R → 0 ≤ Bh R := by
    intro R hR
    have h1 : (0 : ℝ) ≤ Ca * Cp ^ 2 * Dx R :=
      mul_nonneg (mul_nonneg hCa (sq_nonneg _)) (hDx R hR)
    have h2 : (0 : ℝ) ≤ Ca * Bp ^ 2 * Cx R :=
      mul_nonneg (mul_nonneg hCa (sq_nonneg _)) (hCx R hR)
    simp only [Bh]
    linarith
  refine ⟨min ρp ρb, B0, B1, lt_min hρp hρb,
    fun R hR => by
      simp only [B0]
      exact Real.sqrt_nonneg _,
    fun R hR => by
      simp only [B1]
      exact mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) hCip) hR, ?_⟩
  intro T U hT hU δ hδ_le hδ0 hδT hδU hδZ
    R A A4 D2 D3 D4 N hR hA hA4 hD2 hD3 hD4 hN
    hT2 hU2 hT3 hU3 hT4 hU4 hTU2 hTU3 hTU4 hTn hUn hTUn s hs
  have hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le (by norm_num)
  set gmT : SmoothRiemannianMetric I M :=
    realizedFam (I := I) g T 0 hδT hδZ s with hgmT
  set gmU : SmoothRiemannianMetric I M :=
    realizedFam (I := I) g U 0 hδU hδZ s with hgmU
  set P : SmoothCcTensor g 0 2 := s • T with hcP
  set Q : SmoothCcTensor g 0 2 := s • U with hcQ
  have hs_mem : s ∈ realizedSmallSet (δ := δ) (δ' := δ) :=
    Icc_subset_realizedSmallSet hδ_lt hδ_lt hs
  have hsabs : ‖s‖ ≤ (1 : ℝ) := by
    rw [Real.norm_eq_abs, abs_of_nonneg hs.1]
    exact hs.2
  have hPtie : ∀ (x : M) (u v : TangentSpace I x),
      gmT.inner x u v =
        g.inner x u v + ccTensorBilinSymm (I := I) g P x u v := by
    intro x u v
    simpa only [hgmT, hcP, convexPerturbation, smul_zero, zero_add] using
      realizedFam_inner_of_mem (I := I) g T 0 hδT hδZ hs_mem x u v
  have hQtie : ∀ (x : M) (u v : TangentSpace I x),
      gmU.inner x u v =
        g.inner x u v + ccTensorBilinSymm (I := I) g Q x u v := by
    intro x u v
    simpa only [hgmU, hcQ, convexPerturbation, smul_zero, zero_add] using
      realizedFam_inner_of_mem (I := I) g U 0 hδU hδZ hs_mem x u v
  have hPn : ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) P‖ ≤ ρp := by
    rw [hcP, ccTensorToHs_smul, norm_smul]
    exact (mul_le_mul_of_nonneg_right hsabs (norm_nonneg _)).trans
      (by simpa using hTn.trans (min_le_left _ _))
  have hQn : ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) Q‖ ≤ ρp := by
    rw [hcQ, ccTensorToHs_smul, norm_smul]
    exact (mul_le_mul_of_nonneg_right hsabs (norm_nonneg _)).trans
      (by simpa using hUn.trans (min_le_left _ _))
  have hQnb : ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) Q‖ ≤ ρb := by
    rw [hcQ, ccTensorToHs_smul, norm_smul]
    exact (mul_le_mul_of_nonneg_right hsabs (norm_nonneg _)).trans
      (by simpa using hUn.trans (min_le_right _ _))
  have hPQn : ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (P - Q)‖ ≤ N := by
    have hPQ : P - Q = s • (T - U) := by rw [hcP, hcQ, smul_sub]
    rw [hPQ, ccTensorToHs_smul, norm_smul]
    exact (mul_le_mul_of_nonneg_right hsabs (norm_nonneg _)).trans
      (by simpa using hTUn)
  -- the interpolated third-jet size of the two states
  set a : ℝ := Real.sqrt (Cip * (R * A4)) with hadef
  have ha0 : 0 ≤ a := Real.sqrt_nonneg _
  have hasq : a ^ 2 = Cip * (R * A4) :=
    Real.sq_sqrt (mul_nonneg hCip (mul_nonneg hR hA4))
  have hT3i : lowJetSq (I := I) (M := M) g 3 T ≤ a ^ 2 := by
    rw [hasq]
    exact hinterp T R A4 hR hA4 hT2 hT4
  have hU3i : lowJetSq (I := I) (M := M) g 3 U ≤ a ^ 2 := by
    rw [hasq]
    exact hinterp U R A4 hR hA4 hU2 hU4
  set pl2 : ℝ := (1 + a) ^ 2 with hpl2
  have hpl21 : (1 : ℝ) ≤ pl2 := by
    rw [hpl2]
    nlinarith [ha0]
  have hpl20 : 0 ≤ pl2 := le_trans zero_le_one hpl21
  have hpl4 : (0 : ℝ) ≤ pl2 * pl2 := mul_nonneg hpl20 hpl20
  set u : ℝ := D3 ^ 2 + N ^ 2 with hu
  have hu0 : 0 ≤ u := by
    rw [hu]
    positivity
  have hD3le : D3 ^ 2 ≤ u := by
    rw [hu]
    linarith [sq_nonneg N]
  have hNu : N ^ 2 ≤ u := by
    rw [hu]
    linarith [sq_nonneg D3]
  -- the residual identity turns the edge into a single product
  have hUT :
      deTurckLieCovDerivArmField (I := I) (M := M) g gmT g -
        deTurckLieCovDerivRefoldPairTraceFamily (I := I) (M := M)
          g T hδT hδZ
            ![Equiv.swap (0 : Fin 4) 1 * Equiv.swap (0 : Fin 4) 2,
              Equiv.swap (2 : Fin 4) 3 * Equiv.swap (1 : Fin 4) 2 *
                Equiv.swap (0 : Fin 4) 1,
              Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3]
            ![(-1 : ℝ), -1, 1] s =
      (-1 : ℝ) • appCcRS (I := I) (M := M) g 2 6 2
        (lieCovPair (I := I) (M := M) g gmT)
        (rsDomDomCongrSection (I := I) (M := M) g 2 6 lieCovSigma
          (slotExtendIter (I := I) (M := M) g 0 4 2
            (lieCovR4 (I := I) (M := M) g T hδT hδZ s))) := by
    rw [hgmT]
    exact lieCov_residual (I := I) (M := M) g T hδ_lt hδT hδZ hT hs
  have hUU :
      deTurckLieCovDerivArmField (I := I) (M := M) g gmU g -
        deTurckLieCovDerivRefoldPairTraceFamily (I := I) (M := M)
          g U hδU hδZ
            ![Equiv.swap (0 : Fin 4) 1 * Equiv.swap (0 : Fin 4) 2,
              Equiv.swap (2 : Fin 4) 3 * Equiv.swap (1 : Fin 4) 2 *
                Equiv.swap (0 : Fin 4) 1,
              Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3]
            ![(-1 : ℝ), -1, 1] s =
      (-1 : ℝ) • appCcRS (I := I) (M := M) g 2 6 2
        (lieCovPair (I := I) (M := M) g gmU)
        (rsDomDomCongrSection (I := I) (M := M) g 2 6 lieCovSigma
          (slotExtendIter (I := I) (M := M) g 0 4 2
            (lieCovR4 (I := I) (M := M) g U hδU hδZ s))) := by
    rw [hgmU]
    exact lieCov_residual (I := I) (M := M) g U hδ_lt hδU hδZ hU hs
  rw [edgeEq (I := I) (M := M) g T hδT hδZ s,
    edgeEq (I := I) (M := M) g U hδU hδZ s, hUT, hUU]
  have htel :
      (-1 : ℝ) • appCcRS (I := I) (M := M) g 2 6 2
          (lieCovPair (I := I) (M := M) g gmT)
          (rsDomDomCongrSection (I := I) (M := M) g 2 6 lieCovSigma
            (slotExtendIter (I := I) (M := M) g 0 4 2
              (lieCovR4 (I := I) (M := M) g T hδT hδZ s))) -
        (-1 : ℝ) • appCcRS (I := I) (M := M) g 2 6 2
          (lieCovPair (I := I) (M := M) g gmU)
          (rsDomDomCongrSection (I := I) (M := M) g 2 6 lieCovSigma
            (slotExtendIter (I := I) (M := M) g 0 4 2
              (lieCovR4 (I := I) (M := M) g U hδU hδZ s))) =
      (-1 : ℝ) • (appCcRS (I := I) (M := M) g 2 6 2
          (lieCovPair (I := I) (M := M) g gmT -
            lieCovPair (I := I) (M := M) g gmU)
          (rsDomDomCongrSection (I := I) (M := M) g 2 6 lieCovSigma
            (slotExtendIter (I := I) (M := M) g 0 4 2
              (lieCovR4 (I := I) (M := M) g T hδT hδZ s))) +
        appCcRS (I := I) (M := M) g 2 6 2
          (lieCovPair (I := I) (M := M) g gmU)
          (rsDomDomCongrSection (I := I) (M := M) g 2 6 lieCovSigma
              (slotExtendIter (I := I) (M := M) g 0 4 2
                (lieCovR4 (I := I) (M := M) g T hδT hδZ s)) -
            rsDomDomCongrSection (I := I) (M := M) g 2 6 lieCovSigma
              (slotExtendIter (I := I) (M := M) g 0 4 2
                (lieCovR4 (I := I) (M := M) g U hδU hδZ s)))) := by
    rw [appCcRS_sub_left, appCcRS_sub_right]
    module
  rw [htel, jetSmul, neg_one_sq, one_mul]
  -- the four factor moduli, all read at the interpolated size `a`
  have hPairD : lowJetSq (I := I) (M := M) g 2
      (lieCovPair (I := I) (M := M) g gmT -
        lieCovPair (I := I) (M := M) g gmU) ≤ (Cp * N) ^ 2 := by
    refine (hlcvp P Q gmT gmU hPtie hQtie hPn hQn).trans ?_
    exact pow_le_pow_left₀ (mul_nonneg hCp (norm_nonneg _))
      (mul_le_mul_of_nonneg_left hPQn hCp) 2
  have hPairU : lowJetSq (I := I) (M := M) g 2
      (lieCovPair (I := I) (M := M) g gmU) ≤ Bp ^ 2 :=
    hlcvb Q gmU hQtie hQnb
  have hXT : lowJetSq (I := I) (M := M) g 2
      (rsDomDomCongrSection (I := I) (M := M) g 2 6 lieCovSigma
        (slotExtendIter (I := I) (M := M) g 0 4 2
          (lieCovR4 (I := I) (M := M) g T hδT hδZ s))) ≤
      Dx R * (pl2 * pl2) := by
    refine (hcovb T hT hδ_le hδ0 hδT hδZ R a hR ha0 hT2 hT3i hs).trans
      (le_of_eq ?_)
    rw [hpl2]
    ring
  have hXD : lowJetSq (I := I) (M := M) g 2
      (rsDomDomCongrSection (I := I) (M := M) g 2 6 lieCovSigma
          (slotExtendIter (I := I) (M := M) g 0 4 2
            (lieCovR4 (I := I) (M := M) g T hδT hδZ s)) -
        rsDomDomCongrSection (I := I) (M := M) g 2 6 lieCovSigma
          (slotExtendIter (I := I) (M := M) g 0 4 2
            (lieCovR4 (I := I) (M := M) g U hδU hδZ s))) ≤
      Cx R * ((pl2 * pl2) * D3 ^ 2) := by
    refine (hcovp T U hT hU hδ_le hδ0 hδT hδU hδZ R a D3 hR ha0 hD3
      hT2 hU2 hT3i hU3i hTU3 hs).trans (le_of_eq ?_)
    rw [hpl2]
    ring
  -- the two telescope terms
  have hc1 : (0 : ℝ) ≤ Ca * Cp ^ 2 * Dx R :=
    mul_nonneg (mul_nonneg hCa (sq_nonneg _)) (hDx R hR)
  have hc2 : (0 : ℝ) ≤ Ca * Bp ^ 2 * Cx R :=
    mul_nonneg (mul_nonneg hCa (sq_nonneg _)) (hCx R hR)
  have hT1 : lowJetSq (I := I) (M := M) g 2
      (appCcRS (I := I) (M := M) g 2 6 2
        (lieCovPair (I := I) (M := M) g gmT -
          lieCovPair (I := I) (M := M) g gmU)
        (rsDomDomCongrSection (I := I) (M := M) g 2 6 lieCovSigma
          (slotExtendIter (I := I) (M := M) g 0 4 2
            (lieCovR4 (I := I) (M := M) g T hδT hδZ s)))) ≤
      Ca * Cp ^ 2 * Dx R * ((pl2 * pl2) * u) := by
    refine (happ _ _).trans ?_
    have hstep := mul_le_mul (mul_le_mul_of_nonneg_left hPairD hCa) hXT
      (jetNn (I := I) (M := M) (m := 2) g _)
      (mul_nonneg hCa (sq_nonneg _))
    refine hstep.trans ?_
    calc Ca * (Cp * N) ^ 2 * (Dx R * (pl2 * pl2)) =
        Ca * Cp ^ 2 * Dx R * ((pl2 * pl2) * N ^ 2) := by ring
      _ ≤ Ca * Cp ^ 2 * Dx R * ((pl2 * pl2) * u) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hNu hpl4) hc1
  have hT2b : lowJetSq (I := I) (M := M) g 2
      (appCcRS (I := I) (M := M) g 2 6 2
        (lieCovPair (I := I) (M := M) g gmU)
        (rsDomDomCongrSection (I := I) (M := M) g 2 6 lieCovSigma
            (slotExtendIter (I := I) (M := M) g 0 4 2
              (lieCovR4 (I := I) (M := M) g T hδT hδZ s)) -
          rsDomDomCongrSection (I := I) (M := M) g 2 6 lieCovSigma
            (slotExtendIter (I := I) (M := M) g 0 4 2
              (lieCovR4 (I := I) (M := M) g U hδU hδZ s)))) ≤
      Ca * Bp ^ 2 * Cx R * ((pl2 * pl2) * u) := by
    refine (happ _ _).trans ?_
    have hstep := mul_le_mul (mul_le_mul_of_nonneg_left hPairU hCa) hXD
      (jetNn (I := I) (M := M) (m := 2) g _)
      (mul_nonneg hCa (sq_nonneg _))
    refine hstep.trans ?_
    calc Ca * Bp ^ 2 * (Cx R * ((pl2 * pl2) * D3 ^ 2)) =
        Ca * Bp ^ 2 * Cx R * ((pl2 * pl2) * D3 ^ 2) := by ring
      _ ≤ Ca * Bp ^ 2 * Cx R * ((pl2 * pl2) * u) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hD3le hpl4) hc2
  have hwhole : lowJetSq (I := I) (M := M) g 2
      (appCcRS (I := I) (M := M) g 2 6 2
          (lieCovPair (I := I) (M := M) g gmT -
            lieCovPair (I := I) (M := M) g gmU)
          (rsDomDomCongrSection (I := I) (M := M) g 2 6 lieCovSigma
            (slotExtendIter (I := I) (M := M) g 0 4 2
              (lieCovR4 (I := I) (M := M) g T hδT hδZ s))) +
        appCcRS (I := I) (M := M) g 2 6 2
          (lieCovPair (I := I) (M := M) g gmU)
          (rsDomDomCongrSection (I := I) (M := M) g 2 6 lieCovSigma
              (slotExtendIter (I := I) (M := M) g 0 4 2
                (lieCovR4 (I := I) (M := M) g T hδT hδZ s)) -
            rsDomDomCongrSection (I := I) (M := M) g 2 6 lieCovSigma
              (slotExtendIter (I := I) (M := M) g 0 4 2
                (lieCovR4 (I := I) (M := M) g U hδU hδZ s)))) ≤
      Bh R * ((pl2 * pl2) * u) := by
    calc
      lowJetSq (I := I) (M := M) g 2 (_ + _) ≤
          2 * (lowJetSq (I := I) (M := M) g 2 _ +
            lowJetSq (I := I) (M := M) g 2 _) :=
        jetAdd (I := I) (M := M) g 2 _ _
      _ ≤ 2 * (Ca * Cp ^ 2 * Dx R * ((pl2 * pl2) * u) +
          Ca * Bp ^ 2 * Cx R * ((pl2 * pl2) * u)) := by
        linarith [hT1, hT2b]
      _ = Bh R * ((pl2 * pl2) * u) := by
        simp only [Bh]
        ring
  refine hwhole.trans ?_
  rw [hpl2, hu]
  simp only [B0, B1]
  exact amixScalar (hBhnn R hR) hCip hR hA hA4 hD2 hD3 hD4 hN hasq

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
