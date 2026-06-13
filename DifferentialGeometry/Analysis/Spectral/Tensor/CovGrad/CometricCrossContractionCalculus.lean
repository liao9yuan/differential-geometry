import DifferentialGeometry.Geometry.Metric.InverseMetricField
import DifferentialGeometry.Tensor.RSTensor.Derivation.Contract
import DifferentialGeometry.Tensor.RSTensor.Coordinates.CoordinateBasis
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.CometricDoubleTraceField
import DifferentialGeometry.Geometry.Connection.TensorNabla.OperatorFieldCovariantCalculusRS
import DifferentialGeometry.Geometry.Connection.MetricCompatibility.InverseMetricFieldParallel
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.CovGradSlotPermutationNaturality
import DifferentialGeometry.Geometry.Curvature.FiberNormParseval.Slot0SliceFiberNormDomination
import DifferentialGeometry.Geometry.Connection.MetricCompatibility.CovGradCovDerivCommutation
import DifferentialGeometry.Geometry.Connection.TensorNabla.LiftedSectionCovariantRealizeBridge
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.BareTensorProductCovariantLeibniz
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.LoweredConnectionDifferenceCovariantDerivative
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.CometricInverseDifferenceCovariantSection

/-! # The cometric `(0,2)`-cross parallel two-section single contraction `h ⌟ D`

For a closed (compact, boundaryless) smooth Riemannian manifold `(M, g₀)` modelled on a real
inner-product space `E`, this file builds the **section-level parallel fibrewise bilinear `g₀`-single
contraction at valence `(0, 2)`**

```
cometricParallelContraction g₀ S T   :   (0, 2 + a) ⊗ (0, 2 + b) → (0, 2 + a + b),
```

the `g₀`-metric single contraction `h ⌟ D` of a rank-`(2 + a)` factor `S` against a rank-`(2 + b)`
factor `T`, pairing one slot of each factor through the cometric `g₀⁻¹` (parallel, `∇₀ g₀⁻¹ = 0`), so
the result carries the remaining `(2 + a − 1) + (2 + b − 1) = 2 + a + b` covariant slots.  Built from
the model tensor product `Bundle.continuousMultilinearMap.modelProduct` followed by the cometric
`g₀⁻¹` single trace of the two contracted leading slots (frame-free, depending on `g₀` only through the
smooth cometric Hom-section `inverseMetricSharpField`, NO chart-selected ambient frame).

This is the EXACT analogue, at the smaller `(0, 2) ⊗ (0, 2)` arithmetic, of the `(0, 2) ⊗ (0, 3)`
cross-correction contraction `crossCorrParallelContraction` of `CrossCorrectionContractionCalculus`
(whose min output rank is `3`, so the contraction op/perm/keystone genuinely had to be rebuilt at the
`(0, 2)` arithmetic `(1 + b) + (1 + a) = 2 + a + b`); the reusable generic operator-field engines
(`appCcRS`, `slotExtend`, the cometric double-trace field) are shared, not rebuilt.

## What this file provides

* `cometricParallelContraction` — the section-level parallel fibrewise bilinear `g₀`-single
  contraction, fibrewise `ℝ`-bilinear.
* `cometricParallelContraction_eq_appCcRS` — the operator-field bridge (the contraction is the fixed
  cometric trace field post-composed after the frame-free slot-permuted model product section).
* the cross bilinearity primitives (`cometricParallelContraction_add/sub/smul_left/_right`), the slot
  bookkeeping (`cometricCcPerm`), and the `∇₀`-parallelism of the fixed cometric trace field
  (`cometricCcOp_covGrad_eq_zero`).
* `cometricParallelContraction_eq_cometricCrossSection` — the genuinely-new concrete identification of
  this contraction (at `S = realizeSymm T₁`, `T = permute c[0,1] (cometricInverseDiffSection g₁ g₀)`)
  with the cometric cross-correction `(0, 2)`-section `crossCometricSection`.

A reusable covariant-calculus byproduct (R1 — its own first-class home in the covariant-gradient API),
decoupled from the specific factor sections; it does NOT import the seven-term Bochner fold. -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
open DifferentialGeometry.PDE.DeTurck
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck
open DifferentialGeometry.Integral.Measure (chartModelBasis)
open DifferentialGeometry.Analysis.Sobolev.TensorHilbert

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

/-! ## The fibrewise model single cometric contraction at `(0, 2) ⊗ (0, 2)` -/

/-- **Model-fibre rank reindex `Tensor0SModel m → Tensor0SModel n` along `h : m = n`** (local
re-statement, via the isometric `domDomCongrₗᵢ (finCongr h)`). -/
noncomputable def cometricModelRankCast {m n : ℕ} (h : m = n) :
    Tensor0SBundle.Tensor0SModel m ℝ E →L[ℝ] Tensor0SBundle.Tensor0SModel n ℝ E :=
  (ContinuousMultilinearMap.domDomCongrₗᵢ ℝ E ℝ
    (finCongr h)).toContinuousLinearEquiv.toContinuousLinearMap

set_option linter.unusedSectionVars false in
/-- Defining evaluation of the model-fibre rank reindex. -/
theorem cometricModelRankCast_apply' {m n : ℕ} (h : m = n) (T : Tensor0SBundle.Tensor0SModel m ℝ E)
    (v : Fin n → E) :
    cometricModelRankCast (E := E) h T v = T (fun i => v (finCongr h i)) := by
  change (ContinuousMultilinearMap.domDomCongrₗᵢ ℝ E ℝ (finCongr h)) T v = _
  rw [show (ContinuousMultilinearMap.domDomCongrₗᵢ ℝ E ℝ (finCongr h)) T
      = ContinuousMultilinearMap.domDomCongr (finCongr h) T from rfl,
    ContinuousMultilinearMap.domDomCongr_apply]

/-- **The fibrewise model value of the single `g₀`-contraction `(0, 2 + a) ⊗ (0, 2 + b) →
(0, 2 + a + b)`.**  For each model-basis index `i`, raise the dual covector `eⁱ` by the cometric
reading `L` to a vector `♯eⁱ`, read `♯eⁱ` into the leading slot of `Sm` and `eᵢ` into the leading slot
of `Tm`, and tensor-multiply the two reduced tensors, summing over `i` — the single cometric trace of
`Sm ⊗ Tm` pairing the leading slot of each factor.  The reduced `Tm`-factor leads, so the result slots
read `[Tm-reduced (1 + b), Sm-reduced (1 + a)]`, transported across the cast
`(1 + b) + (1 + a) = 2 + a + b`. -/
noncomputable def cometricCcModelFun (L : Tensor0SBundle.Tensor0SModel 1 ℝ E →L[ℝ] E) (a b : ℕ)
    (Sm : Tensor0SBundle.Tensor0SModel (2 + a) ℝ E) (Tm : Tensor0SBundle.Tensor0SModel (2 + b) ℝ E) :
    Tensor0SBundle.Tensor0SModel (2 + a + b) ℝ E :=
  cometricModelRankCast (E := E) (by omega : (1 + b) + (1 + a) = 2 + a + b)
    (∑ i : Fin (Module.finrank ℝ E),
      Bundle.continuousMultilinearMap.modelProduct (𝕜 := ℝ) (F := E) (1 + b) (1 + a)
        (Tensor0SBundle.model_interior_product (1 + b) ((Module.finBasis ℝ E) i)
          (cometricModelRankCast (E := E) (by omega : 2 + b = (1 + b) + 1) Tm))
        (Tensor0SBundle.model_interior_product (1 + a)
          (L (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
            ((Module.finBasis ℝ E).cDualBasis i)))
          (cometricModelRankCast (E := E) (by omega : 2 + a = (1 + a) + 1) Sm)))

/-- **The model cometric reading at `x`** `Tensor0SModel 1 ℝ E →L[ℝ] E`. -/
noncomputable def cometricCcReadingModel (g₀ : SmoothRiemannianMetric I M) (x : M) :
    Tensor0SBundle.Tensor0SModel 1 ℝ E →L[ℝ] E :=
  (inverseMetricSharpFib (I := I) g₀ x).comp
    (Tensor0SBundle.tensor0SSpace_continuousLinearEquiv (𝕜 := ℝ) (I := I) 1 x).symm.toContinuousLinearMap

set_option linter.unusedSectionVars false in
/-- The model cometric reading coincides with the rank-generic cometric reading `cometricLmodel`. -/
theorem cometricCcReadingModel_eq (g₀ : SmoothRiemannianMetric I M) (x : M) :
    cometricCcReadingModel (I := I) g₀ x = cometricLmodel (I := I) g₀ x := rfl

/-- **The unit fibre value of a `(0, s)`-section as a model `Tensor0SModel s`.** -/
noncomputable def cometricCcUnitModel {s : ℕ} (g₀ : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g₀ 0 s) (x : M) : Tensor0SBundle.Tensor0SModel s ℝ E :=
  Tensor0SBundle.Tensor0SSpace.toModel
    ((S.toSection x) (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => TangentSpace I x) 1))

/-- **The cross slot permutation** `Fin ((2 + b) + (2 + a)) ≃ itself`.  On the model product `Tm ⊗ Sm`
it rotates the leading `3 + b` slots cyclically — sending the `Sm`-leading slot (model-product index
`2 + b`) to position `0`, the `Tm`-leading slot (index `0`) to position `1`, the remaining `Tm` slots
to positions `2 … 2 + b`, fixing the trailing `Sm` slots — so the two slots to be contracted become
the leading adjacent pair.  Built as `finRotate ((2 + b) + 1)` on the leading block, identity on the
trailing `1 + a` block. -/
noncomputable def cometricCcPerm (a b : ℕ) : Equiv.Perm (Fin ((2 + b) + (2 + a))) :=
  (finCongr (by omega : ((2 + b) + 1) + (1 + a) = (2 + b) + (2 + a))).permCongr
    (finSumFinEquiv.permCongr (Equiv.sumCongr (finRotate ((2 + b) + 1)) (Equiv.refl (Fin (1 + a)))))

set_option linter.unusedSectionVars false in
/-- A `Tm`-block slot `castAdd (2 + a) j` reads to model-product position `1 + j`. -/
theorem cometricCcPerm_castAdd (a b : ℕ) (j : Fin (2 + b)) :
    ((cometricCcPerm a b) (Fin.castAdd (2 + a) j)).val = 1 + j.val := by
  unfold cometricCcPerm
  simp only [Equiv.permCongr_apply, finCongr_symm, finCongr_apply, Equiv.sumCongr_apply]
  rw [show (Fin.cast (by omega : (2 + b) + (2 + a) = ((2 + b) + 1) + (1 + a)) (Fin.castAdd (2 + a) j))
      = Fin.castAdd (1 + a) (Fin.castSucc j) from by
    apply Fin.ext; simp only [Fin.val_cast, Fin.val_castAdd, Fin.val_castSucc]]
  rw [finSumFinEquiv_symm_apply_castAdd]
  simp only [Sum.map_inl, finSumFinEquiv_apply_left, Fin.val_cast, Fin.val_castAdd,
    finRotate_succ_apply, Fin.val_add_one_of_lt (Fin.castSucc_lt_last j), Fin.val_castSucc]
  omega

set_option linter.unusedSectionVars false in
/-- An `Sm`-block slot `natAdd (2 + b) k` reads to position `0` when `k = 0` and `(2 + b) + k` else. -/
theorem cometricCcPerm_natAdd (a b : ℕ) (k : Fin (2 + a)) :
    ((cometricCcPerm a b) (Fin.natAdd (2 + b) k)).val
      = if k.val = 0 then 0 else (2 + b) + k.val := by
  unfold cometricCcPerm
  simp only [Equiv.permCongr_apply, finCongr_symm, finCongr_apply, Equiv.sumCongr_apply]
  rcases Nat.eq_zero_or_pos k.val with hk | hk
  · rw [show (Fin.cast (by omega : (2 + b) + (2 + a) = ((2 + b) + 1) + (1 + a)) (Fin.natAdd (2 + b) k))
        = Fin.castAdd (1 + a) (Fin.last (2 + b)) from by
      apply Fin.ext; simp only [Fin.val_cast, Fin.val_natAdd, Fin.val_castAdd, Fin.val_last]; omega]
    rw [finSumFinEquiv_symm_apply_castAdd]
    simp only [Sum.map_inl, finSumFinEquiv_apply_left, finRotate_last, Fin.val_cast, Fin.val_castAdd]
    simp [hk]
  · rw [show (Fin.cast (by omega : (2 + b) + (2 + a) = ((2 + b) + 1) + (1 + a)) (Fin.natAdd (2 + b) k))
        = Fin.natAdd ((2 + b) + 1) (⟨k.val - 1, by omega⟩ : Fin (1 + a)) from by
      apply Fin.ext; simp only [Fin.val_cast, Fin.val_natAdd]; omega]
    rw [finSumFinEquiv_symm_apply_natAdd]
    simp only [Sum.map_inr, Equiv.refl_apply, finSumFinEquiv_apply_right, Fin.val_cast, Fin.val_natAdd]
    rw [if_neg (by omega)]; omega

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in
/-- **`domDomCongr` of a smooth `(0, n)`-tensor field is smooth.** -/
theorem cometricTensor0SField_domDomCongr_contMDiff {n : ℕ} (σ : Equiv.Perm (Fin n))
    (Y : ∀ x : M, Tensor0SBundle.Tensor0SSpace n I x)
    (hY : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel n ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel n ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace n I z) x (Y x))) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel n ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel n ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace n I z) x
        (Tensor0SBundle.Tensor0SSpace.ofModel
          (ContinuousMultilinearMap.domDomCongr σ (Tensor0SBundle.Tensor0SSpace.toModel (Y x))))) := by
  classical
  refine (contMDiff_multilinearSection_iff_coord (𝕜 := ℝ) (F := E)
    (E := (TangentSpace I : M → Type _)) (IB := I) (n := (∞ : WithTop ℕ∞)) (Module.finBasis ℝ E)
    (fun x => (Tensor0SBundle.Tensor0SSpace.ofModel
      (ContinuousMultilinearMap.domDomCongr σ (Tensor0SBundle.Tensor0SSpace.toModel (Y x))) :
        Tensor0SBundle.Tensor0SSpace n I x))).mpr ?_
  have hY' := (contMDiff_multilinearSection_iff_coord (𝕜 := ℝ) (F := E)
    (E := (TangentSpace I : M → Type _)) (IB := I) (n := (∞ : WithTop ℕ∞)) (Module.finBasis ℝ E)
    (fun x => (Y x : Tensor0SBundle.Tensor0SSpace n I x))).mp hY
  intro τ x₀
  refine (hY' (τ ∘ σ) x₀).congr_of_eventuallyEq ?_
  have hbase := (trivializationAt (Tensor0SBundle.Tensor0SModel n ℝ E)
    (Bundle.continuousMultilinearMap ℝ n E (TangentSpace I)) x₀).open_baseSet.mem_nhds
    (mem_baseSet_trivializationAt _ _ x₀)
  filter_upwards [hbase] with x _
  rw [continuousMultilinearMap_basis_repr, continuousMultilinearMap_basis_repr]
  rfl

/-- **The frame-free (unpermuted) model product field**. -/
theorem cometricCcProdUnpermField_contMDiff (g₀ : SmoothRiemannianMetric I M) {a b : ℕ}
    (S : SmoothCcTensor g₀ 0 (2 + a)) (T : SmoothCcTensor g₀ 0 (2 + b)) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel ((2 + b) + (2 + a)) ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel ((2 + b) + (2 + a)) ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace ((2 + b) + (2 + a)) I z) x
        ((Tensor0SBundle.Tensor0SSpace.ofModel (𝕜 := ℝ) (I := I) (x := x)
            (Bundle.continuousMultilinearMap.modelProduct (𝕜 := ℝ) (F := E) (2 + b) (2 + a)
              (cometricCcUnitModel (I := I) g₀ T x) (cometricCcUnitModel (I := I) g₀ S x)) :
            Tensor0SBundle.Tensor0SSpace ((2 + b) + (2 + a)) I x))) := by
  letI := Tensor0SBundle.tensor0SBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) ((2 + b) + (2 + a))
  classical
  have hTfield : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel (2 + b) ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel (2 + b) ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace (2 + b) I z) x
        (Tensor0SBundle.Tensor0SSpace.ofModel (cometricCcUnitModel (I := I) g₀ T x))) := by
    simpa only [Tensor0SBundle.Tensor0SSpace.ofModel_toModel] using
      (contMDiff_unitEvalSection (I := I) g₀ (2 + b) T)
  have hSfield : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel (2 + a) ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel (2 + a) ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace (2 + a) I z) x
        (Tensor0SBundle.Tensor0SSpace.ofModel (cometricCcUnitModel (I := I) g₀ S x))) := by
    simpa only [Tensor0SBundle.Tensor0SSpace.ofModel_toModel] using
      (contMDiff_unitEvalSection (I := I) g₀ (2 + a) S)
  refine (contMDiff_multilinearSection_iff_coord (𝕜 := ℝ) (F := E)
    (E := (TangentSpace I : M → Type _)) (IB := I) (n := (∞ : WithTop ℕ∞)) (Module.finBasis ℝ E)
    (fun x => (Tensor0SBundle.Tensor0SSpace.ofModel (𝕜 := ℝ) (I := I) (x := x)
        (Bundle.continuousMultilinearMap.modelProduct (𝕜 := ℝ) (F := E) (2 + b) (2 + a)
          (cometricCcUnitModel (I := I) g₀ T x) (cometricCcUnitModel (I := I) g₀ S x)) :
          Tensor0SBundle.Tensor0SSpace ((2 + b) + (2 + a)) I x))).mpr ?_
  have hT := (contMDiff_multilinearSection_iff_coord (𝕜 := ℝ) (F := E)
    (E := (TangentSpace I : M → Type _)) (IB := I) (n := (∞ : WithTop ℕ∞)) (Module.finBasis ℝ E)
    (fun x => (Tensor0SBundle.Tensor0SSpace.ofModel (cometricCcUnitModel (I := I) g₀ T x) :
      Tensor0SBundle.Tensor0SSpace (2 + b) I x))).mp hTfield
  have hS := (contMDiff_multilinearSection_iff_coord (𝕜 := ℝ) (F := E)
    (E := (TangentSpace I : M → Type _)) (IB := I) (n := (∞ : WithTop ℕ∞)) (Module.finBasis ℝ E)
    (fun x => (Tensor0SBundle.Tensor0SSpace.ofModel (cometricCcUnitModel (I := I) g₀ S x) :
      Tensor0SBundle.Tensor0SSpace (2 + a) I x))).mp hSfield
  intro τ x₀
  refine (((contMDiffAt_const (I := I) (x := x₀) (n := ∞)
    (c := ContinuousLinearMap.mul ℝ ℝ)).clm_apply
      (hT (τ ∘ Fin.castAdd (2 + a)) x₀)).clm_apply
        (hS (τ ∘ Fin.natAdd (2 + b)) x₀)).congr_of_eventuallyEq ?_
  filter_upwards [Filter.univ_mem] with x _
  rw [continuousMultilinearMap_basis_repr, continuousMultilinearMap_basis_repr,
    continuousMultilinearMap_basis_repr]
  change (Bundle.continuousMultilinearMap.modelProduct (𝕜 := ℝ) (F := E) (2 + b) (2 + a)
      (cometricCcUnitModel (I := I) g₀ T x) (cometricCcUnitModel (I := I) g₀ S x))
      (fun j => (Bundle.Trivialization.symmL ℝ (trivializationAt E (TangentSpace I) x₀) x)
        ((Module.finBasis ℝ E) (τ j))) = _
  rw [Bundle.continuousMultilinearMap.modelProduct_apply]
  rfl

/-- **The cross permuted model product field**, smooth. -/
theorem cometricCcProdField_contMDiff (g₀ : SmoothRiemannianMetric I M) {a b : ℕ}
    (S : SmoothCcTensor g₀ 0 (2 + a)) (T : SmoothCcTensor g₀ 0 (2 + b)) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel ((2 + b) + (2 + a)) ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel ((2 + b) + (2 + a)) ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace ((2 + b) + (2 + a)) I z) x
        (Tensor0SBundle.Tensor0SSpace.ofModel
          (ContinuousMultilinearMap.domDomCongr (cometricCcPerm a b)
            (Bundle.continuousMultilinearMap.modelProduct (𝕜 := ℝ) (F := E) (2 + b) (2 + a)
              (cometricCcUnitModel (I := I) g₀ T x) (cometricCcUnitModel (I := I) g₀ S x))))) := by
  letI := Tensor0SBundle.tensor0SBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) ((2 + b) + (2 + a))
  classical
  refine (cometricTensor0SField_domDomCongr_contMDiff (cometricCcPerm a b)
    (fun x => (Tensor0SBundle.Tensor0SSpace.ofModel (𝕜 := ℝ) (I := I) (x := x)
        (Bundle.continuousMultilinearMap.modelProduct (𝕜 := ℝ) (F := E) (2 + b) (2 + a)
          (cometricCcUnitModel (I := I) g₀ T x) (cometricCcUnitModel (I := I) g₀ S x)) :
          Tensor0SBundle.Tensor0SSpace ((2 + b) + (2 + a)) I x))
    (cometricCcProdUnpermField_contMDiff (I := I) g₀ S T)).congr (fun x => ?_)
  simp only [Tensor0SBundle.Tensor0SSpace.toModel_ofModel]

set_option linter.unusedSectionVars false in
/-- The `Tm`-factor tuple identity. -/
private theorem cometricCcTm_tuple (a b : ℕ) (p q : E) (m : Fin (2 + a + b) → E) :
    (fun j : Fin (2 + b) => (Fin.cons p (Fin.cons q m) : Fin ((2 + a + b) + 2) → E)
        (Fin.cast (by omega : (2 + b) + (2 + a) = (2 + a + b) + 2)
          ((cometricCcPerm a b) (Fin.castAdd (2 + a) j))))
      = (Fin.cons q (fun i : Fin (1 + b) => m (Fin.cast (by omega : (1 + b) + (1 + a) = 2 + a + b)
            (Fin.castAdd (1 + a) i))) : Fin ((1 + b) + 1) → E)
          ∘ Fin.cast (by omega : 2 + b = (1 + b) + 1) := by
  funext j
  rw [show (Fin.cast (by omega : (2 + b) + (2 + a) = (2 + a + b) + 2)
        ((cometricCcPerm a b) (Fin.castAdd (2 + a) j)))
      = (⟨1 + j.val, by omega⟩ : Fin ((2 + a + b) + 2)) from by
    apply Fin.ext; rw [Fin.val_cast, cometricCcPerm_castAdd]]
  rw [show (⟨1 + j.val, by omega⟩ : Fin ((2 + a + b) + 2)) = Fin.succ ⟨j.val, by omega⟩ from by
    apply Fin.ext; simp only [Fin.val_succ]; omega]
  rw [Fin.cons_succ]
  simp only [Function.comp_apply]
  rcases Nat.eq_zero_or_pos j.val with hj | hj
  · rw [show (⟨j.val, by omega⟩ : Fin ((2 + a + b) + 1)) = (0 : Fin ((2 + a + b) + 1)) from
      Fin.ext (by rw [Fin.val_zero]; exact hj)]
    rw [Fin.cons_zero]
    rw [show (Fin.cast (by omega : 2 + b = (1 + b) + 1) j) = (0 : Fin ((1 + b) + 1)) from
      Fin.ext (by rw [Fin.val_cast, Fin.val_zero]; exact hj)]
    rw [Fin.cons_zero]
  · rw [show (⟨j.val, by omega⟩ : Fin ((2 + a + b) + 1)) = Fin.succ ⟨j.val - 1, by omega⟩ from by
      apply Fin.ext; simp only [Fin.val_succ]; omega]
    rw [Fin.cons_succ]
    rw [show (Fin.cast (by omega : 2 + b = (1 + b) + 1) j) = Fin.succ (⟨j.val - 1, by omega⟩ : Fin (1 + b)) from by
      apply Fin.ext; simp only [Fin.val_cast, Fin.val_succ]; omega]
    rw [Fin.cons_succ]
    rfl

set_option linter.unusedSectionVars false in
/-- The `Sm`-factor tuple identity. -/
private theorem cometricCcSm_tuple (a b : ℕ) (Lc q : E) (m : Fin (2 + a + b) → E) :
    (fun l : Fin (2 + a) => (Fin.cons Lc (Fin.cons q m) : Fin ((2 + a + b) + 2) → E)
        (Fin.cast (by omega : (2 + b) + (2 + a) = (2 + a + b) + 2)
          ((cometricCcPerm a b) (Fin.natAdd (2 + b) l))))
      = (Fin.cons Lc (fun i : Fin (1 + a) => m (Fin.cast (by omega : (1 + b) + (1 + a) = 2 + a + b)
            (Fin.natAdd (1 + b) i))) : Fin ((1 + a) + 1) → E)
          ∘ Fin.cast (by omega : 2 + a = (1 + a) + 1) := by
  funext l
  simp only [Function.comp_apply]
  rcases Nat.eq_zero_or_pos l.val with hl | hl
  · rw [show (Fin.cast (by omega : (2 + b) + (2 + a) = (2 + a + b) + 2)
          ((cometricCcPerm a b) (Fin.natAdd (2 + b) l)))
        = (0 : Fin ((2 + a + b) + 2)) from by
      apply Fin.ext; rw [Fin.val_cast, cometricCcPerm_natAdd, Fin.val_zero, if_pos hl]]
    rw [Fin.cons_zero]
    rw [show (Fin.cast (by omega : 2 + a = (1 + a) + 1) l) = (0 : Fin ((1 + a) + 1)) from
      Fin.ext (by rw [Fin.val_cast, Fin.val_zero]; exact hl)]
    rw [Fin.cons_zero]
  · rw [show (Fin.cast (by omega : (2 + b) + (2 + a) = (2 + a + b) + 2)
          ((cometricCcPerm a b) (Fin.natAdd (2 + b) l)))
        = Fin.succ (Fin.succ (⟨b + l.val, by omega⟩ : Fin (2 + a + b))) from by
      apply Fin.ext; rw [Fin.val_cast, cometricCcPerm_natAdd, if_neg (by omega)]
      simp only [Fin.val_succ]; omega]
    rw [Fin.cons_succ, Fin.cons_succ]
    rw [show (Fin.cast (by omega : 2 + a = (1 + a) + 1) l) = Fin.succ (⟨l.val - 1, by omega⟩ : Fin (1 + a)) from by
      apply Fin.ext; simp only [Fin.val_cast, Fin.val_succ]; omega]
    rw [Fin.cons_succ]
    exact congrArg m (Fin.ext (by simp only [Fin.val_cast, Fin.val_natAdd]; omega))

set_option linter.unusedSectionVars false in
/-- **The cross single cometric trace is the model double trace of the permuted product.** -/
theorem cometricCcModelFun_eq_modelDoubleTrace_perm
    (L : Tensor0SBundle.Tensor0SModel 1 ℝ E →L[ℝ] E) (a b : ℕ)
    (Sm : Tensor0SBundle.Tensor0SModel (2 + a) ℝ E) (Tm : Tensor0SBundle.Tensor0SModel (2 + b) ℝ E) :
    cometricCcModelFun (E := E) L a b Sm Tm =
      modelDoubleTrace (E := E) (2 + a + b) L
        (modelRankCast (E := E)
            (by omega : (2 + b) + (2 + a) = (2 + a + b) + 2)
          (ContinuousMultilinearMap.domDomCongr (cometricCcPerm a b)
            (Bundle.continuousMultilinearMap.modelProduct (𝕜 := ℝ) (F := E) (2 + b) (2 + a) Tm Sm))) := by
  classical
  apply ContinuousMultilinearMap.ext
  intro m
  rw [modelDoubleTrace_apply]
  unfold cometricCcModelFun
  rw [cometricModelRankCast_apply', ContinuousMultilinearMap.sum_apply]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [Bundle.continuousMultilinearMap.modelProduct_apply]
  have hDsummand : (modelRankCast (E := E)
          (by omega : (2 + b) + (2 + a) = (2 + a + b) + 2)
        (ContinuousMultilinearMap.domDomCongr (cometricCcPerm a b)
          (Bundle.continuousMultilinearMap.modelProduct (𝕜 := ℝ) (F := E) (2 + b) (2 + a) Tm Sm)))
        (Fin.cons (L (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
            ((Module.finBasis ℝ E).cDualBasis k)))
          (Fin.cons ((Module.finBasis ℝ E) k) m))
      = Tm ((fun j : Fin (2 + b) => (Fin.cons (L (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
              ((Module.finBasis ℝ E).cDualBasis k)))
            (Fin.cons ((Module.finBasis ℝ E) k) m) : Fin ((2 + a + b) + 2) → E)
            (Fin.cast (by omega : (2 + b) + (2 + a) = (2 + a + b) + 2)
              ((cometricCcPerm a b) (Fin.castAdd (2 + a) j)))))
          * Sm ((fun l : Fin (2 + a) => (Fin.cons (L (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
              ((Module.finBasis ℝ E).cDualBasis k)))
            (Fin.cons ((Module.finBasis ℝ E) k) m) : Fin ((2 + a + b) + 2) → E)
            (Fin.cast (by omega : (2 + b) + (2 + a) = (2 + a + b) + 2)
              ((cometricCcPerm a b) (Fin.natAdd (2 + b) l))))) := by
    change (ContinuousMultilinearMap.domDomCongr
          (finCongr (by omega : (2 + b) + (2 + a) = (2 + a + b) + 2))
          (ContinuousMultilinearMap.domDomCongr (cometricCcPerm a b)
            (Bundle.continuousMultilinearMap.modelProduct (𝕜 := ℝ) (F := E) (2 + b) (2 + a) Tm Sm))) _ = _
    rw [ContinuousMultilinearMap.domDomCongr_apply, ContinuousMultilinearMap.domDomCongr_apply,
      Bundle.continuousMultilinearMap.modelProduct_apply]
    rfl
  rw [hDsummand]
  rw [cometricCcTm_tuple a b _ ((Module.finBasis ℝ E) k) m,
    cometricCcSm_tuple a b (L (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
      ((Module.finBasis ℝ E).cDualBasis k))) ((Module.finBasis ℝ E) k) m]
  rfl

/-- **Base-point smoothness of the cross model fibre field**. -/
theorem cometricCcField_contMDiff (g₀ : SmoothRiemannianMetric I M) {a b : ℕ}
    (S : SmoothCcTensor g₀ 0 (2 + a)) (T : SmoothCcTensor g₀ 0 (2 + b)) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel (2 + a + b) ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel (2 + a + b) ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace (2 + a + b) I z) x
        (Tensor0SBundle.Tensor0SSpace.ofModel
          (cometricCcModelFun (E := E) (cometricCcReadingModel (I := I) g₀ x) a b
            (cometricCcUnitModel (I := I) g₀ S x) (cometricCcUnitModel (I := I) g₀ T x)))) := by
  set D : ∀ x : M, Tensor0SBundle.Tensor0SSpace ((2 + a + b) + 2) I x :=
    fun x => Tensor0SBundle.Tensor0SSpace.ofModel (𝕜 := ℝ) (I := I) (x := x)
      (modelRankCast (E := E)
        (by omega : (2 + b) + (2 + a) = (2 + a + b) + 2)
        (ContinuousMultilinearMap.domDomCongr (cometricCcPerm a b)
          (Bundle.continuousMultilinearMap.modelProduct (𝕜 := ℝ) (F := E) (2 + b) (2 + a)
            (cometricCcUnitModel (I := I) g₀ T x) (cometricCcUnitModel (I := I) g₀ S x)))) with hD
  have hDsmooth : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel ((2 + a + b) + 2) ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel ((2 + a + b) + 2) ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace ((2 + a + b) + 2) I z) x (D x)) := by
    refine (tensor0SField_castRank_contMDiff (I := I) (by omega : (2 + b) + (2 + a) = (2 + a + b) + 2)
      (fun x => (Tensor0SBundle.Tensor0SSpace.ofModel (𝕜 := ℝ) (I := I) (x := x)
        (ContinuousMultilinearMap.domDomCongr (cometricCcPerm a b)
          (Bundle.continuousMultilinearMap.modelProduct (𝕜 := ℝ) (F := E) (2 + b) (2 + a)
            (cometricCcUnitModel (I := I) g₀ T x) (cometricCcUnitModel (I := I) g₀ S x))) :
              Tensor0SBundle.Tensor0SSpace ((2 + b) + (2 + a)) I x))
      (cometricCcProdField_contMDiff (I := I) g₀ S T)).congr (fun x => ?_)
    rw [hD]
    simp only [Tensor0SBundle.Tensor0SSpace.toModel_ofModel]
  have hraise := cometricRaiseSlot0Fib_section_contMDiff (I := I) g₀ (2 + a + b) D hDsmooth
  have htrace := contractTraceField_contMDiff (I := I) 0 (2 + a + b)
    (fun x => cometricRaiseSlot0Fib (I := I) g₀ (2 + a + b) x (D x)) hraise
  have htraceUnit : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel (2 + a + b) ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel (2 + a + b) ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace (2 + a + b) I z) x
        ((show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace (2 + a + b) I x from
          Tensor0SBundle.contract_trace (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 0 (2 + a + b) x
            (cometricRaiseSlot0Fib (I := I) g₀ (2 + a + b) x (D x)))
          (Integral.Connection.unitZeroSec (I := I) (M := M) x))) :=
    ContMDiff.clm_bundle_apply (b := id) htrace
      (Integral.Connection.unitZeroSec (I := I) (M := M)).contMDiff
  refine htraceUnit.congr (fun x => ?_)
  congr 1
  apply Tensor0SBundle.Tensor0SSpace.toModel_injective
  beta_reduce
  rw [Tensor0SBundle.Tensor0SSpace.toModel_ofModel,
    cometricCcModelFun_eq_modelDoubleTrace_perm (cometricCcReadingModel (I := I) g₀ x) a b
      (cometricCcUnitModel (I := I) g₀ S x) (cometricCcUnitModel (I := I) g₀ T x)]
  rw [cometricCcReadingModel_eq]
  rw [← model_contract_trace_raiseSlot0ModelL
    (E := E) (2 + a + b) (cometricLmodel (I := I) g₀ x)
    (modelRankCast (E := E)
      (by omega : (2 + b) + (2 + a) = (2 + a + b) + 2)
      (ContinuousMultilinearMap.domDomCongr (cometricCcPerm a b)
        (Bundle.continuousMultilinearMap.modelProduct (𝕜 := ℝ) (F := E) (2 + b) (2 + a)
          (cometricCcUnitModel (I := I) g₀ T x) (cometricCcUnitModel (I := I) g₀ S x))))]
  rw [contract_trace_unitZero_toModel (I := I) (2 + a + b) x
    (cometricRaiseSlot0Fib (I := I) g₀ (2 + a + b) x (D x))]
  congr 1

/-- **The cross model fibre field** of the single `g₀`-contraction of two factor sections. -/
noncomputable def cometricCcField (g₀ : SmoothRiemannianMetric I M) {a b : ℕ}
    (S : SmoothCcTensor g₀ 0 (2 + a)) (T : SmoothCcTensor g₀ 0 (2 + b)) :
    Tensor0SBundle.Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) ∞ (2 + a + b) :=
  letI := Tensor0SBundle.tensor0SBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) (2 + a + b)
  letI := TangentBundle.contMDiffVectorBundle (I := I) (M := M) (n := ∞)
  ⟨fun x => Tensor0SBundle.Tensor0SSpace.ofModel
      (cometricCcModelFun (E := E) (cometricCcReadingModel (I := I) g₀ x) a b
        (cometricCcUnitModel (I := I) g₀ S x) (cometricCcUnitModel (I := I) g₀ T x)),
    cometricCcField_contMDiff (I := I) g₀ S T⟩

/-- **The section-level cross parallel `g₀`-single contraction** `(0, 2 + a) ⊗ (0, 2 + b) →
(0, 2 + a + b)`. -/
noncomputable def cometricParallelContraction (g₀ : SmoothRiemannianMetric I M) {a b : ℕ}
    (S : SmoothCcTensor g₀ 0 (2 + a)) (T : SmoothCcTensor g₀ 0 (2 + b)) :
    SmoothCcTensor g₀ 0 (2 + a + b) where
  toSection :=
    MixedSection.fromMultilinearSection (𝕜 := ℝ) (F := E) (IB := I)
      (E := (TangentSpace I : M → Type _)) ∞ (cometricCcField (I := I) g₀ S T)
  hasCompactSupport := HasCompactSupport.of_compactSpace _

/-! ## The operator-field bridge: the parallel contraction as a fixed-cometric post-composition -/

/-- **The frame-free slot-permuted model tensor-product section** `(0, (2 + b) + (2 + a))`. -/
noncomputable def cometricCcProdField (g₀ : SmoothRiemannianMetric I M) {a b : ℕ}
    (S : SmoothCcTensor g₀ 0 (2 + a)) (T : SmoothCcTensor g₀ 0 (2 + b)) :
    Tensor0SBundle.Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) ∞ ((2 + b) + (2 + a)) :=
  letI := Tensor0SBundle.tensor0SBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) ((2 + b) + (2 + a))
  letI := TangentBundle.contMDiffVectorBundle (I := I) (M := M) (n := ∞)
  ⟨fun x => Tensor0SBundle.Tensor0SSpace.ofModel
      (ContinuousMultilinearMap.domDomCongr (cometricCcPerm a b)
        (Bundle.continuousMultilinearMap.modelProduct (𝕜 := ℝ) (F := E) (2 + b) (2 + a)
          (cometricCcUnitModel (I := I) g₀ T x) (cometricCcUnitModel (I := I) g₀ S x))),
    cometricCcProdField_contMDiff (I := I) g₀ S T⟩

noncomputable def cometricCcProdSection (g₀ : SmoothRiemannianMetric I M) {a b : ℕ}
    (S : SmoothCcTensor g₀ 0 (2 + a)) (T : SmoothCcTensor g₀ 0 (2 + b)) :
    SmoothCcTensor g₀ 0 ((2 + b) + (2 + a)) where
  toSection :=
    MixedSection.fromMultilinearSection (𝕜 := ℝ) (F := E) (IB := I)
      (E := (TangentSpace I : M → Type _)) ∞ (cometricCcProdField (I := I) g₀ S T)
  hasCompactSupport := HasCompactSupport.of_compactSpace _

/-- The fibre value of the cometric double-trace operator field at `x`. -/
private noncomputable def cometricCcOpFib (g₀ : SmoothRiemannianMetric I M) (a b : ℕ) (x : M) :
    Tensor0SBundle.TensorRSSpace ((2 + b) + (2 + a)) (2 + a + b) I x :=
  (Tensor0SBundle.tensor0SSpace_continuousLinearEquiv (I := I) (2 + a + b) x).symm.toContinuousLinearMap.comp
    ((modelDoubleTrace (E := E) (2 + a + b)
        (cometricLmodel (I := I) g₀ x)).comp
      ((modelRankCast (E := E)
          (by omega : (2 + b) + (2 + a) = (2 + a + b) + 2)).comp
        (Tensor0SBundle.tensor0SSpace_continuousLinearEquiv (I := I) ((2 + b) + (2 + a)) x).toContinuousLinearMap))

set_option linter.unusedSectionVars false in
/-- The model image of the cometric double-trace fibre operator. -/
theorem cometricCcOpFib_toModel (g₀ : SmoothRiemannianMetric I M) (a b : ℕ) (x : M)
    (P : Tensor0SBundle.Tensor0SSpace ((2 + b) + (2 + a)) I x) :
    Tensor0SBundle.Tensor0SSpace.toModel
        ((show Tensor0SBundle.Tensor0SSpace ((2 + b) + (2 + a)) I x →L[ℝ]
            Tensor0SBundle.Tensor0SSpace (2 + a + b) I x from cometricCcOpFib (I := I) g₀ a b x) P) =
      modelDoubleTrace (E := E) (2 + a + b)
          (cometricLmodel (I := I) g₀ x)
        (modelRankCast (E := E)
          (by omega : (2 + b) + (2 + a) = (2 + a + b) + 2)
          (Tensor0SBundle.Tensor0SSpace.toModel P)) := rfl

/-- **Base-point smoothness of the cometric double-trace operator field**. -/
private theorem cometricCcOpFib_contMDiff (g₀ : SmoothRiemannianMetric I M) (a b : ℕ) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel ((2 + b) + (2 + a)) (2 + a + b) ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SBundle.TensorRSModel ((2 + b) + (2 + a)) (2 + a + b) ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace ((2 + b) + (2 + a)) (2 + a + b) I z) x
        (cometricCcOpFib (I := I) g₀ a b x)) := by
  apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
    (F₁ := Tensor0SBundle.Tensor0SModel ((2 + b) + (2 + a)) ℝ E)
    (V₁ := fun x : M => Tensor0SBundle.Tensor0SSpace ((2 + b) + (2 + a)) I x)
    (F₂ := Tensor0SBundle.Tensor0SModel (2 + a + b) ℝ E)
    (V₂ := fun x : M => Tensor0SBundle.Tensor0SSpace (2 + a + b) I x)
    (φ := fun x => cometricCcOpFib (I := I) g₀ a b x)
  intro Y
  let Y' : ∀ x : M, Tensor0SBundle.Tensor0SSpace ((2 + a + b) + 2) I x :=
    fun x => Tensor0SBundle.Tensor0SSpace.ofModel
      (modelRankCast (E := E)
        (by omega : (2 + b) + (2 + a) = (2 + a + b) + 2)
        (Tensor0SBundle.Tensor0SSpace.toModel (Y x)))
  have hY' : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel ((2 + a + b) + 2) ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel ((2 + a + b) + 2) ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace ((2 + a + b) + 2) I z) x (Y' x)) :=
    tensor0SField_castRank_contMDiff
      (I := I) (by omega : (2 + b) + (2 + a) = (2 + a + b) + 2) (fun x => Y x) Y.contMDiff
  have hraise := cometricRaiseSlot0Fib_section_contMDiff (I := I) g₀ (2 + a + b) Y' hY'
  have htrace := contractTraceField_contMDiff (I := I) 0 (2 + a + b)
    (fun x => cometricRaiseSlot0Fib (I := I) g₀ (2 + a + b) x (Y' x)) hraise
  have htraceUnit : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel (2 + a + b) ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel (2 + a + b) ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace (2 + a + b) I z) x
        ((show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace (2 + a + b) I x from
          Tensor0SBundle.contract_trace (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 0 (2 + a + b) x
            (cometricRaiseSlot0Fib (I := I) g₀ (2 + a + b) x (Y' x)))
          (Integral.Connection.unitZeroSec (I := I) (M := M) x))) :=
    ContMDiff.clm_bundle_apply (b := id) htrace
      (Integral.Connection.unitZeroSec (I := I) (M := M)).contMDiff
  refine htraceUnit.congr (fun x => ?_)
  congr 1
  apply Tensor0SBundle.Tensor0SSpace.toModel_injective
  beta_reduce
  rw [cometricCcOpFib_toModel]
  rw [← model_contract_trace_raiseSlot0ModelL
    (E := E) (2 + a + b) (cometricLmodel (I := I) g₀ x)
    (modelRankCast (E := E)
      (by omega : (2 + b) + (2 + a) = (2 + a + b) + 2)
      (Tensor0SBundle.Tensor0SSpace.toModel (Y x)))]
  rw [contract_trace_unitZero_toModel (I := I) (2 + a + b) x
    (cometricRaiseSlot0Fib (I := I) g₀ (2 + a + b) x (Y' x))]
  congr 1

/-- **The fixed smooth cometric double-trace operator field** as a `SmoothCcTensor`. -/
noncomputable def cometricCcOp (g₀ : SmoothRiemannianMetric I M) (a b : ℕ) :
    SmoothCcTensor g₀ ((2 + b) + (2 + a)) (2 + a + b) where
  toSection :=
    { toFun := fun x : M => cometricCcOpFib (I := I) g₀ a b x
      contMDiff_toFun := cometricCcOpFib_contMDiff (I := I) g₀ a b }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

/-- **The parallel contraction is the operator-field action of the fixed cometric double-trace field
on the frame-free product section**. -/
theorem cometricParallelContraction_eq_appCcRS (g₀ : SmoothRiemannianMetric I M) {a b : ℕ}
    (S : SmoothCcTensor g₀ 0 (2 + a)) (T : SmoothCcTensor g₀ 0 (2 + b)) :
    cometricParallelContraction (I := I) g₀ S T =
      appCcRS (I := I) (M := M) g₀ 0 ((2 + b) + (2 + a)) (2 + a + b)
        (cometricCcOp (I := I) g₀ a b) (cometricCcProdSection (I := I) g₀ S T) := by
  classical
  apply Integral.L2.SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply tensor0s_ext_unitZero (I := I) (M := M) (s := 2 + a + b)
  apply Tensor0SBundle.Tensor0SSpace.toModel_injective
  beta_reduce
  have hLHS : Tensor0SBundle.Tensor0SSpace.toModel
      ((cometricParallelContraction (I := I) g₀ S T).toSection x
        (Integral.Connection.unitZeroSec (I := I) (M := M) x)) =
      cometricCcModelFun (E := E) (cometricCcReadingModel (I := I) g₀ x) a b
        (cometricCcUnitModel (I := I) g₀ S x) (cometricCcUnitModel (I := I) g₀ T x) := by
    change Tensor0SBundle.Tensor0SSpace.toModel
        ((MixedSection.eval₀ (F := E) (E := (TangentSpace I : M → Type _)) x).smulRight
            (cometricCcField (I := I) g₀ S T x)
          (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ))) = _
    rw [ContinuousLinearMap.smulRight_apply, MixedSection.eval₀_apply,
      ContinuousMultilinearMap.constOfIsEmpty_apply, one_smul]
    change Tensor0SBundle.Tensor0SSpace.toModel
      (Tensor0SBundle.Tensor0SSpace.ofModel
        (cometricCcModelFun (E := E) (cometricCcReadingModel (I := I) g₀ x) a b
          (cometricCcUnitModel (I := I) g₀ S x) (cometricCcUnitModel (I := I) g₀ T x))) = _
    rw [Tensor0SBundle.Tensor0SSpace.toModel_ofModel]
  have hRHS : Tensor0SBundle.Tensor0SSpace.toModel
      ((appCcRS (I := I) (M := M) g₀ 0 ((2 + b) + (2 + a)) (2 + a + b)
          (cometricCcOp (I := I) g₀ a b) (cometricCcProdSection (I := I) g₀ S T)).toSection x
        (Integral.Connection.unitZeroSec (I := I) (M := M) x)) =
      modelDoubleTrace (E := E) (2 + a + b)
          (cometricLmodel (I := I) g₀ x)
        (modelRankCast (E := E)
          (by omega : (2 + b) + (2 + a) = (2 + a + b) + 2)
          (ContinuousMultilinearMap.domDomCongr (cometricCcPerm a b)
            (Bundle.continuousMultilinearMap.modelProduct (𝕜 := ℝ) (F := E) (2 + b) (2 + a)
              (cometricCcUnitModel (I := I) g₀ T x) (cometricCcUnitModel (I := I) g₀ S x)))) := by
    rw [appCcRS_toSection (I := I) (M := M) g₀ 0 ((2 + b) + (2 + a)) (2 + a + b)
      (cometricCcOp (I := I) g₀ a b) (cometricCcProdSection (I := I) g₀ S T) x]
    rw [ContinuousLinearMap.comp_apply]
    rw [show (cometricCcOp (I := I) g₀ a b).toSection x
        = cometricCcOpFib (I := I) g₀ a b x from rfl]
    rw [cometricCcOpFib_toModel]
    have hP : Tensor0SBundle.Tensor0SSpace.toModel
        ((show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ]
            Tensor0SBundle.Tensor0SSpace ((2 + b) + (2 + a)) I x from
          (cometricCcProdSection (I := I) g₀ S T).toSection x)
          (Integral.Connection.unitZeroSec (I := I) (M := M) x)) =
        ContinuousMultilinearMap.domDomCongr (cometricCcPerm a b)
          (Bundle.continuousMultilinearMap.modelProduct (𝕜 := ℝ) (F := E) (2 + b) (2 + a)
            (cometricCcUnitModel (I := I) g₀ T x) (cometricCcUnitModel (I := I) g₀ S x)) := by
      change Tensor0SBundle.Tensor0SSpace.toModel
          ((MixedSection.eval₀ (F := E) (E := (TangentSpace I : M → Type _)) x).smulRight
              (cometricCcProdField (I := I) g₀ S T x)
            (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ))) = _
      rw [ContinuousLinearMap.smulRight_apply, MixedSection.eval₀_apply,
        ContinuousMultilinearMap.constOfIsEmpty_apply, one_smul]
      change Tensor0SBundle.Tensor0SSpace.toModel
        (Tensor0SBundle.Tensor0SSpace.ofModel
          (ContinuousMultilinearMap.domDomCongr (cometricCcPerm a b)
            (Bundle.continuousMultilinearMap.modelProduct (𝕜 := ℝ) (F := E) (2 + b) (2 + a)
              (cometricCcUnitModel (I := I) g₀ T x) (cometricCcUnitModel (I := I) g₀ S x)))) = _
      rw [Tensor0SBundle.Tensor0SSpace.toModel_ofModel]
    rw [hP]
  rw [hLHS, hRHS,
    cometricCcModelFun_eq_modelDoubleTrace_perm (cometricCcReadingModel (I := I) g₀ x) a b
      (cometricCcUnitModel (I := I) g₀ S x) (cometricCcUnitModel (I := I) g₀ T x),
    cometricCcReadingModel_eq]

/-! ## The concrete identification: the parallel contraction realizes `crossCometricSection`

The parallel `g₀`-single contraction, evaluated at the symmetric realized perturbation
`h = realizeSymm T₁` (rank `2`) and the slot-swapped cometric inverse-difference section
`permute c[1,0] (cometricInverseDiffSection g₁ g₀)` (rank `2`), reproduces the cometric
cross-correction `(0, 2)`-section `crossCometricSection` exactly.  The model contraction raises the
lowered cometric-inverse-difference output index by the cometric and reconstructs the genuine raised
representative `D = gInvDiffRaisedEndo g₀ g₁` through the cometric dual pair, then feeds it into the
realized perturbation `h`. -/

set_option linter.unusedSectionVars false in
/-- **The fibrewise model value of the single `g₀`-contraction at `(a, b) = (0, 0)`.**  For a
`(0, 2)`-factor `Sm` and a `(0, 2)`-factor `Tm`, the contraction's value at `![p, q]` sums over the
model-basis index `i` the product `Tm![eᵢ, p] · Sm![L(eⁱ), q]`. -/
theorem cometricCcModelFun_eval00 (L : Tensor0SBundle.Tensor0SModel 1 ℝ E →L[ℝ] E)
    (Sm : Tensor0SBundle.Tensor0SModel (2 + 0) ℝ E) (Tm : Tensor0SBundle.Tensor0SModel (2 + 0) ℝ E)
    (p q : E) :
    cometricCcModelFun (E := E) L 0 0 Sm Tm ![p, q] =
      ∑ i : Fin (Module.finrank ℝ E),
        Tm ![(Module.finBasis ℝ E) i, p] *
          Sm ![L (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
            ((Module.finBasis ℝ E).cDualBasis i)), q] := by
  classical
  unfold cometricCcModelFun
  rw [cometricModelRankCast_apply', ContinuousMultilinearMap.sum_apply]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Bundle.continuousMultilinearMap.modelProduct_apply]
  have hT : ((Tensor0SBundle.model_interior_product (1 + 0) ((Module.finBasis ℝ E) i))
        ((cometricModelRankCast (E := E) (by omega : 2 + 0 = (1 + 0) + 1) Tm)))
        ((fun j => (![p, q] : Fin 2 → E) (finCongr (by omega : (1+0)+(1+0)=2+0+0) j)) ∘ Fin.castAdd (1 + 0))
      = Tm ![(Module.finBasis ℝ E) i, p] := by
    change (cometricModelRankCast (E := E) (by omega : 2 + 0 = (1 + 0) + 1) Tm)
        (Fin.cons ((Module.finBasis ℝ E) i) _) = _
    rw [cometricModelRankCast_apply']
    congr 1
    funext j; fin_cases j <;> rfl
  have hS : ((Tensor0SBundle.model_interior_product (1 + 0)
        (L (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E) ((Module.finBasis ℝ E).cDualBasis i))))
        ((cometricModelRankCast (E := E) (by omega : 2 + 0 = (1 + 0) + 1) Sm)))
        ((fun j => (![p, q] : Fin 2 → E) (finCongr (by omega : (1+0)+(1+0)=2+0+0) j)) ∘ Fin.natAdd (1 + 0))
      = Sm ![L (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E) ((Module.finBasis ℝ E).cDualBasis i)), q] := by
    change (cometricModelRankCast (E := E) (by omega : 2 + 0 = (1 + 0) + 1) Sm)
        (Fin.cons (L (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E) ((Module.finBasis ℝ E).cDualBasis i))) _) = _
    rw [cometricModelRankCast_apply']
    congr 1
    funext j; fin_cases j <;> rfl
  rw [hT, hS]

set_option linter.unusedSectionVars false in
/-- The cometric reading of the model dual basis pairs with a tangent vector to give the chart-basis
coordinate. -/
theorem cometricCcReadingModel_dualBasis_inner (g₀ : SmoothRiemannianMetric I M) (y : M)
    (k : Fin (Module.finrank ℝ E)) (u : TangentSpace I y) :
    g₀.inner y (cometricCcReadingModel (I := I) g₀ y
        (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
          ((Module.finBasis ℝ E).cDualBasis k))) u =
      (Module.finBasis ℝ E).repr (u : E) k := by
  have h1 : cometricCcReadingModel (I := I) g₀ y
        (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
          ((Module.finBasis ℝ E).cDualBasis k)) =
      inverseMetricSharpFib (I := I) g₀ y
        ((Tensor0SBundle.tensor0SSpace_continuousLinearEquiv (𝕜 := ℝ) (I := I) 1 y).symm
          (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
            ((Module.finBasis ℝ E).cDualBasis k))) := rfl
  rw [h1, inverseMetricSharpFib_inner (I := I) g₀ y _ u, cotangentToDualLinear_apply,
    cotangentToDual_apply]
  have h2 : (((Tensor0SBundle.tensor0SSpace_continuousLinearEquiv (𝕜 := ℝ) (I := I) 1 y).symm
        (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
          ((Module.finBasis ℝ E).cDualBasis k))) (fun _ : Fin 1 => u) : ℝ) =
      Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
        ((Module.finBasis ℝ E).cDualBasis k) (fun _ : Fin 1 => (u : E)) := rfl
  rw [h2, Tensor0SBundle.model_covectorOfCLM_apply]
  rw [show ((Module.finBasis ℝ E).cDualBasis k) =
      LinearMap.toContinuousLinearMap ((Module.finBasis ℝ E).coord k) from by
    rw [Module.Basis.cDualBasis, Module.Basis.map_apply]
    congr 1
    exact congrFun (Module.Basis.coe_dualBasis (Module.finBasis ℝ E)) k]
  rw [LinearMap.coe_toContinuousLinearMap', Module.Basis.coord_apply]

set_option linter.unusedSectionVars false in
/-- The cometric dual-pair coordinate trace, rank-`1` specialization. -/
theorem cometricCc_sum_phi_cometric_inner_basis (g₀ : SmoothRiemannianMetric I M) (x : M)
    (P : Fin (Module.finrank ℝ E) → TangentSpace I x)
    (hP : ∀ (k : Fin (Module.finrank ℝ E)) (u : TangentSpace I x),
      g₀.inner x (P k) u = (Module.finBasis ℝ E).repr (u : E) k)
    (φ : TangentSpace I x →L[ℝ] ℝ) (V : TangentSpace I x) :
    ∑ i : Fin (Module.finrank ℝ E),
        φ (P i) * g₀.inner x V ((Module.finBasis ℝ E) i) = φ V := by
  classical
  set F : TangentSpace I x →L[ℝ] TangentSpace I x := φ.smulRight V with hF
  have key := sum_inner_dualPair_apply_eq_sum_chartBasis_repr (I := I) (M := M) g₀ x P hP F
  have hLHS : ∑ i : Fin (Module.finrank ℝ E), φ (P i) * g₀.inner x V ((Module.finBasis ℝ E) i)
      = ∑ k : Fin (Module.finrank ℝ E), g₀.inner x (F (P k)) ((Module.finBasis ℝ E) k) := by
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [hF, ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.map_smul,
      ContinuousLinearMap.smul_apply, smul_eq_mul]
  have htr : ∑ i : Fin (Module.finrank ℝ E),
        (chartModelBasis E).repr (F ((chartModelBasis E) i)) i
      = LinearMap.trace ℝ (TangentSpace I x) (F : TangentSpace I x →ₗ[ℝ] TangentSpace I x) :=
    (trace_eq_sum_basis_repr (I := I) (M := M) x (chartModelBasis E) F).symm
  rw [hLHS, key, htr, hF]
  rw [show ((ContinuousLinearMap.smulRight φ V : TangentSpace I x →L[ℝ] TangentSpace I x) :
        TangentSpace I x →ₗ[ℝ] TangentSpace I x)
      = LinearMap.smulRight (φ : TangentSpace I x →ₗ[ℝ] ℝ) V from rfl]
  rw [LinearMap.trace_smulRight]
  rfl

set_option linter.unusedSectionVars false in
/-- The unit-model value of the parallel contraction at `(0, 0)`, read at a tangent pair. -/
theorem cometricParallelContraction_toModel_apply (g₀ : SmoothRiemannianMetric I M)
    (S : Integral.L2.SmoothCcTensor g₀ 0 (2 + 0)) (T : Integral.L2.SmoothCcTensor g₀ 0 (2 + 0)) (x : M)
    (v : Fin 2 → TangentSpace I x) :
    Tensor0SBundle.Tensor0SSpace.toModel
        ((cometricParallelContraction (I := I) g₀ (a := 0) (b := 0) S T).toSection x
          (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ))) v =
      cometricCcModelFun (E := E) (cometricCcReadingModel (I := I) g₀ x) 0 0
        (cometricCcUnitModel (I := I) g₀ S x) (cometricCcUnitModel (I := I) g₀ T x) v := by
  classical
  change Tensor0SBundle.Tensor0SSpace.toModel
      ((MixedSection.eval₀ (F := E) (E := (TangentSpace I : M → Type _)) x).smulRight
          (cometricCcField (I := I) g₀ S T x)
        (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ))) v = _
  rw [ContinuousLinearMap.smulRight_apply, MixedSection.eval₀_apply,
    ContinuousMultilinearMap.constOfIsEmpty_apply, one_smul]
  change Tensor0SBundle.Tensor0SSpace.toModel
    (Tensor0SBundle.Tensor0SSpace.ofModel
      (cometricCcModelFun (E := E) (cometricCcReadingModel (I := I) g₀ x) 0 0
        (cometricCcUnitModel (I := I) g₀ S x) (cometricCcUnitModel (I := I) g₀ T x))) v = _
  rw [Tensor0SBundle.Tensor0SSpace.toModel_ofModel]

set_option linter.unusedSectionVars false in
/-- **The cross contraction realizes the cometric cross-correction section.**

```
cometricParallelContraction g₀ (realizeSymmCcTensor g₀ T₁)
    (permuteCcTensor g₀ c[1, 0] (cometricInverseDiffSection g₁ g₀))
  = crossCometricSection g₁ g₀ T₁.
```

Both sides' unit-evaluated model fibre value, on a tangent pair `(v 0, v 1)`, are
`ccTensorBilinSymm g₀ T₁ x (gInvDiffRaisedEndo g₀ g₁ x (v 0)) (v 1) = h(D (v 0), v 1)`: the right side
by `crossCometricSection_toModel_apply`, the left by `cometricCcModelFun_eval00` plus the cometric
dual-pair coordinate trace `cometricCc_sum_phi_cometric_inner_basis` reconstructing `D (v 0)` from the
cometric inverse-difference section's `g₀(D (v 0), ·)` slot. -/
theorem cometricParallelContraction_eq_cometricCrossSection
    (g₀ g₁ : SmoothRiemannianMetric I M) (T₁ : Integral.L2.SmoothCcTensor g₀ 0 2) :
    cometricParallelContraction (I := I) g₀ (a := 0) (b := 0)
        (realizeSymmCcTensor (I := I) g₀ T₁)
        (permuteCcTensor (I := I) g₀ c[(1 : Fin 2), 0]
          (cometricInverseDiffSection (I := I) g₁ g₀))
      = crossCometricSection (I := I) g₁ g₀ T₁ := by
  classical
  apply Integral.L2.SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply tensor0s_ext_unitZero (I := I) (M := M) (s := 2)
  apply Tensor0SBundle.Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro v
  have hvtuple : v = ![v 0, v 1] := by funext i; fin_cases i <;> rfl
  -- RHS unit model value: `h(D (v 0), v 1)`.
  have hRHS : Tensor0SBundle.Tensor0SSpace.toModel
      ((crossCometricSection (I := I) g₁ g₀ T₁).toSection x
        (unitZeroSec (I := I) (M := M) x)) v =
      ccTensorBilinSymm (I := I) g₀ T₁ x (gInvDiffRaisedEndo (I := I) g₀ g₁ x (v 0)) (v 1) := by
    rw [show (unitZeroSec (I := I) (M := M) x : Tensor0SBundle.Tensor0SSpace 0 I x)
        = ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ) from rfl]
    rw [hvtuple]
    exact crossCometricSection_toModel_apply (I := I) g₁ g₀ T₁ x (v 0) (v 1)
  -- LHS unit model value.
  have hLHS : Tensor0SBundle.Tensor0SSpace.toModel
      ((cometricParallelContraction (I := I) g₀ (a := 0) (b := 0)
          (realizeSymmCcTensor (I := I) g₀ T₁)
          (permuteCcTensor (I := I) g₀ c[(1 : Fin 2), 0]
            (cometricInverseDiffSection (I := I) g₁ g₀))).toSection x
        (unitZeroSec (I := I) (M := M) x)) v =
      ccTensorBilinSymm (I := I) g₀ T₁ x (gInvDiffRaisedEndo (I := I) g₀ g₁ x (v 0)) (v 1) := by
    rw [show (unitZeroSec (I := I) (M := M) x : Tensor0SBundle.Tensor0SSpace 0 I x)
        = ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ) from rfl]
    rw [cometricParallelContraction_toModel_apply (I := I) g₀
      (realizeSymmCcTensor (I := I) g₀ T₁)
      (permuteCcTensor (I := I) g₀ c[(1 : Fin 2), 0] (cometricInverseDiffSection (I := I) g₁ g₀)) x v]
    rw [hvtuple]
    rw [cometricCcModelFun_eval00 (E := E) (cometricCcReadingModel (I := I) g₀ x)
      (cometricCcUnitModel (I := I) g₀ (realizeSymmCcTensor (I := I) g₀ T₁) x)
      (cometricCcUnitModel (I := I) g₀ (permuteCcTensor (I := I) g₀ c[(1 : Fin 2), 0]
        (cometricInverseDiffSection (I := I) g₁ g₀)) x) (v 0) (v 1)]
    -- The `Sm`-factor: `realizeSymm` reads `h`.
    have hA : ∀ i : Fin (Module.finrank ℝ E),
        cometricCcUnitModel (I := I) g₀ (realizeSymmCcTensor (I := I) g₀ T₁) x
          ![cometricCcReadingModel (I := I) g₀ x
              (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                ((Module.finBasis ℝ E).cDualBasis i)), v 1]
          = ccTensorBilinSymm (I := I) g₀ T₁ x
              (cometricCcReadingModel (I := I) g₀ x
                (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                  ((Module.finBasis ℝ E).cDualBasis i))) (v 1) := by
      intro i
      rw [← realizeSymmCcTensor_ccTensorBilin_apply, ccTensorBilin_apply]; rfl
    -- The `Tm`-factor: `permute c[1,0] cometricInverseDiff` reads `g₀(D (v 0), eᵢ)`.
    have hB : ∀ i : Fin (Module.finrank ℝ E),
        cometricCcUnitModel (I := I) g₀ (permuteCcTensor (I := I) g₀ c[(1 : Fin 2), 0]
            (cometricInverseDiffSection (I := I) g₁ g₀)) x
          ![(Module.finBasis ℝ E) i, v 0]
          = g₀.inner x (gInvDiffRaisedEndo (I := I) g₀ g₁ x (v 0)) ((Module.finBasis ℝ E) i) := by
      intro i
      change DifferentialGeometry.Analysis.Parabolic.TensorSpectral.unitModel (I := I) (M := M) g₀ 2
          (permuteCcTensor (I := I) g₀ c[(1 : Fin 2), 0] (cometricInverseDiffSection (I := I) g₁ g₀)) x
          ![(Module.finBasis ℝ E) i, v 0] = _
      rw [permuteCcTensor_unitModel (I := I) g₀ c[(1 : Fin 2), 0]
        (cometricInverseDiffSection (I := I) g₁ g₀) x]
      rw [show (ContinuousMultilinearMap.domDomCongr c[(1 : Fin 2), 0]
            (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.unitModel (I := I) (M := M) g₀ 2
              (cometricInverseDiffSection (I := I) g₁ g₀) x)) ![(Module.finBasis ℝ E) i, v 0]
          = DifferentialGeometry.Analysis.Parabolic.TensorSpectral.unitModel (I := I) (M := M) g₀ 2
              (cometricInverseDiffSection (I := I) g₁ g₀) x ![v 0, (Module.finBasis ℝ E) i] from by
        rw [ContinuousMultilinearMap.domDomCongr_apply]; congr 1; funext j; fin_cases j <;> rfl]
      change Tensor0SBundle.Tensor0SSpace.toModel
        ((cometricInverseDiffSection (I := I) g₁ g₀).toSection x
          (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ)))
            ![v 0, (Module.finBasis ℝ E) i] = _
      rw [cometricInverseDiffSection_toModel_apply (I := I) g₁ g₀ x (v 0) ((Module.finBasis ℝ E) i)]
    rw [Finset.sum_congr rfl (fun i _ => by rw [hA i, hB i])]
    have hflip : ∀ w : TangentSpace I x,
        ccTensorBilinSymm (I := I) g₀ T₁ x w (v 1)
          = (ccTensorBilinSymm (I := I) g₀ T₁ x).flip (v 1) w := fun w => rfl
    rw [show (∑ i : Fin (Module.finrank ℝ E),
          g₀.inner x (gInvDiffRaisedEndo (I := I) g₀ g₁ x (v 0)) ((Module.finBasis ℝ E) i)
            * ccTensorBilinSymm (I := I) g₀ T₁ x
                (cometricCcReadingModel (I := I) g₀ x
                  (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                    ((Module.finBasis ℝ E).cDualBasis i))) (v 1))
        = ∑ i : Fin (Module.finrank ℝ E),
            ((ccTensorBilinSymm (I := I) g₀ T₁ x).flip (v 1))
                (cometricCcReadingModel (I := I) g₀ x
                  (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                    ((Module.finBasis ℝ E).cDualBasis i)))
              * g₀.inner x (gInvDiffRaisedEndo (I := I) g₀ g₁ x (v 0)) ((Module.finBasis ℝ E) i) from by
      refine Finset.sum_congr rfl (fun i _ => ?_); rw [hflip]; ring]
    rw [cometricCc_sum_phi_cometric_inner_basis (I := I) g₀ x
      (fun i => cometricCcReadingModel (I := I) g₀ x
        (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
          ((Module.finBasis ℝ E).cDualBasis i)))
      (fun k u => cometricCcReadingModel_dualBasis_inner (I := I) g₀ x k u)
      ((ccTensorBilinSymm (I := I) g₀ T₁ x).flip (v 1))
      (gInvDiffRaisedEndo (I := I) g₀ g₁ x (v 0))]
    rfl
  rw [hLHS, hRHS]

end Connection
end Integral
end DifferentialGeometry

end
