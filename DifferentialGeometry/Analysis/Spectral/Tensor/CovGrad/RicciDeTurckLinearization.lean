import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.BareTensorProductCovariantLeibniz
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.CovariantBilinearLeibniz
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.CometricDoubleTraceField
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.MetricContractionLeibnizGrid
import DifferentialGeometry.Geometry.Connection.TensorNabla.OperatorFieldContractionBound
import DifferentialGeometry.Geometry.Connection.TensorNabla.OperatorFieldCovariantCalculusRS
import DifferentialGeometry.Geometry.Connection.SingleSlotOperatorFiberNormBound
import DifferentialGeometry.Analysis.Spectral.Tensor.ChartTensor.Inner.InnerBridge
import DifferentialGeometry.Analysis.Spectral.Tensor.ChartTensor.Inner.LowerAllUpperIndices
import DifferentialGeometry.Analysis.Spectral.Tensor.ChartTensor.InnerBounds.InnerLowerBound
import DifferentialGeometry.Analysis.Sobolev.HebeyBlock.ChartParallelTransportOpNorm.ChartLeviCivitaParallelCLM
import DifferentialGeometry.Analysis.Sobolev.Manifold.Rellich
import DifferentialGeometry.Analysis.Elliptic.MetricBounds

/-! # The intrinsic metric-variation foundation of the Ricci–DeTurck right-hand side

For a closed (compact, boundaryless) smooth Riemannian manifold `(M, g)` modelled on a real
inner-product space `E`, the Ricci–DeTurck right-hand side
`F(g) = −2 Ric(g) + 𝓛_{W(g, g_bg)}(g)` is a second-order quasilinear Nemytskii nonlinearity in the
metric.  Its mean-value Fréchet linearization `dF(g)[h]` is a second-order operator
`coeff₀·h + coeff₁·∇h + coeff₂·∇²h` whose intrinsic, chart-free symbols are built from the curvature,
the Christoffel variation, and the inverse-metric (Neumann-series) variation along the metric path.

This file builds the **chart-free `unitModel`-extensionality foundation** of that linearization — the
keystone every concrete `SmoothCcTensor`-valued metric-variation identity needs to lift its on-disk
`unitModel`-component form to a genuine `SmoothCcTensor` equality:

* `smoothCcTensor_ext_of_unitModel` — lifts a pointwise `unitModel`-component equality of two smooth
  compactly-supported `(0, s)`-tensors to a genuine `SmoothCcTensor` equality (the general-rank form of
  the rank-`3` unit-extensionality `tensor03_ext_unit`), via the unit-tensor scalar identity
  `zeroTensor_eq_smul_unitTensor`, the unit-CLM-extensionality `tensor0s_clm_ext_unit`, and
  `Tensor0SSpace.toModel`-injectivity.  No concrete `ParallelTensorProduct` value or section-level
  metric-variation identity exists on disk; this bridge is the missing primitive they all require.
* `unitModel_add`, `unitModel_castRankCc` — the additivity and rank-cast compatibility of the
  `unitModel`-component map, the bookkeeping lemmas the lift consumes.
* `domDomCongrSection` — the **constructive `SmoothCcTensor`-level slot-permutation operator**: for a
  fixed permutation `σ : Equiv.Perm (Fin s)` it reindexes the `s` covariant slots of a smooth
  compactly-supported `(0, s)`-tensor section, producing again a smooth `(0, s)`-tensor section
  (`domDomCongrSection_unitModel` reads off its unit fibre as the constant fibre reindexing
  `domDomCongr σ` of the original).  This is the constructive witness the posited naturality core
  `tensorCovDerivAt_unit_toModel_domDomCongr_of_section` (which currently *assumes* the section
  σ-relation as a hypothesis) requires to be instantiated: `domDomCongrSection σ S` is, by
  construction, the fibrewise σ-reindexing of `S`, so the naturality applies to the genuine pair
  `(S, domDomCongrSection σ S)`.  The fibre slot reindexing being a `g`-fibre isometry, the iterated
  covariant gradient and Riemannian fibre norm of the reindexed section match the original.

Everything is phrased in `unitModel` / `covGrad` / `Tensor0SSpace.toModel` — `g`-native and chart-free;
never a chart-jet ball Lipschitz chain, never the model `opNorm`, never the chart-component route.

## Structural note on the concrete `ParallelTensorProduct` witness

The canonical concrete `ParallelTensorProduct` (`CovariantBilinearLeibniz.lean`) is NOT the bare model
tensor product `unitModelProdSection`: its `covGrad_prod` field is *false-as-stated* for the bare product.
By `unitModel_unitModelProdSection_covGrad_right` (`BareTensorProductCovariantLeibniz.lean:1248`) the
right covariant-Leibniz summand `prod S (∇T)` carries its new gradient slot at the *mid* position
`s₁ + a`, whereas `covGrad (prod S T)` carries it at the *front* position `0`; the field equation omits
the reconciling slot-permutation `domDomCongr σ`.  The exact-field witness is a `g₀`-parallel metric
*contraction* (which collapses the contracted slots and reindexes the surviving gradient slot to the
front), whose front-slot covariant Leibniz is genuine deep intrinsic content — built on top of this
extensionality bridge.

## Main results

* `smoothCcTensor_ext_of_unitModel` — `unitModel`-component extensionality for `SmoothCcTensor g 0 s`.
* `unitModel_add`, `unitModel_castRankCc` — `unitModel`-component additivity and rank-cast compatibility.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators Matrix

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

/-! ## The `unitModel`-component extensionality bridge -/

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] in
/-- Every `(0, 0)`-tensor `D` is its scalar coordinate times the unit `(0, 0)`-tensor:
`D = (tensor0Iso M x D) • unitTensor x`.  The general-rank analogue of
`zeroTensor_eq_smul_unit`, stated for the `TensorSpectral.unitTensor` form (which is `rfl`-equal to
`unitZeroSec x`). -/
private theorem zeroTensor_eq_smul_unitTensor (x : M)
    (D : Tensor0SSpace 0 I x) :
    D = (Tensor0SNabla.tensor0Iso I M x D) • unitTensor (I := I) (M := M) x := by
  classical
  have hunit : Tensor0SNabla.tensor0Iso I M x (unitTensor (I := I) (M := M) x) = (1 : ℝ) := by
    have h := Tensor0SNabla.scalarFn_unitZero (I := I) (M := M)
    have hx := congrFun h x
    simpa [Tensor0SNabla.scalarFn_apply, unitTensor] using hx
  apply (Tensor0SNabla.tensor0Iso I M x).injective
  rw [map_smul, hunit, smul_eq_mul, mul_one]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] in
/-- **Unit-extensionality for `(0, s)`-tensors.** Two continuous linear maps
`φ, ψ : Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x` (i.e. two `(0, s)`-tensors) that agree on the
unit `(0, 0)`-tensor are equal.  The general-rank form of `tensor03_ext_unit`; the proof is
rank-independent (`zeroTensor_eq_smul_unitTensor` + `map_smul`). -/
private theorem tensor0s_clm_ext_unit {s : ℕ} {x : M}
    {φ ψ : Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x}
    (h : φ (unitTensor (I := I) (M := M) x) = ψ (unitTensor (I := I) (M := M) x)) :
    φ = ψ := by
  classical
  ext D
  rw [zeroTensor_eq_smul_unitTensor (I := I) (M := M) x D, map_smul, map_smul, h]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] in
/-- **`unitModel`-component extensionality for `SmoothCcTensor g 0 s`.**  Two smooth
compactly-supported `(0, s)`-tensors whose unit-evaluated model fibres agree at every base point are
equal.  This is the keystone bridge that lifts the on-disk unitModel-component covariant-Leibniz
identities (e.g. `unitModelProdSection_covGrad_unitModel`) to genuine `SmoothCcTensor` equalities.

`unitModel g s S x = toModel (S.toSection x (unitTensor x))`, so a pointwise `unitModel` equality gives,
through `Tensor0SSpace.toModel`-injectivity, the section value at the unit, and then through the
unit-extensionality `tensor0s_clm_ext_unit` the full section value; `SmoothCcTensor.ext` /
`ContMDiffSection.ext` close it. -/
theorem smoothCcTensor_ext_of_unitModel (g : SmoothRiemannianMetric I M) {s : ℕ}
    {S S' : SmoothCcTensor g 0 s}
    (h : ∀ x : M, unitModel (I := I) (M := M) g s S x = unitModel (I := I) (M := M) g s S' x) :
    S = S' := by
  classical
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  have hval : (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from S.toSection x)
      (unitTensor (I := I) (M := M) x) =
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from S'.toSection x)
        (unitTensor (I := I) (M := M) x) := by
    apply Tensor0SSpace.toModel_injective
    have := h x
    simpa [unitModel] using this
  exact tensor0s_clm_ext_unit (I := I) (M := M) hval

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M] in
/-- `unitModel` is additive in the section: `unitModel (S + S') = unitModel S + unitModel S'`. -/
private theorem unitModel_add (g : SmoothRiemannianMetric I M) (s : ℕ)
    (S S' : SmoothCcTensor g 0 s) (x : M) :
    unitModel (I := I) (M := M) g s (S + S') x =
      unitModel (I := I) (M := M) g s S x + unitModel (I := I) (M := M) g s S' x := by
  classical
  simp only [unitModel]
  rw [SmoothCcTensor.toSection_add, ContMDiffSection.coe_add, Pi.add_apply,
    ContinuousLinearMap.add_apply, Tensor0SSpace.toModel_add]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M] in
/-- The unit-evaluated model fibre of a rank-cast `castRankCc g 0 h W` is the rank-cast of the
unit-evaluated model fibre of `W`.  Proved by `subst` on the rank equality, which collapses the cast to
the identity on both sides. -/
private theorem unitModel_castRankCc (g : SmoothRiemannianMetric I M) {a b : ℕ} (h : a = b)
    (W : SmoothCcTensor g 0 a) (x : M) :
    unitModel (I := I) (M := M) g b (castRankCc g 0 h W) x =
      h ▸ unitModel (I := I) (M := M) g a W x := by
  subst h
  rfl

/-! ## The constructive `SmoothCcTensor`-level slot-permutation operator

The naturality core `tensorCovDerivAt_unit_toModel_domDomCongr_of_section`
(`CovGradSlotPermutationNaturality.lean`) is stated for a *pair* of smooth `(0, s)`-tensor sections
`S, S'` whose unit fibres are related by a constant slot reindexing `σ` (the hypothesis `hSS'`).  To
*instantiate* that core one needs, for a given `S`, an actual second section `S'` realizing the
reindexing.  This subsection constructs it: `domDomCongrSection σ S` is the smooth compactly-supported
`(0, s)`-tensor section whose unit fibre is, at every base point, the constant fibre reindexing
`domDomCongr σ (unitModel S x)`.  Then the pair `(S, domDomCongrSection σ S)` satisfies the naturality
hypothesis *by construction*, so every front-slot statement that previously had to assume the relation
now applies to a concrete witness.  The construction mirrors the bare model tensor-product section
`unitModelProdSection`: a smooth `(0, s)`-tensor field assembled through
`MixedSection.fromMultilinearSection`, with smoothness via the basis-coordinate criterion
`contMDiff_multilinearSection_iff_coord` (the reindexed coordinate is a relabeling of the original
smooth coordinate). -/

/-- The frame-free slot-reindexed model field `x ↦ ofModel (domDomCongr σ (unitModel S x))`, a smooth
`(0, s)`-tensor field.  The constant fibre reindexing of the smooth unit field of `S` is smooth: its
trivialised basis coordinate at `τ : Fin s → Fin d` is, by `domDomCongr_apply`, the `(τ ∘ σ)`-coordinate
of the smooth unit field of `S` — a relabeling, hence smooth (the basis-coordinate criterion
`contMDiff_multilinearSection_iff_coord`). -/
theorem domDomCongrField_contMDiff (g : SmoothRiemannianMetric I M) {s : ℕ}
    (σ : Equiv.Perm (Fin s)) (S : SmoothCcTensor g 0 s) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel s ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SModel s ℝ E)
        (E := fun z : M => Tensor0SSpace s I z) x
        ((Tensor0SSpace.ofModel (𝕜 := ℝ) (I := I) (x := x)
            (ContinuousMultilinearMap.domDomCongr σ
              (unitModel (I := I) (M := M) g s S x)) :
            Tensor0SSpace s I x))) := by
  letI := Tensor0SBundle.tensor0SBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) s
  classical
  have hSfield : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel s ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SModel s ℝ E)
        (E := fun z : M => Tensor0SSpace s I z) x
        (Tensor0SSpace.ofModel (unitModel (I := I) (M := M) g s S x))) := by
    simpa only [Tensor0SSpace.ofModel_toModel, unitModel] using
      (contMDiff_unitEvalSection (I := I) (M := M) g s S)
  refine (contMDiff_multilinearSection_iff_coord (𝕜 := ℝ) (F := E)
    (E := (TangentSpace I : M → Type _)) (IB := I) (n := (∞ : WithTop ℕ∞)) (Module.finBasis ℝ E)
    (fun x => (Tensor0SSpace.ofModel (𝕜 := ℝ) (I := I) (x := x)
        (ContinuousMultilinearMap.domDomCongr σ
          (unitModel (I := I) (M := M) g s S x)) :
          Tensor0SSpace s I x))).mpr ?_
  have hS := (contMDiff_multilinearSection_iff_coord (𝕜 := ℝ) (F := E)
    (E := (TangentSpace I : M → Type _)) (IB := I) (n := (∞ : WithTop ℕ∞)) (Module.finBasis ℝ E)
    (fun x => (Tensor0SSpace.ofModel (unitModel (I := I) (M := M) g s S x) :
      Tensor0SSpace s I x))).mp hSfield
  intro τ x₀
  refine (hS (τ ∘ σ) x₀).congr_of_eventuallyEq ?_
  filter_upwards [Filter.univ_mem] with x _
  rw [continuousMultilinearMap_basis_repr, continuousMultilinearMap_basis_repr]
  change (ContinuousMultilinearMap.domDomCongr σ
      (unitModel (I := I) (M := M) g s S x))
      (fun j => (Bundle.Trivialization.symmL ℝ (trivializationAt E (TangentSpace I) x₀) x)
        ((Module.finBasis ℝ E) (τ j))) = _
  rw [ContinuousMultilinearMap.domDomCongr_apply]
  rfl

/-- The frame-free slot-reindexed model field as a `Tensor0SField`. -/
noncomputable def domDomCongrField (g : SmoothRiemannianMetric I M) {s : ℕ}
    (σ : Equiv.Perm (Fin s)) (S : SmoothCcTensor g 0 s) :
    Tensor0SBundle.Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) ∞ s :=
  letI := Tensor0SBundle.tensor0SBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) s
  letI := TangentBundle.contMDiffVectorBundle (I := I) (M := M) (n := ∞)
  ⟨fun x => Tensor0SSpace.ofModel
      (ContinuousMultilinearMap.domDomCongr σ (unitModel (I := I) (M := M) g s S x)),
    domDomCongrField_contMDiff (I := I) g σ S⟩

/-- **The constructive `SmoothCcTensor`-level slot-permutation operator.**  For a fixed permutation
`σ : Equiv.Perm (Fin s)`, `domDomCongrSection σ S` reindexes the `s` covariant slots of the smooth
compactly-supported `(0, s)`-tensor section `S`, producing again a smooth `(0, s)`-tensor section: the
section whose unit fibre is the constant fibre reindexing `domDomCongr σ (unitModel S x)`
(`domDomCongrSection_unitModel`).  It is the constructive witness instantiating the naturality core
`tensorCovDerivAt_unit_toModel_domDomCongr_of_section` (which otherwise *assumes* the σ-relation). -/
noncomputable def domDomCongrSection (g : SmoothRiemannianMetric I M) {s : ℕ}
    (σ : Equiv.Perm (Fin s)) (S : SmoothCcTensor g 0 s) :
    SmoothCcTensor g 0 s where
  toSection :=
    MixedSection.fromMultilinearSection (𝕜 := ℝ) (F := E) (IB := I)
      (E := (TangentSpace I : M → Type _)) ∞ (domDomCongrField (I := I) g σ S)
  hasCompactSupport := HasCompactSupport.of_compactSpace _

set_option linter.unusedSectionVars false in
/-- **The unit fibre of `domDomCongrSection σ S` is the constant fibre reindexing of the unit fibre of
`S`.**  This is the section σ-relation that the naturality core
`tensorCovDerivAt_unit_toModel_domDomCongr_of_section` and the iterated form
`exists_iteratedCovGrad_unit_toModel_domDomCongr` take as their hypothesis `hSS'`; here it is proved
outright, so `(S, domDomCongrSection σ S)` is a genuine instance. -/
theorem domDomCongrSection_unitModel (g : SmoothRiemannianMetric I M) {s : ℕ}
    (σ : Equiv.Perm (Fin s)) (S : SmoothCcTensor g 0 s) (x : M) :
    unitModel (I := I) (M := M) g s (domDomCongrSection (I := I) g σ S) x =
      ContinuousMultilinearMap.domDomCongr σ (unitModel (I := I) (M := M) g s S x) := by
  rw [unitModel]
  rw [show (domDomCongrSection (I := I) g σ S).toSection x (unitTensor (I := I) (M := M) x) =
      (MixedSection.eval₀ (F := E) (E := (TangentSpace I : M → Type _)) x).smulRight
          (domDomCongrField (I := I) g σ S x)
          (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ))
      from rfl]
  rw [ContinuousLinearMap.smulRight_apply, MixedSection.eval₀_apply,
    ContinuousMultilinearMap.constOfIsEmpty_apply, one_smul]
  change Tensor0SSpace.toModel
      (Tensor0SSpace.ofModel
        (ContinuousMultilinearMap.domDomCongr σ (unitModel (I := I) (M := M) g s S x))) = _
  rw [Tensor0SSpace.toModel_ofModel]

/-- **Iterated-gradient naturality through the constructive slot-permutation operator.**  At every
gradient order `i` there is a slot permutation `σ'` of `Fin (s + i)` relating the unit fibres of the
iterated covariant gradients `∇^i (domDomCongrSection σ S)` and `∇^i S`.  Instantiates
`exists_iteratedCovGrad_unit_toModel_domDomCongr` at the concrete witness produced by
`domDomCongrSection_unitModel`; the assumed σ-relation hypothesis is now discharged constructively. -/
theorem exists_iteratedCovGrad_unitModel_domDomCongrSection (g : SmoothRiemannianMetric I M) {s : ℕ}
    (σ : Equiv.Perm (Fin s)) (S : SmoothCcTensor g 0 s) (i : ℕ) :
    ∃ σ' : Equiv.Perm (Fin (s + i)),
      ∀ x : M, unitModel (I := I) (M := M) g (s + i)
          (iteratedCovGrad (I := I) (M := M) g 0 s i (domDomCongrSection (I := I) g σ S)) x =
        ContinuousMultilinearMap.domDomCongr σ'
          (unitModel (I := I) (M := M) g (s + i)
            (iteratedCovGrad (I := I) (M := M) g 0 s i S) x) :=
  exists_iteratedCovGrad_unit_toModel_domDomCongr (I := I) (M := M) g s σ S
    (domDomCongrSection (I := I) g σ S)
    (fun y => domDomCongrSection_unitModel (I := I) g σ S y) i

/-- **The slot-permutation operator preserves the `g`-Riemannian fibre norm of every iterated covariant
gradient.**  The fibre slot reindexing is a `g`-fibre isometry, so at every order `i` the iterated
covariant gradient `∇^i (domDomCongrSection σ S)` has the same Riemannian fibre norm squared as
`∇^i S`.  Instantiates `riemannianFiberNormSq_iteratedCovGrad_eq_of_section_domDomCongr` at the
concrete witness. -/
theorem riemannianFiberNormSq_iteratedCovGrad_domDomCongrSection
    (g : SmoothRiemannianMetric I M) {s : ℕ} (σ : Equiv.Perm (Fin s))
    (S : SmoothCcTensor g 0 s) (i : ℕ) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g 0 (s + i) x
        ((iteratedCovGrad (I := I) (M := M) g 0 s i (domDomCongrSection (I := I) g σ S)).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g 0 (s + i) x
        ((iteratedCovGrad (I := I) (M := M) g 0 s i S).toSection x) :=
  riemannianFiberNormSq_iteratedCovGrad_eq_of_section_domDomCongr (I := I) (M := M) g s σ S
    (domDomCongrSection (I := I) g σ S)
    (fun y => domDomCongrSection_unitModel (I := I) g σ S y) i x

/-! ## The metric-contraction `ParallelTensorProduct` constructor (POSITED — deep)

The canonical concrete `ParallelTensorProduct` witness is a `g₀`-parallel metric *contraction* of a
tensor product, NOT the bare model tensor product `unitModelProdSection`.  The bare product fails the
`ParallelTensorProduct.covGrad_prod` field as literally stated: by `unitModel_unitModelProdSection_covGrad_right`
the right covariant-Leibniz summand `prod S (∇T)` carries its gradient slot at the *mid* position
`s₁ + a`, whereas `covGrad (prod S T)` carries the new gradient slot at the *front* position `0`; the
two differ by a slot-permutation `domDomCongr σ`, which the field does not insert.  A genuine
*contraction* against a parallel tensor (`∇ Φ = 0`) collapses the contracted slots and reindexes the
surviving gradient slot to the front, satisfying the field exactly.  Building that contraction's exact
covariant Leibniz (front-slot placement) is deep intrinsic content; it is posited here. -/

/-! ## The concrete `g₀`-parallel double-cometric-trace `ParallelTensorProduct` value

This subsection inhabits the `ParallelTensorProduct` structure for the first time, with the
`g₀`-parallel double-cometric-trace contraction of the bare model tensor product.  For
`(0, 2 + a)`-tensor `S` and `(0, 2 + b)`-tensor `T` the section-level bilinear product is

```
prod S T := appCc g₀ ((2+a+b)+2) (2+a+b) (cometricDoubleTraceField g₀ (2+a+b)) (S ⊗ T),
```

i.e. form the bare model tensor product `S ⊗ T` (`unitModelProdSection`, a `(0, (2+a)+(2+b)) =
(0, (2+a+b)+2)`-tensor, rank-cast through `castRankCc_db`), then contract its two leading covariant
slots against the cometric `g₀⁻¹` via the rank-generic intrinsic double-trace operator field
`cometricDoubleTraceField g₀ (2+a+b)` (a `((2+a+b)+2, 2+a+b)`-tensor), giving a `(0, 2+a+b)`-tensor.
The result is `r₁ = s₁ = 2`, `r₂ = s₂ = 2`, `r₀ = s₀ = 2`: a `ParallelTensorProduct g₀ 0 2 0 2 0 2`.

The contraction operator field is `∇₀`-parallel (`cometricDoubleTraceField_covGrad_eq_zero`,
`∇₀ g₀⁻¹ = 0`), which is exactly why the `covGrad_prod` covariant Leibniz of the contraction has no
cross-term from the cometric factor and reindexes the surviving gradient slot to the front.

The two genuinely deep fields are isolated as precisely-stated children:
* `gInvGramProd_rfns_bound` — the uniform fibrewise operator bound of the contraction product, in the
  intrinsic `g`-Riemannian squared fibre norm `riemannianFiberNormSq` (chart-trivialisation-free; the
  composite of the intrinsic partial-contraction Cauchy–Schwarz, the `rfns` tensor cross-norm, and the
  rank-uniform `g`-native cometric double-trace fibre bound — NEVER the chart-Jacobian-inverse model
  operator-norm sup of the old model route);
* `gInvGramProd_covGrad` — the exact single-step front-slot covariant Leibniz of the contraction
  product (the deep intrinsic content: the `∇₀`-parallel contraction reindexes the surviving gradient
  slot to the front, with no cometric-factor cross-term).
-/

open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck in
/-- **The section-level `g₀`-parallel double-cometric-trace contraction product.**  Contracts the two
leading covariant slots of the bare model tensor product `S ⊗ T` against the cometric `g₀⁻¹`.  Maps a
`(0, 2 + a)`- and a `(0, 2 + b)`-tensor to a `(0, 2 + a + b)`-tensor. -/
noncomputable def gInvGramProdSection (g₀ : SmoothRiemannianMetric I M) {a b : ℕ}
    (S : SmoothCcTensor g₀ 0 (2 + a)) (T : SmoothCcTensor g₀ 0 (2 + b)) :
    SmoothCcTensor g₀ 0 (2 + a + b) :=
  appCc (I := I) (M := M) g₀ ((2 + a + b) + 2) (2 + a + b)
    (cometricDoubleTraceField (I := I) g₀ (2 + a + b))
    (castRankCc_db (I := I) (M := M) g₀ 0
      (show (2 + a) + (2 + b) = (2 + a + b) + 2 by omega)
      (unitModelProdSection (I := I) g₀ S T))

/-- **Step 1 of the contraction-product covariant Leibniz: the parallel-field cross-term vanishes.**
For the `∇₀`-parallel cometric double-trace field `Φ = cometricDoubleTraceField g₀ n`, the covariant
gradient of the contraction `appCc Φ W` collapses to the SINGLE surviving slot-extended summand
`appCc (slotExtend Φ) (covGrad W)`.  By `covGrad_appCc_eq` the gradient is
`appCc (covGrad Φ) W + appCc (slotExtend Φ) (covGrad W)`, and the first summand vanishes because
`covGrad Φ = 0` (`cometricDoubleTraceField_covGrad_eq_zero`, `appCc_zero_left`).  This is the proved
reduction on which the remaining front-slot reconciliation
(`appCc (slotExtend Φ) (covGrad W)` ↦ the two front-slot contraction products) is built. -/
private theorem covGrad_appCc_cometricDoubleTrace_eq (g₀ : SmoothRiemannianMetric I M) (n : ℕ)
    (W : SmoothCcTensor g₀ 0 (n + 2)) :
    covGrad (I := I) (M := M) g₀ 0 n
        (appCc (I := I) (M := M) g₀ (n + 2) n (cometricDoubleTraceField (I := I) g₀ n) W) =
      appCc (I := I) (M := M) g₀ (n + 2 + 1) (n + 1)
        (slotExtend (I := I) (M := M) g₀ (n + 2) n (cometricDoubleTraceField (I := I) g₀ n))
        (covGrad (I := I) (M := M) g₀ 0 (n + 2) W) := by
  rw [covGrad_appCc_eq (I := I) (M := M) g₀ (n + 2) n (cometricDoubleTraceField (I := I) g₀ n) W,
    cometricDoubleTraceField_covGrad_eq_zero (I := I) g₀ n, appCc_zero_left, zero_add]

open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck in
/-- **The exact single-step front-slot covariant Leibniz of the `g₀`-parallel double-cometric-trace
contraction product (POSITED — deep intrinsic content).**  The covariant gradient of the contraction
product splits into the two one-sided derivatives, each carried by the SAME contraction product, with
the new leading covariant slot at the FRONT (position `0`) and NO cometric-factor cross-term.  The left
summand `gInvGramProdSection (∇S) T` carries covariant rank `(2 + (a+1) + b)`, rank-cast to the
differentiated rank `(2 + a + b) + 1` via `castRankCc`.

This is the deep intrinsic content the bare product fails: by `covGrad_appCc_eq` the covariant gradient
of `appCc Φ (S ⊗ T)` is `appCc (∇Φ) (S ⊗ T) + appCc (slotExtend Φ) (∇(S ⊗ T))`; the first summand
vanishes because `Φ = cometricDoubleTraceField g₀ (2+a+b)` is `∇₀`-parallel
(`cometricDoubleTraceField_covGrad_eq_zero`, `appCc_zero_left`).  The surviving term
`appCc (slotExtend Φ) (∇(S ⊗ T))` reconciles, through the bare-product covariant Leibniz
(`unitModelProdSection_covGrad_unitModel_pub`) lifted to the section level by the keystone
`smoothCcTensor_ext_of_unitModel` and the slot-permutation operator `domDomCongrSection`, with the two
front-slot contraction products `castRankCc (gInvGramProdSection (∇S) T) + gInvGramProdSection S (∇T)`:
the `∇₀`-parallel double trace contracts the two original leading slots, passengering the new gradient
slot to the front in both summands. -/
theorem gInvGramProd_covGrad (g₀ : SmoothRiemannianMetric I M) {a b : ℕ}
    (S : SmoothCcTensor g₀ 0 (2 + a)) (T : SmoothCcTensor g₀ 0 (2 + b)) :
    covGrad (I := I) (M := M) g₀ 0 (2 + a + b) (gInvGramProdSection (I := I) g₀ S T) =
      castRankCc g₀ 0 (show 2 + (a + 1) + b = 2 + a + b + 1 by omega)
          (gInvGramProdSection (I := I) (a := a + 1) (b := b) g₀
            (covGrad (I := I) (M := M) g₀ 0 (2 + a) S) T) +
        gInvGramProdSection (I := I) (a := a) (b := b + 1) g₀ S
          (covGrad (I := I) (M := M) g₀ 0 (2 + b) T) := by
  sorry

/-! ### The `g`-native (chart-trivialisation-free) fibrewise operator bound of the contraction product

The operator bound of `gInvGramPTP` is supplied in the intrinsic `g`-Riemannian squared fibre norm
`riemannianFiberNormSq` (`rfns`), NOT the model fibre norm `‖·‖`.  The model route
(`gInvGramProd_norm_bound`, now removed) was forced to bound the model operator norm of the cometric
raise `‖cometricLmodel g₀ x‖`, whose uniform-over-the-base bound is the chart-Jacobian-inverse
operator-norm sup — chart-trivialisation-CIRCULAR on a multi-chart manifold (`S²` carries an unbounded
chart-Jacobian inverse).  The `rfns` route below stays `g`-native throughout:
`rfns(gInvGramProdSection S T)(x) ≤ gOp · rfns(S)(x) · rfns(T)(x)`, assembled from
* the intrinsic partial-contraction Cauchy–Schwarz for `appCc` (`riemannianFiberNormSq_compRS_le_mul`,
  the `g`-fibre Hilbert–Schmidt submultiplicativity of tensor contraction),
* the `rfns` invariance of the rank-cast `castRankCc_db` (`rfns_iteratedCovGrad_castRankCc_db` at
  order `0`),
* the `rfns` tensor-product cross-norm `riemannianFiberNormSq_unitModelProdSection_le`, and
* the RANK-UNIFORM, base-uniform `g`-native fibre bound of the cometric double-trace operator field
  `exists_uniform_riemannianFiberNormSq_cometricDoubleTraceFib`.
-/

set_option linter.unusedSectionVars false in
/-- **(Deep `g`-native bedrock — the `rfns` tensor-product cross-norm.)**  The intrinsic squared
Riemannian fibre norm of the bare model tensor product `S ⊗ T` is bounded by the product of the factor
fibre norms:
```
rfns_{(0,p+q)}((unitModelProdSection S T)(x)) ≤ rfns_{(0,p)}(S(x)) · rfns_{(0,q)}(T(x)).
```
This is the Hilbert–Schmidt cross-norm identity of the tensor product, intrinsic in the `g`-Riemannian
fibre norm.  Parseval-expanding in a `g_x`-orthonormal tensor frame `e` (with the empty covariant
covector collapsing to the unit `(0, 0)`-tensor, so the `(0, t)`-frame component reads the `unitModel`
multilinear evaluation `unitModel g t W x (e_J)`), the `(p + q)`-component of `S ⊗ T` along `J` splits
(`unitModelProdSection_unitModel`, `modelProduct_apply`) as `S_{J∘castAdd} · T_{J∘natAdd}`, so the
double sum of squares factorises along the `Fin p ⊕ Fin q ≃ Fin (p + q)` reindexing as
`∑_J (S_{J₁} T_{J₂})² = (∑_{J₁} S_{J₁}²)(∑_{J₂} T_{J₂}²)`.  Posited here as a deep frame-expansion leaf
(it re-derives, in the `(0, t)` valence, the any-rank single-frame Riemannian-fibre-norm representation
that on disk exists only as the private `rfns_repr_of_orthoFrame_cb`); expressed entirely in
`riemannianFiberNormSq` (no chart trivialisation, no model operator norm).

**Non-vacuity.**  The bound vanishes as `S → 0` (`riemannianFiberNormSq_zero`); both factors are read,
so a degenerate constant stand-in is rejected. -/
private theorem riemannianFiberNormSq_unitModelProdSection_le (g₀ : SmoothRiemannianMetric I M)
    {p q : ℕ} (S : SmoothCcTensor g₀ 0 p) (T : SmoothCcTensor g₀ 0 q) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 0 (p + q) x
        ((unitModelProdSection (I := I) g₀ S T).toSection x) ≤
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 p x (S.toSection x) *
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 q x (T.toSection x) := by
  classical
  obtain ⟨n, e, _bse, hn, _hbse, horth, _hpar, _hexp, _hreprS⟩ :=
    tangent_orthonormalBasisS_witness (I := I) (M := M) g₀ 0 x
  set K₀ : Fin 0 → Fin n := fun k => k.elim0 with hK₀
  -- The empty-covector frame component of a `(0, t)`-section reads its `unitModel` on the frame tuple.
  have hcomp : ∀ {t : ℕ} (W : SmoothCcTensor g₀ 0 t) (J : Fin t → Fin n),
      DifferentialGeometry.Integral.Connection.fiberNormSqComponent (I := I) (M := M) g₀ x 0 t
          (show TensorRSSpace 0 t I x from W.toSection x) n e K₀ J =
        unitModel (I := I) (M := M) g₀ t W x (fun k => e (J k)) := by
    intro t W J
    have hweight : ((ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin 0) ℝ).compContinuousLinearMap
        (fun k => g₀.inner x (e (K₀ k))) : Tensor0SSpace 0 I x) =
        unitTensor (I := I) (M := M) x := by
      apply Tensor0SSpace.toModel_injective
      apply ContinuousMultilinearMap.ext
      intro mm
      rw [show (Tensor0SSpace.toModel
          ((ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin 0) ℝ).compContinuousLinearMap
            (fun k => g₀.inner x (e (K₀ k))) : Tensor0SSpace 0 I x)) mm = 1 from by
        change ((ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin 0) ℝ).compContinuousLinearMap
            (fun k => g₀.inner x (e (K₀ k)))) mm = 1
        rw [ContinuousMultilinearMap.compContinuousLinearMap_apply,
          ContinuousMultilinearMap.mkPiAlgebra_apply]
        simp]
      rw [show (Tensor0SSpace.toModel (unitTensor (I := I) (M := M) x)) mm = 1 from by
        rw [unitTensor, Tensor0SSpace.toModel_ofModel]; rfl]
    rw [DifferentialGeometry.Integral.Connection.fiberNormSqComponent, hweight, unitModel]
    rfl
  -- Represent all three fibre norms in the single frame, then collapse the empty `∑_K`.
  rw [DifferentialGeometry.Integral.Connection.rfns_repr_of_orthoFrame_cb (I := I) (M := M) g₀
        (p + q) x _ e hn horth,
      DifferentialGeometry.Integral.Connection.rfns_repr_of_orthoFrame_cb (I := I) (M := M) g₀
        p x _ e hn horth,
      DifferentialGeometry.Integral.Connection.rfns_repr_of_orthoFrame_cb (I := I) (M := M) g₀
        q x _ e hn horth]
  rw [Finset.sum_eq_single K₀ (fun K _ hK => absurd (Subsingleton.elim K K₀) hK)
        (fun h => absurd (Finset.mem_univ K₀) h),
      Finset.sum_eq_single K₀ (fun K _ hK => absurd (Subsingleton.elim K K₀) hK)
        (fun h => absurd (Finset.mem_univ K₀) h),
      Finset.sum_eq_single K₀ (fun K _ hK => absurd (Subsingleton.elim K K₀) hK)
        (fun h => absurd (Finset.mem_univ K₀) h)]
  -- The `(p + q)`-component of the bare product factorises as `(S-component) · (T-component)`.
  have hsplit : ∀ J : Fin (p + q) → Fin n,
      DifferentialGeometry.Integral.Connection.fiberNormSqSummand (I := I) (M := M) g₀ x 0 (p + q)
          (show TensorRSSpace 0 (p + q) I x from (unitModelProdSection (I := I) g₀ S T).toSection x)
          n e K₀ J =
        (DifferentialGeometry.Integral.Connection.fiberNormSqComponent (I := I) (M := M) g₀ x 0 p
            (show TensorRSSpace 0 p I x from S.toSection x) n e K₀ (J ∘ Fin.castAdd q)) ^ 2 *
          (DifferentialGeometry.Integral.Connection.fiberNormSqComponent (I := I) (M := M) g₀ x 0 q
            (show TensorRSSpace 0 q I x from T.toSection x) n e K₀ (J ∘ Fin.natAdd p)) ^ 2 := by
    intro J
    rw [DifferentialGeometry.Integral.Connection.fiberNormSqSummand_eq_component_sq,
      hcomp (unitModelProdSection (I := I) g₀ S T) J,
      hcomp S (J ∘ Fin.castAdd q), hcomp T (J ∘ Fin.natAdd p),
      unitModelProdSection_unitModel (I := I) g₀ S T x,
      Bundle.continuousMultilinearMap.modelProduct_apply]
    rw [show ((fun k => e (J k)) ∘ Fin.castAdd q) = (fun k => e ((J ∘ Fin.castAdd q) k)) from rfl,
      show ((fun k => e (J k)) ∘ Fin.natAdd p) = (fun k => e ((J ∘ Fin.natAdd p) k)) from rfl,
      mul_pow]
  rw [Finset.sum_congr rfl (fun J _ => hsplit J)]
  -- Factorise `∑_J cS² cT²` along `Fin p ⊕ Fin q ≃ Fin (p + q)`.
  set cS : (Fin p → Fin n) → ℝ := fun J₁ =>
    (DifferentialGeometry.Integral.Connection.fiberNormSqComponent (I := I) (M := M) g₀ x 0 p
      (show TensorRSSpace 0 p I x from S.toSection x) n e K₀ J₁) ^ 2 with hcS
  set cT : (Fin q → Fin n) → ℝ := fun J₂ =>
    (DifferentialGeometry.Integral.Connection.fiberNormSqComponent (I := I) (M := M) g₀ x 0 q
      (show TensorRSSpace 0 q I x from T.toSection x) n e K₀ J₂) ^ 2 with hcT
  have hreindex : (∑ J : Fin (p + q) → Fin n, cS (J ∘ Fin.castAdd q) * cT (J ∘ Fin.natAdd p)) =
      (∑ J₁ : Fin p → Fin n, cS J₁) * (∑ J₂ : Fin q → Fin n, cT J₂) := by
    let eqv : (Fin (p + q) → Fin n) ≃ (Fin p → Fin n) × (Fin q → Fin n) :=
      (Equiv.arrowCongr finSumFinEquiv (Equiv.refl (Fin n))).symm.trans
        (Equiv.sumArrowEquivProdArrow (Fin p) (Fin q) (Fin n))
    have hL : (∑ J : Fin (p + q) → Fin n, cS (J ∘ Fin.castAdd q) * cT (J ∘ Fin.natAdd p)) =
        ∑ pr : (Fin p → Fin n) × (Fin q → Fin n), cS pr.1 * cT pr.2 := by
      rw [← Equiv.sum_comp eqv (fun pr : (Fin p → Fin n) × (Fin q → Fin n) => cS pr.1 * cT pr.2)]
      refine Finset.sum_congr rfl (fun J _ => ?_)
      have h1 : (eqv J).1 = J ∘ Fin.castAdd q := by
        funext i
        change J (finSumFinEquiv (Sum.inl i)) = J (Fin.castAdd q i)
        rw [finSumFinEquiv_apply_left]
      have h2 : (eqv J).2 = J ∘ Fin.natAdd p := by
        funext i
        change J (finSumFinEquiv (Sum.inr i)) = J (Fin.natAdd p i)
        rw [finSumFinEquiv_apply_right]
      rw [h1, h2]
    rw [hL, Fintype.sum_prod_type, ← Fintype.sum_mul_sum]
  rw [hreindex, hcS, hcT]
  refine le_of_eq ?_
  congr 1 <;>
    exact Finset.sum_congr rfl (fun J _ =>
      (DifferentialGeometry.Integral.Connection.fiberNormSqSummand_eq_component_sq
        (I := I) (M := M) g₀ x 0 _ _ n e K₀ J).symm)

/-- **(Deep `g`-native bedrock — the RANK-UNIFORM, base-uniform `g`-Riemannian fibre ACTION bound of
the cometric double-trace operator.)**  There is a single nonnegative constant `Cdt = dim`, uniform
over BOTH the passenger count `n` AND the base point `x`, controlling the cometric double-trace
*action* on any `(0, n + 2)`-tensor `Wx`:
```
rfns_{(0,n)}((cometricDoubleTraceFib g₀ n x).comp Wx) ≤ Cdt · rfns_{(0,n+2)}(Wx).
```
This is the `g`-native, chart-trivialisation-free, RANK-UNIFORM action bound.  It is stated as an
*action* bound (operator applied to a tensor), NOT as a fibre-`rfns` bound on the operator field
itself: the Hilbert–Schmidt fibre norm `rfns(cometricDoubleTraceFib g₀ n x)` GROWS like `dim^{(n+1)}`
with the passenger count `n` (in a `g`-orthonormal frame the cometric is the identity, so the
double-trace operator has `dim^{n+1}` nonzero unit-norm frame components), so no single rank-uniform
constant bounds it — only its *action* on a vector is rank-uniformly bounded (the operator norm, not
the HS norm).  The proof Parseval-expands both fibre norms in the `g_x`-orthonormal smooth frame
`smoothOrthoFrame g₀ x · x`: the result's `J`-component is the cometric diagonal trace
`∑_i Wx-component(i, i, J)` (`cometricDoubleTraceFib_eq_orthoFrame_diag`, the cometric is the identity
on the `g`-orthonormal frame), a per-output discrete Cauchy–Schwarz over the `dim` diagonal indices
gives `(∑_i c(i,i,J))² ≤ dim · ∑_i c(i,i,J)²`, and the diagonal-index sub-sum is dominated by the full
`(n + 2)`-index Hilbert–Schmidt sum `rfns(Wx)²`.  `Cdt = dim` is base-uniform (the frame is
`g`-orthonormal at every base point) and rank-uniform (the `dim` factor is from the single contracted
pair, independent of the `n` passenger slots).

**Non-vacuity.**  The bound genuinely uses `Wx` (the operator is applied to it); it vanishes as
`Wx → 0`, so a degenerate constant stand-in is rejected. -/
private theorem exists_uniform_rfns_cometricDoubleTrace_comp_le
    (g₀ : SmoothRiemannianMetric I M) :
    ∃ Cdt : ℝ, 0 ≤ Cdt ∧ ∀ (n : ℕ) (x : M) (Wx : TensorRSSpace 0 (n + 2) I x),
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 n x
          (show TensorRSSpace 0 n I x from
            (cometricDoubleTraceFib (I := I) g₀ n x).comp
              (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (n + 2) I x from Wx)) ≤
        Cdt * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (n + 2) x Wx := by
  classical
  refine ⟨(Module.finrank ℝ E : ℝ), Nat.cast_nonneg _, ?_⟩
  intro n x Wx
  set d : ℕ := Module.finrank ℝ E with hd
  -- The `g₀(x)`-orthonormal smooth frame attached at `x`, read at its own centre.
  set e : Fin d → TangentSpace I x := fun i => smoothOrthoFrame (I := I) g₀ x i x with he
  have hxnbhd : x ∈ smoothOrthoFrameNbhd (I := I) (M := M) x :=
    mem_smoothOrthoFrameNbhd_self (I := I) (M := M) x
  have horth : ∀ i j : Fin d, g₀.inner x (e i) (e j) = if i = j then (1 : ℝ) else 0 :=
    fun i j => smoothOrthoFrame_orthonormal (I := I) g₀ x hxnbhd i j
  have hdrank : d = Module.finrank ℝ (TangentSpace I x) := rfl
  set K₀ : Fin 0 → Fin d := fun k => k.elim0 with hK₀
  -- The result `(0, n)`-tensor's `J`-component is the cometric diagonal trace of `Wx`'s components.
  have hcompTrace : ∀ J : Fin n → Fin d,
      DifferentialGeometry.Integral.Connection.fiberNormSqComponent (I := I) (M := M) g₀ x 0 n
          (show TensorRSSpace 0 n I x from
            (cometricDoubleTraceFib (I := I) g₀ n x).comp
              (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (n + 2) I x from Wx)) d e K₀ J =
        ∑ i : Fin d,
          DifferentialGeometry.Integral.Connection.fiberNormSqComponent (I := I) (M := M) g₀ x 0
            (n + 2) (show TensorRSSpace 0 (n + 2) I x from Wx) d e K₀
            (Fin.cons i (Fin.cons i J)) := by
    intro J
    -- Unfold the component: it is `(Φ.comp Wx)(unit)(e_J) = toModel(Φ (Wx unit))(e_J)`.
    have hunit : ((ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin 0) ℝ).compContinuousLinearMap
        (fun k => g₀.inner x (e (K₀ k))) : Tensor0SSpace 0 I x) = unitTensor (I := I) (M := M) x := by
      apply Tensor0SSpace.toModel_injective
      apply ContinuousMultilinearMap.ext
      intro mm
      rw [show (Tensor0SSpace.toModel
          ((ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin 0) ℝ).compContinuousLinearMap
            (fun k => g₀.inner x (e (K₀ k))) : Tensor0SSpace 0 I x)) mm = 1 from by
        change ((ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin 0) ℝ).compContinuousLinearMap
            (fun k => g₀.inner x (e (K₀ k)))) mm = 1
        rw [ContinuousMultilinearMap.compContinuousLinearMap_apply,
          ContinuousMultilinearMap.mkPiAlgebra_apply]; simp]
      rw [show (Tensor0SSpace.toModel (unitTensor (I := I) (M := M) x)) mm = 1 from by
        rw [unitTensor, Tensor0SSpace.toModel_ofModel]; rfl]
    set D : Tensor0SSpace (n + 2) I x :=
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (n + 2) I x from Wx)
        (unitTensor (I := I) (M := M) x) with hD
    -- The component is the model evaluation `toModel(Φ D)(e_J)`.
    have hLHS : DifferentialGeometry.Integral.Connection.fiberNormSqComponent (I := I) (M := M) g₀ x
          0 n (show TensorRSSpace 0 n I x from
            (cometricDoubleTraceFib (I := I) g₀ n x).comp
              (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (n + 2) I x from Wx)) d e K₀ J =
        Tensor0SSpace.toModel (cometricDoubleTraceFib (I := I) g₀ n x D) (fun k => (e (J k) : E)) := by
      rw [DifferentialGeometry.Integral.Connection.fiberNormSqComponent, hunit,
        ContinuousLinearMap.comp_apply, ← hD]
      rfl
    -- Each `Wx`-component is the model evaluation `toModel(D)(e_ξ)`.
    have hRHScomp : ∀ i : Fin d,
        DifferentialGeometry.Integral.Connection.fiberNormSqComponent (I := I) (M := M) g₀ x 0
            (n + 2) (show TensorRSSpace 0 (n + 2) I x from Wx) d e K₀ (Fin.cons i (Fin.cons i J)) =
          Tensor0SSpace.toModel D
            (Fin.cons (e i : E) (Fin.cons (e i : E) (fun k => (e (J k) : E)))) := by
      intro i
      have htuple : (fun k => e ((Fin.cons i (Fin.cons i J) : Fin (n + 2) → Fin d) k)) =
          Fin.cons (e i) (Fin.cons (e i) (fun k => e (J k))) := by
        funext k
        refine Fin.cases ?_ (fun k => ?_) k
        · rfl
        · exact Fin.cases rfl (fun _ => rfl) k
      rw [DifferentialGeometry.Integral.Connection.fiberNormSqComponent, hunit, ← hD, htuple]
      rfl
    rw [hLHS]
    rw [cometricDoubleTraceFib_toModel (I := I) g₀ n x D]
    rw [modelDoubleTrace_apply (E := E) n (cometricLmodel (I := I) g₀ x)
      (Tensor0SSpace.toModel D) (fun k => (e (J k) : E))]
    rw [cometric_dualTrace_eq_orthoFrame_diag (I := I) g₀ (s := n) x hxnbhd
      (Tensor0SSpace.toModel D) (fun k => (e (J k) : E))]
    refine (Finset.sum_congr rfl (fun i _ => ?_)).symm
    rw [hRHScomp i]
  -- Represent both fibre norms in the single `g`-orthonormal frame, collapse the empty covector.
  rw [DifferentialGeometry.Integral.Connection.rfns_repr_of_orthoFrame_cb (I := I) (M := M) g₀
        n x _ e hdrank horth]
  rw [Finset.sum_eq_single K₀ (fun K _ hK => absurd (Subsingleton.elim K K₀) hK)
        (fun h => absurd (Finset.mem_univ K₀) h)]
  rw [DifferentialGeometry.Integral.Connection.rfns_repr_of_orthoFrame_cb (I := I) (M := M) g₀
        (n + 2) x _ e hdrank horth]
  rw [Finset.sum_eq_single K₀ (fun K _ hK => absurd (Subsingleton.elim K K₀) hK)
        (fun h => absurd (Finset.mem_univ K₀) h)]
  -- Per-output Cauchy–Schwarz + sub-sum domination of the diagonal indices.
  set c : (Fin (n + 2) → Fin d) → ℝ := fun ξ =>
    DifferentialGeometry.Integral.Connection.fiberNormSqComponent (I := I) (M := M) g₀ x 0 (n + 2)
      (show TensorRSSpace 0 (n + 2) I x from Wx) d e K₀ ξ with hc
  have hCS : ∀ J : Fin n → Fin d,
      DifferentialGeometry.Integral.Connection.fiberNormSqSummand (I := I) (M := M) g₀ x 0 n
          (show TensorRSSpace 0 n I x from
            (cometricDoubleTraceFib (I := I) g₀ n x).comp
              (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (n + 2) I x from Wx)) d e K₀ J ≤
        (d : ℝ) * ∑ i : Fin d, c (Fin.cons i (Fin.cons i J)) ^ 2 := by
    intro J
    rw [DifferentialGeometry.Integral.Connection.fiberNormSqSummand_eq_component_sq, hcompTrace J]
    calc (∑ i : Fin d, c (Fin.cons i (Fin.cons i J))) ^ 2
        = (∑ i : Fin d, (1 : ℝ) * c (Fin.cons i (Fin.cons i J))) ^ 2 := by
          simp
      _ ≤ (∑ i : Fin d, (1 : ℝ) ^ 2) * ∑ i : Fin d, c (Fin.cons i (Fin.cons i J)) ^ 2 :=
          Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin d))
            (fun _ : Fin d => (1 : ℝ)) (fun i => c (Fin.cons i (Fin.cons i J)))
      _ = (d : ℝ) * ∑ i : Fin d, c (Fin.cons i (Fin.cons i J)) ^ 2 := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]; simp
  -- The diagonal-index sub-sum is dominated by the full Hilbert–Schmidt sum (injective reindex).
  have hsub : (∑ J : Fin n → Fin d, ∑ i : Fin d, c (Fin.cons i (Fin.cons i J)) ^ 2) ≤
      ∑ ξ : Fin (n + 2) → Fin d, c ξ ^ 2 := by
    let g : ((Fin n → Fin d) × Fin d) → (Fin (n + 2) → Fin d) :=
      fun p => Fin.cons p.2 (Fin.cons p.2 p.1)
    have hginj : Function.Injective g := by
      intro p₁ p₂ hpe
      have h0 : g p₁ 0 = g p₂ 0 := by rw [hpe]
      have h2 : p₁.1 = p₂.1 := by
        funext k
        have := congrFun hpe (Fin.succ (Fin.succ k))
        simpa [g, Fin.cons_succ] using this
      have h1 : p₁.2 = p₂.2 := by simpa [g, Fin.cons_zero] using h0
      exact Prod.ext h2 h1
    calc (∑ J : Fin n → Fin d, ∑ i : Fin d, c (Fin.cons i (Fin.cons i J)) ^ 2)
        = ∑ p : (Fin n → Fin d) × Fin d, c (g p) ^ 2 := by
          rw [Fintype.sum_prod_type]
      _ = ∑ ξ ∈ (Finset.univ.image g), c ξ ^ 2 := by
          rw [Finset.sum_image (fun a _ b _ hab => hginj hab)]
      _ ≤ ∑ ξ : Fin (n + 2) → Fin d, c ξ ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
            (fun ξ _ _ => sq_nonneg _)
  calc (∑ J : Fin n → Fin d,
          DifferentialGeometry.Integral.Connection.fiberNormSqSummand (I := I) (M := M) g₀ x 0 n
            (show TensorRSSpace 0 n I x from
              (cometricDoubleTraceFib (I := I) g₀ n x).comp
                (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (n + 2) I x from Wx)) d e K₀ J)
      ≤ ∑ J : Fin n → Fin d, (d : ℝ) * ∑ i : Fin d, c (Fin.cons i (Fin.cons i J)) ^ 2 :=
        Finset.sum_le_sum (fun J _ => hCS J)
    _ = (d : ℝ) * ∑ J : Fin n → Fin d, ∑ i : Fin d, c (Fin.cons i (Fin.cons i J)) ^ 2 := by
        rw [Finset.mul_sum]
    _ ≤ (d : ℝ) * ∑ ξ : Fin (n + 2) → Fin d, c ξ ^ 2 :=
        mul_le_mul_of_nonneg_left hsub (Nat.cast_nonneg d)
    _ = (d : ℝ) * ∑ J : Fin (n + 2) → Fin d,
          DifferentialGeometry.Integral.Connection.fiberNormSqSummand (I := I) (M := M) g₀ x 0
            (n + 2) (show TensorRSSpace 0 (n + 2) I x from Wx) d e K₀ J := by
        refine congrArg (fun t => (d : ℝ) * t) ?_
        exact Finset.sum_congr rfl (fun ξ _ =>
          (DifferentialGeometry.Integral.Connection.fiberNormSqSummand_eq_component_sq
            (I := I) (M := M) g₀ x 0 (n + 2) _ d e K₀ ξ))

set_option linter.unusedSectionVars false in
/-- **The `g`-native uniform fibrewise operator bound of the `g₀`-parallel double-cometric-trace
contraction product (chart-trivialisation-free).**  There is a single nonnegative constant `C` bounding
the intrinsic `g`-Riemannian squared fibre norm of `gInvGramProdSection g₀ S T` by
`C · rfns(S) · rfns(T)` uniformly over the base point and over the extra-slot counts `a, b`:
```
rfns(gInvGramProdSection g₀ S T)(x) ≤ C · rfns(S)(x) · rfns(T)(x).
```
The constant is the rank-uniform cometric double-trace ACTION bound `Cdt = dim`
(`exists_uniform_rfns_cometricDoubleTrace_comp_le`).  The pointwise step reads
`gInvGramProdSection = appCc Φ (castRankCc_db (S ⊗ T))`, whose fibre value is the composition
`(Φ x).comp ((castRankCc_db (S ⊗ T)) x)`; the rank-uniform cometric double-trace ACTION bound
`rfns((Φ x).comp Wx) ≤ Cdt · rfns(Wx)` bounds it by `Cdt · rfns((castRankCc_db (S ⊗ T)) x)`, the
rank-cast `rfns`-invariance `rfns_iteratedCovGrad_castRankCc_db` (order `0`) drops the cast, and the
tensor cross-norm `riemannianFiberNormSq_unitModelProdSection_le` factorises
`rfns(S ⊗ T) ≤ rfns(S) · rfns(T)`.  Crucially the contraction is bounded by its rank-uniform OPERATOR
norm (the `Cdt` action bound), NOT the rank-DEPENDENT Hilbert–Schmidt fibre norm of the cometric
double-trace operator field — which grows like `dim^{n+1}` and supports no uniform constant.  Never the
model operator norm, never `cometricLmodel`, never the chart-Jacobian-inverse sup. -/
theorem gInvGramProd_rfns_bound (g₀ : SmoothRiemannianMetric I M) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {a b : ℕ} (S : SmoothCcTensor g₀ 0 (2 + a))
      (T : SmoothCcTensor g₀ 0 (2 + b)) (x : M),
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + a + b) x
          ((gInvGramProdSection (I := I) g₀ S T).toSection x) ≤
        C * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + a) x (S.toSection x) *
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + b) x (T.toSection x) := by
  obtain ⟨Cdt, hCdt_nn, hCdt⟩ :=
    exists_uniform_rfns_cometricDoubleTrace_comp_le (I := I) g₀
  refine ⟨Cdt, hCdt_nn, ?_⟩
  intro a b S T x
  set n := 2 + a + b with hn
  have hcast := rfns_iteratedCovGrad_castRankCc_db (I := I) (M := M) g₀ 0
    (show (2 + a) + (2 + b) = n + 2 by omega)
    (unitModelProdSection (I := I) g₀ S T) 0 x
  rw [iteratedCovGrad_zero, iteratedCovGrad_zero] at hcast
  -- rfns(gInvGramProdSection) ≤ Cdt · rfns((castRankCc_db (S ⊗ T)) x), the rank-uniform action bound.
  have hcs : riemannianFiberNormSq (I := I) (M := M) g₀ 0 n x
        ((gInvGramProdSection (I := I) g₀ S T).toSection x) ≤
      Cdt * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (n + 2) x
          ((castRankCc_db (I := I) (M := M) g₀ 0
            (show (2 + a) + (2 + b) = n + 2 by omega)
            (unitModelProdSection (I := I) g₀ S T)).toSection x) := by
    rw [gInvGramProdSection, appCc_toSection, cometricDoubleTraceField_toSection]
    exact hCdt n x
      (show TensorRSSpace 0 (n + 2) I x from
        (castRankCc_db (I := I) (M := M) g₀ 0
          (show (2 + a) + (2 + b) = n + 2 by omega)
          (unitModelProdSection (I := I) g₀ S T)).toSection x)
  -- drop the cast, then factorise the tensor product
  rw [hcast] at hcs
  have hprod := riemannianFiberNormSq_unitModelProdSection_le (I := I) (M := M) g₀ S T x
  have hSnn := riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + a) x (S.toSection x)
  have hTnn := riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + b) x (T.toSection x)
  calc riemannianFiberNormSq (I := I) (M := M) g₀ 0 n x
          ((gInvGramProdSection (I := I) g₀ S T).toSection x)
      ≤ Cdt * riemannianFiberNormSq (I := I) (M := M) g₀ 0 ((2 + a) + (2 + b)) x
            ((unitModelProdSection (I := I) g₀ S T).toSection x) := hcs
    _ ≤ Cdt * (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + a) x (S.toSection x) *
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + b) x (T.toSection x)) :=
        mul_le_mul_of_nonneg_left hprod hCdt_nn
    _ = Cdt * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + a) x (S.toSection x) *
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + b) x (T.toSection x) := by ring

set_option linter.unusedVariables false in
/-- **The first inhabitant of `ParallelTensorProduct`: the `g₀`-parallel double-cometric-trace
contraction product.**  Its `prod` is `gInvGramProdSection` (the double-`g₀⁻¹` contraction of the bare
model tensor product); its `opNorm` is the `g`-native uniform bound constant from
`gInvGramProd_rfns_bound`; its `rfns_prod_le` is that `g`-Riemannian fibrewise operator bound (no model
operator norm, no chart-Jacobian-inverse sup); its `covGrad_prod` is the exact front-slot covariant
Leibniz `gInvGramProd_covGrad` (the cometric factor's gradient vanishes by `∇₀ g₀⁻¹ = 0`).  This is the
structural unlock for the intrinsic Ricci–DeTurck linearization — the witness realizing
`D(g⁻¹)[h] = −g₀⁻¹ h g₀⁻¹` as a parallel cometric contraction. -/
noncomputable def gInvGramPTP (g₀ : SmoothRiemannianMetric I M) :
    ParallelTensorProduct g₀ 0 2 0 2 0 2 where
  prod := fun {a b} S T => gInvGramProdSection (I := I) g₀ S T
  opNorm := Classical.choose (gInvGramProd_rfns_bound (I := I) g₀)
  opNorm_nonneg := (Classical.choose_spec (gInvGramProd_rfns_bound (I := I) g₀)).1
  rfns_prod_le := fun {a b} S T x =>
    (Classical.choose_spec (gInvGramProd_rfns_bound (I := I) g₀)).2 S T x
  covGrad_prod := fun {a b} S T => gInvGramProd_covGrad (I := I) g₀ S T

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry
