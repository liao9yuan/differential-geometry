import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.RicciConnDiffPalatini
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.Defs
import DifferentialGeometry.Geometry.Connection.TensorNabla.CotangentExtension
import DifferentialGeometry.Tensor.Multilinear.BundleSmoothEval
import DifferentialGeometry.Geometry.Connection.Realization.SmoothSections
import DifferentialGeometry.Tensor.Multilinear.Basis

/-!
# The connection-difference tensor as a bundled `(1, 2)`-tensor, and its covariant gradient

For two smooth Riemannian metrics `g₀, g₁` on a closed manifold `M` the connection-difference
tensor `A = connDiff g₁ g₀ = ∇₁ − ∇₀` (`Geometry/Flow/ConnectionDifference.lean`) is a
vector-field-valued `(1, 2)`-tensor: at each `x` it is a continuous bilinear map
`TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x` (two covariant vector slots, one
contravariant vector output).  This file packages it as a genuine `SmoothCcTensor g₀ 1 2` — the
project's `Hom(Tensor0SSpace 1, Tensor0SSpace 2)` valence — through the **metric-free dual pairing**
`A♭(om)(Y, Z) := om(A(Y, Z))` (a covector `om` paired with the vector output `A(Y, Z)`), and bridges its
bundled iterated covariant gradient `covGrad g₀ 1 2` to the directional Palatini covariant derivative
`covDerivConnDiff g₀ g₁` (`Geometry/Curvature/CurvatureOperator/RicciConnDiffPalatini.lean`).

## Main definitions

* `connDiffFib g₁ g₀ x : TensorRSSpace 1 2 I x` — the fibrewise dual-pairing packaging of
  `connDiff g₁ g₀ x` as a `(1, 2)`-tensor: `connDiffFib x om (Y, Z) = om(connDiff x Y Z)`.
* `connDiffSection g₁ g₀ : SmoothCcTensor g₀ 1 2` — the smooth, compactly-supported `(1, 2)`-tensor
  section assembled from `connDiffFib`, smooth by `connDiff_contMDiff` and the metric-free pairing,
  compactly supported because `M` is compact.

## Main theorems

* `connDiffFib_apply_eval` — the defining evaluation formula
  `(connDiffFib x om).toModel [Y, Z] = om [connDiff x Y Z]`.
* `connDiffSection_covGrad_eq_covDerivConnDiff` — **the bridge**: the bundled iterated covariant
  gradient `covGrad g₀ 1 2 (connDiffSection g₁ g₀)` (a `SmoothCcTensor g₀ 1 3`) equals the dual-pairing
  packaging of the Palatini directional covariant derivative `covDerivConnDiff g₀ g₁` of the
  connection-difference tensor.  This connects the analysis/operator-field covariant-gradient machinery
  (`covGrad`/`tensorRSCovariantDerivative`) to the vector-field/Palatini machinery
  (`covDerivConnDiff`/`covDerivDiff`), the bedrock the central Lichnerowicz `_core` consumes.
-/

noncomputable section

set_option linter.style.setOption false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1600000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators Matrix

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.PDE.DeTurck
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open TensorMultilinear
open TensorRSNabla

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

/-! ## The dual-pairing packaging of the connection-difference tensor as a `(1, 2)`-tensor -/

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
/-- A `(0, 1)`-tensor `om : Tensor0SSpace 1 I x` is additive when evaluated on the single tangent slot:
`om [a + b] = om [a] + om [b]`.  This is the additivity of the arity-`1` multilinear map, transferred
through the `continuousMultilinearCurryFin1` equivalence to a genuine continuous linear functional. -/
private lemma tensor0SOne_apply_add (x : M) (om : Tensor0SSpace 1 I x)
    (a b : TangentSpace I x) :
    om (fun _ : Fin 1 => a + b) = om (fun _ : Fin 1 => a) + om (fun _ : Fin 1 => b) := by
  let φ := continuousMultilinearCurryFin1 ℝ (TangentSpace I x) ℝ
    (om : ContinuousMultilinearMap ℝ (fun _ : Fin 1 => TangentSpace I x) ℝ)
  have ha : (om : ContinuousMultilinearMap ℝ (fun _ : Fin 1 => TangentSpace I x) ℝ)
      (fun _ : Fin 1 => a) = φ a := by rw [continuousMultilinearCurryFin1_apply]; rfl
  have hb : (om : ContinuousMultilinearMap ℝ (fun _ : Fin 1 => TangentSpace I x) ℝ)
      (fun _ : Fin 1 => b) = φ b := by rw [continuousMultilinearCurryFin1_apply]; rfl
  have hab : (om : ContinuousMultilinearMap ℝ (fun _ : Fin 1 => TangentSpace I x) ℝ)
      (fun _ : Fin 1 => a + b) = φ (a + b) := by rw [continuousMultilinearCurryFin1_apply]; rfl
  change (om : ContinuousMultilinearMap ℝ (fun _ : Fin 1 => TangentSpace I x) ℝ) (fun _ => a + b) = _
  rw [hab, ha, hb, map_add]

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
/-- A `(0, 1)`-tensor `om : Tensor0SSpace 1 I x` is homogeneous when evaluated on the single tangent
slot: `om [c • a] = c • om [a]`. -/
private lemma tensor0SOne_apply_smul (x : M) (om : Tensor0SSpace 1 I x)
    (c : ℝ) (a : TangentSpace I x) :
    om (fun _ : Fin 1 => c • a) = c • om (fun _ : Fin 1 => a) := by
  let φ := continuousMultilinearCurryFin1 ℝ (TangentSpace I x) ℝ
    (om : ContinuousMultilinearMap ℝ (fun _ : Fin 1 => TangentSpace I x) ℝ)
  have ha : (om : ContinuousMultilinearMap ℝ (fun _ : Fin 1 => TangentSpace I x) ℝ)
      (fun _ : Fin 1 => a) = φ a := by rw [continuousMultilinearCurryFin1_apply]; rfl
  have hca : (om : ContinuousMultilinearMap ℝ (fun _ : Fin 1 => TangentSpace I x) ℝ)
      (fun _ : Fin 1 => c • a) = φ (c • a) := by rw [continuousMultilinearCurryFin1_apply]; rfl
  change (om : ContinuousMultilinearMap ℝ (fun _ : Fin 1 => TangentSpace I x) ℝ) (fun _ => c • a) = _
  rw [hca, ha, map_smul]

/-- The `(0, 2)`-tensor fibre `(Y, Z) ↦ om(connDiff g₁ g₀ x Y Z)` paired against a covector `om`. -/
def connDiffPairing (g₁ g₀ : SmoothRiemannianMetric I M) (x : M)
    (om : Tensor0SSpace 1 I x) : Tensor0SSpace 2 I x :=
  (show ContinuousMultilinearMap ℝ (fun _ : Fin 2 => TangentSpace I x) ℝ from
    { toFun := fun YZ => om (fun _ : Fin 1 => connDiff (I := I) g₁ g₀ x (YZ 0) (YZ 1))
      map_update_add' := by
        have hne10 : (1 : Fin 2) ≠ 0 := by decide
        have hne01 : (0 : Fin 2) ≠ 1 := by decide
        intro _ YZ i Y Y'
        fin_cases i <;>
          · simp only [Fin.isValue, Fin.mk_zero, Fin.mk_one, Function.update_self,
              Function.update_of_ne, ne_eq, hne10, hne01, not_false_eq_true,
              ContinuousLinearMap.add_apply, map_add]
            rw [tensor0SOne_apply_add (I := I) x om]
      map_update_smul' := by
        have hne10 : (1 : Fin 2) ≠ 0 := by decide
        have hne01 : (0 : Fin 2) ≠ 1 := by decide
        intro _ YZ i c Y
        fin_cases i <;>
          · simp only [Fin.isValue, Fin.mk_zero, Fin.mk_one, Function.update_self,
              Function.update_of_ne, ne_eq, hne10, hne01, not_false_eq_true,
              ContinuousLinearMap.smul_apply, map_smul]
            rw [tensor0SOne_apply_smul (I := I) x om]
      cont := by
        have hpair : Continuous (fun YZ : Fin 2 → TangentSpace I x => (YZ 0, YZ 1)) :=
          (continuous_apply 0).prodMk (continuous_apply 1)
        have hbil : Continuous (fun YZ : Fin 2 → TangentSpace I x =>
            connDiff (I := I) g₁ g₀ x (YZ 0) (YZ 1)) :=
          (connDiff (I := I) g₁ g₀ x).continuous₂.comp hpair
        exact ((ContinuousMultilinearMap.coe_continuous
          (om : ContinuousMultilinearMap ℝ (fun _ : Fin 1 => TangentSpace I x) ℝ)).comp
          (continuous_pi (fun _ => hbil))) } : Tensor0SSpace 2 I x)

omit [CompactSpace M] [I.Boundaryless] in
/-- The `(0, 2)`-fibre `connDiffPairing` evaluated (FunLike) on a tangent tuple `YZ` reads `om`
against the connection-difference output `connDiff g₁ g₀ x (YZ 0) (YZ 1)`. -/
@[simp] lemma connDiffPairing_apply (g₁ g₀ : SmoothRiemannianMetric I M) (x : M)
    (om : Tensor0SSpace 1 I x) (YZ : Fin 2 → TangentSpace I x) :
    (connDiffPairing (I := I) g₁ g₀ x om) YZ =
      om (fun _ : Fin 1 => connDiff (I := I) g₁ g₀ x (YZ 0) (YZ 1)) := rfl

omit [CompactSpace M] [I.Boundaryless] in
/-- `connDiffPairing` is additive in the covector. -/
lemma connDiffPairing_add (g₁ g₀ : SmoothRiemannianMetric I M) (x : M)
    (om om' : Tensor0SSpace 1 I x) :
    connDiffPairing (I := I) g₁ g₀ x (om + om') =
      connDiffPairing (I := I) g₁ g₀ x om + connDiffPairing (I := I) g₁ g₀ x om' := by
  apply ContinuousMultilinearMap.ext
  intro YZ
  exact ContinuousMultilinearMap.add_apply om om' _

omit [CompactSpace M] [I.Boundaryless] in
/-- `connDiffPairing` is homogeneous in the covector. -/
lemma connDiffPairing_smul (g₁ g₀ : SmoothRiemannianMetric I M) (x : M)
    (c : ℝ) (om : Tensor0SSpace 1 I x) :
    connDiffPairing (I := I) g₁ g₀ x (c • om) =
      c • connDiffPairing (I := I) g₁ g₀ x om := by
  apply ContinuousMultilinearMap.ext
  intro YZ
  exact ContinuousMultilinearMap.smul_apply om c _

/-- **The fibrewise dual-pairing packaging of the connection-difference tensor.**  At a base point
`x`, `connDiffFib g₁ g₀ x` is the `(1, 2)`-tensor (`TensorRSSpace 1 2 I x =
Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x`) sending a covector `om` to the bilinear form
`(Y, Z) ↦ om(connDiff g₁ g₀ x Y Z)`: the metric-free pairing of `om` with the vector output of the
connection-difference tensor. -/
def connDiffFib (g₁ g₀ : SmoothRiemannianMetric I M) (x : M) :
    TensorRSSpace 1 2 I x :=
  TensorRSSpace.ofCLM
    (LinearMap.toContinuousLinearMap
      { toFun := fun om => connDiffPairing (I := I) g₁ g₀ x om
        map_add' := connDiffPairing_add g₁ g₀ x
        map_smul' := connDiffPairing_smul g₁ g₀ x })

omit [CompactSpace M] [I.Boundaryless] in
/-- The `(1, 2)`-tensor `connDiffFib g₁ g₀ x` applied to a covector `om` is the `(0, 2)`-pairing
`connDiffPairing g₁ g₀ x om`. -/
@[simp] lemma connDiffFib_apply (g₁ g₀ : SmoothRiemannianMetric I M) (x : M)
    (om : Tensor0SSpace 1 I x) :
    (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from connDiffFib (I := I) g₁ g₀ x) om =
      connDiffPairing (I := I) g₁ g₀ x om := rfl

omit [CompactSpace M] [I.Boundaryless] in
/-- **The defining evaluation formula for the `(1, 2)`-tensor packaging.**  The `(1, 2)`-tensor
`connDiffFib g₁ g₀ x` applied to a covector `om` and evaluated on a pair of tangent vectors `(Y, Z)`
reads `om` against the connection-difference output `connDiff g₁ g₀ x Y Z`:
`(connDiffFib x om)[Y, Z] = om[connDiff x Y Z]`. -/
lemma connDiffFib_apply_eval (g₁ g₀ : SmoothRiemannianMetric I M) (x : M)
    (om : Tensor0SSpace 1 I x) (YZ : Fin 2 → TangentSpace I x) :
    ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from connDiffFib (I := I) g₁ g₀ x) om) YZ =
      om (fun _ : Fin 1 => connDiff (I := I) g₁ g₀ x (YZ 0) (YZ 1)) := by
  rw [connDiffFib_apply, connDiffPairing_apply]

/-! ## Smoothness of the dual-pairing packaging, and the `SmoothCcTensor` section -/

/-- The smoothness of the dual-pairing packaging as a Hom-bundle `(1, 2)`-tensor section: the field
`x ↦ connDiffFib g₁ g₀ x` is smooth.

By the Hom-bundle smoothness criterion `contMDiff_clm_section_of_pointwise` (source bundle the
covector bundle `Tensor0SSpace 1`, target the `(0, 2)`-tensor bundle `Tensor0SSpace 2`) it suffices
that for every smooth covector section `om`, the `(0, 2)`-tensor field
`x ↦ connDiffFib g₁ g₀ x (om x) = connDiffPairing g₁ g₀ x (om x)` is smooth.  That `(0, 2)`-section
smoothness is the coordinate criterion `contMDiff_multilinearSection_iff_coord`: through
`continuousMultilinearMap_basis_repr` the coordinate at a multi-index `σ : Fin 2 → Fin (finrank ℝ E)`
reads `connDiffPairing` against the trivialisation frame vectors, which on the trivialisation base set
agree with smooth tangent local frame fields `Y (σ 0), Y (σ 1)`.  There
`connDiffPairing(om x)(Y(σ 0)x, Y(σ 1)x) = om(connDiff x (Y(σ 0)x)(Y(σ 1)x))`, smooth by
`connDiff_contMDiff` (the connection-difference output is a smooth tangent field) followed by the
multilinear-section evaluation `contMDiffAt_section_apply` of the smooth covector `om` against it. -/
theorem connDiffFib_contMDiff (g₁ g₀ : SmoothRiemannianMetric I M) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 1 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel 1 2 ℝ E)
        (E := fun z : M => TensorRSSpace 1 2 I z) x (connDiffFib (I := I) g₁ g₀ x)) := by
  classical
  apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
    (F₁ := Tensor0SModel 1 ℝ E) (V₁ := fun x : M => Tensor0SSpace 1 I x)
    (F₂ := Tensor0SModel 2 ℝ E) (V₂ := fun x : M => Tensor0SSpace 2 I x)
    (φ := fun x : M => (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from
      connDiffFib (I := I) g₁ g₀ x))
  -- For every smooth covector section `om`, the `(0, 2)`-tensor field
  -- `x ↦ connDiffFib g₁ g₀ x (om x) = connDiffPairing g₁ g₀ x (om x)` is smooth.
  intro om
  letI := Tensor0SBundle.tensor0SBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 2
  have hsec : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SModel 2 ℝ E)
        (E := fun z : M => Tensor0SSpace 2 I z) x
        (connDiffPairing (I := I) g₁ g₀ x (om x))) := by
    refine (contMDiff_multilinearSection_iff_coord (𝕜 := ℝ) (F := E)
      (E := (TangentSpace I : M → Type _)) (IB := I) (n := (∞ : WithTop ℕ∞)) (Module.finBasis ℝ E)
      (fun x : M => (connDiffPairing (I := I) g₁ g₀ x (om x) :
        Bundle.continuousMultilinearMap ℝ 2 E (TangentSpace I) x))).mpr ?_
    intro σ x₀
    set b := Module.finBasis ℝ E with hb
    set e₁ := trivializationAt E (TangentSpace I : M → Type _) x₀ with he₁def
    have he₁ : x₀ ∈ e₁.baseSet := mem_baseSet_trivializationAt E (TangentSpace I) x₀
    have hframe := e₁.isLocalFrameOn_localFrame_baseSet I (⊤ : ℕ∞) b
    obtain ⟨Y, hY⟩ := hframe.exists_contMDiffSection_eqOn_nhd e₁.open_baseSet he₁
    -- The connection-difference output `x ↦ connDiff x (Y (σ 0) x) (Y (σ 1) x)` is a smooth field.
    have hconn : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
        (fun x : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) x
          (((connDiff (I := I) g₁ g₀ x) (Y (σ 0) x)) (Y (σ 1) x))) :=
      connDiff_contMDiff (I := I) g₁ g₀ (Y (σ 0)).contMDiff (Y (σ 1)).contMDiff
    -- Pairing the smooth covector `om` against the smooth field is a smooth scalar.
    have hscalar : ContMDiffAt I 𝓘(ℝ, ℝ) ∞
        (fun x : M => Tensor0SSpace.toModel (om x)
          (fun _ : Fin 1 => ((connDiff (I := I) g₁ g₀ x) (Y (σ 0) x)) (Y (σ 1) x))) x₀ :=
      TensorMultilinear.contMDiffAt_section_apply (n := 1) (x₀ := x₀)
        (fun x : M => om x) (om.contMDiff x₀)
        (fun _ : Fin 1 => fun x : M => ((connDiff (I := I) g₁ g₀ x) (Y (σ 0) x)) (Y (σ 1) x))
        (fun _ => (hconn x₀))
    refine hscalar.congr_of_eventuallyEq ?_
    have h_base₁ : ∀ᶠ x in 𝓝 x₀, x ∈ e₁.baseSet := e₁.open_baseSet.mem_nhds he₁
    filter_upwards [h_base₁, hY] with x hx₁ hYx
    -- The coordinate reads `connDiffPairing` against the frame vectors `symmL (b (σ j))`.
    rw [continuousMultilinearMap_basis_repr]
    -- The frame vectors `symmL e₁ x (b (σ j))` equal the smooth tangent sections `Y (σ j) x` near `x₀`.
    have hframe0 : e₁.symmL ℝ x (b (σ 0)) = (Y (σ 0)) x := by
      rw [hYx (σ 0), Trivialization.localFrame_apply_of_mem_baseSet (hx := hx₁)]
      simp [Trivialization.basisAt]
    have hframe1 : e₁.symmL ℝ x (b (σ 1)) = (Y (σ 1)) x := by
      rw [hYx (σ 1), Trivialization.localFrame_apply_of_mem_baseSet (hx := hx₁)]
      simp [Trivialization.basisAt]
    -- Read the multilinear-map application as `connDiffPairing` on the tangent tuple, then unfold.
    change (connDiffPairing (I := I) g₁ g₀ x (om x))
        (fun j : Fin 2 => e₁.symmL ℝ x (b (σ j))) = _
    rw [connDiffPairing_apply]
    -- Reduce `Tensor0SSpace.toModel (om x)` (RHS) to the bare FunLike application (`toModel` is the
    -- identity coercion on the carrier), then match the frame vectors with the smooth fields `Y`.
    rw [Tensor0SSpace.toModel, tensor0SSpace_continuousLinearEquiv_apply]
    rw [hframe0, hframe1]
    rfl
  refine hsec.congr ?_
  intro x
  rfl

/-- **The connection-difference tensor as a smooth, compactly-supported `(1, 2)`-tensor section.**
Its fibre value at `x` is the dual-pairing packaging `connDiffFib g₁ g₀ x`
(`om ↦ (Y, Z) ↦ om(connDiff g₁ g₀ x Y Z)`), smooth by `connDiffFib_contMDiff`; on the closed
manifold it has compact support.  This is the bundled `SmoothCcTensor g₀ 1 2` the covariant-gradient
machinery `covGrad g₀ 1 2` consumes. -/
def connDiffSection (g₁ g₀ : SmoothRiemannianMetric I M) : SmoothCcTensor g₀ 1 2 where
  toSection :=
    { toFun := fun x : M => connDiffFib (I := I) g₁ g₀ x
      contMDiff_toFun := connDiffFib_contMDiff (I := I) g₁ g₀ }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

/-- The underlying section value of `connDiffSection g₁ g₀` at `x` is the fibre `connDiffFib g₁ g₀ x`.
Definitional. -/
@[simp] lemma connDiffSection_toSection (g₁ g₀ : SmoothRiemannianMetric I M) (x : M) :
    (connDiffSection (I := I) g₁ g₀).toSection x = connDiffFib (I := I) g₁ g₀ x := rfl

/-! ## The covariant-gradient ↔ Palatini directional-derivative bridge -/

set_option linter.unusedSectionVars false in
/-- **Hom product-rule split of the directional covariant derivative of `connDiffSection`.**
For smooth covector field `om` and smooth tangent fields `X Y Z`, the directional covariant derivative
`tensorCovDerivAt g₀ 1 2 (connDiffSection g₁ g₀)` along `X x`, applied to the covector `om x` and read
on the tangent pair `(Y x, Z x)`, splits by the Hom-bundle product rule
(`tensorRSCovariantDerivative_apply_of_mdifferentiableAt`) into the `(0, 2)`-derivative of the
dual-pairing `y ↦ connDiffPairing g₁ g₀ y (om y)` minus the dual-pairing of the `(0, 1)`-derivative of
`om`:
```
(∇_{X x} (connDiffSection))(om x)(Y x, Z x)
  = (∇^{(0,2)}_{X x}(y ↦ connDiffPairing g₁ g₀ y (om y)))(Y x, Z x)
    − connDiffPairing g₁ g₀ x (∇^{(0,1)}_{X x} om)(Y x, Z x).
``` -/
private lemma connDiffSection_tensorCovDerivAt_homSplit
    (g₁ g₀ : SmoothRiemannianMetric I M)
    (om : Cₛ^∞⟮I; Tensor0SModel 1 ℝ E, (fun x : M => Tensor0SSpace 1 I x)⟯)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) :
    (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from
        tensorCovDerivAt (I := I) (M := M) g₀ 1 2 (connDiffSection (I := I) g₁ g₀) x (X x))
        (om x) =
      Tensor0SNabla.tensor0SCovariantDerivative I M 2 (LeviCivita (I := I) g₀)
          (fun y : M => connDiffPairing (I := I) g₁ g₀ y (om y)) x (X x) -
        connDiffPairing (I := I) g₁ g₀ x
          (Tensor0SNabla.tensor0SCovariantDerivative I M 1 (LeviCivita (I := I) g₀)
            (fun y : M => om y) x (X x)) := by
  have hτ : MDifferentiableAt I (I.prod 𝓘(ℝ, TensorRSModel 1 2 ℝ E))
      (fun y : M => TotalSpace.mk' (TensorRSModel 1 2 ℝ E)
        (E := fun z : M => TensorRSSpace 1 2 I z) y
        ((connDiffSection (I := I) g₁ g₀).toSection y)) x :=
    (connDiffSection (I := I) g₁ g₀).toSection.contMDiff.contMDiffAt.mdifferentiableAt (by simp)
  have hw : MDifferentiableAt I (I.prod 𝓘(ℝ, Tensor0SModel 1 ℝ E))
      (fun y : M => TotalSpace.mk' (Tensor0SModel 1 ℝ E)
        (E := fun z : M => Tensor0SSpace 1 I z) y (om y)) x :=
    om.contMDiff.contMDiffAt.mdifferentiableAt (by simp)
  have hV : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun y : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) y (X y)) x :=
    X.contMDiff.contMDiffAt.mdifferentiableAt (by simp)
  rw [tensorCovDerivAt_def (I := I) (M := M) g₀ 1 2 (connDiffSection (I := I) g₁ g₀) x (X x)]
  have hsplit := tensorRSCovariantDerivative_apply_of_mdifferentiableAt (I := I) (M := M)
    1 2 (LeviCivita (I := I) g₀)
    (fun y : M => (connDiffSection (I := I) g₁ g₀).toSection y) (fun y : M => om y)
    (fun y : M => X y) hτ hw hV
  -- The fibre value of `connDiffSection.toSection y` applied to `om y` is `connDiffPairing`.
  have hval : (fun y : M =>
        (show Tensor0SSpace 1 I y →L[ℝ] Tensor0SSpace 2 I y from
          (connDiffSection (I := I) g₁ g₀).toSection y) (om y)) =
      (fun y : M => connDiffPairing (I := I) g₁ g₀ y (om y)) := by
    funext y
    rw [connDiffSection_toSection]
    rfl
  rw [hsplit, hval]
  rfl

end Connection
end Integral
end DifferentialGeometry
