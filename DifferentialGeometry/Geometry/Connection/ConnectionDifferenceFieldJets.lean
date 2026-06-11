import DifferentialGeometry.Geometry.Connection.ConnectionDifferenceField
import DifferentialGeometry.Geometry.Connection.TensorNabla.IteratedTensorCovDeriv
import DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricRealization.ConnectionDifferenceKoszul
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.CovariantBilinearLeibniz
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.SegmentMetricRicciSectionIdentity
import DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricRealization.RealizeSymmIteratedCovGradFiberNormBound
import DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricRealization.PosDefPerturbation
import DifferentialGeometry.Geometry.Connection.TensorNabla.LiftedSectionCovariantRealizeBridge
import DifferentialGeometry.Analysis.Sobolev.Embedding.RawConnLapToHsOrderDropping

/-! # The metrically-lowered connection difference as a covariant section and its iterated-jet bound

For two smooth Riemannian metrics `g₁`, `g₀` on a closed (compact, boundaryless) smooth manifold
`M` modelled on a real inner-product space `E`, the connection-difference operator field
`connDiffField g₁ g₀` (`Geometry/Connection/ConnectionDifferenceField.lean`) is a smooth section of
the `(1, 2)`-tensor bundle `Hom(TM, Hom(TM, TM))`.  Pairing its fibre value with the background
metric `g₀` produces a genuine **covariant `(0, 3)`-tensor** — the metrically-lowered connection
difference

```
loweredConnDiffSection g₁ g₀ : SmoothCcTensor g₀ 0 3,
toModel(loweredConnDiffSection g₁ g₀ x) ![a, b, c] = g₀.inner x (connDiffField g₁ g₀ x b a) c.
```

This file packages that lowered object as a first-class `SmoothCcTensor` and supplies the
intrinsic **iterated-covariant-jet bound** the higher-order metric-difference (covariant
Faà-di-Bruno) development consumes.

## What the lowered section is and why it is the right object

The Koszul difference formula `connDiff_koszul_realize_g0` (`ConnectionDifferenceKoszul.lean`) reads
the `g₀`-pairing of the connection difference as the realized `≤ 1`-jet of the perturbation
`h = ccTensorBilinSymm g₀ T₁` plus the perturbation·connection-difference correction `−2·h(D, c)`:
$$
  2\,g_0(D\,b\,a, c) = (\nabla^0 h\text{-combination}) - 2\,h(D\,b\,a, c),
  \qquad D = \operatorname{connDiff} g_1\,g_0.
$$
The lowering uses the *background* metric `g₀`, whose Levi-Civita covariant derivative is parallel
(`∇₀ g₀ = 0`), so the metric-lowering is a **parallel fibre operation** that commutes with `∇₀` and
neither raises the differentiation order nor enlarges the `g₀`-fibre norm.  The `(0, 3)`-section is
therefore the natural covariant carrier of the connection difference — exactly the shape under which
its iterated covariant gradient `∇^p` can be controlled.

## Uniformity: a fibre-small ball gate is required (the Koszul correction is nonlinear in `T₁`)

Unlike the metric-realization map `T ↦ realizeSymmCcTensor g₀ T` (which is fibrewise *linear*, so its
iterated-jet bound `exists_riemannianFiberNormSq_iteratedCovGrad_realizeSymm_le_jetSum` is
unconditional with constant `1`), the lowered connection difference is a **nonlinear** function of
the perturbation `T₁`: the Koszul correction `h(D, c)` carries the connection difference `D` itself,
and `D = g₁^{-1}\cdot(\nabla_0 h)` involves the *perturbed*-metric inverse `g₁^{-1}`.  As the family
of realized metrics `g₁ = g₀ + ccTensorBilinSymm g₀ T₁` ranges, `g₁` can degenerate (the realize
idiom imposes no uniform ellipticity), so `g₁^{-1}` — hence `D`, hence the lowered section — is *not*
controlled by the jets of `T₁` uniformly.  The iterated-jet bound therefore holds only on a
**fibre-small ball** `gFibreOpBound g₀ (ccTensorBilinSymm g₀ T₁) δ` with `δ < 1`
(`PosDefPerturbation.lean`): there the `i = 0` Leibniz term of the correction is absorbed by the
fibre-smallness (`‖h‖ ≤ δ` in the `g₀`-fibre operator norm), closing the order-by-order recursion.
The C4 consumers (the sealed Ricci–DeTurck curvature-difference development) live in this fibre-small
regime.

## Main definitions

* `loweredConnDiffSection g₁ g₀` — the `g₀`-metrically-lowered connection-difference field, as a
  genuine covariant `SmoothCcTensor g₀ 0 3`.  Compact support is automatic on the compact manifold.

## Main results

* `loweredConnDiffSection_toModel_apply` — its fibre value
  `toModel(loweredConnDiffSection g₁ g₀ x) ![a, b, c] = g₀.inner x (connDiff g₁ g₀ x b a) c`.
* `loweredConnDiffSection_self` — the lowered connection difference of a metric with itself is the
  zero section (the non-vacuity litmus; `connDiffField_self`).
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

open Bundle Manifold Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff BigOperators

namespace DifferentialGeometry
namespace PDE
namespace DeTurck

open DifferentialGeometry
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2 (SmoothCcTensor)
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [SigmaCompactSpace M] [T2Space M] [I.Boundaryless] [BoundarylessManifold I M]

/-! ### T1-pre: the metrically-lowered connection difference as a covariant `(0,3)`-section -/

/-- **The `g₀`-lowered connection-difference bilinear form** at `x`, as a continuous trilinear form
`T_x M →L T_x M →L T_x M →L ℝ`: `(a, b, c) ↦ g₀.inner x (connDiffField g₁ g₀ x b a) c`.  This is the
metrically-lowered connection difference as an operator-packaged covariant `(0, 3)`-form (the
`a`-slot is the direction, the `b`-slot the differentiated vector, the `c`-slot the lowered output
index).  Linearity in all three slots is the bilinearity of `connDiffField g₁ g₀ x` and the
linearity of `g₀.inner x`.

Concretely: `(connDiffField g₁ g₀ x).flip` is `a ↦ b ↦ connDiffField g₁ g₀ x b a`, and
postcomposing its output endomorphism with the lowering `g₀.inner x : T_x →L (T_x →L ℝ)` (via
`ContinuousLinearMap.compL`) lowers the output index to `c`. -/
def loweredConnDiffTri (g₁ g₀ : SmoothRiemannianMetric I M) (x : M) :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ :=
  (ContinuousLinearMap.compL ℝ (TangentSpace I x) (TangentSpace I x)
      (TangentSpace I x →L[ℝ] ℝ) (g₀.inner x)).comp
    ((connDiffField (I := I) g₁ g₀ x).flip)

@[simp] lemma loweredConnDiffTri_apply (g₁ g₀ : SmoothRiemannianMetric I M) (x : M)
    (a b c : TangentSpace I x) :
    loweredConnDiffTri (I := I) g₁ g₀ x a b c =
      g₀.inner x (connDiffField (I := I) g₁ g₀ x b a) c := by
  rfl

/-- **Smoothness of the `g₀`-lowered connection-difference trilinear form on smooth fields.**  For
smooth tangent vector fields `X`, `Y`, `Z`, the scalar field
`x ↦ loweredConnDiffTri g₁ g₀ x (X x) (Y x) (Z x) = g₀.inner x (connDiff g₁ g₀ x (Y x) (X x)) (Z x)`
is smooth.  The inner connection-difference field `x ↦ connDiff g₁ g₀ x (Y x) (X x)` is smooth by
`connDiff_contMDiff` (a whole-contraction read, not a term-wise basis read), and the `g₀`-inner
pairing of two smooth tangent fields is smooth by `contMDiff_g_inner_of_smooth_sections`. -/
theorem loweredConnDiffTri_pairing_contMDiff (g₁ g₀ : SmoothRiemannianMetric I M)
    {X Y Z : Π b : M, TangentSpace I b}
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% X))
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Y))
    (hZ : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Z)) :
    ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun b : M => loweredConnDiffTri (I := I) g₁ g₀ b (X b) (Y b) (Z b)) := by
  have hinner : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (T% (fun b : M => connDiff (I := I) g₁ g₀ b (Y b) (X b))) :=
    connDiff_contMDiff (I := I) g₁ g₀ hY hX
  let D : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    ContMDiffSection.mk (fun b : M => connDiff (I := I) g₁ g₀ b (Y b) (X b)) hinner
  let Zs : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    ContMDiffSection.mk Z hZ
  have hpair : ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun b : M => g₀.inner b (D b) (Zs b)) :=
    contMDiff_g_inner_of_smooth_sections (I := I) g₀ D Zs
  refine hpair.congr (fun b => ?_)
  change g₀.inner b (connDiff (I := I) g₁ g₀ b (Y b) (X b)) (Z b) =
    loweredConnDiffTri (I := I) g₁ g₀ b (X b) (Y b) (Z b)
  rw [loweredConnDiffTri_apply, connDiffField_apply]

/-- The pointwise `(0,3)`-tensor model value of the `g₀`-lowered connection difference: the model
multilinear map obtained from the trilinear form `loweredConnDiffTri g₁ g₀ x` by the fibre bridge
`triFormToModel`. -/
private def loweredModelFun (g₁ g₀ : SmoothRiemannianMetric I M) (x : M) : Tensor0SSpace 3 I x :=
  Tensor0SSpace.ofModel (triFormToModel (TangentSpace I x) (loweredConnDiffTri (I := I) g₁ g₀ x))

omit [I.Boundaryless] in
private theorem loweredModelFun_toModel_apply (g₁ g₀ : SmoothRiemannianMetric I M) (x : M)
    (v : Fin 3 → TangentSpace I x) :
    Tensor0SSpace.toModel (loweredModelFun (I := I) g₁ g₀ x) v =
      loweredConnDiffTri (I := I) g₁ g₀ x (v 0) (v 1) (v 2) := by
  unfold loweredModelFun
  rw [Tensor0SSpace.toModel_ofModel]
  exact triFormToModel_apply (TangentSpace I x) (loweredConnDiffTri (I := I) g₁ g₀ x) v

/-- **The `g₀`-lowered connection difference as a smooth covariant `(0,3)`-tensor field.**  Its
chart-component smoothness is the trilinear-form pairing smoothness
`loweredConnDiffTri_pairing_contMDiff` on the chart-`α`-pushforward frame `chartFrameVec` (the same
`contMDiff_multilinearSection_iff_coord` route as `crossField` / `ricciNeg2Field`). -/
def loweredConnDiffField (g₁ g₀ : SmoothRiemannianMetric I M) :
    Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) ∞ 3 :=
  letI := tensor0SBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 3
  letI := TangentBundle.contMDiffVectorBundle (I := I) (M := M) (n := ∞)
  ⟨fun x => loweredModelFun (I := I) g₁ g₀ x, by
    let d := Module.finrank ℝ E
    let b : Module.Basis (Fin d) ℝ E := chartModelBasis E
    refine (contMDiff_multilinearSection_iff_coord (TangentSpace I) ∞ b _).mpr
      fun σ x₀ => ?_
    have hcomp : ContMDiffOn I 𝓘(ℝ, ℝ) ∞
        (fun x : M =>
          loweredConnDiffTri (I := I) g₁ g₀ x
            (chartFrameVec (I := I) x₀ (σ 0) x)
            (chartFrameVec (I := I) x₀ (σ 1) x)
            (chartFrameVec (I := I) x₀ (σ 2) x))
        (chartAt H x₀).source := by
      intro x hx
      have hframe_on : ∀ k : Fin (Module.finrank ℝ E),
          ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
            (fun bb : M => TotalSpace.mk' E bb (chartFrameVec (I := I) x₀ k bb))
            (chartAt H x₀).source := fun k => by
        have h := chartAlphaFrame_section_contMDiffOn (I := I) x₀ k
        exact h
      obtain ⟨S, hS_eq⟩ :=
        exists_contMDiffSection_eqOn_nhd
          (s := fun k : Fin (Module.finrank ℝ E) => fun bb : M => chartFrameVec (I := I) x₀ k bb)
          (u := (chartAt H x₀).source) (p := x)
          hframe_on ((chartAt H x₀).open_source) hx
      have hSk : ∀ k, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
          (T% (fun bb : M => (S k) bb : Π bb : M, TangentSpace I bb)) := fun k => (S k).contMDiff
      have hpair : ContMDiff I 𝓘(ℝ, ℝ) ∞
          (fun bb : M => loweredConnDiffTri (I := I) g₁ g₀ bb
            ((S (σ 0)) bb) ((S (σ 1)) bb) ((S (σ 2)) bb)) :=
        loweredConnDiffTri_pairing_contMDiff (I := I) g₁ g₀ (hSk (σ 0)) (hSk (σ 1)) (hSk (σ 2))
      have hpair_at : ContMDiffAt I 𝓘(ℝ, ℝ) ∞
          (fun bb : M => loweredConnDiffTri (I := I) g₁ g₀ bb
            ((S (σ 0)) bb) ((S (σ 1)) bb) ((S (σ 2)) bb)) x :=
        hpair x
      have hchart_at : ContMDiffAt I 𝓘(ℝ, ℝ) ∞
          (fun x : M => loweredConnDiffTri (I := I) g₁ g₀ x
            (chartFrameVec (I := I) x₀ (σ 0) x)
            (chartFrameVec (I := I) x₀ (σ 1) x)
            (chartFrameVec (I := I) x₀ (σ 2) x)) x := by
        refine hpair_at.congr_of_eventuallyEq ?_
        filter_upwards [hS_eq] with bb hb
        rw [hb (σ 0), hb (σ 1), hb (σ 2)]
      exact hchart_at.contMDiffWithinAt
    have hx₀_src : x₀ ∈ (chartAt H x₀).source := mem_chart_source H x₀
    have hx₀_base : x₀ ∈ (trivializationAt E (TangentSpace I) x₀).baseSet :=
      mem_baseSet_trivializationAt E (TangentSpace I) x₀
    have h_src_nhd : (chartAt H x₀).source ∈ 𝓝 x₀ :=
      (chartAt H x₀).open_source.mem_nhds hx₀_src
    refine ((hcomp x₀ hx₀_src).contMDiffAt h_src_nhd).congr_of_eventuallyEq ?_
    have h_base_nhd :
        (trivializationAt E (TangentSpace I) x₀).baseSet ∈ 𝓝 x₀ :=
      (trivializationAt E (TangentSpace I) x₀).open_baseSet.mem_nhds hx₀_base
    filter_upwards [h_base_nhd] with x hx
    rw [continuousMultilinearMap_basis_repr]
    change Tensor0SSpace.toModel (loweredModelFun (I := I) g₁ g₀ x)
        (fun j => (trivializationAt E (TangentSpace I) x₀).symmL ℝ x (b (σ j))) = _
    rw [loweredModelFun_toModel_apply]
    rfl⟩

/-- The `g₀`-lowered connection difference as a smooth mixed `(0,3)`-tensor section. -/
def loweredConnDiffMixedSection (g₁ g₀ : SmoothRiemannianMetric I M) :
    Cₛ^∞⟮I; TensorRSModel 0 3 ℝ E, (fun x : M => TensorRSSpace 0 3 I x)⟯ :=
  MixedSection.fromMultilinearSection (𝕜 := ℝ) (F := E) (IB := I)
    (E := (TangentSpace I : M → Type _)) ∞ (loweredConnDiffField (I := I) g₁ g₀)

/-- **The `g₀`-metrically-lowered connection difference as a `SmoothCcTensor g₀ 0 3`** — the genuine
covariant section-level lowered connection-difference object.  Its fibre is
`toModel(loweredConnDiffSection g₁ g₀ x) ![a, b, c] = g₀.inner x (connDiff g₁ g₀ x b a) c`
(`loweredConnDiffSection_toModel_apply`); compact support is automatic on the compact manifold `M`.
-/
def loweredConnDiffSection (g₁ g₀ : SmoothRiemannianMetric I M) :
    Integral.L2.SmoothCcTensor g₀ 0 3 where
  toSection := loweredConnDiffMixedSection (I := I) g₁ g₀
  hasCompactSupport := HasCompactSupport.of_compactSpace _

set_option linter.unusedSectionVars false in
/-- **The fibre value of the lowered connection-difference section.**  Evaluating the underlying
`(0,3)` mixed tensor at the canonical unit `(0,0)`-tensor and a tangent triple recovers the
`g₀`-pairing of the connection difference,
`g₀.inner x (connDiff g₁ g₀ x b a) c`, by traversing the packaging chain
`loweredConnDiffSection → MixedSection.fromMultilinearSection loweredConnDiffField`
(`MixedSection.eval₀_apply`) then `loweredConnDiffField → Tensor0SSpace.ofModel ∘ triFormToModel`
(`loweredModelFun_toModel_apply`) and the trilinear-form evaluation `loweredConnDiffTri_apply`. -/
theorem loweredConnDiffSection_toModel_apply (g₁ g₀ : SmoothRiemannianMetric I M) (x : M)
    (a b c : TangentSpace I x) :
    Tensor0SSpace.toModel
        ((loweredConnDiffSection (I := I) g₁ g₀).toSection x
          (ContinuousMultilinearMap.constOfIsEmpty ℝ
            (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ))) ![a, b, c] =
      g₀.inner x (connDiff (I := I) g₁ g₀ x b a) c := by
  classical
  change Tensor0SSpace.toModel
      ((MixedSection.eval₀ (F := E) (E := (TangentSpace I : M → Type _)) x).smulRight
          (loweredConnDiffField (I := I) g₁ g₀ x)
        (ContinuousMultilinearMap.constOfIsEmpty ℝ
          (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ))) ![a, b, c] = _
  rw [ContinuousLinearMap.smulRight_apply, MixedSection.eval₀_apply,
    ContinuousMultilinearMap.constOfIsEmpty_apply, one_smul]
  change Tensor0SSpace.toModel (loweredModelFun (I := I) g₁ g₀ x) ![a, b, c] = _
  rw [loweredModelFun_toModel_apply, loweredConnDiffTri_apply, connDiffField_apply]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.tail_cons,
    Matrix.head_cons]

/-- **The lowered connection-difference trilinear form of a metric with itself vanishes.**  When the
two metrics coincide, the connection-difference field is the zero section (`connDiffField_self`), so
the lowered trilinear form is the zero form. -/
theorem loweredConnDiffTri_self (g : SmoothRiemannianMetric I M) (x : M) :
    loweredConnDiffTri (I := I) g g x = 0 := by
  ext a b c
  rw [loweredConnDiffTri_apply]
  have h0 : connDiffField (I := I) g g x b a = 0 := by
    rw [connDiffField_self]
    simp
  rw [h0, map_zero, ContinuousLinearMap.zero_apply]
  rfl

set_option linter.unusedSectionVars false in
/-- **Self-vanishing of the lowered connection-difference section** (non-vacuity litmus).  The fibre
value of the `g`-lowered connection difference of `g` with itself vanishes on every tangent triple:
the two Levi-Civita covariant derivatives coincide, so `connDiff g g = 0`, hence every fibre
`g`-pairing is zero.  This rejects the degenerate reading of the lowered object (it is genuinely the
difference, not a constant nonzero `(0,3)`-section), consistent with `connDiffField_self`. -/
theorem loweredConnDiffSection_self_toModel (g : SmoothRiemannianMetric I M) (x : M)
    (a b c : TangentSpace I x) :
    Tensor0SSpace.toModel
        ((loweredConnDiffSection (I := I) g g).toSection x
          (ContinuousMultilinearMap.constOfIsEmpty ℝ
            (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ))) ![a, b, c] = 0 := by
  rw [loweredConnDiffSection_toModel_apply]
  have h0 : connDiff (I := I) g g x b a = 0 := by
    rw [connDiff_self]; rfl
  rw [h0, map_zero, ContinuousLinearMap.zero_apply]

/-! ### The cross-correction `(0,3)`-section `h ⌟ D` (the Koszul `g₀`-lowering correction)

The `g₀`-lowered Koszul difference formula `connDiff_koszul_realize_g0` carries the
perturbation·connection-difference correction `−2·h(D, c)` with `h = ccTensorBilinSymm g₀ T₁` and
`D = connDiff g₁ g₀`.  This subsection packages that correction's `(0,3)`-fibre value
`h(D b a, c)` as a genuine covariant `SmoothCcTensor g₀ 0 3`, built by the same trilinear-form →
field → mixed-section chain as `loweredConnDiffSection`. -/

/-- **The cross-correction trilinear form** `(a, b, c) ↦ ccTensorBilinSymm g₀ T₁ x (connDiffField
g₁ g₀ x b a) c`, the `(0,3)`-fibre value of the Koszul `g₀`-lowering correction `h(D, ·)`. -/
def crossCorrectionTri (g₁ g₀ : SmoothRiemannianMetric I M)
    (T₁ : Integral.L2.SmoothCcTensor g₀ 0 2) (x : M) :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ :=
  (ContinuousLinearMap.compL ℝ (TangentSpace I x) (TangentSpace I x)
      (TangentSpace I x →L[ℝ] ℝ) (ccTensorBilinSymm (I := I) g₀ T₁ x)).comp
    ((connDiffField (I := I) g₁ g₀ x).flip)

@[simp] lemma crossCorrectionTri_apply (g₁ g₀ : SmoothRiemannianMetric I M)
    (T₁ : Integral.L2.SmoothCcTensor g₀ 0 2) (x : M) (a b c : TangentSpace I x) :
    crossCorrectionTri (I := I) g₁ g₀ T₁ x a b c =
      ccTensorBilinSymm (I := I) g₀ T₁ x (connDiffField (I := I) g₁ g₀ x b a) c := by
  rfl

/-- **Smoothness of the cross-correction trilinear form on smooth fields.**  For smooth tangent
vector fields `X`, `Y`, `Z`, the scalar field
`x ↦ crossCorrectionTri g₁ g₀ T₁ x (X x) (Y x) (Z x)` is smooth.  The inner connection-difference
field is smooth by `connDiff_contMDiff`, and the `ccTensorBilinSymm`-pairing of two smooth tangent
fields is smooth by `contMDiff_ccTensorBilinSymm_pairing`. -/
theorem crossCorrectionTri_pairing_contMDiff (g₁ g₀ : SmoothRiemannianMetric I M)
    (T₁ : Integral.L2.SmoothCcTensor g₀ 0 2)
    {X Y Z : Π b : M, TangentSpace I b}
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% X))
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Y))
    (hZ : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Z)) :
    ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun b : M => crossCorrectionTri (I := I) g₁ g₀ T₁ b (X b) (Y b) (Z b)) := by
  have hinner : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (T% (fun b : M => connDiff (I := I) g₁ g₀ b (Y b) (X b))) :=
    connDiff_contMDiff (I := I) g₁ g₀ hY hX
  let D : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    ContMDiffSection.mk (fun b : M => connDiff (I := I) g₁ g₀ b (Y b) (X b)) hinner
  let Zs : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    ContMDiffSection.mk Z hZ
  have hpair : ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun b : M => ccTensorBilinSymm (I := I) g₀ T₁ b (D b) (Zs b)) :=
    contMDiff_ccTensorBilinSymm_pairing (I := I) g₀ T₁ D Zs
  refine hpair.congr (fun b => ?_)
  change ccTensorBilinSymm (I := I) g₀ T₁ b (connDiff (I := I) g₁ g₀ b (Y b) (X b)) (Z b) =
    crossCorrectionTri (I := I) g₁ g₀ T₁ b (X b) (Y b) (Z b)
  rw [crossCorrectionTri_apply, connDiffField_apply]

/-- The pointwise `(0,3)`-tensor model value of the cross-correction. -/
private def crossCorrectionModelFun (g₁ g₀ : SmoothRiemannianMetric I M)
    (T₁ : Integral.L2.SmoothCcTensor g₀ 0 2) (x : M) : Tensor0SSpace 3 I x :=
  Tensor0SSpace.ofModel
    (triFormToModel (TangentSpace I x) (crossCorrectionTri (I := I) g₁ g₀ T₁ x))

omit [I.Boundaryless] in
private theorem crossCorrectionModelFun_toModel_apply (g₁ g₀ : SmoothRiemannianMetric I M)
    (T₁ : Integral.L2.SmoothCcTensor g₀ 0 2) (x : M) (v : Fin 3 → TangentSpace I x) :
    Tensor0SSpace.toModel (crossCorrectionModelFun (I := I) g₁ g₀ T₁ x) v =
      crossCorrectionTri (I := I) g₁ g₀ T₁ x (v 0) (v 1) (v 2) := by
  unfold crossCorrectionModelFun
  rw [Tensor0SSpace.toModel_ofModel]
  exact triFormToModel_apply (TangentSpace I x) (crossCorrectionTri (I := I) g₁ g₀ T₁ x) v

/-- **The cross-correction as a smooth covariant `(0,3)`-tensor field.** -/
def crossCorrectionField (g₁ g₀ : SmoothRiemannianMetric I M)
    (T₁ : Integral.L2.SmoothCcTensor g₀ 0 2) :
    Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) ∞ 3 :=
  letI := tensor0SBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 3
  letI := TangentBundle.contMDiffVectorBundle (I := I) (M := M) (n := ∞)
  ⟨fun x => crossCorrectionModelFun (I := I) g₁ g₀ T₁ x, by
    let d := Module.finrank ℝ E
    let b : Module.Basis (Fin d) ℝ E := chartModelBasis E
    refine (contMDiff_multilinearSection_iff_coord (TangentSpace I) ∞ b _).mpr
      fun σ x₀ => ?_
    have hcomp : ContMDiffOn I 𝓘(ℝ, ℝ) ∞
        (fun x : M =>
          crossCorrectionTri (I := I) g₁ g₀ T₁ x
            (chartFrameVec (I := I) x₀ (σ 0) x)
            (chartFrameVec (I := I) x₀ (σ 1) x)
            (chartFrameVec (I := I) x₀ (σ 2) x))
        (chartAt H x₀).source := by
      intro x hx
      have hframe_on : ∀ k : Fin (Module.finrank ℝ E),
          ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
            (fun bb : M => TotalSpace.mk' E bb (chartFrameVec (I := I) x₀ k bb))
            (chartAt H x₀).source := fun k => chartAlphaFrame_section_contMDiffOn (I := I) x₀ k
      obtain ⟨S, hS_eq⟩ :=
        exists_contMDiffSection_eqOn_nhd
          (s := fun k : Fin (Module.finrank ℝ E) => fun bb : M => chartFrameVec (I := I) x₀ k bb)
          (u := (chartAt H x₀).source) (p := x)
          hframe_on ((chartAt H x₀).open_source) hx
      have hSk : ∀ k, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
          (T% (fun bb : M => (S k) bb : Π bb : M, TangentSpace I bb)) := fun k => (S k).contMDiff
      have hpair : ContMDiff I 𝓘(ℝ, ℝ) ∞
          (fun bb : M => crossCorrectionTri (I := I) g₁ g₀ T₁ bb
            ((S (σ 0)) bb) ((S (σ 1)) bb) ((S (σ 2)) bb)) :=
        crossCorrectionTri_pairing_contMDiff (I := I) g₁ g₀ T₁ (hSk (σ 0)) (hSk (σ 1)) (hSk (σ 2))
      have hchart_at : ContMDiffAt I 𝓘(ℝ, ℝ) ∞
          (fun x : M => crossCorrectionTri (I := I) g₁ g₀ T₁ x
            (chartFrameVec (I := I) x₀ (σ 0) x)
            (chartFrameVec (I := I) x₀ (σ 1) x)
            (chartFrameVec (I := I) x₀ (σ 2) x)) x := by
        refine (hpair x).congr_of_eventuallyEq ?_
        filter_upwards [hS_eq] with bb hb
        rw [hb (σ 0), hb (σ 1), hb (σ 2)]
      exact hchart_at.contMDiffWithinAt
    have hx₀_src : x₀ ∈ (chartAt H x₀).source := mem_chart_source H x₀
    have hx₀_base : x₀ ∈ (trivializationAt E (TangentSpace I) x₀).baseSet :=
      mem_baseSet_trivializationAt E (TangentSpace I) x₀
    have h_src_nhd : (chartAt H x₀).source ∈ 𝓝 x₀ :=
      (chartAt H x₀).open_source.mem_nhds hx₀_src
    refine ((hcomp x₀ hx₀_src).contMDiffAt h_src_nhd).congr_of_eventuallyEq ?_
    have h_base_nhd :
        (trivializationAt E (TangentSpace I) x₀).baseSet ∈ 𝓝 x₀ :=
      (trivializationAt E (TangentSpace I) x₀).open_baseSet.mem_nhds hx₀_base
    filter_upwards [h_base_nhd] with x hx
    rw [continuousMultilinearMap_basis_repr]
    change Tensor0SSpace.toModel (crossCorrectionModelFun (I := I) g₁ g₀ T₁ x)
        (fun j => (trivializationAt E (TangentSpace I) x₀).symmL ℝ x (b (σ j))) = _
    rw [crossCorrectionModelFun_toModel_apply]
    rfl⟩

/-- The cross-correction as a smooth mixed `(0,3)`-tensor section. -/
def crossCorrectionMixedSection (g₁ g₀ : SmoothRiemannianMetric I M)
    (T₁ : Integral.L2.SmoothCcTensor g₀ 0 2) :
    Cₛ^∞⟮I; TensorRSModel 0 3 ℝ E, (fun x : M => TensorRSSpace 0 3 I x)⟯ :=
  MixedSection.fromMultilinearSection (𝕜 := ℝ) (F := E) (IB := I)
    (E := (TangentSpace I : M → Type _)) ∞ (crossCorrectionField (I := I) g₁ g₀ T₁)

/-- **The cross-correction `h ⌟ D` as a `SmoothCcTensor g₀ 0 3`.**  Its fibre is
`toModel(crossCorrectionSection g₁ g₀ T₁ x) ![a, b, c] = ccTensorBilinSymm g₀ T₁ x (connDiff g₁ g₀ x
b a) c` (`crossCorrectionSection_toModel_apply`); compact support is automatic on `M`. -/
def crossCorrectionSection (g₁ g₀ : SmoothRiemannianMetric I M)
    (T₁ : Integral.L2.SmoothCcTensor g₀ 0 2) :
    Integral.L2.SmoothCcTensor g₀ 0 3 where
  toSection := crossCorrectionMixedSection (I := I) g₁ g₀ T₁
  hasCompactSupport := HasCompactSupport.of_compactSpace _

set_option linter.unusedSectionVars false in
/-- **The fibre value of the cross-correction section.** -/
theorem crossCorrectionSection_toModel_apply (g₁ g₀ : SmoothRiemannianMetric I M)
    (T₁ : Integral.L2.SmoothCcTensor g₀ 0 2) (x : M) (a b c : TangentSpace I x) :
    Tensor0SSpace.toModel
        ((crossCorrectionSection (I := I) g₁ g₀ T₁).toSection x
          (ContinuousMultilinearMap.constOfIsEmpty ℝ
            (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ))) ![a, b, c] =
      ccTensorBilinSymm (I := I) g₀ T₁ x (connDiff (I := I) g₁ g₀ x b a) c := by
  classical
  change Tensor0SSpace.toModel
      ((MixedSection.eval₀ (F := E) (E := (TangentSpace I : M → Type _)) x).smulRight
          (crossCorrectionField (I := I) g₁ g₀ T₁ x)
        (ContinuousMultilinearMap.constOfIsEmpty ℝ
          (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ))) ![a, b, c] = _
  rw [ContinuousLinearMap.smulRight_apply, MixedSection.eval₀_apply,
    ContinuousMultilinearMap.constOfIsEmpty_apply, one_smul]
  change Tensor0SSpace.toModel (crossCorrectionModelFun (I := I) g₁ g₀ T₁ x) ![a, b, c] = _
  rw [crossCorrectionModelFun_toModel_apply, crossCorrectionTri_apply, connDiffField_apply]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.tail_cons,
    Matrix.head_cons]

/-! ### The section-level `g₀`-lowered Koszul identity

The `g₀`-lowered Koszul difference formula `connDiff_koszul_realize_g0`, lifted to the
`(0,3)`-section level: the *cancellation-clean linear part* (the symmetric realized
`covDerivRealizeEval`-combination of the `≤ 1`-jet of `h = ccTensorBilinSymm g₀ T₁`) is exactly
`2·loweredConnDiffSection + 2·crossCorrectionSection`.  This is the section identity on which the
iterated-jet bound `T1` rests: it splits the lowered connection difference into the clean linear part
(jet-bounded by the perturbation, `koszulCombSection_iteratedCovGrad_rfns_le`) minus the nonlinear
cross correction (jet-bounded with the fibre-small absorption, `crossCorrectionSection_iteratedCovGrad_rfns_le`). -/

/-- **The Koszul clean-linear-part `(0,3)`-section** of the `g₀`-lowered connection difference: the
algebraic combination `2·loweredConnDiffSection + 2·crossCorrectionSection`.  By the `g₀`-lowered
Koszul difference formula (`connDiff_koszul_realize_g0`) this combination is the
*connection-difference-free* symmetric realized `covDerivRealizeEval`-combination of the `≤ 1`-jet of
`h = ccTensorBilinSymm g₀ T₁` (the connection-difference dependence cancels), as verified at the
fibre level by `koszulCombSection_toModel_apply`. -/
def koszulCombSection (g₁ g₀ : SmoothRiemannianMetric I M)
    (T₁ : Integral.L2.SmoothCcTensor g₀ 0 2) :
    Integral.L2.SmoothCcTensor g₀ 0 3 :=
  (2 : ℝ) • loweredConnDiffSection (I := I) g₁ g₀ +
    (2 : ℝ) • crossCorrectionSection (I := I) g₁ g₀ T₁

set_option linter.unusedSectionVars false in
/-- **The fibre value of the Koszul clean-linear-part section is the realized
`covDerivRealizeEval`-combination** (the section-level `g₀`-lowered Koszul identity).  For the realize
idiom `g₁ = g₀ + ccTensorBilinSymm g₀ T₁`, the unit-eval fibre value of `koszulCombSection` on a
tangent triple is the connection-difference-free symmetric combination
`(∇⁰_a h)(b,c) + (∇⁰_b h)(a,c) − (∇⁰_c h)(a,b)` of the realized perturbation — exactly the right-hand
side of `connDiff_koszul_realize_g0`.  Proved by distributing the unit-eval over the algebraic
combination (`loweredConnDiffSection_toModel_apply`, `crossCorrectionSection_toModel_apply`) and the
pointwise Koszul formula. -/
theorem koszulCombSection_toModel_apply
    (g₁ g₀ : SmoothRiemannianMetric I M) (T₁ : Integral.L2.SmoothCcTensor g₀ 0 2)
    (hr : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T₁ y v w)
    (x : M) (a b c : TangentSpace I x) :
    Tensor0SSpace.toModel
        ((koszulCombSection (I := I) g₁ g₀ T₁).toSection x
          (ContinuousMultilinearMap.constOfIsEmpty ℝ
            (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ))) ![a, b, c] =
      covDerivRealizeEval (I := I) g₀ T₁ x a b c
        + covDerivRealizeEval (I := I) g₀ T₁ x b a c
        - covDerivRealizeEval (I := I) g₀ T₁ x c a b := by
  classical
  have hsec : (koszulCombSection (I := I) g₁ g₀ T₁).toSection =
      (2 : ℝ) • (loweredConnDiffSection (I := I) g₁ g₀).toSection +
        (2 : ℝ) • (crossCorrectionSection (I := I) g₁ g₀ T₁).toSection := by
    rw [koszulCombSection, Integral.L2.SmoothCcTensor.toSection_add,
      Integral.L2.SmoothCcTensor.toSection_smul, Integral.L2.SmoothCcTensor.toSection_smul]
  rw [hsec, ContMDiffSection.coe_add, Pi.add_apply, ContMDiffSection.coe_smul,
    ContMDiffSection.coe_smul, Pi.smul_apply, Pi.smul_apply,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smul_apply, Tensor0SSpace.toModel_add,
    Tensor0SSpace.toModel_smul, Tensor0SSpace.toModel_smul,
    ContinuousMultilinearMap.add_apply, ContinuousMultilinearMap.smul_apply,
    ContinuousMultilinearMap.smul_apply,
    loweredConnDiffSection_toModel_apply, crossCorrectionSection_toModel_apply]
  have hkos := connDiff_koszul_realize_g0 (I := I) g₁ g₀ T₁ hr x a b c
  rw [show smoothExtensionTangent (I := I) x b x = b from smoothExtensionTangent_eq (I := I) x b,
      show smoothExtensionTangent (I := I) x a x = a from smoothExtensionTangent_eq (I := I) x a]
    at hkos
  simp only [smul_eq_mul]
  linarith [hkos]

/-! ### T1: the iterated-covariant-jet bound (fibre-small ball regime)

The two genuine deep covariant-jet posits below — the *clean-linear-part jet bound* and the
*fibre-small-gated cross-correction jet bound* — are the strictly-smaller bricks of the route-(a)
differentiated-Koszul recursion; `T1` is their algebraic combination over the section-level Koszul
identity. -/

/-- **The Koszul clean-linear-part section as a symmetric combination of one realized covariant
gradient.**  Under the realize identity, `koszulCombSection g₁ g₀ T₁` equals the symmetric covariant
combination
```
R + permuteCcTensor (swap 0 1) R − permuteCcTensor c[0,2,1] R,   R := covGrad g₀ 0 2 (realizeSymm g₀ T₁),
```
where the slot-permutations realize the `(b,a,c)` and `(c,a,b)` readings of the realized
covariant-derivative evaluation.  Proved by unit-extensionality (`tensor0s_ext_unitZero`): the
unit-evaluated model form of `koszulCombSection` is the `covDerivRealizeEval` combination
(`koszulCombSection_toModel_apply`), and each summand's unit-evaluated model form is the corresponding
slot reading of `R`'s (`covGrad_realizeSymm_unitModel_eq_covDerivRealizeEval`, transported by the slot
reindexing `permuteCcTensor_unitModel`). -/
private theorem koszulCombSection_eq_permuted_covGrad_realizeSymm
    (g₁ g₀ : SmoothRiemannianMetric I M) (T₁ : Integral.L2.SmoothCcTensor g₀ 0 2)
    (hr : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T₁ y v w) :
    koszulCombSection (I := I) g₁ g₀ T₁ =
      Analysis.Parabolic.TensorSpectral.covGrad (I := I) (M := M) g₀ 0 2
          (realizeSymmCcTensor (I := I) g₀ T₁)
      + permuteCcTensor (I := I) g₀ (Equiv.swap 0 1)
          (Analysis.Parabolic.TensorSpectral.covGrad (I := I) (M := M) g₀ 0 2
            (realizeSymmCcTensor (I := I) g₀ T₁))
      - permuteCcTensor (I := I) g₀ c[(0 : Fin 3), 2, 1]
          (Analysis.Parabolic.TensorSpectral.covGrad (I := I) (M := M) g₀ 0 2
            (realizeSymmCcTensor (I := I) g₀ T₁)) := by
  classical
  set R := Analysis.Parabolic.TensorSpectral.covGrad (I := I) (M := M) g₀ 0 2
    (realizeSymmCcTensor (I := I) g₀ T₁) with hR
  apply Integral.L2.SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply tensor0s_ext_unitZero (I := I) (M := M) (s := 3)
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro v
  -- The unit `(0,0)`-tensor `unitZeroSec x` is the canonical `constOfIsEmpty 1`.
  have hunit : (unitZeroSec (I := I) (M := M) x : Tensor0SSpace 0 I x) =
      ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ) := rfl
  -- LHS unit-evaluated model form: the `covDerivRealizeEval` combination.
  have hL : Tensor0SSpace.toModel
      ((koszulCombSection (I := I) g₁ g₀ T₁).toSection x
        (unitZeroSec (I := I) (M := M) x)) v =
      covDerivRealizeEval (I := I) g₀ T₁ x (v 0) (v 1) (v 2)
        + covDerivRealizeEval (I := I) g₀ T₁ x (v 1) (v 0) (v 2)
        - covDerivRealizeEval (I := I) g₀ T₁ x (v 2) (v 0) (v 1) := by
    have h := koszulCombSection_toModel_apply (I := I) g₁ g₀ T₁ hr x (v 0) (v 1) (v 2)
    rw [hunit]
    have hvtuple : (![v 0, v 1, v 2] : Fin 3 → TangentSpace I x) = v := by
      funext i; fin_cases i <;> rfl
    rw [hvtuple] at h
    exact h
  -- The three summands' unit-evaluated model forms via the bridge + slot reindexings.
  have hRu : ∀ w : Fin 3 → TangentSpace I x, Analysis.Parabolic.TensorSpectral.unitModel (I := I) (M := M) g₀ 3 R x w =
      covDerivRealizeEval (I := I) g₀ T₁ x (w 0) (w 1) (w 2) := by
    intro w
    rw [hR, Analysis.Parabolic.TensorSpectral.unitModel]
    have h := covGrad_realizeSymm_unitModel_eq_covDerivRealizeEval (I := I) g₀ T₁ x
      (w 0) (w 1) (w 2)
    have hwtuple : (![w 0, w 1, w 2] : Fin 3 → TangentSpace I x) = w := by
      funext i; fin_cases i <;> rfl
    rw [hwtuple] at h
    exact h
  -- Read the RHS section value at the unit through additivity / the perm unit-models.
  rw [show (R + permuteCcTensor (I := I) g₀ (Equiv.swap 0 1) R
        - permuteCcTensor (I := I) g₀ c[(0 : Fin 3), 2, 1] R).toSection x
          (unitZeroSec (I := I) (M := M) x) =
      R.toSection x (unitZeroSec (I := I) (M := M) x)
        + (permuteCcTensor (I := I) g₀ (Equiv.swap 0 1) R).toSection x
            (unitZeroSec (I := I) (M := M) x)
        - (permuteCcTensor (I := I) g₀ c[(0 : Fin 3), 2, 1] R).toSection x
            (unitZeroSec (I := I) (M := M) x) from by
    rw [Integral.L2.SmoothCcTensor.toSection_sub, Integral.L2.SmoothCcTensor.toSection_add,
      ContMDiffSection.coe_sub, ContMDiffSection.coe_add, Pi.sub_apply, Pi.add_apply,
      ContinuousLinearMap.sub_apply, ContinuousLinearMap.add_apply]]
  simp only [Tensor0SSpace.toModel_sub, Tensor0SSpace.toModel_add,
    ContinuousMultilinearMap.sub_apply, ContinuousMultilinearMap.add_apply]
  rw [hL]
  -- The three RHS terms are the three slot readings of `R`'s unit-model.
  have hP1 := permuteCcTensor_unitModel (I := I) g₀ (Equiv.swap (0 : Fin 3) 1) R x
  have hP2 := permuteCcTensor_unitModel (I := I) g₀ c[(0 : Fin 3), 2, 1] R x
  have e0 : Tensor0SSpace.toModel (R.toSection x (unitZeroSec (I := I) (M := M) x)) v =
      covDerivRealizeEval (I := I) g₀ T₁ x (v 0) (v 1) (v 2) := by
    have hmod : Tensor0SSpace.toModel (R.toSection x (unitZeroSec (I := I) (M := M) x)) v =
        Analysis.Parabolic.TensorSpectral.unitModel (I := I) (M := M) g₀ 3 R x v := rfl
    rw [hmod]; exact hRu v
  have e1 : Tensor0SSpace.toModel
      ((permuteCcTensor (I := I) g₀ (Equiv.swap (0 : Fin 3) 1) R).toSection x
        (unitZeroSec (I := I) (M := M) x)) v =
      covDerivRealizeEval (I := I) g₀ T₁ x (v 1) (v 0) (v 2) := by
    have hmod : Tensor0SSpace.toModel
        ((permuteCcTensor (I := I) g₀ (Equiv.swap (0 : Fin 3) 1) R).toSection x
          (unitZeroSec (I := I) (M := M) x)) v =
        Analysis.Parabolic.TensorSpectral.unitModel (I := I) (M := M) g₀ 3
          (permuteCcTensor (I := I) g₀ (Equiv.swap (0 : Fin 3) 1) R) x v := rfl
    rw [hmod, hP1, ContinuousMultilinearMap.domDomCongr_apply]
    exact hRu _
  have e2 : Tensor0SSpace.toModel
      ((permuteCcTensor (I := I) g₀ c[(0 : Fin 3), 2, 1] R).toSection x
        (unitZeroSec (I := I) (M := M) x)) v =
      covDerivRealizeEval (I := I) g₀ T₁ x (v 2) (v 0) (v 1) := by
    have hmod : Tensor0SSpace.toModel
        ((permuteCcTensor (I := I) g₀ c[(0 : Fin 3), 2, 1] R).toSection x
          (unitZeroSec (I := I) (M := M) x)) v =
        Analysis.Parabolic.TensorSpectral.unitModel (I := I) (M := M) g₀ 3
          (permuteCcTensor (I := I) g₀ c[(0 : Fin 3), 2, 1] R) x v := rfl
    rw [hmod, hP2, ContinuousMultilinearMap.domDomCongr_apply]
    exact hRu _
  rw [e0, e1, e2]

/-- **(POSIT — the clean-linear-part jet brick.)**  The intrinsic squared fibre norm of the
order-`p` covariant gradient of the Koszul clean-linear-part section `koszulCombSection` is dominated
by the `≤ (p+1)`-jet of the perturbation `T₁`, with a constant uniform over the realize family.

This is the **realize-jet domination of the symmetric `covDerivRealizeEval`-combination** (proved at
the fibre level to be connection-difference-free, `koszulCombSection_toModel_apply`): the combination
is the `∇₀` of the realized `≤ 1`-jet of `h = ccTensorBilinSymm g₀ T₁`, so — exactly like the
realization map's no-derivative-gain bound `exists_riemannianFiberNormSq_iteratedCovGrad_realizeSymm_le_jetSum`
(which is unconditional, the combination being *linear* in `T₁`) — its order-`p` covariant jet is
controlled by `∑_{l ≤ p+1} rfns(∇^l T₁)` (one extra derivative from the `∇₀h` shifts the window from
`≤ p` to `≤ p+1`).  It is strictly smaller than `T1` (the **linear** part only, no connection
difference) and is **not** `T1` restated.

* **j = 0 collapse litmus.**  At `p = 0` this is `rfns(koszulCombSection)(x) ≤ C·∑_{l ≤ 1} rfns(∇^l T₁)(x)`,
  i.e. the `covDerivRealizeEval`-combination is bounded by the `≤ 1`-jet of `T₁` — exactly the realized
  `≤ 1`-jet terms `|covDerivRealizeEval g₀ T₁ x a b c| + …` of `connDiffField_g0_fibre_abs_bound`.
* **self-zero litmus.**  At `T₁ = 0`, `ccTensorBilinSymm g₀ 0 = 0`, so the combination vanishes and the
  bound is `0 ≤ 0`. -/
theorem koszulCombSection_iteratedCovGrad_rfns_le
    (g₀ : SmoothRiemannianMetric I M) (p : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (T₁ : Integral.L2.SmoothCcTensor g₀ 0 2) (g₁ : SmoothRiemannianMetric I M),
        (∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T₁ y v w) →
        ∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + p) x
              ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 p
                  (koszulCombSection (I := I) g₁ g₀ T₁)).toSection x) ≤
            C * ∑ l ∈ Finset.range (p + 1 + 1),
              riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
                ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l T₁).toSection x) := by
  classical
  obtain ⟨Crz, hCrz0, hCrz⟩ :=
    exists_riemannianFiberNormSq_iteratedCovGrad_realizeSymm_le_jetSum (I := I) g₀ (p + 1)
  refine ⟨18 * Crz, by positivity, ?_⟩
  intro T₁ g₁ hr x
  set R := Analysis.Parabolic.TensorSpectral.covGrad (I := I) (M := M) g₀ 0 2
    (realizeSymmCcTensor (I := I) g₀ T₁) with hR
  set S := ∑ l ∈ Finset.range (p + 1 + 1),
    riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
      ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l T₁).toSection x) with hS
  -- Abbreviate the order-`p` jet fibre norm of `R` and the two slot-permuted copies.
  set LR := riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + p) x
    ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 p R).toSection x) with hLR
  have hLR_nn : 0 ≤ LR := riemannianFiberNormSq_nonneg _ _ _ _ _
  -- The two permuted copies have the same order-`p` jet fibre norm as `R`.
  have hP1eq : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + p) x
      ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 p
        (permuteCcTensor (I := I) g₀ (Equiv.swap (0 : Fin 3) 1) R)).toSection x) = LR := by
    rw [hLR]; exact riemannianFiberNormSq_iteratedCovGrad_permuteCcTensor (I := I) g₀
      (Equiv.swap (0 : Fin 3) 1) R p x
  have hP2eq : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + p) x
      ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 p
        (permuteCcTensor (I := I) g₀ c[(0 : Fin 3), 2, 1] R)).toSection x) = LR := by
    rw [hLR]; exact riemannianFiberNormSq_iteratedCovGrad_permuteCcTensor (I := I) g₀
      c[(0 : Fin 3), 2, 1] R p x
  -- The order-`p` jet of `R = ∇₀ realizeSymm` is the order-`(p+1)` jet of `realizeSymm`.
  have hRcomm : LR = riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (p + 1)) x
      ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 (p + 1)
        (realizeSymmCcTensor (I := I) g₀ T₁)).toSection x) := by
    rw [hLR, hR]
    -- `∇^p (∇₀ realizeSymm) ≍ ∇^{p+1} realizeSymm` (front/back commutation), so rfns agree.
    exact riemannianFiberNormSq_toSection_heq (I := I) (M := M) g₀
      (by omega : (3 : ℕ) + p = 2 + (p + 1))
      (iteratedCovGrad_covGrad_comm_heq_local (I := I) (M := M) g₀ 2 p
        (realizeSymmCcTensor (I := I) g₀ T₁)) x
  have hRz : LR ≤ Crz * S := by
    rw [hRcomm]
    exact hCrz T₁ x
  -- Subadditivity over the section identity `koszulComb = R + P1 − P2`.
  rw [koszulCombSection_eq_permuted_covGrad_realizeSymm (I := I) g₁ g₀ T₁ hr]
  rw [← hR]
  rw [PDE.RicciFlow.iteratedCovGrad_sub, PDE.RicciFlow.iteratedCovGrad_add]
  rw [Integral.L2.SmoothCcTensor.toSection_sub, Integral.L2.SmoothCcTensor.toSection_add,
    ContMDiffSection.coe_sub, ContMDiffSection.coe_add, Pi.sub_apply, Pi.add_apply]
  refine le_trans (riemannianFiberNormSq_sub_le (I := I) (M := M) g₀ 0 (3 + p) x _ _) ?_
  rw [show ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 p R).toSection x +
        (PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 p
          (permuteCcTensor (I := I) g₀ (Equiv.swap (0 : Fin 3) 1) R)).toSection x) =
      ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 p R).toSection x +
        (PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 p
          (permuteCcTensor (I := I) g₀ (Equiv.swap (0 : Fin 3) 1) R)).toSection x) from rfl]
  have hadd := riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 0 (3 + p) x
    ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 p R).toSection x)
    ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 p
      (permuteCcTensor (I := I) g₀ (Equiv.swap (0 : Fin 3) 1) R)).toSection x)
  rw [hP1eq] at hadd
  rw [hP2eq]
  -- Combine: rfns(koszulComb) ≤ 2·(2·LR + 2·LR) + 2·LR = 18·LR ≤ 18·Crz·S.
  nlinarith [hadd, hLR_nn, hRz, hCrz0,
    Finset.sum_nonneg (fun l (_ : l ∈ Finset.range (p + 1 + 1)) =>
      riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + l) x
        ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l T₁).toSection x))]

end DeTurck
end PDE
end DifferentialGeometry
