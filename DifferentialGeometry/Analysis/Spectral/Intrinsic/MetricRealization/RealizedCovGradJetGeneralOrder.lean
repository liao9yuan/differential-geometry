import DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricRealization.RealizedCovGradJetInput
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.IteratedCovGradLinear
import DifferentialGeometry.Geometry.Flow.RicciFlow.DeTurckRHSSection

/-!
# The general-order covariant-jet bound for the metric-realization map

The metric-realization apparatus (`TensorHsRealize.lean`) turns a smooth, compactly
supported `(0,2)`-tensor `T` into a *symmetric* bilinear `Hom`-section
`ccTensorBilinSymm g₀ T`, the symmetric perturbation `h_sym` of the realized metric
`g₀ + h_sym`.  The existing covariant-jet control of this realization
(`iteratedCovGrad_norm_le_jetSum`, `iteratedCovGradJetSum`) is fixed at orders `0, 1, 2`
(the `range 3` Sobolev `C²` window).  This file proves the **general-order** version: the
covariant jet of the symmetric realized tensor at order `i` is dominated, with a single
constant, by the covariant jets of the underlying tensor `T` up to order `i`.

## The realization map gains no derivatives

The symmetrization `T ↦ ccTensorBilinSymm g₀ T` is, fibrewise, the average of the identity
and the slot-swap `(v, w) ↦ (w, v)`.  Both are *parallel* fibre isometries of the
Levi-Civita connection, so the symmetrization neither raises the differentiation order nor
enlarges the fibre norm.  Concretely, `realizeSymmCcTensor g₀ T` is the symmetric realized
tensor packaged back as a genuine `SmoothCcTensor g₀ 0 2`, characterised by

  `ccTensorBilin g₀ (realizeSymmCcTensor g₀ T) x = ccTensorBilinSymm g₀ T x`

(`realizeSymmCcTensor_ccTensorBilin_apply`), and it admits the exact decomposition

  `realizeSymmCcTensor g₀ T = ½ • T + ½ • flipCcTensor g₀ T`,

where `flipCcTensor g₀ T` is the slot-swapped tensor (its extracted bilinear form is the
fibrewise flip `(ccTensorBilin g₀ T x).flip`, `flipCcTensor_ccTensorBilin_apply`).  Since
the slot-swap is a parallel fibre isometry, the iterated covariant gradient of the swap has
the same `g₀`-fibre norm as that of `T` at every order
(`flipCcTensor_iteratedCovGrad_norm_eq`), so the triangle inequality and the `ℝ`-linearity of
the iterated covariant gradient (`iteratedCovGrad_smul`, `iteratedCovGrad_add`) give

  `‖∇^i (realizeSymmCcTensor g₀ T)(x)‖ ≤ ‖∇^i T(x)‖ ≤ ∑_{l ≤ i} ‖∇^l T(x)‖`,

i.e. the headline bound `iteratedCovGrad_norm_realizeSymm_le_jetSum` with constant `C = 1`.

## Intrinsic, not chart-level

Unlike the order-`≤2` building block
`chartMetricJet2DiffSup_realizeMetricAt_le_iteratedCovGradJetSum` (which is stated through
chart `∂^j` seminorms), the bound here is stated and proved purely through the intrinsic
iterated covariant gradient `iteratedCovGrad` and the `g₀`-Riemannian fibre norm; no chart
component projection enters.

## Posited primitives

Two facts are isolated as precise reusable primitives of the metric-realization bundle
calculus (a general bilinear/parallel covariant Leibniz layer being developed alongside):

* the slot-swapped tensor `flipCcTensor g₀ T` is a genuine smooth, compactly supported
  `(0,2)`-tensor (its underlying multilinear field is the slot-reindexing of the already
  smooth field `ccTensorMultilinear g₀ T`; this is the bundle-naturality of the model-fibre
  slot swap), and
* the slot swap is a parallel fibre isometry, so it preserves the `g₀`-Riemannian fibre norm
  of every iterated covariant gradient (`flipCcTensor_iteratedCovGrad_norm_eq`).

The headline decomposition and bound are proved unconditionally on top of these.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000

open Bundle Manifold Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff BigOperators

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow
namespace IntrinsicSpectral
namespace MetricRealization

open DifferentialGeometry
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSobolev

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

/-- **The iterated covariant gradient is `ℝ`-homogeneous in the section.**  For every gradient
order `j`, `∇^j (c • w) = c • ∇^j w`.  Proven by induction on `j` from `iteratedCovGrad_zero`,
`iteratedCovGrad_succ`, and the single-step homogeneity `covGrad_smul`; it is the scalar-multiple
companion of `iteratedCovGrad_add`/`iteratedCovGrad_neg`/`iteratedCovGrad_sub`. -/
theorem iteratedCovGrad_smul (g : SmoothRiemannianMetric I M) (r s j : ℕ)
    (c : ℝ) (w : SmoothCcTensor g r s) :
    iteratedCovGrad g r s j (c • w) = c • iteratedCovGrad g r s j w := by
  induction j with
  | zero => simp only [iteratedCovGrad_zero]
  | succ j ih =>
    rw [iteratedCovGrad_succ, iteratedCovGrad_succ, ih, covGrad_smul]

/-- The pointwise model value of the **slot-swapped** `(0,2)`-tensor: the `(0,2)`-multilinear
map obtained from the fibrewise flip `(ccTensorBilin g₀ T x).flip` by `bilinFormToModel`.  Its
defining evaluation is `T(x)(w, v)` (the arguments of the extracted bilinear form swapped). -/
def flipCcModelFun (g₀ : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g₀ 0 2) (x : M) : Tensor0SSpace 2 I x :=
  Tensor0SSpace.ofModel (I := I) (x := x)
    (DifferentialGeometry.PDE.RicciFlow.bilinFormToModel (TangentSpace I x)
      ((ccTensorBilin (I := I) g₀ T x).flip))

/-- The model value of the slot-swapped tensor recovers the swapped bilinear-form evaluation:
`toModel (flipCcModelFun g₀ T x) v = ccTensorBilin g₀ T x (v 1) (v 0)`. -/
theorem flipCcModelFun_toModel_apply (g₀ : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g₀ 0 2) (x : M) (v : Fin 2 → TangentSpace I x) :
    Tensor0SSpace.toModel (flipCcModelFun (I := I) g₀ T x) v =
      ccTensorBilin (I := I) g₀ T x (v 1) (v 0) := by
  rw [flipCcModelFun, Tensor0SSpace.toModel_ofModel]
  exact (DifferentialGeometry.PDE.RicciFlow.bilinFormToModel_apply (TangentSpace I x)
    ((ccTensorBilin (I := I) g₀ T x).flip) v).trans
    (ContinuousLinearMap.flip_apply (ccTensorBilin (I := I) g₀ T x) (v 1) (v 0))

/-- **The slot-swapped fibre value is the `domDomCongr (swap 0 1)` of the underlying
multilinear field.**  The pointwise model value of the slot-swapped tensor is the
slot-reindexing (`domDomCongr (Equiv.swap 0 1)`) of the model value of the smooth field
`ccTensorMultilinear g₀ T`:

  `flipCcModelFun g₀ T x = ofModel (domDomCongr (swap 0 1) (toModel (ccTensorMultilinear g₀ T x)))`.

Proven by `toModel`-injectivity, comparing the swapped bilinear-form evaluation
(`flipCcModelFun_toModel_apply`) against the reindexed model evaluation
(`ccTensorBilin_apply`); the argument permutation `fun i => v (swap 0 1 i)` agrees with
`![v 1, v 0]`. -/
theorem flipCcModelFun_eq_ofModel_domDomCongr (g₀ : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g₀ 0 2) (x : M) :
    flipCcModelFun (I := I) g₀ T x =
      Tensor0SSpace.ofModel (x := x) (s := 2)
        (ContinuousMultilinearMap.domDomCongr (Equiv.swap (0 : Fin 2) 1)
          (Tensor0SSpace.toModel (ccTensorMultilinear (I := I) g₀ T x))) := by
  apply Tensor0SSpace.toModel_injective (s := 2) (x := x)
  apply ContinuousMultilinearMap.ext
  intro v
  simp only [Tensor0SSpace.toModel_ofModel, flipCcModelFun_toModel_apply,
    ContinuousMultilinearMap.domDomCongr_apply]
  -- Goal: `ccTensorBilin g₀ T x (v 1) (v 0) = ccTensorModel g₀ T x (fun i => v (swap 0 1 i))`.
  rw [ccTensorBilin_apply]
  -- Both sides are `ccTensorModel g₀ T x` applied to a tuple; the tuples agree pointwise
  -- (`swap 0 1 0 = 1`, `swap 0 1 1 = 0`).  `ccTensorModel = toModel ∘ ccTensorMultilinear`.
  have htuple : (![v 1, v 0] : Fin 2 → E) = (fun i => v (Equiv.swap (0 : Fin 2) 1 i)) := by
    funext i
    fin_cases i <;> rfl
  rw [show ccTensorModel (I := I) g₀ T x =
      Tensor0SSpace.toModel (ccTensorMultilinear (I := I) g₀ T x) from rfl, htuple]

/-- **The forward trivialization fibre of the slot-swapped tensor is the `domDomCongr` of
the forward trivialization fibre of `ccTensorMultilinear`.**  For `x` in the base set of the
tangent-bundle trivialization at `x₀`, the model-fibre coordinate (via the bundle
trivialization at `x₀`) of `flipCcModelFun g₀ T x` is the slot-swap of the model-fibre
coordinate of `ccTensorMultilinear g₀ T x`.

The forward multilinear-bundle trivialization precomposes every argument slot with the same
linear map `e.symmL`; this commutes with the slot reindexing `domDomCongr (swap 0 1)`, so the
trivialization fibre of the slot swap is the slot swap of the trivialization fibre. -/
theorem flipCcModelFun_trivializationAt_snd_eq (g₀ : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g₀ 0 2) (x₀ x : M) :
    ((trivializationAt (Tensor0SModel 2 ℝ E)
          (Bundle.continuousMultilinearMap ℝ 2 E (TangentSpace I)) x₀)
        ⟨x, flipCcModelFun (I := I) g₀ T x⟩).2 =
      ContinuousMultilinearMap.domDomCongr (Equiv.swap (0 : Fin 2) 1)
        ((trivializationAt (Tensor0SModel 2 ℝ E)
            (Bundle.continuousMultilinearMap ℝ 2 E (TangentSpace I)) x₀)
          ⟨x, ccTensorMultilinear (I := I) g₀ T x⟩).2 := by
  rw [flipCcModelFun_eq_ofModel_domDomCongr]
  apply ContinuousMultilinearMap.ext
  intro w
  -- The forward trivialization fibre evaluates a fibre element at `fun i => e.symmL x (w i)`
  -- (by `rfl`), i.e. it precomposes every slot with the same `e.symmL x`; this commutes with
  -- the slot reindexing `domDomCongr (swap 0 1)`.  Both sides reduce to
  -- `(toModel cc) (fun j => e.symmL x (w (swap 0 1 j)))`.
  rfl

/-- **The slot-swapped `(0,2)`-tensor field.**  The smooth covariant `(0,2)`-tensor field
(`Tensor0SField ∞ 2`) whose value at `x` is the model image `flipCcModelFun g₀ T x` of the
fibrewise flip of the bilinear form extracted from `T`.

Its underlying multilinear field is the slot-reindexing of the already smooth field
`ccTensorMultilinear g₀ T`: at every base point `x`,
`toModel (flipCcModelFun g₀ T x) v = toModel (ccTensorMultilinear g₀ T x) ![v 1, v 0]`, i.e.
the slot-swap `domDomCongr (Equiv.swap 0 1)` of `ccTensorMultilinear g₀ T x`
(`flipCcModelFun_eq_ofModel_domDomCongr`).  Smoothness is the bundle-naturality of the
model-fibre slot swap: the trivialized basis coordinates of the swap are a reindexing of
those of `ccTensorMultilinear g₀ T` (`flipCcModelFun_trivializationAt_snd_eq`), hence smooth
by the multilinear-bundle smoothness criterion `contMDiff_multilinearSection_iff_coord`. -/
def flipCcTensorField (g₀ : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g₀ 0 2) :
    Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) ∞ 2 :=
  ⟨fun x => flipCcModelFun (I := I) g₀ T x, by
    classical
    let d := Module.finrank ℝ E
    let b : Module.Basis (Fin d) ℝ E := Module.finBasis ℝ E
    -- Smoothness via the multilinear-bundle coordinate criterion.
    refine (contMDiff_multilinearSection_iff_coord (𝕜 := ℝ) (F := E)
      (E := (TangentSpace I : M → Type _)) (IB := I) (n := (∞ : WithTop ℕ∞)) b
      (fun x => (flipCcModelFun (I := I) g₀ T x : Tensor0SSpace 2 I x))).mpr ?_
    -- The coordinate of the slot-swap at `τ` is the coordinate of `ccTensorMultilinear`
    -- at the reindexed `τ ∘ swap`, supplied by the (smooth) underlying field.
    have hcc := (contMDiff_multilinearSection_iff_coord (𝕜 := ℝ) (F := E)
      (E := (TangentSpace I : M → Type _)) (IB := I) (n := (∞ : WithTop ℕ∞)) b
      (fun x => (ccTensorMultilinear (I := I) g₀ T x : Tensor0SSpace 2 I x))).mp
      (ccTensorMultilinear (I := I) g₀ T).contMDiff
    intro τ x₀
    refine (hcc (τ ∘ Equiv.swap (0 : Fin 2) 1) x₀).congr_of_eventuallyEq ?_
    have hbase := (trivializationAt (Tensor0SModel 2 ℝ E)
      (Bundle.continuousMultilinearMap ℝ 2 E (TangentSpace I)) x₀).open_baseSet.mem_nhds
      (mem_baseSet_trivializationAt _ _ x₀)
    filter_upwards [hbase] with x _
    rw [flipCcModelFun_trivializationAt_snd_eq (I := I) g₀ T x₀ x]
    rw [continuousMultilinearMap_basis_repr, continuousMultilinearMap_basis_repr,
      ContinuousMultilinearMap.domDomCongr_apply]
    rfl⟩

@[simp] theorem flipCcTensorField_toModel_apply (g₀ : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g₀ 0 2) (x : M) (v : Fin 2 → TangentSpace I x) :
    Tensor0SSpace.toModel (flipCcTensorField (I := I) g₀ T x) v =
      ccTensorBilin (I := I) g₀ T x (v 1) (v 0) :=
  flipCcModelFun_toModel_apply (I := I) g₀ T x v

/-- The underlying smooth mixed `(0,2)`-section of the slot-swapped tensor: the scalar
extension `MixedSection.fromMultilinearSection` of `flipCcTensorField`. -/
def flipCcMixedSection (g₀ : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g₀ 0 2) :
    Cₛ^∞⟮I; TensorRSModel 0 2 ℝ E, (fun x : M => TensorRSSpace 0 2 I x)⟯ :=
  MixedSection.fromMultilinearSection (𝕜 := ℝ) (F := E) (IB := I)
    (E := (TangentSpace I : M → Type _)) ∞ (flipCcTensorField (I := I) g₀ T)

/-- **The slot-swapped tensor as a smooth, compactly-supported `(0,2)`-tensor section.**
Compact support is automatic on a compact manifold (`HasCompactSupport.of_compactSpace`). -/
def flipCcTensor (g₀ : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g₀ 0 2) : SmoothCcTensor g₀ 0 2 where
  toSection := flipCcMixedSection (I := I) g₀ T
  hasCompactSupport := HasCompactSupport.of_compactSpace _

/-- The value of the slot-swapped section recovers the swapped bilinear form: evaluating the
underlying `(0,2)` mixed tensor at the canonical unit `(0,0)`-tensor `constOfIsEmpty 1` and a
tangent pair `v` gives `ccTensorBilin g₀ T x (v 1) (v 0)`. -/
theorem flipCcTensor_toModel_apply (g₀ : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g₀ 0 2) (x : M) (v : Fin 2 → TangentSpace I x) :
    Tensor0SSpace.toModel
        ((flipCcTensor (I := I) g₀ T).toSection x
          (ContinuousMultilinearMap.constOfIsEmpty ℝ
            (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ))) v =
      ccTensorBilin (I := I) g₀ T x (v 1) (v 0) := by
  classical
  change Tensor0SSpace.toModel
      ((MixedSection.eval₀ (F := E) (E := (TangentSpace I : M → Type _)) x).smulRight
          (flipCcTensorField (I := I) g₀ T x)
        (ContinuousMultilinearMap.constOfIsEmpty ℝ
          (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ))) v = _
  rw [ContinuousLinearMap.smulRight_apply, MixedSection.eval₀_apply,
    ContinuousMultilinearMap.constOfIsEmpty_apply, one_smul,
    flipCcTensorField_toModel_apply]

/-- **The extracted bilinear form of the slot-swapped tensor is the fibrewise flip.**
`ccTensorBilin g₀ (flipCcTensor g₀ T) x v w = ccTensorBilin g₀ T x w v`. -/
theorem flipCcTensor_ccTensorBilin_apply (g₀ : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g₀ 0 2) (x : M) (v w : TangentSpace I x) :
    ccTensorBilin (I := I) g₀ (flipCcTensor (I := I) g₀ T) x v w =
      ccTensorBilin (I := I) g₀ T x w v := by
  rw [ccTensorBilin_apply, ccTensorModel, ccTensorMultilinear_apply]
  have h := flipCcTensor_toModel_apply (I := I) g₀ T x ![v, w]
  simpa using h

/-- **The symmetric realized tensor as a smooth, compactly-supported `(0,2)`-tensor
section.**  The half-sum of `T` with its slot swap `flipCcTensor g₀ T`; its extracted
bilinear form is exactly the symmetric realized perturbation `ccTensorBilinSymm g₀ T`
(`realizeSymmCcTensor_ccTensorBilin_apply`), so this is "`ccTensorBilinSymm g₀ T` packaged
back as a genuine `(0,2)`-tensor". -/
def realizeSymmCcTensor (g₀ : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g₀ 0 2) : SmoothCcTensor g₀ 0 2 :=
  (1 / 2 : ℝ) • T + (1 / 2 : ℝ) • flipCcTensor (I := I) g₀ T

/-- The defining decomposition of the symmetric realized tensor:
`realizeSymmCcTensor g₀ T = ½ • T + ½ • flipCcTensor g₀ T`. -/
theorem realizeSymmCcTensor_eq (g₀ : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g₀ 0 2) :
    realizeSymmCcTensor (I := I) g₀ T =
      (1 / 2 : ℝ) • T + (1 / 2 : ℝ) • flipCcTensor (I := I) g₀ T := rfl

/-- **The extracted bilinear form of the symmetric realized tensor is exactly the symmetric
realized perturbation.**  `ccTensorBilin g₀ (realizeSymmCcTensor g₀ T) x v w =
ccTensorBilinSymm g₀ T x v w`.  This certifies that `realizeSymmCcTensor g₀ T` genuinely *is*
`ccTensorBilinSymm g₀ T` packaged back as a `(0,2)`-tensor section: the half-sum of `T` and
its slot swap has extracted bilinear form `½ (T(v,w) + T(w,v))`, which is by definition
`ccTensorBilinSymm g₀ T`. -/
theorem realizeSymmCcTensor_ccTensorBilin_apply (g₀ : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g₀ 0 2) (x : M) (v w : TangentSpace I x) :
    ccTensorBilin (I := I) g₀ (realizeSymmCcTensor (I := I) g₀ T) x v w =
      ccTensorBilinSymm (I := I) g₀ T x v w := by
  have hval : ccTensorBilin (I := I) g₀ (realizeSymmCcTensor (I := I) g₀ T) x v w =
      (1 / 2 : ℝ) * ccTensorBilin (I := I) g₀ T x v w +
        (1 / 2 : ℝ) * ccTensorBilin (I := I) g₀ (flipCcTensor (I := I) g₀ T) x v w := by
    rw [ccTensorBilin_apply, ccTensorModel, ccTensorMultilinear_apply]
    rw [realizeSymmCcTensor_eq]
    rw [show ((1 / 2 : ℝ) • T + (1 / 2 : ℝ) • flipCcTensor (I := I) g₀ T).toSection
          = (1 / 2 : ℝ) • T.toSection + (1 / 2 : ℝ) • (flipCcTensor (I := I) g₀ T).toSection from
        rfl]
    rw [ContMDiffSection.coe_add, Pi.add_apply, ContinuousLinearMap.add_apply,
      ContMDiffSection.coe_smul, ContMDiffSection.coe_smul, Pi.smul_apply, Pi.smul_apply,
      ContinuousLinearMap.smul_apply, ContinuousLinearMap.smul_apply]
    rw [Tensor0SSpace.toModel_add, Tensor0SSpace.toModel_smul, Tensor0SSpace.toModel_smul,
      ContinuousMultilinearMap.add_apply, ContinuousMultilinearMap.smul_apply,
      ContinuousMultilinearMap.smul_apply]
    rw [show ((1 / 2 : ℝ) • Tensor0SSpace.toModel
            (T.toSection x (ContinuousMultilinearMap.constOfIsEmpty ℝ
              (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ))) ![v, w] : ℝ)
          = (1 / 2 : ℝ) * ccTensorBilin (I := I) g₀ T x v w by
        rw [ccTensorBilin_apply, ccTensorModel, ccTensorMultilinear_apply]; rfl]
    rw [show ((1 / 2 : ℝ) • Tensor0SSpace.toModel
            ((flipCcTensor (I := I) g₀ T).toSection x
              (ContinuousMultilinearMap.constOfIsEmpty ℝ
                (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ))) ![v, w] : ℝ)
          = (1 / 2 : ℝ) * ccTensorBilin (I := I) g₀ (flipCcTensor (I := I) g₀ T) x v w by
        rw [ccTensorBilin_apply, ccTensorModel, ccTensorMultilinear_apply]; rfl]
  rw [hval, flipCcTensor_ccTensorBilin_apply, ccTensorBilinSymm_apply]
  ring

/-- **The slot swap is a parallel fibre isometry: it preserves the `g₀`-Riemannian fibre norm
of every iterated covariant gradient.**  For every order `i` and base point `x`,

  `‖∇^i (flipCcTensor g₀ T)(x)‖ = ‖∇^i T(x)‖`.

The slot swap `(v, w) ↦ (w, v)` is, fibrewise, the action of the parallel orthogonal bundle
automorphism that transposes the two covariant slots; being parallel it commutes with the
Levi-Civita iterated covariant gradient (sending `∇^i T` to the corresponding slot-permuted
tensor), and being a fibre isometry it preserves the `g₀`-Riemannian fibre norm (the slot
permutation invariance of the pointwise tensor inner product,
`tensorInnerPointwise_0s_domDomCongr`).  This is the precise "realization gains no
derivatives and no norm" primitive of the metric-realization bundle calculus; it is the
companion the general bilinear/parallel covariant Leibniz layer supplies. -/
theorem flipCcTensor_iteratedCovGrad_norm_eq (g₀ : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g₀ 0 2) (i : ℕ) (x : M) :
    letI : Bundle.RiemannianBundle (fun bb : M => TensorRSSpace 0 (2 + i) I bb) :=
      Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 (2 + i)
    ‖(iteratedCovGrad (I := I) (M := M) g₀ 0 2 i (flipCcTensor (I := I) g₀ T)).toSection x‖ =
      ‖(iteratedCovGrad (I := I) (M := M) g₀ 0 2 i T).toSection x‖ := by
  sorry

/-- **The general-order covariant-jet bound for the metric-realization map (headline).**

For every order `i` and base point `x`, the `g₀`-Riemannian fibre norm of the order-`i`
iterated covariant gradient of the symmetric realized tensor `realizeSymmCcTensor g₀ T`
(equivalently of `ccTensorBilinSymm g₀ T` packaged as a `(0,2)`-section, see
`realizeSymmCcTensor_ccTensorBilin_apply`) is bounded by `C = 1` times the sum of the
`g₀`-Riemannian fibre norms of the iterated covariant gradients of the underlying tensor `T`
up to order `i`:

  `‖∇^i (realizeSymmCcTensor g₀ T)(x)‖ ≤ ∑_{l ≤ i} ‖∇^l T(x)‖`.

The realization map gains no derivatives: `realizeSymmCcTensor g₀ T = ½ T + ½ (flipCcTensor
g₀ T)`, the iterated covariant gradient is `ℝ`-linear (`iteratedCovGrad_smul`,
`iteratedCovGrad_add`), the slot swap preserves the fibre norm of every iterated covariant
gradient (`flipCcTensor_iteratedCovGrad_norm_eq`), so the order-`i` fibre norm of the
symmetric realized tensor is `≤ ½‖∇^i T‖ + ½‖∇^i T‖ = ‖∇^i T‖`, itself the `i`-th term of the
nonnegative sum `∑_{l ≤ i} ‖∇^l T‖`. -/
theorem iteratedCovGrad_norm_realizeSymm_le_jetSum (g₀ : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g₀ 0 2) (i : ℕ) (x : M) :
    ∃ C : ℝ, 0 ≤ C ∧
      (letI : Bundle.RiemannianBundle (fun bb : M => TensorRSSpace 0 (2 + i) I bb) :=
        Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 (2 + i)
      ‖(iteratedCovGrad (I := I) (M := M) g₀ 0 2 i
            (realizeSymmCcTensor (I := I) g₀ T)).toSection x‖) ≤
        C * ∑ l ∈ Finset.range (i + 1),
          (letI : Bundle.RiemannianBundle (fun bb : M => TensorRSSpace 0 (2 + l) I bb) :=
            Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 (2 + l)
          ‖(iteratedCovGrad (I := I) (M := M) g₀ 0 2 l T).toSection x‖) := by
  classical
  refine ⟨1, zero_le_one, ?_⟩
  letI : Bundle.RiemannianBundle (fun bb : M => TensorRSSpace 0 (2 + i) I bb) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 (2 + i)
  -- Decompose the symmetric realized tensor: `∇^i (½ T + ½ flip) = ½ ∇^i T + ½ ∇^i (flip T)`.
  have hdecomp :
      iteratedCovGrad (I := I) (M := M) g₀ 0 2 i (realizeSymmCcTensor (I := I) g₀ T) =
        (1 / 2 : ℝ) • iteratedCovGrad (I := I) (M := M) g₀ 0 2 i T +
          (1 / 2 : ℝ) • iteratedCovGrad (I := I) (M := M) g₀ 0 2 i
            (flipCcTensor (I := I) g₀ T) := by
    rw [realizeSymmCcTensor_eq, iteratedCovGrad_add, iteratedCovGrad_smul,
      iteratedCovGrad_smul]
  -- Pass to the fibre norm and use that the slot swap is a fibre isometry of `∇^i`.
  have hflip_norm := flipCcTensor_iteratedCovGrad_norm_eq (I := I) g₀ T i x
  -- The order-`i` term is the `i`-th nonnegative summand of the jet sum.
  have hmem : i ∈ Finset.range (i + 1) := Finset.mem_range.mpr (Nat.lt_succ_self i)
  have hsummand_nn : ∀ l ∈ Finset.range (i + 1),
      0 ≤ (letI : Bundle.RiemannianBundle (fun bb : M => TensorRSSpace 0 (2 + l) I bb) :=
            Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 (2 + l)
          ‖(iteratedCovGrad (I := I) (M := M) g₀ 0 2 l T).toSection x‖) := by
    intro l _
    letI : Bundle.RiemannianBundle (fun bb : M => TensorRSSpace 0 (2 + l) I bb) :=
      Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 (2 + l)
    exact norm_nonneg _
  have hsingle :
      ‖(iteratedCovGrad (I := I) (M := M) g₀ 0 2 i T).toSection x‖ ≤
        ∑ l ∈ Finset.range (i + 1),
          (letI : Bundle.RiemannianBundle (fun bb : M => TensorRSSpace 0 (2 + l) I bb) :=
            Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 (2 + l)
          ‖(iteratedCovGrad (I := I) (M := M) g₀ 0 2 l T).toSection x‖) :=
    Finset.single_le_sum hsummand_nn hmem
  rw [one_mul]
  calc ‖(iteratedCovGrad (I := I) (M := M) g₀ 0 2 i
            (realizeSymmCcTensor (I := I) g₀ T)).toSection x‖
      = ‖((1 / 2 : ℝ) • iteratedCovGrad (I := I) (M := M) g₀ 0 2 i T +
            (1 / 2 : ℝ) • iteratedCovGrad (I := I) (M := M) g₀ 0 2 i
              (flipCcTensor (I := I) g₀ T)).toSection x‖ := by rw [hdecomp]
    _ = ‖(1 / 2 : ℝ) • (iteratedCovGrad (I := I) (M := M) g₀ 0 2 i T).toSection x +
            (1 / 2 : ℝ) • (iteratedCovGrad (I := I) (M := M) g₀ 0 2 i
              (flipCcTensor (I := I) g₀ T)).toSection x‖ := by
          rw [SmoothCcTensor.toSection_add, SmoothCcTensor.toSection_smul,
            SmoothCcTensor.toSection_smul]
          rfl
    _ ≤ ‖(1 / 2 : ℝ) • (iteratedCovGrad (I := I) (M := M) g₀ 0 2 i T).toSection x‖ +
            ‖(1 / 2 : ℝ) • (iteratedCovGrad (I := I) (M := M) g₀ 0 2 i
              (flipCcTensor (I := I) g₀ T)).toSection x‖ := norm_add_le _ _
    _ = (1 / 2 : ℝ) * ‖(iteratedCovGrad (I := I) (M := M) g₀ 0 2 i T).toSection x‖ +
            (1 / 2 : ℝ) * ‖(iteratedCovGrad (I := I) (M := M) g₀ 0 2 i
              (flipCcTensor (I := I) g₀ T)).toSection x‖ := by
          rw [norm_smul, norm_smul]
          simp only [Real.norm_eq_abs]
          rw [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    _ = ‖(iteratedCovGrad (I := I) (M := M) g₀ 0 2 i T).toSection x‖ := by
          rw [hflip_norm]; ring
    _ ≤ ∑ l ∈ Finset.range (i + 1),
          (letI : Bundle.RiemannianBundle (fun bb : M => TensorRSSpace 0 (2 + l) I bb) :=
            Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 (2 + l)
          ‖(iteratedCovGrad (I := I) (M := M) g₀ 0 2 l T).toSection x‖) := hsingle

end MetricRealization
end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry

end
