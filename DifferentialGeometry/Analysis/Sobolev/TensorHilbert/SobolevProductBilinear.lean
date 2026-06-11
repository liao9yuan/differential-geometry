import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.JetReadoffContDiff
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.BanachAlgebraSmoothness

/-! # The bounded bilinear product on chart-Sobolev Hilbert completions

A bilinear pointwise product (or contraction) `prod` of smooth compactly-carried tensor sections
— supplied together with the **supercritical Banach-algebra estimate** `‖(prod S T).toHs s'‖ ≤
C · ‖S.toHs s‖ · ‖T.toHs s‖` on the dense smooth subspace — extends to a genuinely
**bounded bilinear map between the intrinsic chart-Sobolev Hilbert completions**
`H^s × H^s → H^{s'}`, with the factoring law
`B (S.toHs s) (T.toHs s) = (prod S T).toHs s'` recovered on the dense range.

This is the reusable density-completion bedrock the chart-Sobolev rational/Nemytskii smoothness
tower needs: `BanachAlgebraSmoothness.contDiffOn_bilinDiag` turns a bounded bilinear map (here
exposed via `ContinuousLinearMap.isBoundedBilinearMap` of the curried CLM
`productBilinCLM`) into `ContDiffOn ℝ ∞` of the diagonal `x ↦ B (f x, h x)` — the product bricks
of a chart-rational functional.  The deep DeTurck retag node
`exists_deTurckRHSRetag_toHs_contDiffOn_ball` consumes exactly this object: products of
realized-metric jet entries read as `ContDiffOn` maps `H^q → H^a`.

## Construction (curry, then extend linearly in each slot)

A bilinear map is not uniformly continuous, so `UniformSpace.Completion.extension₂` does not apply
directly.  Instead we curry and extend the resulting *linear* maps along the dense completion
embedding, twice (`LinearMap.extendOfNorm`, the operator-norm-controlled dense extension already
used for the order-dropping inclusion CLM in `JetReadoffContDiff`):

* `productSlot2CLM S` — for a fixed smooth `S`, the dense extension of `T ↦ (prod S T).toHs s'`,
  a continuous linear map `H^s → H^{s'}` of operator norm `≤ C · ‖S.toHs s‖`;
* `productBilinCLM` — the dense extension of `S ↦ productSlot2CLM S` (linear into the Banach space
  of continuous linear maps `H^s →L H^{s'}`), a continuous linear map
  `H^s →L[ℝ] (H^s →L[ℝ] H^{s'})`.

The outer slot's additivity / homogeneity are recovered by density (both sides agree on smooth
sections, where the factoring law pins them).  The final factoring law
`productBilinCLM (S.toHs s) (T.toHs s) = (prod S T).toHs s'` follows from the two `extendOfNorm`
defining identities on the dense range.

## What is — and is not — proven here

The supercritical dense estimate itself (the `bound` hypothesis: `‖fg‖_{H^{s'}} ≲ ‖f‖_{H^s}‖g‖_{H^s}`
for `2s > dim M + …`, the classical Sobolev Banach-algebra property) is **taken as an honest
quantitative hypothesis**, not packaged: it is a norm inequality on the dense smooth subspace, while
the conclusion is the existence and the analytic properties (continuity, bilinearity, the factoring
law) of the bilinear extension to the completion.  Library-wide the only realizations of that dense
estimate currently route through the deferred covariant interpolation / Moser-tame product inputs;
this file supplies the sorry-free machinery that turns *any* such bound into the consumer's bounded
bilinear object.  Sorry-free. -/

noncomputable section

open Bundle
open scoped Manifold ContDiff NNReal ENNReal Topology BigOperators

set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 3200000
set_option maxHeartbeats 1600000

namespace DifferentialGeometry.Analysis.Sobolev.TensorHilbert

open DifferentialGeometry
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSobolev

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]
  (g : SmoothRiemannianMetric I M)
  {r₁ s₁ r₂ s₂ r₃ s₃ : ℕ} (s s' : ℕ)
  (prod : Integral.L2.SmoothCcTensor g r₁ s₁ →ₗ[ℝ]
    Integral.L2.SmoothCcTensor g r₂ s₂ →ₗ[ℝ] Integral.L2.SmoothCcTensor g r₃ s₃)

/-- `ℝ`-scalar multiplication on the operator space `H^s →L H^{s'}` is norm-bounded
(`IsBoundedSMul`), derived canonically from the operator-norm submultiplicativity
`ContinuousLinearMap.opNorm_smul_le`.  Recorded as a local instance because `NormedSpace.toIsBoundedSMul`
does not auto-chain through the operator norm here; `LinearMap.extendOfNorm` needs it on its CLM
codomain `F = H^s →L H^{s'}` (the first-slot extension's target). -/
local instance instIsBoundedSMulSlot2CLM :
    IsBoundedSMul ℝ (TensorPouSobolevHilbert (I := I) (M := M) g r₂ s₂ s →L[ℝ]
      TensorPouSobolevHilbert (I := I) (M := M) g r₃ s₃ s') :=
  IsBoundedSMul.of_norm_smul_le (fun c f => ContinuousLinearMap.opNorm_smul_le c f)

/-- The supercritical Banach-algebra (dense product) estimate for `prod` at orders `(s, s')` with
constant `C`: `‖(prod S T).toHs s'‖ ≤ C · ‖S.toHs s‖ · ‖T.toHs s‖` for all smooth sections.  This is
the honest quantitative hypothesis the bilinear extension is built on (a norm inequality on the
dense smooth subspace, distinct from the existence/continuity conclusion). -/
def SobolevProductBound (C : ℝ) : Prop :=
  ∀ (S : Integral.L2.SmoothCcTensor g r₁ s₁) (T : Integral.L2.SmoothCcTensor g r₂ s₂),
    ‖SmoothCcTensor.toHs (g := g) (r := r₃) (s := s₃) s' (prod S T)‖ ≤
      C * (‖SmoothCcTensor.toHs (g := g) (r := r₁) (s := s₁) s S‖ *
        ‖SmoothCcTensor.toHs (g := g) (r := r₂) (s := s₂) s T‖)

/-- The slot-2 linear map `T ↦ (prod S T).toHs s'` for a fixed smooth `S`, as an `ℝ`-linear map
`SmoothCcTensor g r₂ s₂ →ₗ[ℝ] H^{s'}`: the post-composition of the bilinear `prod` (applied to `S`)
with the order-`s'` completion embedding `toHsLinearMap`. -/
def productSlot2Linear (S : Integral.L2.SmoothCcTensor g r₁ s₁) :
    Integral.L2.SmoothCcTensor g r₂ s₂ →ₗ[ℝ]
      TensorPouSobolevHilbert (I := I) (M := M) g r₃ s₃ s' :=
  (toHsLinearMap (I := I) g r₃ s₃ s').comp (prod S)

@[simp] theorem productSlot2Linear_apply (S : Integral.L2.SmoothCcTensor g r₁ s₁)
    (T : Integral.L2.SmoothCcTensor g r₂ s₂) :
    productSlot2Linear (I := I) g s' prod S T =
      SmoothCcTensor.toHs (g := g) (r := r₃) (s := s₃) s' (prod S T) := rfl

/-- The per-`S` slot-2 norm domination `‖(prod S T).toHs s'‖ ≤ (C · ‖S.toHs s‖) · ‖T.toHs s‖`,
in the exact `‖f T‖ ≤ K · ‖e T‖` shape `LinearMap.extendOfNorm` consumes (here `K = C · ‖S.toHs s‖`,
`e = toHsLinearMap … s`). -/
theorem productSlot2Linear_norm_le {C : ℝ} (hbound : SobolevProductBound (I := I) g s s' prod C)
    (S : Integral.L2.SmoothCcTensor g r₁ s₁) (T : Integral.L2.SmoothCcTensor g r₂ s₂) :
    ‖productSlot2Linear (I := I) g s' prod S T‖ ≤
      (C * ‖SmoothCcTensor.toHs (g := g) (r := r₁) (s := s₁) s S‖) *
        ‖toHsLinearMap (I := I) g r₂ s₂ s T‖ := by
  rw [productSlot2Linear_apply, toHsLinearMap_apply, mul_assoc]
  exact hbound S T

/-- The slot-2 continuous linear map `H^s → H^{s'}` for a fixed smooth `S`: the dense extension of
`productSlot2Linear S` along the dense order-`s` chart-Sobolev embedding `toHsLinearMap … s`. -/
def productSlot2CLM (S : Integral.L2.SmoothCcTensor g r₁ s₁) :
    TensorPouSobolevHilbert (I := I) (M := M) g r₂ s₂ s →L[ℝ]
      TensorPouSobolevHilbert (I := I) (M := M) g r₃ s₃ s' :=
  LinearMap.extendOfNorm (productSlot2Linear (I := I) g s' prod S)
    (toHsLinearMap (I := I) g r₂ s₂ s)

/-- The defining identity of the slot-2 CLM on the dense range:
`productSlot2CLM S (T.toHs s) = (prod S T).toHs s'`. -/
@[simp] theorem productSlot2CLM_apply_toHs {C : ℝ}
    (hbound : SobolevProductBound (I := I) g s s' prod C)
    (S : Integral.L2.SmoothCcTensor g r₁ s₁) (T : Integral.L2.SmoothCcTensor g r₂ s₂) :
    productSlot2CLM (I := I) g s s' prod S
        (SmoothCcTensor.toHs (g := g) (r := r₂) (s := s₂) s T)
      = SmoothCcTensor.toHs (g := g) (r := r₃) (s := s₃) s' (prod S T) := by
  have hext := LinearMap.extendOfNorm_eq
    (f := productSlot2Linear (I := I) g s' prod S)
    (e := toHsLinearMap (I := I) g r₂ s₂ s)
    (smoothCcTensor_denseRange_toHs (I := I) g r₂ s₂ s)
    ⟨C * ‖SmoothCcTensor.toHs (g := g) (r := r₁) (s := s₁) s S‖,
      productSlot2Linear_norm_le (I := I) g s s' prod hbound S⟩ T
  rw [toHsLinearMap_apply] at hext
  rw [productSlot2CLM, hext, productSlot2Linear_apply]

/-- The slot-2 CLM has operator norm `≤ C · ‖S.toHs s‖`: the `extendOfNorm` operator-norm bound from
the per-`S` domination `productSlot2Linear_norm_le`. -/
theorem productSlot2CLM_opNorm_le {C : ℝ} (hbound : SobolevProductBound (I := I) g s s' prod C)
    (hC : 0 ≤ C) (S : Integral.L2.SmoothCcTensor g r₁ s₁) :
    ‖productSlot2CLM (I := I) g s s' prod S‖ ≤
      C * ‖SmoothCcTensor.toHs (g := g) (r := r₁) (s := s₁) s S‖ := by
  refine LinearMap.opNorm_extendOfNorm_le
    (smoothCcTensor_denseRange_toHs (I := I) g r₂ s₂ s)
    (mul_nonneg hC (norm_nonneg _)) ?_
  intro T
  exact productSlot2Linear_norm_le (I := I) g s s' prod hbound S T

/-- The slot-2 CLM is additive in the (smooth) first slot: both sides agree on the dense range of
the order-`s` embedding (where the factoring law pins each to `(prod · T).toHs s'`), hence equal by
density.  The bilinearity of `prod` is what makes the dense-range values add. -/
theorem productSlot2CLM_add {C : ℝ} (hbound : SobolevProductBound (I := I) g s s' prod C)
    (S₁ S₂ : Integral.L2.SmoothCcTensor g r₁ s₁) :
    productSlot2CLM (I := I) g s s' prod (S₁ + S₂)
      = productSlot2CLM (I := I) g s s' prod S₁ + productSlot2CLM (I := I) g s s' prod S₂ := by
  apply ContinuousLinearMap.ext
  intro x
  refine smoothCcTensor_denseRange_toHs (I := I) g r₂ s₂ s |>.induction_on x ?_ ?_
  · exact isClosed_eq (by fun_prop) (by fun_prop)
  · intro T
    rw [ContinuousLinearMap.add_apply,
      productSlot2CLM_apply_toHs (I := I) g s s' prod hbound,
      productSlot2CLM_apply_toHs (I := I) g s s' prod hbound,
      productSlot2CLM_apply_toHs (I := I) g s s' prod hbound, map_add, LinearMap.add_apply,
      SmoothCcTensor.toHs_add (I := I) (M := M) (g := g) s' (prod S₁ T) (prod S₂ T)]

/-- The slot-2 CLM is homogeneous in the (smooth) first slot, by the same density argument. -/
theorem productSlot2CLM_smul {C : ℝ} (hbound : SobolevProductBound (I := I) g s s' prod C)
    (c : ℝ) (S : Integral.L2.SmoothCcTensor g r₁ s₁) :
    productSlot2CLM (I := I) g s s' prod (c • S)
      = c • productSlot2CLM (I := I) g s s' prod S := by
  apply ContinuousLinearMap.ext
  intro x
  refine smoothCcTensor_denseRange_toHs (I := I) g r₂ s₂ s |>.induction_on x ?_ ?_
  · exact isClosed_eq (by fun_prop) (by fun_prop)
  · intro T
    rw [ContinuousLinearMap.smul_apply,
      productSlot2CLM_apply_toHs (I := I) g s s' prod hbound,
      productSlot2CLM_apply_toHs (I := I) g s s' prod hbound, map_smul, LinearMap.smul_apply,
      DifferentialGeometry.Analysis.Parabolic.TensorSpectral.SobolevScale.smoothCcTensor_toHs_smul
        (I := I) (M := M) (g := g) s' c (prod S T)]

/-- The first-slot linear map `S ↦ productSlot2CLM S` into the Banach space of continuous linear
maps `H^s →L[ℝ] H^{s'}`, as an `ℝ`-linear map from smooth sections.  Additivity / homogeneity are
the density lemmas `productSlot2CLM_add` / `productSlot2CLM_smul`. -/
def productSlot1Linear {C : ℝ} (hbound : SobolevProductBound (I := I) g s s' prod C) :
    Integral.L2.SmoothCcTensor g r₁ s₁ →ₗ[ℝ]
      (TensorPouSobolevHilbert (I := I) (M := M) g r₂ s₂ s →L[ℝ]
        TensorPouSobolevHilbert (I := I) (M := M) g r₃ s₃ s') where
  toFun S := productSlot2CLM (I := I) g s s' prod S
  map_add' S₁ S₂ := productSlot2CLM_add (I := I) g s s' prod hbound S₁ S₂
  map_smul' c S := by
    simp only [RingHom.id_apply]
    exact productSlot2CLM_smul (I := I) g s s' prod hbound c S

@[simp] theorem productSlot1Linear_apply {C : ℝ}
    (hbound : SobolevProductBound (I := I) g s s' prod C)
    (S : Integral.L2.SmoothCcTensor g r₁ s₁) :
    productSlot1Linear (I := I) g s s' prod hbound S
      = productSlot2CLM (I := I) g s s' prod S := rfl

/-- The first-slot norm domination `‖productSlot2CLM S‖ ≤ C · ‖S.toHs s‖`, in the
`‖f S‖ ≤ K · ‖e S‖` shape `LinearMap.extendOfNorm` consumes (`K = C`, `e = toHsLinearMap … s`). -/
theorem productSlot1Linear_norm_le {C : ℝ} (hbound : SobolevProductBound (I := I) g s s' prod C)
    (hC : 0 ≤ C) (S : Integral.L2.SmoothCcTensor g r₁ s₁) :
    ‖productSlot1Linear (I := I) g s s' prod hbound S‖ ≤
      C * ‖toHsLinearMap (I := I) g r₁ s₁ s S‖ := by
  rw [productSlot1Linear_apply, toHsLinearMap_apply]
  exact productSlot2CLM_opNorm_le (I := I) g s s' prod hbound hC S

/-- **The bounded bilinear product on the chart-Sobolev Hilbert completions, curried.**

The dense extension of the first-slot linear map `S ↦ productSlot2CLM S` along the order-`s`
chart-Sobolev embedding: a continuous linear map
`H^s →L[ℝ] (H^s →L[ℝ] H^{s'})`.  Uncurried (`fun p => productBilinCLM p.1 p.2`) this is a
bounded bilinear map (`isBoundedBilinearMap_productBilin`); on the dense smooth sections it factors
the order-`s'` class of the product through the two order-`s` embeddings
(`productBilinCLM_apply_toHs`). -/
def productBilinCLM {C : ℝ} (hbound : SobolevProductBound (I := I) g s s' prod C) :
    TensorPouSobolevHilbert (I := I) (M := M) g r₁ s₁ s →L[ℝ]
      (TensorPouSobolevHilbert (I := I) (M := M) g r₂ s₂ s →L[ℝ]
        TensorPouSobolevHilbert (I := I) (M := M) g r₃ s₃ s') :=
  LinearMap.extendOfNorm
    (F := TensorPouSobolevHilbert (I := I) (M := M) g r₂ s₂ s →L[ℝ]
      TensorPouSobolevHilbert (I := I) (M := M) g r₃ s₃ s')
    (productSlot1Linear (I := I) g s s' prod hbound)
    (toHsLinearMap (I := I) g r₁ s₁ s)

/-- **The factoring law on the dense smooth subspace.**
`productBilinCLM (S.toHs s) (T.toHs s) = (prod S T).toHs s'` for all smooth `S, T`. -/
@[simp] theorem productBilinCLM_apply_toHs {C : ℝ}
    (hbound : SobolevProductBound (I := I) g s s' prod C) (hC : 0 ≤ C)
    (S : Integral.L2.SmoothCcTensor g r₁ s₁) (T : Integral.L2.SmoothCcTensor g r₂ s₂) :
    productBilinCLM (I := I) g s s' prod hbound
        (SmoothCcTensor.toHs (g := g) (r := r₁) (s := s₁) s S)
        (SmoothCcTensor.toHs (g := g) (r := r₂) (s := s₂) s T)
      = SmoothCcTensor.toHs (g := g) (r := r₃) (s := s₃) s' (prod S T) := by
  have hext : (productSlot1Linear (I := I) g s s' prod hbound).extendOfNorm
        (toHsLinearMap (I := I) g r₁ s₁ s)
        (toHsLinearMap (I := I) g r₁ s₁ s S)
      = productSlot1Linear (I := I) g s s' prod hbound S :=
    LinearMap.extendOfNorm_eq
      (smoothCcTensor_denseRange_toHs (I := I) g r₁ s₁ s)
      ⟨C, productSlot1Linear_norm_le (I := I) g s s' prod hbound hC⟩ S
  rw [toHsLinearMap_apply] at hext
  have hS : productBilinCLM (I := I) g s s' prod hbound
      (SmoothCcTensor.toHs (g := g) (r := r₁) (s := s₁) s S)
      = productSlot2CLM (I := I) g s s' prod S := by
    rw [productBilinCLM, hext, productSlot1Linear_apply]
  rw [hS, productSlot2CLM_apply_toHs (I := I) g s s' prod hbound]

/-- **The uncurried bilinear product is a bounded bilinear map.**
`fun p => productBilinCLM p.1 p.2 : H^s × H^s → H^{s'}` is `IsBoundedBilinearMap ℝ`, the exact shape
`BanachAlgebraSmoothness.contDiffOn_bilinDiag` consumes (a bounded bilinear map is `C^∞`, so the
diagonal `x ↦ B (f x, h x)` of two `C^∞` factors is `C^∞`). -/
theorem isBoundedBilinearMap_productBilin {C : ℝ}
    (hbound : SobolevProductBound (I := I) g s s' prod C) :
    IsBoundedBilinearMap ℝ
      (fun p : TensorPouSobolevHilbert (I := I) (M := M) g r₁ s₁ s ×
          TensorPouSobolevHilbert (I := I) (M := M) g r₂ s₂ s =>
        productBilinCLM (I := I) g s s' prod hbound p.1 p.2) :=
  ContinuousLinearMap.isBoundedBilinearMap (productBilinCLM (I := I) g s s' prod hbound)

end DifferentialGeometry.Analysis.Sobolev.TensorHilbert

end
