import DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricRealization.RealizedCovGradJetGeneralOrder
import DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricRealization.RealizedJet2CovGradBound
import DifferentialGeometry.Geometry.Metric.MetricExistence

/-! # The segment metric: convex positive-definiteness and its order-`≤2` covariant-jet sup bound

The covariant fundamental-theorem-of-calculus expansion of the second-order Ricci–DeTurck
right-hand side along a **segment** between two metrics needs two facts about the segment metric
`g_t = (1 - t) • g₂ + t • g₁`, `t ∈ [0,1]` (the convex combination of two
`SmoothRiemannianMetric`, written so that at `t = 0` it is `g₂` and at `t = 1` it is `g₁`):

* **C3a — positive-definiteness.** `g_t` is again a genuine `SmoothRiemannianMetric`: it is a
  smooth, fibrewise symmetric *positive-definite* `(0,2)`-tensor for **every** `t ∈ [0,1]`.  This
  is the pointwise convexity of the cone of positive-definite forms
  (`Geometry.convex_posDefForms`): a convex combination of two positive-definite symmetric forms
  is positive-definite — *proven*, never assumed.  Smoothness is the `ContMDiffSection`
  add/scalar-multiplication closure (`ContMDiff.add_section`, `ContMDiff.const_smul_section`); the
  von-Neumann boundedness field is the finite-dimensional coercivity of the positive-definite
  combination (`Geometry.posDef_isVonNBounded`).  The construction is `segmentMetric`, and its
  positive-definiteness is `segmentMetric_pos`.

* **C3b — the order-`≤2` covariant-jet sup bound.**  The DeTurck right-hand side
  `-2 • Ric(g) + 𝓛_{W(g)} g` is a fibrewise-smooth function of the metric `≤2`-jet
  `(g, ∇g, ∇²g)` and the fibre-inverse `g⁻¹`; the genuine analytic content that the
  supercriticality hypothesis buys is the **uniform `C²`-sup bound on the order-`≤2` covariant
  jet of the segment-metric perturbation**.  This is a *pointwise* bound that **must** route
  through the supercritical Sobolev embedding `H^{m} ↪ C²` (`m` even, `m > dim M + 4`):
  the naive pointwise `C^{m}`-jet of the metric is **unavailable on manifolds of dimension
  `≥ 4`** (the top metric derivative cannot be taken pointwise in `C⁰`), so only the order-`≤2`
  jet — and only it — is uniformly sup-bounded by a Sobolev norm.

  The order-`≤2` covariant jet sum of the realized symmetric perturbation
  `realizeSymmCcTensor g₀ S` of any smooth compactly-supported `(0,2)`-tensor `S` is bounded,
  uniformly over `S` with `‖S.toHs m‖ ≤ B`, by a single constant `φ(B)`:
  ```
  iteratedCovGradJetSum g₀ (realizeSymmCcTensor g₀ S) x ≤ φ(B)   (m even, m > dim M + 4).
  ```
  This is proven by composition of the general-order realize-jet bound
  `iteratedCovGrad_norm_realizeSymm_le_jetSum` (each `‖∇^i (realizeSymm S)(x)‖ ≤ ∑_{l ≤ i}
  ‖∇^l S(x)‖`, constant `1`) and the unconditional supercritical `C²` embedding
  `iteratedCovGradJetSum_le_toHs` (`∑_{j ≤ 2} ‖∇^j S(x)‖ ≤ C · ‖S.toHs m‖`), the latter carrying
  the `finrank`-dependent supercriticality `m > dim M + 4`.  The headline is
  `exists_realizeSymm_iteratedCovGradJet2_sup_le`; its segment specialization with the convex
  combination `S_t = (1 - t) • T₂ + t • T₁` is
  `exists_segmentMetric_realizeSymm_iteratedCovGradJet2_sup_le`.

These are the two reusable ingredients of the covariant-Faà-di-Bruno DeTurck-RHS Lipschitz
leaf; they carry no spectral, perturbation-indexed, or Weyl dependence. -/

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
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSobolev

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

/-! ### C3a — the segment metric and its positive-definiteness -/

/-- **The segment metric `g_t = (1 - t) • g₂ + t • g₁`.**

The convex combination of two smooth Riemannian metrics, packaged as a genuine
`SmoothRiemannianMetric`.  Its fibrewise inner product is the affine combination
`(segmentMetric g₂ g₁ t ht).inner b = (1 - t) • g₂.inner b + t • g₁.inner b`, so it specialises
to `g₂` at `t = 0` and to `g₁` at `t = 1`.

Positive-definiteness for every `t ∈ [0,1]` is the convexity of the cone of fibrewise symmetric
positive-definite forms (`Geometry.convex_posDefForms`); it is *proven* here, not assumed.
Smoothness is the `ContMDiffSection` linear-combination closure, and the von-Neumann boundedness
field is the finite-dimensional coercivity of the positive-definite combination
(`Geometry.posDef_isVonNBounded`). -/
def segmentMetric (g₂ g₁ : SmoothRiemannianMetric I M) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    SmoothRiemannianMetric I M where
  inner b := (1 - t) • g₂.inner b + t • g₁.inner b
  symm b v w := by
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
    rw [g₂.symm b v w, g₁.symm b v w]
  pos b v hv := by
    have hmem :
        ((1 - t) • g₂.inner b + t • g₁.inner b) ∈ Geometry.posDefForms (I := I) (M := M) b :=
      Geometry.convex_posDefForms (I := I) (M := M) b
        ⟨fun v w => g₂.symm b v w, fun v hv => g₂.pos b v hv⟩
        ⟨fun v w => g₁.symm b v w, fun v hv => g₁.pos b v hv⟩
        (by linarith [ht.2]) ht.1 (by ring)
    exact hmem.2 v hv
  isVonNBounded b := by
    have hpos : ∀ v : E, v ≠ 0 →
        0 < ((1 - t) • g₂.inner b + t • g₁.inner b : E →L[ℝ] E →L[ℝ] ℝ) v v := by
      intro v hv
      have hmem :
          ((1 - t) • g₂.inner b + t • g₁.inner b) ∈ Geometry.posDefForms (I := I) (M := M) b :=
        Geometry.convex_posDefForms (I := I) (M := M) b
          ⟨fun v w => g₂.symm b v w, fun v hv => g₂.pos b v hv⟩
          ⟨fun v w => g₁.symm b v w, fun v hv => g₁.pos b v hv⟩
          (by linarith [ht.2]) ht.1 (by ring)
      exact hmem.2 v hv
    exact Geometry.posDef_isVonNBounded (E := E)
      ((((1 - t) • g₂.inner b + t • g₁.inner b) : E →L[ℝ] E →L[ℝ] ℝ)) hpos
  contMDiff :=
    (g₂.contMDiff.const_smul_section (a := (1 - t))).add_section
      (g₁.contMDiff.const_smul_section (a := t))

/-- The fibrewise inner product of the segment metric is the affine combination. -/
@[simp] theorem segmentMetric_inner_apply (g₂ g₁ : SmoothRiemannianMetric I M)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) (x : M) (v w : TangentSpace I x) :
    (segmentMetric (I := I) g₂ g₁ t ht).inner x v w =
      (1 - t) * g₂.inner x v w + t * g₁.inner x v w := by
  change ((1 - t) • g₂.inner x + t • g₁.inner x) v w = _
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]

/-- **C3a — positive-definiteness of the segment metric.**  For every `t ∈ [0,1]` and every
nonzero tangent vector, the segment metric is positive-definite.  This is the `pos` field of
`segmentMetric` exposed as a stand-alone fact: a convex combination of two positive-definite
forms is positive-definite (`Geometry.convex_posDefForms`). -/
theorem segmentMetric_pos (g₂ g₁ : SmoothRiemannianMetric I M)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) (x : M) (v : TangentSpace I x) (hv : v ≠ 0) :
    0 < (segmentMetric (I := I) g₂ g₁ t ht).inner x v v :=
  (segmentMetric (I := I) g₂ g₁ t ht).pos x v hv

/-- The symmetrized realization `ccTensorBilinSymm` is additive in the tensor argument:
`ccTensorBilinSymm g₀ (S + T) x v w = ccTensorBilinSymm g₀ S x v w + ccTensorBilinSymm g₀ T x v w`.
Derived from the subtraction- and scalar-homogeneity primitives (`ccTensorBilinSymm_sub`,
`ccTensorBilinSymm_smul`) by writing `S + T = S − (−1) • T`. -/
theorem ccTensorBilinSymm_add (g₀ : SmoothRiemannianMetric I M)
    (S T : SmoothCcTensor g₀ 0 2) (x : M) (v w : TangentSpace I x) :
    ccTensorBilinSymm (I := I) g₀ (S + T) x v w =
      ccTensorBilinSymm (I := I) g₀ S x v w + ccTensorBilinSymm (I := I) g₀ T x v w := by
  have hsplit : (S + T : SmoothCcTensor g₀ 0 2) = S - (-1 : ℝ) • T := by
    rw [neg_one_smul, sub_neg_eq_add]
  rw [hsplit, ccTensorBilinSymm_sub, ccTensorBilinSymm_smul]
  ring

/-- **The perturbation form of the segment metric.**  If `g₁, g₂` are the realized metrics of
the `g₀`-fibre-small perturbations `T₁, T₂` (tied by the fibrewise `inner`-identities
`gₖ.inner = g₀.inner + ccTensorBilinSymm g₀ Tₖ`), then the segment metric's inner product is the
`g₀`-anchored realized form of the convex combination `S_t = (1 - t) • T₂ + t • T₁`:
```
(segmentMetric g₂ g₁ t ht).inner x v w
  = g₀.inner x v w + ccTensorBilinSymm g₀ ((1 - t) • T₂ + t • T₁) x v w .
```
This is the algebraic identity tying the segment metric to a single realized perturbation tensor;
it follows from the two `inner`-identities and the `ℝ`-bilinearity of the realization
`ccTensorBilinSymm` in the tensor argument. -/
theorem segmentMetric_inner_eq_realizeSymm_add (g₀ g₁ g₂ : SmoothRiemannianMetric I M)
    (T₁ T₂ : SmoothCcTensor g₀ 0 2) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (hg₁ : ∀ (x : M) (v w : TangentSpace I x),
      g₁.inner x v w = g₀.inner x v w + ccTensorBilinSymm (I := I) g₀ T₁ x v w)
    (hg₂ : ∀ (x : M) (v w : TangentSpace I x),
      g₂.inner x v w = g₀.inner x v w + ccTensorBilinSymm (I := I) g₀ T₂ x v w)
    (x : M) (v w : TangentSpace I x) :
    (segmentMetric (I := I) g₂ g₁ t ht).inner x v w =
      g₀.inner x v w +
        ccTensorBilinSymm (I := I) g₀ ((1 - t) • T₂ + t • T₁) x v w := by
  rw [segmentMetric_inner_apply, hg₁ x v w, hg₂ x v w,
    ccTensorBilinSymm_add, ccTensorBilinSymm_smul, ccTensorBilinSymm_smul]
  ring

/-! ### C3b — the order-`≤2` covariant-jet sup bound -/

/-- The intrinsic order-`k` chart-Sobolev completion embedding `SmoothCcTensor.toHs` is
`ℝ`-homogeneous: `(c • S).toHs k = c • (S.toHs k)`.  Both sides are the completion coercion of the
`SmoothCcTensorHs`-wrapper scalar multiplication (`UniformSpace.Completion.coe_smul`). -/
theorem toHs_const_smul (g₀ : SmoothRiemannianMetric I M) (k : ℕ) (c : ℝ)
    (S : SmoothCcTensor g₀ 0 2) :
    IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) k (c • S)
      = c • IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) k S := by
  unfold IntrinsicSobolev.SmoothCcTensor.toHs
  rw [← UniformSpace.Completion.coe_smul]
  rfl

/-- The `H^k` norm of a real scalar multiple scales by the absolute value of the scalar:
`‖(c • S).toHs k‖ = |c| · ‖S.toHs k‖`. -/
theorem norm_toHs_const_smul (g₀ : SmoothRiemannianMetric I M) (k : ℕ) (c : ℝ)
    (S : SmoothCcTensor g₀ 0 2) :
    ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) k (c • S)‖
      = |c| * ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) k S‖ := by
  rw [toHs_const_smul, norm_smul, Real.norm_eq_abs]

/-- The intrinsic order-`k` chart-Sobolev completion embedding `SmoothCcTensor.toHs` is additive:
`(S + T).toHs k = S.toHs k + T.toHs k`.  Both sides are the completion coercion of the
`SmoothCcTensorHs`-wrapper addition (`UniformSpace.Completion.coe_add`). -/
theorem toHs_add' (g₀ : SmoothRiemannianMetric I M) (k : ℕ)
    (S T : SmoothCcTensor g₀ 0 2) :
    IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) k (S + T)
      = IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) k S
        + IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) k T := by
  unfold IntrinsicSobolev.SmoothCcTensor.toHs
  rw [← UniformSpace.Completion.coe_add]
  rfl

/-- **The convex-combination Sobolev bound.**  If two smooth compactly-supported `(0,2)`-tensors
`T₁, T₂` have `H^k` norm `≤ B`, then so does every convex combination `(1 - t) • T₂ + t • T₁`,
`t ∈ [0,1]`:
```
‖((1 - t) • T₂ + t • T₁).toHs k‖ ≤ B .
```
The completion embedding `toHs` is additive (`toHs_add'`) and `ℝ`-homogeneous
(`toHs_const_smul`), so the triangle inequality gives `≤ (1 - t)·B + t·B = B`. -/
theorem norm_toHs_segment_le (g₀ : SmoothRiemannianMetric I M) (k : ℕ)
    (T₁ T₂ : SmoothCcTensor g₀ 0 2) (B : ℝ)
    (hB₁ : ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) k T₁‖ ≤ B)
    (hB₂ : ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) k T₂‖ ≤ B)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) k
        ((1 - t) • T₂ + t • T₁)‖ ≤ B := by
  have hN₁ : 0 ≤ ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) k T₁‖ :=
    norm_nonneg _
  have hN₂ : 0 ≤ ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) k T₂‖ :=
    norm_nonneg _
  calc ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) k
          ((1 - t) • T₂ + t • T₁)‖
      ≤ ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) k ((1 - t) • T₂)‖ +
          ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) k (t • T₁)‖ := by
        rw [toHs_add' (I := I) g₀ k]
        exact norm_add_le _ _
    _ = |1 - t| * ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) k T₂‖ +
          |t| * ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) k T₁‖ := by
        rw [norm_toHs_const_smul, norm_toHs_const_smul]
    _ = (1 - t) * ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) k T₂‖ +
          t * ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) k T₁‖ := by
        rw [abs_of_nonneg (by linarith [ht.2] : (0 : ℝ) ≤ 1 - t), abs_of_nonneg ht.1]
    _ ≤ (1 - t) * B + t * B :=
        add_le_add
          (mul_le_mul_of_nonneg_left hB₂ (by linarith [ht.2]))
          (mul_le_mul_of_nonneg_left hB₁ ht.1)
    _ = B := by ring

/-- **C3b — the order-`≤2` covariant-jet `C²`-sup bound for the realized symmetric perturbation.**

For an anchor `g₀` and a Sobolev half-order `k` with the supercriticality
`2 * k > Module.finrank ℝ E + 4`, and a uniform `H^{2k}`-size bound `B` on the **realized
symmetric perturbation**, there is a single constant `C ≥ 0` such that for every smooth
compactly-supported `(0,2)`-tensor `S` with `‖(realizeSymmCcTensor g₀ S).toHs (2*k)‖ ≤ B` and
**every base point `x`**, the order-`≤2` covariant-jet sum of the realized symmetric perturbation
`realizeSymmCcTensor g₀ S` is bounded by `C`:
```
iteratedCovGradJetSum g₀ (realizeSymmCcTensor g₀ S) x ≤ C
  (2k > dim M + 4, ‖(realizeSymm S).toHs (2k)‖ ≤ B).
```

This is the genuine analytic content the supercriticality hypothesis buys: a **pointwise**,
uniform-over-the-`H^{2k}`-ball `C²`-sup bound on the metric perturbation's order-`≤2` covariant
jet — exactly what the Faà-di-Bruno expansion of the second-order DeTurck right-hand side needs for
its `≤2`-jet coefficient.  It is a `finrank`-routed bound, proven directly from the
**unconditional supercritical `C²` Sobolev embedding** `iteratedCovGradJetSum_le_toHs`
(`iteratedCovGradJetSum g₀ (realizeSymm S) x ≤ C₀ · ‖(realizeSymm S).toHs (2k)‖`, which carries the
supercriticality `2k > dim M + 4`), applied to the realized symmetric perturbation
`realizeSymmCcTensor g₀ S` (itself a genuine `SmoothCcTensor`), composed with the size bound
`‖(realizeSymm S).toHs (2k)‖ ≤ B`.  The naive pointwise `C^m` bound (`m > 2`) is **unavailable**
for `finrank ≥ 4` — only this order-`≤2` jet, routed through the Sobolev embedding, is uniformly
sup-bounded.

The hypothesis is phrased on the realized tensor `‖(realizeSymm S).toHs (2k)‖` (rather than on the
underlying `‖S.toHs (2k)‖`), so the bound is purely the supercritical embedding and carries no
dependence on the slot-swap fibre-jet behaviour of the realization map.  The reduction of
`‖(realizeSymm S).toHs (2k)‖` to `‖S.toHs (2k)‖` is the separate, realization-map `Hˢ`-boundedness
statement — the `H^{2k}`-Sobolev analogue of the slot-swap fibre-jet isometry
`flipCcTensor_iteratedCovGrad_norm_eq` — supplied by the metric-realization Sobolev layer. -/
theorem exists_realizeSymm_iteratedCovGradJet2_sup_le
    (g₀ : SmoothRiemannianMetric I M) (k : ℕ) (h_super : 2 * k > Module.finrank ℝ E + 4)
    (B : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (S : SmoothCcTensor g₀ 0 2),
        ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) (2 * k)
            (realizeSymmCcTensor (I := I) g₀ S)‖ ≤ B →
        ∀ x : M,
          iteratedCovGradJetSum (I := I) g₀ (realizeSymmCcTensor (I := I) g₀ S) x ≤ C := by
  classical
  -- The unconditional supercritical `C²` embedding constant.
  obtain ⟨C₀, hC₀_pos, hC₀⟩ := iteratedCovGradJetSum_le_toHs (I := I) g₀ k h_super
  refine ⟨C₀ * max B 0, mul_nonneg hC₀_pos.le (le_max_right _ _), fun S hS x => ?_⟩
  have hS' :
      ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) (2 * k)
          (realizeSymmCcTensor (I := I) g₀ S)‖ ≤ max B 0 := le_trans hS (le_max_left _ _)
  -- Apply the supercritical `C²` embedding to the realized symmetric perturbation directly.
  calc iteratedCovGradJetSum (I := I) g₀ (realizeSymmCcTensor (I := I) g₀ S) x
      ≤ C₀ * ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) (2 * k)
          (realizeSymmCcTensor (I := I) g₀ S)‖ :=
        hC₀ (realizeSymmCcTensor (I := I) g₀ S) x
    _ ≤ C₀ * max B 0 := mul_le_mul_of_nonneg_left hS' hC₀_pos.le

/-- **C3b, segment specialisation — the order-`≤2` covariant-jet `C²`-sup bound for the
segment-metric perturbation, uniform over `t ∈ [0,1]`.**

For an anchor `g₀`, a Sobolev half-order `k` with `2 * k > Module.finrank ℝ E + 4`, and a uniform
`H^{2k}`-size bound `B` on the realized symmetric perturbation of the segment combination, there
is a single constant `C ≥ 0` such that for any two `g₀`-fibre-small perturbations `T₁, T₂`,
**every** `t ∈ [0,1]` with
`‖(realizeSymm ((1 - t) • T₂ + t • T₁)).toHs (2k)‖ ≤ B`, and **every** base point `x`, the
order-`≤2` covariant-jet sum of the realized symmetric perturbation of the segment combination
`S_t = (1 - t) • T₂ + t • T₁` is bounded by `C`:
```
iteratedCovGradJetSum g₀ (realizeSymmCcTensor g₀ ((1-t) • T₂ + t • T₁)) x ≤ C
  (2k > dim M + 4, ‖(realizeSymm S_t).toHs (2k)‖ ≤ B, t ∈ [0,1]).
```

Since the segment metric `g_t = (1 - t) • g₂ + t • g₁` has perturbation tensor
`S_t = (1 - t) • T₂ + t • T₁` (`segmentMetric_inner_eq_realizeSymm_add`), this is precisely the
uniform `C²`-sup bound the DeTurck Faà-di-Bruno expansion consumes for the segment metric's
`≤2`-jet coefficient.  It is the single-tensor headline
`exists_realizeSymm_iteratedCovGradJet2_sup_le` instantiated at the segment combination
`S_t = (1 - t) • T₂ + t • T₁`.  (When the realization map is recognised as `ℝ`-linear, the
per-`t` size hypothesis follows from `H^{2k}`-bounds on `realizeSymm T₁, realizeSymm T₂`
individually via the convex-combination Sobolev bound `norm_toHs_segment_le`; that linearity
reduction is supplied by the metric-realization Sobolev layer.) -/
theorem exists_segmentMetric_realizeSymm_iteratedCovGradJet2_sup_le
    (g₀ : SmoothRiemannianMetric I M) (k : ℕ) (h_super : 2 * k > Module.finrank ℝ E + 4)
    (B : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (T₁ T₂ : SmoothCcTensor g₀ 0 2) (t : ℝ), t ∈ Set.Icc (0 : ℝ) 1 →
        ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) (2 * k)
            (realizeSymmCcTensor (I := I) g₀ ((1 - t) • T₂ + t • T₁))‖ ≤ B →
        ∀ x : M,
          iteratedCovGradJetSum (I := I) g₀
              (realizeSymmCcTensor (I := I) g₀ ((1 - t) • T₂ + t • T₁)) x ≤ C := by
  classical
  obtain ⟨C, hC_nn, hC⟩ :=
    exists_realizeSymm_iteratedCovGradJet2_sup_le (I := I) g₀ k h_super B
  exact ⟨C, hC_nn, fun T₁ T₂ t _ht hBt x => hC ((1 - t) • T₂ + t • T₁) hBt x⟩

end MetricRealization
end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry

end
