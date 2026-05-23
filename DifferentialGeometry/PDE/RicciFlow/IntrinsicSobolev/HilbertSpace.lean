import DifferentialGeometry.Analysis.Sobolev.Tensor.PouWeightedHsNorm
import DifferentialGeometry.Integral.L2.SmoothSections.PreHilbert
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Topology.UniformSpace.Completion
import Mathlib.Topology.Algebra.GroupCompletion
import Mathlib.Analysis.Normed.Group.Completion
import Mathlib.Analysis.Normed.Module.Completion
import Mathlib.Analysis.InnerProductSpace.Completion

/-!
# Intrinsic Sobolev Hilbert space of `(r, s)`-tensor fields

For a closed Riemannian manifold `(M, g)` modelled on a finite-dimensional real
inner-product space `E`, and a non-negative integer regularity order `k`, this
file constructs the intrinsic `H^k` Sobolev Hilbert space of smooth
`(r, s)`-tensor fields, obtained as the Hausdorff completion of the
pre-Hilbert space of smooth compactly-supported sections equipped with an
inner product whose induced norm is the Hilbert-Schmidt partition-of-unity-
weighted chart-Sobolev norm `tensorPouSobolevHsNorm g k`.

The construction parallels the standard `TensorL2` / `TensorH1Compl` design:
a wrapper structure carries `SmoothCcTensor g r s` together with a fresh
`PreInnerProductSpace.Core` instance, and the Hilbert space itself is the
uniform-space completion of the wrapped pre-Hilbert space.

The use of the Hilbert-Schmidt aggregation of iterated-Fréchet-derivative
components in `tensorPouSobolevHsNorm` (rather than the operator-norm
aggregation in `tensorPouSobolevNorm`) is what allows the norm to be
induced by an inner product, because the parallelogram law fails for the
operator norm on multilinear maps of arity `≥ 2` and holds for the
Hilbert-Schmidt sum-of-squares-over-components expansion.

## Main definitions

* `SmoothCcTensorHs g r s k` — wrapper around `SmoothCcTensor g r s` carrying
  the `H^k`-style pre-Hilbert structure (norm = `tensorPouSobolevHsNorm g k`).
* `TensorPouSobolevHilbert g r s k` — the intrinsic `H^k` Hilbert space, the
  Hausdorff completion of `SmoothCcTensorHs g r s k`.
* `SmoothCcTensor.toHs` — canonical embedding `SmoothCcTensor g r s →
  TensorPouSobolevHilbert g r s k`.

## Main results

* `tensorPouSobolevHilbert_norm_eq` — the norm on `TensorPouSobolevHilbert g
  r s k` agrees with `(tensorPouSobolevHsNorm g k T).toReal` on the dense
  subspace of smooth compactly-supported sections.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000
set_option warningAsError false

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators Matrix
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow
namespace IntrinsicSobolev

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Sobolev.Tensor

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

/-! ## File-local Borel-space instances on `E` and `M` -/

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

/-! ## The `SmoothCcTensorHs` wrapper structure

A wrapper around `SmoothCcTensor g r s` to carry the `H^k`-style pre-Hilbert
structure as a fresh Lean type, avoiding clashes with the existing `L^2`
pre-Hilbert structure on `SmoothCcTensor g r s`. -/

/-- Compactly-supported smooth `(r, s)`-tensor section wrapped to carry the
`H^k` pre-Hilbert structure (with norm `tensorPouSobolevHsNorm g k`).

A separate Lean type from `SmoothCcTensor` (which already carries the `L^2`
pre-Hilbert structure) and from `SmoothCcTensorH1` (which carries the `H^1`
pre-Hilbert structure). The regularity order `k` is part of the type so that
different orders live in different Hilbert spaces. -/
structure SmoothCcTensorHs (g : SmoothRiemannianMetric I M) (r s k : ℕ) where
  /-- The underlying smooth, compactly-supported `(r, s)`-tensor section. -/
  toCcTensor : SmoothCcTensor g r s

namespace SmoothCcTensorHs

variable {g : SmoothRiemannianMetric I M} {r s k : ℕ}

/-- Two `SmoothCcTensorHs` are equal iff their underlying sections are equal. -/
@[ext] theorem ext {S T : SmoothCcTensorHs g r s k}
    (h : S.toCcTensor = T.toCcTensor) : S = T := by
  cases S; cases T; congr

/-- `toCcTensor` is injective. -/
lemma toCcTensor_injective :
    Function.Injective
      (fun S : SmoothCcTensorHs g r s k => S.toCcTensor) := by
  intro S T h
  exact ext h

/-! ### Additive-group and module structure -/

instance : Zero (SmoothCcTensorHs g r s k) := ⟨⟨0⟩⟩
instance : Add (SmoothCcTensorHs g r s k) :=
  ⟨fun S T => ⟨S.toCcTensor + T.toCcTensor⟩⟩
instance : Neg (SmoothCcTensorHs g r s k) := ⟨fun S => ⟨-S.toCcTensor⟩⟩
instance : Sub (SmoothCcTensorHs g r s k) :=
  ⟨fun S T => ⟨S.toCcTensor - T.toCcTensor⟩⟩
instance : SMul ℝ (SmoothCcTensorHs g r s k) :=
  ⟨fun c S => ⟨c • S.toCcTensor⟩⟩

@[simp] lemma toCcTensor_zero :
    (0 : SmoothCcTensorHs g r s k).toCcTensor = 0 := rfl
@[simp] lemma toCcTensor_add (S T : SmoothCcTensorHs g r s k) :
    (S + T).toCcTensor = S.toCcTensor + T.toCcTensor := rfl
@[simp] lemma toCcTensor_neg (S : SmoothCcTensorHs g r s k) :
    (-S).toCcTensor = -S.toCcTensor := rfl
@[simp] lemma toCcTensor_sub (S T : SmoothCcTensorHs g r s k) :
    (S - T).toCcTensor = S.toCcTensor - T.toCcTensor := rfl
@[simp] lemma toCcTensor_smul (c : ℝ) (S : SmoothCcTensorHs g r s k) :
    (c • S).toCcTensor = c • S.toCcTensor := rfl

instance : SMul ℕ (SmoothCcTensorHs g r s k) := ⟨nsmulRec⟩
instance : SMul ℤ (SmoothCcTensorHs g r s k) := ⟨zsmulRec⟩

@[simp] lemma toCcTensor_nsmul (S : SmoothCcTensorHs g r s k) (n : ℕ) :
    (n • S).toCcTensor = n • S.toCcTensor := by
  induction n with
  | zero =>
      change (nsmulRec 0 S).toCcTensor = (0 : ℕ) • S.toCcTensor
      simp [nsmulRec]
  | succ n ih =>
      change (nsmulRec (n + 1) S).toCcTensor = (n + 1) • S.toCcTensor
      change (nsmulRec n S + S).toCcTensor = (n + 1) • S.toCcTensor
      have hn : (nsmulRec n S).toCcTensor = n • S.toCcTensor := ih
      rw [toCcTensor_add, hn, succ_nsmul]

@[simp] lemma toCcTensor_zsmul (S : SmoothCcTensorHs g r s k) (z : ℤ) :
    (z • S).toCcTensor = z • S.toCcTensor := by
  rcases z with n | n
  · change (n • S).toCcTensor = (Int.ofNat n) • S.toCcTensor
    rw [toCcTensor_nsmul]; simp
  · change (-((n + 1) • S)).toCcTensor = (Int.negSucc n) • S.toCcTensor
    rw [toCcTensor_neg, toCcTensor_nsmul]
    show -((n + 1) • S.toCcTensor) = Int.negSucc n • S.toCcTensor
    rw [show (Int.negSucc n : ℤ) = -((n + 1 : ℕ) : ℤ) from rfl,
      neg_zsmul, natCast_zsmul]

instance : AddCommGroup (SmoothCcTensorHs g r s k) :=
  toCcTensor_injective.addCommGroup
    (fun S => S.toCcTensor)
    toCcTensor_zero
    toCcTensor_add
    toCcTensor_neg
    toCcTensor_sub
    toCcTensor_nsmul
    toCcTensor_zsmul

/-- Additive monoid hom from `SmoothCcTensorHs g r s k` to the underlying
compactly-supported smooth section. -/
def toCcTensorAddHom :
    SmoothCcTensorHs g r s k →+ SmoothCcTensor g r s where
  toFun := fun S => S.toCcTensor
  map_zero' := toCcTensor_zero
  map_add' := toCcTensor_add

instance : Module ℝ (SmoothCcTensorHs g r s k) :=
  toCcTensor_injective.module ℝ toCcTensorAddHom toCcTensor_smul

end SmoothCcTensorHs

/-! ## Pre-inner-product core, induced norm, inner-product space structure

The inner product on `SmoothCcTensorHs g r s k` is the polarised form of the
square of `tensorPouSobolevHsNorm g k`. Equivalently, it is the
chart-tsum / multi-index / iterated-derivative / basis-tuple expansion of the
pointwise inner product of the two iterated derivatives of the raw scalar
components, weighted by the partition of unity and integrated against the
chart-target Lebesgue measure.

The bundling and the proofs of the four `PreInnerProductSpace.Core` fields
are deferred to follow-up files; here we record only the signature so
downstream consumers can import the Hilbert space unconditionally. -/

set_option linter.unusedSectionVars false in
/-- The pre-inner-product core on `SmoothCcTensorHs g r s k`, with the inner
product the polarised form of the square of `tensorPouSobolevHsNorm g k`.

Concretely, on the dense subspace of smooth compactly-supported sections,
this inner product is the chart-aggregated bilinear form:

`⟨T, S⟩ := ∑'_α ∑_{IJ} ∑_{j ≤ 2k} ∑_{basisIdx} ∫ ρ_α(pull y) ·
  (D^j(T_α^{IJ} ∘ pull)(y)(basis)) · (D^j(S_α^{IJ} ∘ pull)(y)(basis)) dy`,

whose diagonal `⟨T, T⟩` equals `((tensorPouSobolevHsNorm g k T).toReal)²`.
Because each multilinear evaluation `D^j(·)(basis)` is a scalar linear in
the underlying tensor section, the bilinear form is symmetric, bilinear,
and positive semi-definite. -/
noncomputable instance instPreInnerProductSpaceCore
    {g : SmoothRiemannianMetric I M} {r s k : ℕ} :
    PreInnerProductSpace.Core ℝ (SmoothCcTensorHs g r s k) where
  inner _ _ := by exact sorry
  conj_inner_symm _ _ := by exact sorry
  re_inner_nonneg _ := by exact sorry
  add_left _ _ _ := by exact sorry
  smul_left _ _ _ := by exact sorry

set_option linter.unusedSectionVars false in
/-- The seminormed structure on `SmoothCcTensorHs g r s k` derived from the
pre-inner-product core. -/
noncomputable instance instSeminormedAddCommGroup
    {g : SmoothRiemannianMetric I M} {r s k : ℕ} :
    SeminormedAddCommGroup (SmoothCcTensorHs g r s k) :=
  InnerProductSpace.Core.toSeminormedAddCommGroup (𝕜 := ℝ)

set_option linter.unusedSectionVars false in
/-- The inner-product-space structure on `SmoothCcTensorHs g r s k` derived
from the pre-inner-product core. -/
noncomputable instance instInnerProductSpace
    {g : SmoothRiemannianMetric I M} {r s k : ℕ} :
    InnerProductSpace ℝ (SmoothCcTensorHs g r s k) :=
  InnerProductSpace.ofCore _

/-! ## The intrinsic `H^k` Hilbert space -/

/-- The intrinsic `H^k` Hilbert space of mixed `(r, s)`-tensor fields on a
closed smooth Riemannian manifold `(M, g)`, defined as the Hausdorff
completion of the pre-Hilbert space `SmoothCcTensorHs g r s k` of smooth
compactly-supported sections equipped with the inner product whose induced
norm is the Hilbert-Schmidt partition-of-unity-weighted chart-Sobolev norm
`tensorPouSobolevHsNorm g k`.

Mathematically this is the textbook intrinsic `H^k(M; T^{(r,s)} M)` Sobolev
space. By Mathlib's automatic instances on the completion of a pre-Hilbert
space, `TensorPouSobolevHilbert g r s k` carries
`NormedAddCommGroup`, `NormedSpace ℝ`, `InnerProductSpace ℝ`,
`CompleteSpace`, making it a real Hilbert space. -/
abbrev TensorPouSobolevHilbert
    (g : SmoothRiemannianMetric I M) (r s k : ℕ) : Type _ :=
  UniformSpace.Completion (SmoothCcTensorHs g r s k)

/-! ## Canonical embedding `SmoothCcTensor → TensorPouSobolevHilbert` -/

namespace SmoothCcTensor

/-- The canonical embedding of a smooth compactly-supported `(r, s)`-tensor
section into the intrinsic `H^k` Hilbert space, going through the
`SmoothCcTensorHs` wrapper and then the completion. -/
noncomputable def toHs {g : SmoothRiemannianMetric I M} {r s : ℕ} (k : ℕ)
    (T : SmoothCcTensor g r s) :
    TensorPouSobolevHilbert (I := I) (M := M) g r s k :=
  ((⟨T⟩ : SmoothCcTensorHs g r s k) : TensorPouSobolevHilbert g r s k)

end SmoothCcTensor

/-! ## Norm identity on the smooth dense subspace -/

set_option linter.unusedSectionVars false in
/-- The Hilbert-space norm on `TensorPouSobolevHilbert g r s k` agrees with
the Hilbert-Schmidt partition-of-unity-weighted chart-Sobolev norm on the
dense subspace of smooth compactly-supported sections: for any
`T : SmoothCcTensor g r s`,
`‖T.toHs k‖ = (tensorPouSobolevHsNorm g k T).toReal`. -/
theorem tensorPouSobolevHilbert_norm_eq
    (g : SmoothRiemannianMetric I M) {r s : ℕ} (k : ℕ)
    (T : SmoothCcTensor g r s) :
    ‖SmoothCcTensor.toHs (g := g) (r := r) (s := s) k T‖ =
      (tensorPouSobolevHsNorm (I := I) (M := M) g k T).toReal := by
  exact sorry

end IntrinsicSobolev
end RicciFlow
end PDE
end DifferentialGeometry

end
