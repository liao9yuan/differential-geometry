import DifferentialGeometry.Geometry.Flow.ConnectionDifference
import DifferentialGeometry.Geometry.Connection.Realization.SmoothSections
import DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricRealization.ConnectionDifferenceKoszul

/-!
# The connection-difference operator field of two Riemannian metrics

For two smooth Riemannian metrics `g₁` and `g₀` on a closed smooth manifold `M` modelled on a
real inner-product space `E`, their Levi-Civita covariant derivatives differ by a genuine
`(1, 2)`-tensor field, the connection-difference tensor `connDiff g₁ g₀`
(`Geometry/Flow/ConnectionDifference.lean`).  At each point `x : M` it is the continuous
bilinear map

```
connDiff g₁ g₀ x : TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x,
```

equivalently a fibre of the iterated endomorphism bundle `Hom(TM, Hom(TM, TM))`.  This file
packages it as a **smooth bundle section** — a first-class reusable operator field — together
with its evaluation, self-vanishing, smoothness, Koszul representation, and a fibrewise
`g₀`-pairing envelope.

The companion `connDiff` (pointwise) already provides the per-point bilinear map and its three
smoothness lemmas on smooth tangent fields.  Here we lift those to the *section level*: the
pointwise field `x ↦ connDiff g₁ g₀ x` is a smooth section of the `(1, 2)`-tensor bundle.  The
output shape — `Hom(TM, Hom(TM, TM))` — is the genuine `(1, 2)` mixed-tensor shape (one
contravariant output index, two covariant input indices), so it is *not* a covariant
`SmoothCcTensor` (which is `Hom(Tensor0S r, Tensor0S s)` with both indices covariant); the
metrically-lowered form is the covariant object, and that is exactly what the Koszul
representation `connDiff_koszul_realize` already computes.

## Main definitions

* `connDiffField g₁ g₀` — the connection-difference operator field of `g₁` and `g₀`, as a
  smooth section of `Hom(TM, Hom(TM, TM))`.

## Main results

* `connDiffField_apply` — its fibre value at `x` is `connDiff g₁ g₀ x`.
* `connDiffField_self` — the connection-difference field of a metric with itself is the zero
  section (the non-vacuity litmus: `g₁ = g₀ ⟹ connDiffField = 0`).
* `connDiffField_contMDiff` — the underlying field is a smooth section (this is the content of
  the packaging; it lifts `connDiff_contMDiff` to the operator-field level).
* `connDiffField_eq_koszul_contraction` — the section-level Koszul representation: the
  `g₁`-pairing of the field against a test vector equals the realized `(0, 3)`-covariant
  derivative combination of the perturbation `h = ccTensorBilinSymm g₀ T`
  (`g₁ = g₀ + h`).  This is the form the higher-order metric-difference development consumes.
* `connDiffField_g0_fibre_abs_bound` — the fibrewise `g₀`-pairing envelope: the `g₀`-pairing of
  the field is controlled by the `≤ 1`-jet realized covariant-derivative data of `h` plus the
  perturbation·field correction (the connection difference's fibre bound by the metrics' jet
  data).
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

open Bundle Manifold Set
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry
namespace PDE
namespace DeTurck

open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2 (SmoothCcTensor)
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
open Tensor0SBundle

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [SigmaCompactSpace M] [T2Space M] [I.Boundaryless] [BoundarylessManifold I M]

omit [CompactSpace M] [I.Boundaryless] in
/-- The connection-difference tensor `connDiff g₁ g₀ x`, with the differentiated slot frozen to
the value of a globally smooth tangent vector field `σ`, is a smooth section of the
endomorphism bundle `Hom(TM, TM)`.

This is the inner step of the operator-field packaging: it applies the pointwise-smoothness
bridge `contMDiff_clm_section_of_pointwise` to the per-vector evaluations
`x ↦ connDiff g₁ g₀ x (σ x) (τ x)`, each of which is smooth by `connDiff_contMDiff`. -/
private theorem connDiff_innerHom_contMDiff (g₁ g₀ : SmoothRiemannianMetric I M)
    {σ : Π x : M, TangentSpace I x}
    (hσ : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% σ)) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun x : M => TotalSpace.mk' (E →L[ℝ] E)
        (E := fun z : M => TangentSpace I z →L[ℝ] TangentSpace I z) x
        (connDiff (I := I) g₁ g₀ x (σ x))) := by
  apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
    (F₁ := E) (V₁ := fun x : M => TangentSpace I x)
    (F₂ := E) (V₂ := fun x : M => TangentSpace I x)
    (φ := fun x => connDiff (I := I) g₁ g₀ x (σ x))
  intro Y
  exact connDiff_contMDiff (I := I) g₁ g₀ hσ Y.contMDiff

omit [CompactSpace M] [I.Boundaryless] in
/-- **Smoothness of the connection-difference operator field.**  The pointwise field
`x ↦ connDiff g₁ g₀ x : Hom(TM, Hom(TM, TM))` is a smooth section of the `(1, 2)`-tensor
bundle.

The proof applies the pointwise-smoothness bridge `contMDiff_clm_section_of_pointwise` to the
*outer* slot: for every globally smooth tangent vector field `Y` the field
`x ↦ connDiff g₁ g₀ x (Y x) : Hom(TM, TM)` is smooth by `connDiff_innerHom_contMDiff`, so the
operator-valued field `x ↦ connDiff g₁ g₀ x` is itself a smooth section of the iterated Hom
bundle. -/
theorem connDiffField_contMDiff (g₁ g₀ : SmoothRiemannianMetric I M) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] (E →L[ℝ] E))) ∞
      (fun x : M => TotalSpace.mk' (E →L[ℝ] (E →L[ℝ] E))
        (E := fun z : M =>
          TangentSpace I z →L[ℝ] (TangentSpace I z →L[ℝ] TangentSpace I z)) x
        (connDiff (I := I) g₁ g₀ x)) := by
  apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
    (F₁ := E) (V₁ := fun x : M => TangentSpace I x)
    (F₂ := E →L[ℝ] E) (V₂ := fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x)
    (φ := fun x => connDiff (I := I) g₁ g₀ x)
  intro Y
  exact connDiff_innerHom_contMDiff (I := I) g₁ g₀ Y.contMDiff

/-- **The connection-difference operator field** of two smooth Riemannian metrics `g₁` and
`g₀`, as a smooth section of the `(1, 2)`-tensor bundle `Hom(TM, Hom(TM, TM))`.  Its fibre
value at `x` is the pointwise connection-difference tensor `connDiff g₁ g₀ x`; smoothness is
`connDiffField_contMDiff`. -/
def connDiffField (g₁ g₀ : SmoothRiemannianMetric I M) :
    Cₛ^∞⟮I; E →L[ℝ] (E →L[ℝ] E),
      (fun x : M => TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] TangentSpace I x))⟯ where
  toFun := fun x : M => connDiff (I := I) g₁ g₀ x
  contMDiff_toFun := connDiffField_contMDiff (I := I) g₁ g₀

omit [CompactSpace M] [I.Boundaryless] in
/-- The fibre value of the connection-difference operator field at `x` is the pointwise
connection-difference tensor `connDiff g₁ g₀ x`.  Definitional. -/
@[simp] lemma connDiffField_apply (g₁ g₀ : SmoothRiemannianMetric I M) (x : M) :
    connDiffField (I := I) g₁ g₀ x = connDiff (I := I) g₁ g₀ x := rfl

omit [CompactSpace M] [I.Boundaryless] in
/-- **Self-vanishing of the connection-difference operator field** (non-vacuity litmus).  The
connection-difference field of a metric with itself is the zero section: the two Levi-Civita
covariant derivatives coincide, so the field vanishes identically.  This rejects the degenerate
reading of the field (it is genuinely the difference, not a constant). -/
@[simp] theorem connDiffField_self (g : SmoothRiemannianMetric I M) :
    connDiffField (I := I) g g = 0 := by
  classical
  apply ContMDiffSection.ext
  intro x
  rw [connDiffField_apply]
  change connDiff (I := I) g g x = (0 : Cₛ^∞⟮I; E →L[ℝ] (E →L[ℝ] E),
    (fun y : M => TangentSpace I y →L[ℝ] (TangentSpace I y →L[ℝ] TangentSpace I y))⟯) x
  rw [connDiff_self]
  rfl

/-- **The section-level Koszul representation of the connection-difference field.**  For two
smooth Riemannian metrics with `g₁ = g₀ + ccTensorBilinSymm g₀ T`, the `g₁`-pairing of the
connection-difference operator field against a test vector `c` is characterised through the
`g₀`-covariant derivative of the realized perturbation `h = ccTensorBilinSymm g₀ T`:
$$
  2\,g_1\bigl((\nabla^{g_1}-\nabla^{g_0})_a\,b, c\bigr)
    = (\nabla^{0}_a h)(b,c) + (\nabla^{0}_b h)(a,c) - (\nabla^{0}_c h)(a,b).
$$
This is the field-level restatement of `connDiff_koszul_realize` (through the definitional
bridge `connDiffField_apply`): it expresses the metrically-lowered connection difference — the
genuine covariant `(0, 3)`-tensor — as a contraction of the inverse-metric-implicit Koszul
combination of `∇₀h`, the form the higher-order metric-difference development consumes. -/
theorem connDiffField_eq_koszul_contraction
    (g₁ g₀ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
    (hr : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T y v w)
    (x : M) (a b c : TangentSpace I x) :
    2 * g₁.inner x
        (connDiffField (I := I) g₁ g₀ x
          (smoothExtensionTangent (I := I) x b x)
          (smoothExtensionTangent (I := I) x a x)) c =
      covDerivRealizeEval (I := I) g₀ T x a b c
      + covDerivRealizeEval (I := I) g₀ T x b a c
      - covDerivRealizeEval (I := I) g₀ T x c a b := by
  rw [connDiffField_apply]
  exact connDiff_koszul_realize (I := I) g₁ g₀ T hr x a b c

/-- **Fibrewise `g₀`-pairing envelope of the connection-difference field.**  The absolute value
of the `g₀`-pairing `2·g₀(connDiffField g₁ g₀ · b a, c)` is controlled by the three realized
`(0, 3)`-covariant-derivative evaluations of `h = ccTensorBilinSymm g₀ T` (the `≤ 1`-jet of the
perturbation `T`) plus the perturbation·field correction.  This is the `κ`/fibre envelope: the
connection difference's fibre pairing is bounded by the metrics' `≤ 1`-jet data.  It is the
field-level restatement of `connDiff_g0_fibre_abs_bound`. -/
theorem connDiffField_g0_fibre_abs_bound
    (g₁ g₀ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
    (hr : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T y v w)
    (x : M) (a b c : TangentSpace I x) :
    |2 * g₀.inner x
        (connDiffField (I := I) g₁ g₀ x
          (smoothExtensionTangent (I := I) x b x)
          (smoothExtensionTangent (I := I) x a x)) c|
      ≤ |covDerivRealizeEval (I := I) g₀ T x a b c|
        + |covDerivRealizeEval (I := I) g₀ T x b a c|
        + |covDerivRealizeEval (I := I) g₀ T x c a b|
        + 2 * |ccTensorBilinSymm (I := I) g₀ T x
            (connDiffField (I := I) g₁ g₀ x
              (smoothExtensionTangent (I := I) x b x)
              (smoothExtensionTangent (I := I) x a x)) c| := by
  simp only [connDiffField_apply]
  exact connDiff_g0_fibre_abs_bound (I := I) g₁ g₀ T hr x a b c

end DeTurck
end PDE
end DifferentialGeometry
