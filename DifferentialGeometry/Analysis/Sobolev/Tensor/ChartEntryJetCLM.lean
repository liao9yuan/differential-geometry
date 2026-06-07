import DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricRealization.CcTensorBilinFibreHsBound
import DifferentialGeometry.Analysis.Sobolev.Embedding.SobolevEmbeddingCmOrderDropping
import DifferentialGeometry.Geometry.Metric.ChartGram

/-!
# The base-point-smooth continuous-linear functional reading a single chart-frame entry of
`ccTensorBilinSymm g (·)` from a Sobolev element (the finite-order jet wall)

For a closed Riemannian manifold `(M, g)`, a fixed chart centred at `α` with chart frame
`e_i = chartBasisVecFiber α i`, and a smooth compactly-supported `(0, 2)`-tensor section `T`,
the chart-`α` scalar matrix entry

  `entry_T(x) := ccTensorBilinSymm g T x (e_i x) (e_j x)`

depends `ℝ`-linearly on `T` and is controlled, together with all of its base-point jets up to
any finite order `N`, by the intrinsic supercritical Sobolev norm `‖T.toHs (2 m)‖`
(`2 m > dim M + 2 N`).  This is the supercritical Sobolev embedding `H^{2m} ↪ C^N` read in the
fixed chart's frame: it produces, for each finite jet order `N`, a **continuous linear
functional family**

  `A : M → (TensorPouSobolevHilbert g 0 2 (2 m) →L[ℝ] ℝ)`

that is itself `ContMDiffOn ℝ N` in the base point on the chart base set and reads the entry on
the dense smooth subspace: `A x (T.toHs (2 m)) = entry_T(x)`.

## Why this is the genuine analytic content (the finite-order jet wall)

Mathlib's supercritical Sobolev embedding and this library's tensor version
(`tensorPouSobolevHilbert_embedding_Ck`, `iteratedCovGrad_toSobolev_embedding_Cm_unconditional`)
are delivered as **norm/seminorm** bounds (`‖∇^j T x‖ ≤ C · ‖T.toHs (2m)‖`), not as a
*continuous-linear-map family that is smooth in the base point*.  Upgrading a per-order
sup-norm embedding to a base-point-`C^N` continuous-linear functional family — the operator
norm of every base-point jet `∂_x^β A x` (`|β| ≤ N`) being bounded by the embedding constant,
uniformly on the chart base set — is the missing analytic step.  A single Sobolev space
`H^{2m}` embeds only into `C^N` for `N < m − dim M / 2`, so the order `N` and the Sobolev
exponent `m` are genuinely coupled (the *bigraded* nature of the jet wall): there is no fixed
`m` for which `A` is `C^∞`.

This functional family is the linchpin of the joint `(t, x)`-smoothness child
`jointContMDiffOn_ccTensorBilinSymm_chartEntry_baseSet`
(`Analysis/Sobolev/Tensor/ChartEntryJointSmoothness.lean`): composing the base-point-`C^N`
family `A` (read at a per-`N` supercritical exponent `m`) with the all-order time control of
the Sobolev time-tower `t ↦ (T_s t).toHs (2 m)` (which is `ContDiffOn ℝ N`) through
`ContMDiffOn.clm_apply` yields the joint `C^N` smoothness of the entry for every finite `N`,
hence joint `C^∞`.

## Why this is not hypothesis-packaging, and why it is not vacuous

The conclusion of the consumer is the joint `(t, x)`-smoothness of a *scalar function on
`ℝ × M`*; the content here is a *base-point-only* smooth continuous-linear functional family
on the fixed chart base set — a different object, never assuming the consumer's conclusion.

The agreement clause `A x (T.toHs (2 m)) = ccTensorBilinSymm g T x (e_i x) (e_j x)` quantified
over **all** smooth sections `T` pins `A` genuinely: the zero family `A = 0` does not satisfy
it (on a non-empty manifold there is a smooth `T` with a non-zero chart-`α` entry at some
base-set point, e.g. a bump times the chart-frame dual covector pair).  So the predicate
rejects the degenerate witness; it is not vacuous.

The body is `sorry`: this is the genuine missing finite-order Sobolev-embedding jet-CLM
theorem, isolated as a first-class reusable analytic leaf.  Consumers transitively depend on
`sorryAx`. -/

noncomputable section

open Set Filter Topology Bundle
open scoped Manifold ContDiff NNReal ENNReal Topology BigOperators

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow
namespace IntrinsicSpectral
namespace MetricRealization

open DifferentialGeometry
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSobolev

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

/-- **Base-point-`C^N` continuous-linear functional reading a single chart-frame entry of
`ccTensorBilinSymm g (·)` from a Sobolev element (the finite-order jet wall).**

For a closed Riemannian metric `g`, a chart centre `α`, frame indices `(i, j)`, and a finite
base-point jet order `N`, there is a supercritical Sobolev exponent `m` (`2 m > dim M + 2 N`)
and a continuous-linear functional family

  `A : M → (TensorPouSobolevHilbert g 0 2 (2 m) →L[ℝ] ℝ)`

that is `ContMDiffOn ℝ N` in the base point on the chart base set `(trivializationAt E
(TangentSpace I) α).baseSet`, and reads the chart-`α` matrix entry on the dense smooth
subspace: for every smooth compactly-supported `(0, 2)`-tensor section `T`,

  `A x (T.toHs (2 m)) = ccTensorBilinSymm g T x (chartBasisVecFiber α i x)
                                                (chartBasisVecFiber α j x)`.

This is the supercritical Sobolev embedding `H^{2m} ↪ C^N` read, in the fixed chart's frame,
as a base-point-smooth continuous-linear functional family — the finite-order jet wall (the
order `N` and the exponent `m` are genuinely coupled, since `H^{2m}` embeds only into `C^N`
for `N < m − dim M / 2`).  See the file header for the full discussion.

The agreement clause quantified over all smooth `T` rejects the zero family, so the statement
is not vacuous; the conclusion is a base-point-only smooth functional family, distinct from the
joint `(t, x)`-smoothness statement that consumes it, so no packaging.  The body is `sorry`;
consumers transitively depend on `sorryAx`. -/
theorem exists_contMDiffOn_chartEntryJetCLM_baseSet
    (g : SmoothRiemannianMetric I M) (α : M) (i j : Fin (Module.finrank ℝ E)) (N : ℕ) :
    ∃ (m : ℕ) (A : M → (IntrinsicSobolev.TensorPouSobolevHilbert g 0 2 (2 * m) →L[ℝ] ℝ)),
      ContMDiffOn I 𝓘(ℝ, IntrinsicSobolev.TensorPouSobolevHilbert g 0 2 (2 * m) →L[ℝ] ℝ)
          (N : ℕ∞) A (trivializationAt E (TangentSpace I) α).baseSet ∧
      ∀ (T : Integral.L2.SmoothCcTensor g 0 2)
        (x : M), x ∈ (trivializationAt E (TangentSpace I) α).baseSet →
        A x (IntrinsicSobolev.SmoothCcTensor.toHs (g := g) (r := 0) (s := 2) (2 * m) T) =
          ccTensorBilinSymm (I := I) g T x
            (chartBasisVecFiber (I := I) α i x)
            (chartBasisVecFiber (I := I) α j x) := sorry

end MetricRealization
end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry

end
