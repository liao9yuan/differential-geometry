import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.NablaRicciTraceCarrier
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.MovingFrameIntegratedNullity
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.DifferentiatedSlotwiseCurvature
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.ContractedBianchi

/-!
# The frame-summed tension-field curvature-divergence nullity (the differentiated-Ricci covariant IBP)

For a closed (compact, boundaryless) smooth Riemannian manifold `(M, g)` this file isolates the single
genuinely-missing analytic primitive at the bottom of the rank-`0` seven-term Bochner fold: the
**frame-summed tension-field curvature-divergence nullity**.

For a fixed smooth Parseval frame family `V a` (a finite tangent field family reproducing every vector,
`∑_a g(V a, u)·V a = u`) and each fixed slot-`0` direction `b`, the frame sum over `a` of the integral of
the metric pairing of the two **tension-field curvature carriers**
```
R(∇_{V a} V b, V a) S + R(V b, ∇_{V a} V a) S
```
(each carrying a frame covariant derivative `∇V` inside a curvature slot) against the slot-`0` gradient
`∇_{V b} S` vanishes:
```
∑_a ∫_M ⟨R(∇_{V a} V b, V a) S + R(V b, ∇_{V a} V a) S, slot0_{V b}(∇S)⟩_g dvol_g = 0.
```

## Why it is integrated, not pointwise — and genuinely curvature content

The two carriers are individually frame-dependent and nonzero pointwise: the fixed Parseval frame is
*not* pointwise covariantly divergence-free, so the `a`-sum of the tension-field curvature terms does not
vanish at a point. They cancel only after integration: the frame sum over `a` of the once-contracted
second Bianchi identity (`contracted_second_bianchi`, `div Ric = ½ d scal`) rewrites the differentiated
curvature trace `∑_a (∇_{V a} R)(V a, V b)` onto the divergence of Ricci, whose integrated covariant
integration by parts against `∇_{V b} S` — fed through the frame-summed covariant-IBP engine
`integral_frameSummed_covDeriv_combined_eq_zero` (`MovingFrameIntegratedNullity`) — is exactly a total
covariant divergence, integrating to `0` over the closed manifold. It is *false* with an arbitrary
section in place of the tension-field curvature trace, so it genuinely uses the Riemann curvature `R`,
its covariant derivative `∇R`, the frame's `∇V` structure, and the Parseval reproduction `hPar`. At
`s = 0` the carriers remain the nonzero leading-slot curvature reads (the gradient slot is the scalar
gradient), so the identity is non-vacuous.

## Currency

The statement is phrased entirely in upstream `riemannOp` / `LeviCivita` / `covGrad` / `tensor0SAsRS`
currency, so it sits strictly upstream of the seven-term Bochner fold
(`ParsevalSevenTermBochnerFold`) and feeds it directly: the fold's per-direction tension-field nullity
`bochnerGroupElt3IiiIv_perB_integral_eq_zero` is the definitional read of this primitive against the
fold's local `bochnerGroupElt3IiiIv` / `bochnerGradSlot0` carriers. The differentiated-Ricci-trace
carrier `nablaRicTraceSection g (V b) s S` (`NablaRicciTraceCarrier`, `appCc (nablaRicSlotOpField g
(V b) s) (∇S)`) is the global smooth section through which the once-contracted second Bianchi reads the
differentiated curvature; the genuine integrated covariant integration by parts of `∇R` against `∇S`
this primitive carries occurs nowhere else in the library nor in Mathlib.
-/

noncomputable section

set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1600000

open Bundle Manifold Set FiberBundle NormedSpace Filter CovariantDerivative
open scoped Manifold Topology ContDiff BigOperators
open Tensor0SBundle Tensor0SNabla

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open TensorMultilinear
open TensorRSNabla

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

set_option linter.unusedSectionVars false in
set_option backward.isDefEq.respectTransparency false in
/-- **The frame-summed tension-field curvature-divergence nullity (the differentiated-Ricci covariant
integration-by-parts primitive, per slot-`0` direction `b`).** For a fixed smooth Parseval frame family
`V a` (`∑_a g(V a, u)·V a = u`) and each fixed `b`, the frame sum over `a` of the integral of the
`(0, s)` metric pairing of the two tension-field curvature carriers
`R(∇_{V a} V b, V a) S + R(V b, ∇_{V a} V a) S` (read on the unit, `riemannOp` currency) against the
slot-`0` gradient `slot0_{V b}(∇S) = tensor0S_curry s x ((∇S)(unit)) (V b)` vanishes:
```
∑_a ∫_M ⟨R(∇_{V a} V b, V a) S + R(V b, ∇_{V a} V a) S, slot0_{V b}(∇S)⟩_g dvol_g = 0.
```

This is the **single genuinely-missing analytic primitive of the rank-`0` Bochner tension-field
nullity**, the once-contracted second-Bianchi covariant divergence of the differentiated curvature
integrated against `∇S`. The two carriers are individually frame-dependent and nonzero pointwise (the
fixed Parseval frame is not pointwise covariantly divergence-free), cancelling only after the frame-summed
integrated covariant integration by parts: the frame sum of `∑_a (∇_{V a} R)(V a, V b)` collapses, through
the once-contracted second Bianchi (`contracted_second_bianchi`, `div Ric = ½ d scal`) read over the
Parseval frame and Theorem A (`nablaCurvSec_diag_frame_trace_eq_nablaRicci_sub`), onto the differentiated
Ricci content carried by the global smooth section `nablaRicTraceSection g (V b) s S`
(`NablaRicciTraceCarrier`), whose integrated covariant IBP against `∇_{V b} S` is a total covariant
divergence integrating to `0` (`integral_frameSummed_covDeriv_combined_eq_zero`,
`MovingFrameIntegratedNullity`). It is *false* with an arbitrary section in place of the tension-field
curvature trace, so it genuinely uses `R`, `∇R`, the frame's `∇V` structure, and `hPar`; at `s = 0` the
carriers remain the nonzero leading-slot curvature reads.

Body `sorry`: the genuine integrated second-Bianchi covariant integration by parts of the differentiated
curvature `∇R` against `∇S`; consumers transitively depend on its `sorryAx`. -/
theorem parsevalFrameSum_tensionFieldCurvatureDivergence_perB_eq_zero
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s)
    {N : ℕ} (V : Fin N → Π b : M, TangentSpace I b)
    (hV : ∀ a, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => (⟨b, V a b⟩ : TotalSpace E (TangentSpace I))))
    (hPar : ∀ (x : M) (u : TangentSpace I x),
      (∑ a : Fin N, g.inner x (V a x) u • V a x) = u) (b : Fin N) :
    (∑ a : Fin N,
        ∫ x, tensorInnerPointwise (I := I) (M := M) g 0 s x
            (TensorRSSpace.toModel
              (tensor0SAsRS (I := I) (M := M) x
                ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
                    riemannOp (tensorCov (I := I) g 0 s) x
                      ((LeviCivita (I := I) g).toFun (V b) x (V a x)) (V a x) (S.toSection x))
                    (unitZeroSec (I := I) (M := M) x) +
                  (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
                    riemannOp (tensorCov (I := I) g 0 s) x (V b x)
                      ((LeviCivita (I := I) g).toFun (V a) x (V a x)) (S.toSection x))
                    (unitZeroSec (I := I) (M := M) x))))
            (TensorRSSpace.toModel
              (tensor0SAsRS (I := I) (M := M) x
                ((tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x
                  ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
                    (covGrad (I := I) (M := M) g 0 s S).toSection x)
                    (unitZeroSec (I := I) (M := M) x))) (V b x))))
          ∂(riemannianVolumeMeasure (I := I) (M := M) g)) = 0 := by
  sorry

end Connection
end Integral
end DifferentialGeometry

end
