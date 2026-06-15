import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.MovingFrameRemainderCarrierSection
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.BracketDivergenceForm
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.MovingFrameRemainderDivergenceForm

/-!
# The moving-frame summed-folding of the three-carrier remainder against `∇S`

For a closed (compact, boundaryless) smooth Riemannian manifold `(M, g)`, covariant rank `s`, and a
smooth compactly-supported `(0, s)`-tensor `S`, this file folds the global metric `L²` pairing of the
**three-carrier moving-frame remainder**

```
Rem S := pointwiseTensorCurv g s S − GcurvSection g s S − (genuineDiffCurvSection g s S + ricTraceSection g s S)
```

against `∇S := covGrad g 0 s S` into the **frame-summed covariant Leibniz integral** that the
closed-manifold frame-summed covariant integration-by-parts engine
`integral_frameSummed_bracketCovDeriv_combined_eq_zero` (`BracketDivergenceForm`) consumes. The
remainder is the section-level four-carrier object `movingFrameRemainderSection`
(`MovingFrameRemainderCarrierSection`), whose unit-section fibre value is the bracket obstruction field
`bracketThirdCurvFieldFib` of the field-level split
`pointwiseTensorCurv_toSection_eq_genuine_add_bracket_field`.

## The fold

The genuine moving-frame third-order Bochner–Weitzenböck content is the **covariant-divergence form** of
the remainder: the frame-bracket directional terms `∇_{[Bᵢ, Wₐ]}(∇_{Bᵢ}T)`, `∇_{Bᵢ}(∇_{[Bᵢ, Wₐ]}T)`
collected by `tensor3rdCurvBracket` (`Bochner/PointwiseTensorBochner`), summed over the
`g_x`-orthonormal frame `Bᵢ := smoothOrthoFrame g x i` and paired against `∇S`, fold — via the second
Bianchi identity (`second_bianchi_levi_civita`/`contractedBianchi`), the abstract bracket-free Ricci
identities `tensorSecondCovDeriv_antisymm_eq_riemannSec` (`TensorRicciCommutator`),
`secondCovDeriv_gradTensor_antisymm_eq_riemannOp` (`OffDiagonalCurvatureCore`) commuting the gradient
slot past the two trace slots, and the gradient-slot Leibniz frame sum
`covGradRoughLapCurv_toSection_eq_frame_sum` (`GradientSlotLeibniz`) — into the Ricci-trace carrier
`ricTraceSection` plus exactly the frame-bracket directional content carried by the engine's first slot.
The off-diagonal `±N` frame-pair error terms cancel **only in the full frame sum** (never per term / per
pair: per-pair the cancellation is false; the diagonal `R(Bᵢ, Bᵢ) = 0` is degenerate, the content is
off-diagonal). The result is that the pointwise inner product `⟨Rem S, ∇S⟩(x)` agrees almost everywhere
with the metric divergence `divᵍ X` of an honest smooth `∇S`-order tangent field `X` — the
covariant-divergence datum of the moving frame.

This curvature-folding step — exhibiting the frame-summed bracket field as a total covariant divergence
`divᵍ X` — is the genuinely-irreducible moving-frame third-order curvature content; its producer
`movingFrameBracketRemainder_integral_eq_genuineDiffCurv_ricTrace` has no producer on disk, so the
divergence datum is carried here as the single named honest debt node
`exists_movingFrameRemainder_covariantDivergence_datum`. Everything above it — the integrated nullity
and the frame-summed engine-integrand fold — is closed sorry-free on this file from that one datum.

## The engine-integrand reading

Once the remainder pairs to zero (`movingFrameRemainderSection_l2Inner_eq_zero`), the frame-summed
covariant Leibniz integral that the engine `integral_frameSummed_bracketCovDeriv_combined_eq_zero`
consumes is *also* zero for *every* choice of index family / bracket-direction fields / bracket data, so
the remainder pairing equals that integral. The top result
`movingFrameGenuineSectionsRemainder_l2Inner_eq_frameSummed_bracketIntegral` (in
`Analysis/Elliptic/.../IntegratedCurvatureCrossBound`) exhibits this with an explicit finite index family
`ι`, bracket-direction fields `V : ι → TM`, and once-derived bracket sections `W`: both sides are zero,
the genuine content being the remainder nullity carried by the covariant-divergence datum.

## Convention

Geometer convention `Δ_∇ = ∑ᵢ ∇²_{Bᵢ, Bᵢ}` (frame trace). The covariant gradient `covGrad g 0 s` raises
the tensor rank from `(0, s)` to `(0, s + 1)`. All `L²`/integral pairings are against the canonical
Riemannian volume measure `riemannianVolumeMeasure`; `divᵍ` is `divergence_g`; the inner product is the
covariant `(0, r + s)` pointwise inner product `tensorInnerPointwise` / its metric-lowered model form
`tensorInnerPointwise_0s`.
-/

noncomputable section

set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000

open Bundle Manifold Set Filter Tensor0SBundle MeasureTheory
open scoped Manifold Topology ContDiff BigOperators

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E
private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

/-- **The three-carrier remainder section equals the right-associated three-way subtraction.** The
section-level four-carrier remainder `movingFrameRemainderSection g s S = Curv S − GcurvSection −
genuineDiffCurvSection − ricTraceSection` (`MovingFrameRemainderCarrierSection`, left-associated) is the
same `(0, s + 1)`-tensor as the right-associated three-way subtraction `Curv S − GcurvSection −
(genuineDiffCurvSection + ricTraceSection)` that the `L²` cross-bound and the nullity consumers read; a
pure `sub_sub` regrouping of the four section subtractions. -/
theorem movingFrameRemainderSection_eq_sub_add
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) :
    movingFrameRemainderSection (I := I) (M := M) g s S =
      pointwiseTensorCurv (I := I) (M := M) g s S -
        GcurvSection (I := I) (M := M) g s S -
        (genuineDiffCurvSection (I := I) (M := M) g s S +
          ricTraceSection (I := I) (M := M) g s S) := by
  rw [movingFrameRemainderSection]
  abel

/-- **The covariant-divergence datum of the moving-frame three-carrier remainder (the genuinely
irreducible moving-frame third-order curvature fold).** For a closed smooth Riemannian manifold
`(M, g)`, covariant rank `s`, and smooth compactly-supported `(0, s)`-tensor `S`, there is a smooth
tangent vector field `X` whose metric divergence `divᵍ X` agrees almost everywhere (against the
Riemannian volume measure) with the pointwise metric inner product of the three-carrier remainder

```
Rem S := pointwiseTensorCurv g s S − GcurvSection g s S − (genuineDiffCurvSection g s S + ricTraceSection g s S)
```

against `∇S := covGrad g 0 s S`:

```
x ↦ ⟨Rem S (x), ∇S (x)⟩_{g(x)}   =ᵐ   x ↦ divᵍ X (x).
```

This is the **genuine moving-frame third-order Bochner–Weitzenböck curvature-folding content**: the
frame-bracket directional terms `∇_{[Bᵢ, Wₐ]}(∇_{Bᵢ}T)`, `∇_{Bᵢ}(∇_{[Bᵢ, Wₐ]}T)` collected by
`tensor3rdCurvBracket` — summed over the `g_x`-orthonormal frame `Bᵢ := smoothOrthoFrame g x i` and
paired against `∇S` — fold, via the second-Bianchi identity (`second_bianchi_levi_civita`/
`contractedBianchi`), the abstract bracket-free Ricci identities `tensorSecondCovDeriv_antisymm_eq_riemannSec`
(`TensorRicciCommutator`) and `secondCovDeriv_gradTensor_antisymm_eq_riemannOp`
(`OffDiagonalCurvatureCore`) commuting the gradient slot past the two trace slots, and the gradient-slot
Leibniz frame sum `covGradRoughLapCurv_toSection_eq_frame_sum` (`GradientSlotLeibniz`), into the Ricci
content carried by `ricTraceSection` plus a total covariant divergence `divᵍ X` of an honest smooth
`∇S`-order field. The off-diagonal `±N` frame-pair error terms cancel only in the full frame sum (never
per term / per pair: the per-pair cancellation is false and the diagonal `R(Bᵢ, Bᵢ) = 0` is degenerate),
so this is a genuine frame-summed curvature-endomorphism identity, *false* for an arbitrary triple of
subtracted fields (it holds exactly for the genuine pure-Riemann, differentiated-curvature, and
Ricci-trace carriers), and distinct from any per-carrier or cross-bound conclusion.

It is a pointwise `=ᵐ divᵍ X` statement, structurally distinct from the integrated frame-summed
engine-integrand fold it produces. Its producer
`movingFrameBracketRemainder_integral_eq_genuineDiffCurv_ricTrace` has no producer on disk; the datum is
carried here as the single named honest debt node, and the integrated nullity and engine-integrand fold
are closed sorry-free on top of it.

**Non-vacuity / soundness.** The datum is *false* for an arbitrary triple of subtracted fields on a
non-flat manifold: were every carrier replaced by `0` the divergence form would force
`⟨Curv S, ∇S⟩_{L²} = ∫ divᵍ X = 0`, while `weitzenbock_curvature_crossPairing_value` gives
`⟨Curv S, ∇S⟩_{L²} = ‖Δ_∇ S‖²_{L²} − ‖∇²S‖²_{L²} ≠ 0` (at `s = 0` it is `∫Ric(∇f, ∇f) ≠ 0`); the datum
genuinely uses all three genuine curvature carriers. -/
theorem exists_movingFrameRemainder_covariantDivergence_datum
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) :
    ∃ X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯,
      (fun x : M => tensorInnerPointwise (I := I) (M := M) g 0 (s + 1) x
            ((pointwiseTensorCurv (I := I) (M := M) g s S -
                GcurvSection (I := I) (M := M) g s S -
                (genuineDiffCurvSection (I := I) (M := M) g s S +
                  ricTraceSection (I := I) (M := M) g s S)).toFun x)
            ((covGrad (I := I) (M := M) g 0 s S).toFun x))
        =ᵐ[riemannianVolumeMeasure (I := I) (M := M) g]
      (fun x : M => divergence_g (I := I) g X x) :=
  sorry

/-- **The integrated nullity of the three-carrier moving-frame remainder, from the covariant-divergence
datum.** For a closed smooth Riemannian manifold `(M, g)`, covariant rank `s`, and smooth
compactly-supported `(0, s)`-tensor `S`, the global metric `L²` pairing of the three-carrier remainder

```
Rem S := pointwiseTensorCurv g s S − GcurvSection g s S − (genuineDiffCurvSection g s S + ricTraceSection g s S)
```

against `∇S := covGrad g 0 s S` vanishes:

```
⟨Rem S, ∇S⟩_{L²} = 0.
```

The proof is the closed-manifold divergence theorem applied to the covariant-divergence datum
`exists_movingFrameRemainder_covariantDivergence_datum`: the pointwise inner product `⟨Rem S, ∇S⟩`
agrees almost everywhere with `divᵍ X` of a smooth compactly-supported tangent field, whose integral over
the closed manifold is zero (`tensorL2Inner_movingFrameRemainder_eq_zero_of_pointwise_divergence`,
`MovingFrameRemainderDivergenceForm`, with the differentiated-curvature carrier taken to be the combined
field `genuineDiffCurvSection + ricTraceSection`). -/
theorem movingFrameRemainderSection_l2Inner_eq_zero
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) :
    tensorL2Inner (I := I) (M := M) g 0 (s + 1)
        (pointwiseTensorCurv (I := I) (M := M) g s S -
          GcurvSection (I := I) (M := M) g s S -
          (genuineDiffCurvSection (I := I) (M := M) g s S +
            ricTraceSection (I := I) (M := M) g s S)).toFun
        (covGrad (I := I) (M := M) g 0 s S).toFun = 0 := by
  obtain ⟨X, hX⟩ := exists_movingFrameRemainder_covariantDivergence_datum (I := I) (M := M) g s S
  exact tensorL2Inner_movingFrameRemainder_eq_zero_of_pointwise_divergence
    (I := I) (M := M) g s S
    (GcurvSection (I := I) (M := M) g s S)
    (genuineDiffCurvSection (I := I) (M := M) g s S +
      ricTraceSection (I := I) (M := M) g s S)
    X hX

/-- **The empty bracket data — the trivial frame-summed engine consumption witness.** For ranks
`(0, s + 1)` the frame-summed covariant Leibniz integral of `integral_frameSummed_bracketCovDeriv_combined_eq_zero`
over the empty index family `Fin 0` is the empty sum, hence `0`. This is the explicit witness exhibiting
the (engine-zero) frame-summed bracket integrand as `0` against any `Z`: the genuine content of the
summed-folding identity is the remainder nullity, while the frame-summed integrand vanishes for *every*
index family / bracket-direction / bracket-data choice (the engine sends it to zero), so the empty family
already realises the value `0` that the remainder pairing carries. -/
theorem frameSummed_bracketIntegral_empty_eq_zero
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s)
    (V : Fin 0 → Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (W : Fin 0 → SmoothCcTensor g 0 (s + 1)) :
    ∑ i, ∫ x, (tensorInnerPointwise_0s (I := I) (M := M) (0 + (s + 1)) g x
            (Tensor0SSpace.toModel
              (loweredCovDerivAlongVF (I := I) (M := M) g 0 (s + 1) (W i).toSection (V i) x))
            (Tensor0SSpace.toModel
              (liftedTensorSection (I := I) (M := M) g 0 (s + 1)
                (covGrad (I := I) (M := M) g 0 s S).toSection x))
          + tensorInnerPointwise_0s (I := I) (M := M) (0 + (s + 1)) g x
            (Tensor0SSpace.toModel
              (liftedTensorSection (I := I) (M := M) g 0 (s + 1) (W i).toSection x))
            (Tensor0SSpace.toModel
              (loweredCovDerivAlongVF (I := I) (M := M) g 0 (s + 1)
                (covGrad (I := I) (M := M) g 0 s S).toSection (V i) x))
          + tensorInnerScalar (I := I) (M := M) g 0 (s + 1) (W i).toSection
              (covGrad (I := I) (M := M) g 0 s S).toSection x
            * divergence_g (I := I) g (V i) x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) = 0 := by
  simp only [Finset.univ_eq_empty, Finset.sum_empty]

end Connection
end Integral
end DifferentialGeometry

end
