import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.MovingFrameDiffCurvTraceSection

/-!
# The frame-summed integrand of the moving-frame remainder pairing

For a closed (compact, boundaryless) smooth Riemannian manifold `(M, g)` this file builds the
**frame-summed pointwise integrand** of the curvature cross-pairing `⟨Curv S, ∇S⟩_{L²}` of the
rank-generic order-`2` rough-Laplacian / covariant-gradient commutator defect
`Curv S := Δ_∇(∇S) − ∇(Δ_∇ S)` (`pointwiseTensorCurv g s S`, `∇S = covGrad g 0 s S`), and reduces the
curvature line's terminal quantitative leaf `genuineCurvFields_residue_eq_weitzenbockValue` to a single
strictly-smaller integrated identity.

## The frame-summand decomposition of the integrand

The sorry-free representation `pointwiseTensorCurv_toSection_eq_frame_sum`
(`Bochner/PointwiseTensorBochner`) reads the defect, at every point `x` and over the `g_x`-orthonormal
frame `Bᵢ := smoothOrthoFrame g x i`, as the fixed-frame sum of the **per-summand third-order
difference**
```
remDiffFib g s S x i
  := ∇²_{Bᵢ, Bᵢ}(∇S)(x) − covGradBundleEquiv 0 s x (∇·(∇²_{Bᵢ, Bᵢ} S)(x)),
```
the gradient-slot reordering of the three covariant-derivative slots (the genuine off-diagonal Riemann
curvature). Pairing against `∇S(x)` and distributing the metric inner product over the frame sum gives
the **integrand frame-sum identity** (`pointwiseTensorCurvPairing_eq_frameSum`):
```
⟨Curv S, ∇S⟩(x) = ∑ᵢ ⟨remDiffFib g s S x i, ∇S(x)⟩.
```
This is the genuinely-new structural content of the divergence-current program: it exhibits the
pointwise integrand of the curvature cross-pairing as a fixed-frame sum of per-direction third-order
differences, the starting point for the frame-summed Ricci-commutation / integration-by-parts
telescoping that carries the remainder pairing to zero.

## The reduction of the terminal leaf

The leaf `genuineCurvFields_residue_eq_weitzenbockValue` is — through the two sorry-free bridges
`genuineCurvFields_crossPairing_eq_residue` (the three-pairing residue equals
`⟨GcurvSection + genuineDiffCurvSection, ∇S⟩_{L²}`) and `weitzenbock_curvature_crossPairing_value`
(`⟨Curv S, ∇S⟩_{L²} = ‖Δ_∇S‖²_{L²} − ‖∇²S‖²_{L²}`) — equivalent to the genuine curvature-fields value
```
⟨GcurvSection g s S + genuineDiffCurvSection g s S, ∇S⟩_{L²} = ⟨Curv S, ∇S⟩_{L²}.   (★)
```
`genuineCurvFields_residue_of_genuineFieldsValue` records this reduction (sorry-free): the leaf-shaped
conclusion follows from `(★)` by the two bridges and `ring`. `(★)` is the integrated form of the
classical Bochner curvature-term identity — the curvature line's irreducible third-order
Weitzenböck content (the genuine fields carry the entire defect cross-pairing) — left here as the
single coupled posit `genuineCurvFields_value_frameSummedWeitzenbock`, the integrated frame-summed
Ricci-commutation identity, strictly below the leaf's residue/value packaging.

## Main results

* `remDiffFib` — the per-summand third-order difference field (the `i`-th summand of representation
  (A)).
* `pointwiseTensorCurvPairing_eq_frameSum` — **sorry-free**: the pointwise integrand of
  `⟨Curv S, ∇S⟩` is the frame sum of the per-summand pairings `⟨remDiffFib …, ∇S⟩`.
* `genuineCurvFields_residue_of_genuineFieldsValue` — **sorry-free**: the leaf statement follows from
  the genuine curvature-fields value `(★)` via the two on-disk bridges.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 1200000
set_option maxHeartbeats 1600000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

/-- **The per-summand third-order difference field of representation (A).** At a point `x`, with the
`g_x`-orthonormal frame `Bᵢ := smoothOrthoFrame g x i`, the `i`-th summand of the fixed-frame
representation `pointwiseTensorCurv_toSection_eq_frame_sum` of the order-`2` commutator defect:
```
remDiffFib g s S x i
  := ∇²_{Bᵢ, Bᵢ}(∇S)(x) − covGradBundleEquiv 0 s x (∇·(∇²_{Bᵢ, Bᵢ} S)(x)),
```
the difference of the rank-`(0, s + 1)` second covariant derivative of the gradient tensor
`∇S = covGrad g 0 s S` and the `(0, s + 1)`-tensor covariant gradient of the rank-`(0, s)` second
covariant derivative `∇²_{Bᵢ, Bᵢ} S`. It is the gradient-slot reordering of the three covariant
derivative slots — the genuine off-diagonal Riemann curvature, the per-direction third-order
Bochner–Weitzenböck term. -/
def remDiffFib (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) (x : M)
    (i : Fin (Module.finrank ℝ E)) : TensorRSSpace 0 (s + 1) I x :=
  tensorSecondCovDeriv (I := I) g 0 (s + 1)
      (smoothOrthoFrame (I := I) g x i) (smoothOrthoFrame (I := I) g x i)
      (fun y : M => (covGrad (I := I) (M := M) g 0 s S).toSection y) x -
    covGradBundleEquiv (I := I) (M := M) 0 s x
      ((tensorCov (I := I) g 0 s).toFun
        (fun y : M => tensorSecondCovDeriv (I := I) g 0 s
          (smoothOrthoFrame (I := I) g x i) (smoothOrthoFrame (I := I) g x i)
          (fun z : M => S.toSection z) y) x)

/-- **The frame-summand integrand identity (sorry-free).** For a closed smooth Riemannian manifold
`(M, g)`, covariant rank `s`, smooth compactly-supported `(0, s)`-tensor `S`, and point `x`, the
pointwise metric inner product of the order-`2` commutator defect `Curv S := pointwiseTensorCurv g s S`
against the gradient field `∇S := covGrad g 0 s S` — the integrand of the curvature cross-pairing
`⟨Curv S, ∇S⟩_{L²}` — is the fixed-frame sum of the per-summand pairings of the third-order difference
fields against `∇S`:
```
⟨Curv S, ∇S⟩(x) = ∑ᵢ ⟨remDiffFib g s S x i, ∇S(x)⟩,   Bᵢ := smoothOrthoFrame g x i.
```

**Proof (sorry-free).** Read the defect at `x` by the fixed-frame representation
`pointwiseTensorCurv_toSection_eq_frame_sum`, push the model coercion through the frame sum by
additivity of `TensorRSSpace.toModel`, and distribute the pointwise metric inner product over the frame
sum by `tensorInnerPointwise_sum_left`. No moving-frame derivative and no curvature input is used — this
is the purely structural integrand decomposition. -/
theorem pointwiseTensorCurvPairing_eq_frameSum
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) (x : M) :
    tensorInnerPointwise (I := I) (M := M) g 0 (s + 1) x
        ((pointwiseTensorCurv (I := I) (M := M) g s S).toFun x)
        ((covGrad (I := I) (M := M) g 0 s S).toFun x) =
      ∑ i : Fin (Module.finrank ℝ E),
        tensorInnerPointwise (I := I) (M := M) g 0 (s + 1) x
          (TensorRSSpace.toModel (remDiffFib (I := I) (M := M) g s S x i))
          ((covGrad (I := I) (M := M) g 0 s S).toFun x) := by
  classical
  have hCurv : (pointwiseTensorCurv (I := I) (M := M) g s S).toFun x =
      TensorRSSpace.toModel ((pointwiseTensorCurv (I := I) (M := M) g s S).toSection x) := rfl
  have htoM : TensorRSSpace.toModel
        (∑ i : Fin (Module.finrank ℝ E), remDiffFib (I := I) (M := M) g s S x i) =
      ∑ i : Fin (Module.finrank ℝ E),
        TensorRSSpace.toModel (remDiffFib (I := I) (M := M) g s S x i) := by
    induction (Finset.univ : Finset (Fin (Module.finrank ℝ E))) using Finset.induction with
    | empty => simp [TensorRSSpace.toModel_zero]
    | insert i₀ s'' hi₀ ih =>
        rw [Finset.sum_insert hi₀, TensorRSSpace.toModel_add, ih, Finset.sum_insert hi₀]
  rw [hCurv, pointwiseTensorCurv_toSection_eq_frame_sum (I := I) (M := M) g s S x]
  rw [show (∑ i : Fin (Module.finrank ℝ E),
        (tensorSecondCovDeriv (I := I) g 0 (s + 1)
            (smoothOrthoFrame (I := I) g x i) (smoothOrthoFrame (I := I) g x i)
            (fun y : M => (covGrad (I := I) (M := M) g 0 s S).toSection y) x -
          covGradBundleEquiv (I := I) (M := M) 0 s x
            ((tensorCov (I := I) g 0 s).toFun
              (fun y : M => tensorSecondCovDeriv (I := I) g 0 s
                (smoothOrthoFrame (I := I) g x i) (smoothOrthoFrame (I := I) g x i)
                (fun z : M => S.toSection z) y) x))) =
      ∑ i : Fin (Module.finrank ℝ E), remDiffFib (I := I) (M := M) g s S x i from rfl]
  rw [htoM]
  rw [show (∑ i : Fin (Module.finrank ℝ E),
        TensorRSSpace.toModel (remDiffFib (I := I) (M := M) g s S x i)) =
      ∑ i : Fin (Module.finrank ℝ E), (1 : ℝ) •
        TensorRSSpace.toModel (remDiffFib (I := I) (M := M) g s S x i) from by
    refine Finset.sum_congr rfl (fun i _ => ?_); rw [one_smul]]
  rw [tensorInnerPointwise_sum_left (I := I) (M := M) g 0 (s + 1) x Finset.univ]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [one_mul]

/-- **The genuine curvature-fields value implies the terminal-leaf statement (sorry-free reduction).**
For a closed smooth Riemannian manifold `(M, g)`, covariant rank `s`, and smooth compactly-supported
`(0, s)`-tensor `S`, suppose the genuine curvature-fields value `(★)` holds — the global metric `L²`
pairing of `GcurvSection g s S + genuineDiffCurvSection g s S` against `∇S := covGrad g 0 s S` equals
the cross-pairing of the order-`2` commutator defect `Curv S := pointwiseTensorCurv g s S` against `∇S`:
```
⟨GcurvSection g s S + genuineDiffCurvSection g s S, ∇S⟩_{L²} = ⟨Curv S, ∇S⟩_{L²}.   (★)
```
Then the curvature line's terminal quantitative leaf statement holds — the explicit three-pairing
curvature residue equals the integrated Weitzenböck value `‖Δ_∇S‖²_{L²} − ‖∇²S‖²_{L²}`.

**Proof (sorry-free composition over two on-disk bridges).** The left-hand residue equals
`⟨GcurvSection + genuineDiffCurvSection, ∇S⟩_{L²}` by the sorry-free bookkeeping bridge
`genuineCurvFields_crossPairing_eq_residue` (run backwards); rewriting by `(★)` turns the goal into
`⟨Curv S, ∇S⟩_{L²} = ‖Δ_∇S‖²_{L²} − ‖∇²S‖²_{L²}`, which is exactly
`weitzenbock_curvature_crossPairing_value` (sorry-free). No curvature input of this file's own is
consumed; it is the algebraic reduction of the leaf to the value `(★)`. -/
theorem genuineCurvFields_residue_of_genuineFieldsValue
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s)
    (hstar : tensorL2Inner (I := I) (M := M) g 0 (s + 1)
        (GcurvSection (I := I) (M := M) g s S +
          genuineDiffCurvSection (I := I) (M := M) g s S).toFun
        (covGrad (I := I) (M := M) g 0 s S).toFun =
      tensorL2Inner (I := I) (M := M) g 0 (s + 1)
        (pointwiseTensorCurv (I := I) (M := M) g s S).toFun
        (covGrad (I := I) (M := M) g 0 s S).toFun) :
    tensorL2Inner (I := I) (M := M) g 0 (s + 1)
          (pureRGenuineDiffOp (I := I) (M := M) g 0 (s + 1)
            (covGrad (I := I) (M := M) g 0 s S)).toFun
          (covGrad (I := I) (M := M) g 0 s S).toFun -
        tensorL2Inner (I := I) (M := M) g 0 s
            (rawTensorConnLapSmooth (I := I) g 0 s
              (pureRGenuineDiffOp (I := I) (M := M) g 0 s S)).toFun S.toFun -
          tensorL2Inner (I := I) (M := M) g 0 (s + 1)
            (appCc (I := I) (M := M) g (s + 1) (s + 1)
              (slotExtend (I := I) (M := M) g (s + 0) (s + 0)
                (curvOpField (I := I) (M := M) g s))
              (covGrad (I := I) (M := M) g 0 s S)).toFun
            (covGrad (I := I) (M := M) g 0 s S).toFun =
      tensorL2Norm (I := I) (M := M) g 0 s
          (rawTensorConnLapSmooth (I := I) g 0 s S).toFun ^ 2 -
        tensorL2Norm (I := I) (M := M) g 0 (s + 1 + 1)
          (covGrad (I := I) (M := M) g 0 (s + 1)
            (covGrad (I := I) (M := M) g 0 s S)).toFun ^ 2 := by
  rw [← genuineCurvFields_crossPairing_eq_residue (I := I) (M := M) g s S]
  rw [hstar]
  exact weitzenbock_curvature_crossPairing_value (I := I) (M := M) g s S

end Connection
end Integral
end DifferentialGeometry

end
