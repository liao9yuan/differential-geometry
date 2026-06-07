import DifferentialGeometry.Geometry.Curvature.Bochner.PointwiseTensorBochnerFieldSplit
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.IntegratedOrder2WeitzenbockCurvature
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RiemannianFiberNormSq.UniformCurvatureSup
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.FrozenFramePureRCurvatureTower

/-!
# The fibre order of the order-`2` rough-Laplacian / covariant-gradient commutator defect

For a closed (compact, boundaryless) smooth Riemannian manifold `(M, g)` this file isolates the single
genuinely-irreducible quantitative fibre atom of the rank-generic order-`2` rough-Laplacian /
covariant-gradient commutator defect

```
Curv S := Δ_∇(∇S) − ∇(Δ_∇ S)
```

(`pointwiseTensorCurv g s S`, a `(0, s + 1)`-tensor field; `∇S = covGrad g 0 s S`): **the defect is
order-`≤ 2` in `S`**, with a *valence-dependent* uniform fibre bound by the sum of the fibre norms of
`∇²S`, `∇S` and `S`.

## Why this is the irreducible fibre atom (the iterated Ricci identity controls the defect)

By definition `Curv S = Δ_∇(∇S) − ∇(Δ_∇ S)` (`Bochner/PointwiseTensorBochner`), the rough Laplacian of
the gradient field minus the gradient of the rough Laplacian. Reading both as fixed-`g`-orthonormal-frame
traces of the second covariant derivative and commuting the two derivative slots by the rank-`(0, s + 1)`
Ricci identity `secondCovDeriv_covGrad_antisymm_eq_riemannOp_gen` (`IntegratedOrder2WeitzenbockCurvature`),
the top-order `∇³S` terms cancel: the difference is a sum of curvature contractions of the gradient field
`R(∇S)` (each fibre-bounded by `‖R‖_∞ · rfns(∇S)` via the uniform curvature fibre bound
`riemannOp_covGrad_fiberNormSq_le_gen`), plus genuine `(∇R) S` and frame-derivative terms of
`rfns(S)`-order, plus a residual `∇²S`-order moving-frame remainder (`tensor3rdCurvBracket`, the
frame-bracket discrepancy of the field split `pointwiseTensorCurv_toSection_eq_genuine_add_bracket_field`).
Aggregating the three over the finite frame with the per-point curvature sup made *uniform* over `M` by
compactness (`exists_uniform_riemannianFiberNormSq_covGrad_riemannOp_bound`, the curvature-operator
`g`-norm sup) gives the single nonnegative valence-dependent constant `C`. The `∇³S`-cancellation is
*false term-by-term* through the non-tensorial `smoothExtensionTangent` reading (chart-selection-unbounded
on `S²`); only the intrinsic frame-summed defect is `∇²S`-order.

## Main result

* `exists_pointwiseTensorCurv_fiberOrder_bound` — the **order-`2` commutator-defect fibre order**: a
  *valence-dependent* nonnegative constant `C : ℕ → ℝ` such that at every covariant rank `s`, every
  smooth compactly-supported `(0, s)`-tensor `S`, and *every point* `x`,
  ```
  rfns(Curv S)(x) ≤ (C s)² · ( rfns(∇²S)(x) + rfns(∇S)(x) + rfns(S)(x) ).
  ```
  It is the genuine quantitative fibre atom of the curvature line, homed *upstream* of the moving-frame
  spine so the four-carrier remainder fibre bound and the genuine-fields fibre decomposition consume it
  without an import cycle through the downstream `L²` chain.

## Convention

Geometer convention `Δ_∇ = ∑ᵢ ∇²_{Bᵢ, Bᵢ}` (frame trace). All fibre norms are the intrinsic Riemannian
fibre norm `riemannianFiberNormSq` (`rfns`).
-/

noncomputable section

set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1600000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.PDE.RicciFlow

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

/-- **Posited genuine moving-frame remainder fibre order (the order-`2` commutator defect with the
pure-Riemann channel peeled off).** For a closed smooth Riemannian manifold `(M, g)` there is a
*valence-dependent* nonnegative constant `C : ℕ → ℝ` such that, at every covariant rank `s`, every smooth
compactly-supported `(0, s)`-tensor `S`, and *every point* `x`, the intrinsic fibre norm of the
moving-frame remainder `Curv S − GcurvSection g s S` of the order-`2` rough-Laplacian /
covariant-gradient commutator defect `Curv S := pointwiseTensorCurv g s S`, with the concrete
pure-Riemann `R(∇S)` trace `GcurvSection g s S` subtracted off, is bounded by `(C s)²` times the **sum**
of the intrinsic fibre norms of `∇²S`, `∇S` and `S`:
```
rfns(Curv S − GcurvSection g s S)(x)
  ≤ (C s)² · ( rfns(∇²S)(x) + rfns(∇S)(x) + rfns(S)(x) ).
```

**This is the genuine, strictly-smaller, irreducible pointwise content of the curvature-defect fibre
order — the differentiated-curvature `(∇R) S` channel plus the moving-frame / frame-bracket discrepancy,
with the pure-Riemann channel removed.** The aggregate fibre order
`exists_pointwiseTensorCurv_fiberOrder_bound` is proved by composition over it: the pure-Riemann part
`GcurvSection g s S` is fibre-bounded *sorry-free* by `(c s 0)² · rfns(∇S)(x)` through the moving-centre
pure-Riemann curvature-jet grid bound `exists_GcurvSection_iteratedCovGrad_grid_bound`
(`FrozenFramePureRCurvatureTower`) at gradient order `k = 0`, and the two contributions are merged by
fibre subadditivity `riemannianFiberNormSq_add_le` on `Curv S = GcurvSection g s S + (Curv S −
GcurvSection g s S)`.

**Why it is the genuine missing content (the `∇³S`-cancellation is fenced).** By the explicit field-level
genuine + bracket split `pointwiseTensorCurv_toSection_eq_genuine_add_bracket_field`, the defect's section
value reconstructs, in the slot-`0` witness frame, as the genuine third-order curvature field
`genuineThirdCurvFieldFib` (the `R(∇S)` and `(∇R) S` contractions) plus the obstruction field
`bracketThirdCurvFieldFib` (the bracket discrepancy `tensor3rdCurvBracket`, the moving-frame trace
discrepancy `covGradRoughLapTraceDiscrepancy_gen`, and the moving-frame residual
`covGradRoughLapMovingFrameResidual_gen`). After the pure-Riemann `R(∇S)` channel (the concrete frame-free
`GcurvSection`) is removed, the surviving remainder carries the differentiated-curvature `(∇R) S` term
(genuinely `rfns(S)`-order, the `tensor3rdCurvGenuine` covariant-derivative summand) and the bracket
obstruction (genuinely `rfns(∇²S)`-order after the iterated Ricci identity
`secondCovDeriv_covGrad_antisymm_eq_riemannOp_gen` cancels the top-order `∇³S` terms). The `∇³S`-cancellation
and the `∇²S`-order bound of the bracket discrepancy are *false term-by-term* through the non-tensorial
`smoothExtensionTangent` reading (chart-selection-unbounded on `S²`); only the intrinsic frame-summed
remainder is `∇²S`-order, and the bracket/discrepancy/residual have no sorry-free fibre bound below this
file. The bound is stated for the intrinsic fibre norm `rfns` of the single tensor `Curv S −
GcurvSection g s S` throughout (never a per-direction `M → E` quantity), so it is trap-screened.

**Non-vacuity (the `s = 0` litmus).** With `C s = 0` the bound forces `rfns(Curv S − GcurvSection g s
S)(x) = 0`. At `s = 0` the pure-Riemann trace vanishes (`GcurvSection g 0 f` is the curvature of a scalar,
which vanishes), so the bound would force `Curv f = 0` pointwise — false on a non-flat manifold for a
non-harmonic `f` (the scalar commutator defect is `Curv f = Ric(∇f, ·)` integrated, nonzero when
curvature is present, `ricTraceSection_zero_apply`, `weitzenbock_integrated_covGrad_l2_normSq`). So `C` is
genuinely positive. The body is `sorry` (the genuine classical moving-frame third-order curvature content:
the `∇³S` cancellation followed by the differentiated-curvature and bracket-discrepancy fibre sups);
consumers transitively depend on `sorryAx`. -/
theorem exists_pointwiseTensorCurv_subGcurv_obstruction_fiberOrder_bound
    (g : SmoothRiemannianMetric I M) :
    ∃ C : ℕ → ℝ, (∀ s, 0 ≤ C s) ∧
      ∀ (s : ℕ) (S : SmoothCcTensor g 0 s) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
            ((pointwiseTensorCurv (I := I) (M := M) g s S -
              GcurvSection (I := I) (M := M) g s S).toSection x) ≤
          C s ^ 2 *
            (riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1 + 1) x
                ((covGrad (I := I) (M := M) g 0 (s + 1)
                  (covGrad (I := I) (M := M) g 0 s S)).toSection x) +
              riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
                  ((covGrad (I := I) (M := M) g 0 s S).toSection x) +
              riemannianFiberNormSq (I := I) (M := M) g 0 s x (S.toSection x)) := by
  sorry

/-- **The order-`2` commutator-defect fibre order (the curvature line's irreducible quantitative atom,
posited upstream of the moving-frame spine).** For a closed smooth Riemannian manifold `(M, g)` there is
a *valence-dependent* nonnegative constant `C : ℕ → ℝ` such that, at every covariant rank `s`, for every
smooth compactly-supported `(0, s)`-tensor `S`, and at *every point* `x`, the intrinsic fibre norm of the
order-`2` rough-Laplacian / covariant-gradient commutator defect `Curv S := pointwiseTensorCurv g s S` is
bounded by `(C s)²` times the **sum** of the intrinsic fibre norms of `∇²S = covGrad g 0 (s + 1)
(covGrad g 0 s S)`, `∇S = covGrad g 0 s S` and `S`:
```
rfns(Curv S)(x) ≤ (C s)² · ( rfns(∇²S)(x) + rfns(∇S)(x) + rfns(S)(x) ).
```

**Why this is TRUE — the iterated Ricci identity controls the commutator defect.** By definition
`Curv S = Δ_∇(∇S) − ∇(Δ_∇ S)` (`Bochner/PointwiseTensorBochner`), the rough Laplacian of the gradient
field minus the gradient of the rough Laplacian. Reading both as fixed-`g`-orthonormal-frame traces of
the second covariant derivative (`rawTensorConnLap_eq_frame_trace_secondCovDeriv`) and commuting the two
derivative slots by the rank-`(0, s + 1)` Ricci identity `secondCovDeriv_covGrad_antisymm_eq_riemannOp_gen`
(`IntegratedOrder2WeitzenbockCurvature`), the top-order `∇³S` terms cancel: the difference is a sum of
(i) curvature contractions of the gradient field `R(∇S)`, each fibre-bounded by `‖R‖_∞ · rfns(∇S)` via
the uniform curvature fibre bound `riemannOp_covGrad_fiberNormSq_le_gen`, plus (ii) genuine `(∇R) S` and
frame-derivative terms of `rfns(S)`-order (the `tensor3rdCurvGenuine` covariant-derivative summand), plus
(iii) a residual `∇²S`-order moving-frame remainder (`tensor3rdCurvBracket`, the frame-bracket discrepancy
of the field split `pointwiseTensorCurv_toSection_eq_genuine_add_bracket_field`). Aggregating the three
over the finite frame with the per-point curvature sup made *uniform* over `M` by compactness
(`exists_uniform_riemannianFiberNormSq_covGrad_riemannOp_bound`, the curvature-operator `g`-norm sup)
gives the single nonnegative valence-dependent `C`.

**Why the pointwise per-direction split is fenced.** The `∇³S`-cancellation is *false term-by-term*
through the non-tensorial `smoothExtensionTangent` reading (chart-selection-unbounded on `S²`); only the
intrinsic frame-summed defect is `∇²S`-order. The bound is stated for the intrinsic fibre norm `rfns` of
the single tensor `pointwiseTensorCurv g s S` throughout — it never extracts a per-direction `M → E`
quantity — so it is trap-screened.

**Non-vacuity (the bound rejects the degenerate `C ≡ 0` on a non-flat manifold).** With `C s = 0` the
bound would force `rfns(Curv S)(x) = 0`, i.e. `Δ_∇(∇S) = ∇(Δ_∇ S)` at every point — the covariant
derivatives commute through the rough Laplacian. This is *false* on a non-flat manifold (`R ≠ 0`) for a
non-parallel `S`: the commutator defect `Curv S` is exactly the genuine third-order Weitzenböck curvature
field `⟨Curv S, ∇S⟩_{L²} = ‖Δ_∇ S‖²_{L²} − ‖∇²S‖²_{L²}` (`weitzenbock_integrated_covGrad_l2_normSq`),
nonzero when curvature is present. So `C` is genuinely positive.

**Proof (composition over the moving-frame remainder fibre order).** This is now proved by composition,
peeling the pure-Riemann channel *sorry-free*. The defect splits as
`Curv S = GcurvSection g s S + (Curv S − GcurvSection g s S)` (the section identity is `sub_add_cancel`),
so by fibre subadditivity `riemannianFiberNormSq_add_le` the fibre norm of `Curv S` is bounded by twice
the fibre norm of the pure-Riemann trace `GcurvSection g s S` plus twice that of the moving-frame
remainder `Curv S − GcurvSection g s S`. The pure-Riemann fibre norm is bounded *sorry-free* by
`(c s 0)² · rfns(∇S)(x)` via the moving-centre pure-Riemann curvature-jet grid bound
`exists_GcurvSection_iteratedCovGrad_grid_bound` (`FrozenFramePureRCurvatureTower`) specialised to
gradient order `k = 0` (where `∇^0 (GcurvSection) = GcurvSection` and the single-term sum reads
`rfns(∇S)`), and the moving-frame remainder fibre norm is bounded by the posited genuine remainder fibre
order `exists_pointwiseTensorCurv_subGcurv_obstruction_fiberOrder_bound` (the `(∇R) S` channel plus the
bracket / discrepancy / residual after the `∇³S` cancellation). Taking `C s := 2 · max (c s 0) (Cobs s)`
absorbs both contributions, since every fibre norm on the right is nonnegative. Consumers transitively
depend on the posited remainder's `sorryAx`. -/
theorem exists_pointwiseTensorCurv_fiberOrder_bound
    (g : SmoothRiemannianMetric I M) :
    ∃ C : ℕ → ℝ, (∀ s, 0 ≤ C s) ∧
      ∀ (s : ℕ) (S : SmoothCcTensor g 0 s) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
            ((pointwiseTensorCurv (I := I) (M := M) g s S).toSection x) ≤
          C s ^ 2 *
            (riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1 + 1) x
                ((covGrad (I := I) (M := M) g 0 (s + 1)
                  (covGrad (I := I) (M := M) g 0 s S)).toSection x) +
              riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
                  ((covGrad (I := I) (M := M) g 0 s S).toSection x) +
              riemannianFiberNormSq (I := I) (M := M) g 0 s x (S.toSection x)) := by
  classical
  obtain ⟨c, hc_nn, hc⟩ := exists_GcurvSection_iteratedCovGrad_grid_bound (I := I) (M := M) g
  obtain ⟨Cobs, hCobs_nn, hCobs⟩ :=
    exists_pointwiseTensorCurv_subGcurv_obstruction_fiberOrder_bound (I := I) (M := M) g
  refine ⟨fun s => Real.sqrt (2 * (c s 0) ^ 2 + 2 * (Cobs s) ^ 2),
    fun s => Real.sqrt_nonneg _, fun s S x => ?_⟩
  -- Abbreviations for the three nonnegative fibre-norm orders on the right.
  set A : ℝ := riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1 + 1) x
      ((covGrad (I := I) (M := M) g 0 (s + 1)
        (covGrad (I := I) (M := M) g 0 s S)).toSection x) with hA
  set B : ℝ := riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
      ((covGrad (I := I) (M := M) g 0 s S).toSection x) with hB
  set D : ℝ := riemannianFiberNormSq (I := I) (M := M) g 0 s x (S.toSection x) with hD
  have hA_nn : 0 ≤ A := riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 (s + 1 + 1) x _
  have hB_nn : 0 ≤ B := riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 (s + 1) x _
  have hD_nn : 0 ≤ D := riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 s x _
  -- The defect splits as the pure-Riemann trace plus the moving-frame remainder.
  have hsub_apply : (pointwiseTensorCurv (I := I) (M := M) g s S -
        GcurvSection (I := I) (M := M) g s S).toSection x =
      (pointwiseTensorCurv (I := I) (M := M) g s S).toSection x -
        (GcurvSection (I := I) (M := M) g s S).toSection x := by
    rw [SmoothCcTensor.toSection_sub]; rfl
  have hsplit : (pointwiseTensorCurv (I := I) (M := M) g s S).toSection x =
      (GcurvSection (I := I) (M := M) g s S).toSection x +
        (pointwiseTensorCurv (I := I) (M := M) g s S -
          GcurvSection (I := I) (M := M) g s S).toSection x := by
    rw [hsub_apply]; abel
  -- Fibre subadditivity over the split.
  have hadd := riemannianFiberNormSq_add_le (I := I) (M := M) g 0 (s + 1) x
    ((GcurvSection (I := I) (M := M) g s S).toSection x)
    ((pointwiseTensorCurv (I := I) (M := M) g s S -
      GcurvSection (I := I) (M := M) g s S).toSection x)
  rw [← hsplit] at hadd
  -- The pure-Riemann fibre bound, sorry-free, at gradient order `k = 0`.
  have hG := hc s S 0 x
  rw [iteratedCovGrad_zero (I := I) (M := M) g 0 (s + 1)
    (GcurvSection (I := I) (M := M) g s S)] at hG
  -- The contracted-order sum `∑_{i < 1}` collapses to the single `rfns(∇S)` term.
  rw [Finset.sum_range_one] at hG
  rw [iteratedCovGrad_succ (I := I) (M := M) g 0 s 0 S,
    iteratedCovGrad_zero (I := I) (M := M) g 0 s S] at hG
  -- Normalise the trivial rank reassociation `(s + 1) + 0 = s + 1`.
  simp only [Nat.add_zero] at hG
  rw [← hB] at hG
  -- The moving-frame remainder fibre bound (the posited genuine child).
  have hR := hCobs s S x
  rw [← hA, ← hB, ← hD] at hR
  -- Assemble: `rfns(Curv) ≤ 2·rfns(Gcurv) + 2·rfns(rem) ≤ 2c²·B + 2Cobs²·(A+B+D) ≤ C²·(A+B+D)`.
  have hCsq : (Real.sqrt (2 * (c s 0) ^ 2 + 2 * (Cobs s) ^ 2)) ^ 2 =
      2 * (c s 0) ^ 2 + 2 * (Cobs s) ^ 2 := by
    rw [Real.sq_sqrt]
    positivity
  rw [hCsq]
  calc riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
          ((pointwiseTensorCurv (I := I) (M := M) g s S).toSection x)
      ≤ 2 * riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
            ((GcurvSection (I := I) (M := M) g s S).toSection x) +
          2 * riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
            ((pointwiseTensorCurv (I := I) (M := M) g s S -
              GcurvSection (I := I) (M := M) g s S).toSection x) := hadd
    _ ≤ 2 * ((c s 0) ^ 2 * B) + 2 * ((Cobs s) ^ 2 * (A + B + D)) :=
        add_le_add (by linarith [hG]) (by linarith [hR])
    _ ≤ (2 * (c s 0) ^ 2 + 2 * (Cobs s) ^ 2) * (A + B + D) := by
        nlinarith [hA_nn, hD_nn, sq_nonneg (c s 0)]

end Connection
end Integral
end DifferentialGeometry

end
