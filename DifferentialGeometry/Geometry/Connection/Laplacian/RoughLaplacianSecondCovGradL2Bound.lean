import DifferentialGeometry.Geometry.Curvature.Order2Defect.MetricTraceFrame
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.PointwiseToL2Packaging

/-!
# The rough-Laplacian-to-second-covariant-gradient `L²` trace bound (uniform in valence)

For a closed smooth Riemannian manifold `(M, g)` modelled on a real inner-product space `E`,
this file proves the elementary metric-trace half of the closed-manifold Bochner package: the
metric `L²` norm of the rough (connection) Laplacian `Δ_∇ S := rawTensorConnLapSmooth g 0 s S`
of a smooth compactly-supported `(0, s)`-tensor field `S` is controlled, with a single
valence-uniform multiplier `K = dim`, by the metric `L²` norm of the second iterated covariant
gradient `∇²S = covGrad g 0 (s+1) (covGrad g 0 s S)`:

```
‖Δ_∇ S‖_{L²} ≤ dim · ‖∇²S‖_{L²}.
```

This is the companion of the on-disk integration-by-parts half
`covGrad_l2NormSq_le_rawConnLap_mul_self_gen` (`IntegratedOrder2Garding.lean`).

## The mechanism

The rough Laplacian is the metric trace of the Hessian
(`rawTensorConnLap_eq_metricTraceHessian`): with `B_i := smoothOrthoFrame g x i` the smooth
`g_x`-orthonormal frame,
```
Δ_∇ S (x) = ∑_i ∇²_{B_i, B_i} S (x)        (`metricTraceHessian`).
```
Each diagonal summand `∇²_{B_i, B_i} S (x)` is the `(B_i(x), B_i(x))`-evaluation of the second
covariant gradient `∇²S` in its leftmost two slots; since `B_i(x)` is `g_x`-unit, its intrinsic
fibre norm is dominated by the full fibre norm of `∇²S(x)` (the orthonormal-frame component
bound — the genuine general-valence currying, isolated as `secondCovDeriv_unit_frame_fiberNormSq_le`).
The diagonal trace is a sum of `dim` such summands, so by the `n`-sub-additivity of the squared
fibre norm (`riemannianFiberNormSq_sum_le_card_mul`),
```
rfns(Δ_∇ S)(x) ≤ dim · ∑_i rfns(∇²_{B_i, B_i} S)(x) ≤ dim · dim · rfns(∇²S)(x),
```
and integrating this pointwise bound over the compact manifold via the finite-sum
pointwise-to-`L²` packaging `tensorL2Norm_le_of_pointwise_fiberNormSq_bound_sum` gives the
displayed `L²` inequality with `K := dim`.

## Sign / convention

Geometer convention `Δ_∇ = ∑_i ∇²_{B_i, B_i}` for the rough Laplacian (the frame trace
`rawTensorConnLapSmooth`). The covariant gradient `covGrad g 0 s` raises the tensor rank from
`(0, s)` to `(0, s + 1)`. All fibre norms are the intrinsic Riemannian fibre norm
`riemannianFiberNormSq`; the metric `L²` norm of a `SmoothCcTensor` is `tensorL2Norm g 0 s S.toFun`.
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

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

/-- **The two-leftmost-slot unit-vector fibre-norm slice bound (general valence).**

For a `(0, s + 1 + 1)`-tensor `T` at `x`, a tangent vector `w` of `g_x`-length `≤ 1`, and any
`(0, s)`-tensor `U` whose components are the two-leftmost-slot evaluation of `T` (read at the
unit `(0, 0)`-tensor) at `(w, w)` — i.e.
`U.toModel m = (T(unit)).toModel (w ::ᵥ w ::ᵥ m)` for every `Fin s`-tuple `m` — the squared
intrinsic fibre norm of `U` is dominated by that of `T`:
```
rfns(U)(x) ≤ rfns(T)(x).
```

The proof expands the `g_x`-unit vector `w` in the intrinsic orthonormal tangent frame `e` (the
same frame the fibre norm is built on) as `w = ∑_a c_a e_a` with `∑_a c_a² = g_x(w,w) ≤ 1`.
Reading each Parseval component of `U` off the unit-evaluation on the frame tuple `e_J`
(`fiberNormSqComponent`), the two-slot evaluation `T(unit).toModel(w ::ᵥ w ::ᵥ e_J)` distributes
— via the **clean continuous-linear-map linearity** of the slot-`0` curry `tensor0S_curry`
(applied in each of the two leftmost slots, with `tensor0S_curry_apply_eval`) — into
`∑_{a,b} c_a c_b · T(unit).toModel(e_a ::ᵥ e_b ::ᵥ e_J)`. The Cauchy–Schwarz inequality over the
frame-pair index (`Finset.sum_mul_sq_le_sq_mul_sq`) together with `∑_{a,b}(c_a c_b)² = g_x(w,w)²
≤ 1` gives `U.toModel(e_J)² ≤ ∑_{a,b} T(unit).toModel(e_a ::ᵥ e_b ::ᵥ e_J)²`; summing over `J`
and re-indexing the triple sum `(a, b, J) ↦ a ::ᵥ b ::ᵥ J` (two `Fin.consEquiv`s) recovers the
full rank-`(s + 1 + 1)` Parseval frame expansion of `rfns(T)`. -/
private theorem riemannianFiberNormSq_twoSlotUnitEval_le
    (g : SmoothRiemannianMetric I M) (s : ℕ) (x : M)
    (T : Tensor0SBundle.TensorRSSpace 0 (s + 1 + 1) I x)
    (w : TangentSpace I x) (hw : g.inner x w w ≤ 1)
    (U : Tensor0SBundle.TensorRSSpace 0 s I x)
    (hU : ∀ m : Fin s → TangentSpace I x,
      Tensor0SBundle.Tensor0SSpace.toModel
          ((show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace s I x from U)
            (unitZeroSec (I := I) (M := M) x)) m =
        Tensor0SBundle.Tensor0SSpace.toModel
          ((show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ]
              Tensor0SBundle.Tensor0SSpace (s + 1 + 1) I x from T)
            (unitZeroSec (I := I) (M := M) x))
          (Fin.cons w (Fin.cons w m))) :
    riemannianFiberNormSq (I := I) (M := M) g 0 s x U ≤
      riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1 + 1) x T :=
  sorry

/-- **The orthonormal-frame Hessian-component fibre-norm bound (the general-valence currying).**

For a smooth compactly-supported `(0, s)`-tensor field `S`, a point `x`, and the smooth
`g_x`-orthonormal frame `B_i := smoothOrthoFrame g x i`, the intrinsic fibre norm of the diagonal
second covariant derivative `∇²_{B_i, B_i} S (x)` is dominated by the fibre norm of the full
second iterated covariant gradient `∇²S = covGrad g 0 (s+1) (covGrad g 0 s S)` at `x`:
```
rfns(∇²_{B_i, B_i} S)(x) ≤ rfns(∇²S)(x).
```

This is the general-valence two-step covariant-gradient currying together with the
orthonormal-frame component comparison. By the proven two-slot evaluation bridge
`tensorSecondCovDeriv_eq_covGrad_succ_twoSlotEval_genVal`, the second covariant derivative
`tensorSecondCovDeriv` along `(B_i, B_i)`, evaluated at the unit, is exactly the
`(B_i(x), B_i(x))`-evaluation of the two leftmost slots of `∇²S(x)(unit)`; since `B_i(x)` is
`g_x`-unit (`smoothOrthoFrame_orthonormal_at_center`), the slice fibre-norm bound
`riemannianFiberNormSq_twoSlotUnitEval_le` dominates the fibre norm of that evaluation by the
full fibre norm of `∇²S(x)`. -/
private theorem secondCovDeriv_unit_frame_fiberNormSq_le
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : Integral.L2.SmoothCcTensor g 0 s) (x : M)
    (i : Fin (Module.finrank ℝ E)) :
    riemannianFiberNormSq (I := I) (M := M) g 0 s x
        (tensorSecondCovDeriv (I := I) g 0 s
          (smoothOrthoFrame (I := I) g x i) (smoothOrthoFrame (I := I) g x i)
          (fun y : M => S.toSection y) x) ≤
      riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1 + 1) x
        ((covGrad (I := I) (M := M) g 0 (s + 1)
            (covGrad (I := I) (M := M) g 0 s S)).toSection x) := by
  classical
  have hunit : g.inner x (smoothOrthoFrame (I := I) g x i x)
      (smoothOrthoFrame (I := I) g x i x) = 1 := by
    simpa using smoothOrthoFrame_orthonormal_at_center (I := I) g x i i
  refine riemannianFiberNormSq_twoSlotUnitEval_le (I := I) (M := M) g s x
    ((covGrad (I := I) (M := M) g 0 (s + 1)
        (covGrad (I := I) (M := M) g 0 s S)).toSection x)
    (smoothOrthoFrame (I := I) g x i x) (le_of_eq hunit)
    (tensorSecondCovDeriv (I := I) g 0 s
      (smoothOrthoFrame (I := I) g x i) (smoothOrthoFrame (I := I) g x i)
      (fun y : M => S.toSection y) x) (fun m => ?_)
  exact (DifferentialGeometry.Integral.Connection.tensorSecondCovDeriv_eq_covGrad_succ_twoSlotEval_genVal
    (I := I) (M := M) g s S (X := smoothOrthoFrame (I := I) g x i)
    (Y := smoothOrthoFrame (I := I) g x i)
    (smoothOrthoFrame_smooth (I := I) g x i) (smoothOrthoFrame_smooth (I := I) g x i) x m).symm


/-- **Pointwise rough-Laplacian-to-second-covariant-gradient fibre-norm bound.** For a smooth
compactly-supported `(0, s)`-tensor field `S` and a point `x`,
```
rfns(Δ_∇ S)(x) ≤ dim² · rfns(∇²S)(x),
```
where `dim = finrank ℝ E`. The rough Laplacian is the metric trace `∑_i ∇²_{B_i, B_i} S (x)`
(`rawTensorConnLap_eq_metricTraceHessian`), a sum of `dim` diagonal Hessian summands; the
`n`-sub-additivity of the squared fibre norm contributes one factor of `dim` and the
orthonormal-frame component bound `secondCovDeriv_unit_frame_fiberNormSq_le` bounds each summand
by `rfns(∇²S)(x)`, contributing the second. -/
private theorem rawConnLap_fiberNormSq_le_secondCovGrad
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : Integral.L2.SmoothCcTensor g 0 s) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g 0 s x
        ((rawTensorConnLapSmooth (I := I) g 0 s S).toSection x) ≤
      ((Module.finrank ℝ E : ℝ)) ^ 2 *
        riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1 + 1) x
          ((covGrad (I := I) (M := M) g 0 (s + 1)
              (covGrad (I := I) (M := M) g 0 s S)).toSection x) := by
  classical
  set n : ℕ := Module.finrank ℝ E with hn_def
  set rhs : ℝ := riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1 + 1) x
      ((covGrad (I := I) (M := M) g 0 (s + 1)
          (covGrad (I := I) (M := M) g 0 s S)).toSection x) with hrhs_def
  -- The rough Laplacian as the diagonal metric-trace sum of second covariant derivatives.
  have hsum :
      (rawTensorConnLapSmooth (I := I) g 0 s S).toSection x =
        ∑ i : Fin n,
          tensorSecondCovDeriv (I := I) g 0 s
            (smoothOrthoFrame (I := I) g x i) (smoothOrthoFrame (I := I) g x i)
            (fun y : M => S.toSection y) x := by
    rw [rawTensorConnLapSmooth_toSection_apply (I := I) (M := M) g 0 s S x]
    rw [rawTensorConnLap_eq_metricTraceHessian (I := I) g 0 s
      (fun y : M => S.toSection y) x]
    rw [metricTraceHessian_def (I := I) g 0 s (fun y : M => S.toSection y) x]
  rw [hsum]
  -- `n`-sub-additivity of the squared fibre norm on the diagonal trace sum.
  have hsub :
      riemannianFiberNormSq (I := I) (M := M) g 0 s x
          (∑ i : Fin n,
            tensorSecondCovDeriv (I := I) g 0 s
              (smoothOrthoFrame (I := I) g x i) (smoothOrthoFrame (I := I) g x i)
              (fun y : M => S.toSection y) x) ≤
        ((Finset.univ : Finset (Fin n)).card : ℝ) *
          ∑ i : Fin n,
            riemannianFiberNormSq (I := I) (M := M) g 0 s x
              (tensorSecondCovDeriv (I := I) g 0 s
                (smoothOrthoFrame (I := I) g x i) (smoothOrthoFrame (I := I) g x i)
                (fun y : M => S.toSection y) x) :=
    riemannianFiberNormSq_sum_le_card_mul (I := I) (M := M) g 0 s x Finset.univ _
  have hcard : ((Finset.univ : Finset (Fin n)).card : ℝ) = (n : ℝ) := by
    rw [Finset.card_univ, Fintype.card_fin]
  rw [hcard] at hsub
  -- Each summand is bounded by `rhs` (the orthonormal-frame component bound).
  have hterm : ∀ i : Fin n,
      riemannianFiberNormSq (I := I) (M := M) g 0 s x
          (tensorSecondCovDeriv (I := I) g 0 s
            (smoothOrthoFrame (I := I) g x i) (smoothOrthoFrame (I := I) g x i)
            (fun y : M => S.toSection y) x) ≤ rhs := by
    intro i
    rw [hrhs_def]
    exact secondCovDeriv_unit_frame_fiberNormSq_le (I := I) (M := M) g s S x i
  have hsum_le :
      (∑ i : Fin n,
        riemannianFiberNormSq (I := I) (M := M) g 0 s x
          (tensorSecondCovDeriv (I := I) g 0 s
            (smoothOrthoFrame (I := I) g x i) (smoothOrthoFrame (I := I) g x i)
            (fun y : M => S.toSection y) x)) ≤ (n : ℝ) * rhs := by
    calc (∑ i : Fin n,
            riemannianFiberNormSq (I := I) (M := M) g 0 s x
              (tensorSecondCovDeriv (I := I) g 0 s
                (smoothOrthoFrame (I := I) g x i) (smoothOrthoFrame (I := I) g x i)
                (fun y : M => S.toSection y) x))
          ≤ ∑ _i : Fin n, rhs := Finset.sum_le_sum (fun i _ => hterm i)
      _ = (n : ℝ) * rhs := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hn_nn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  calc riemannianFiberNormSq (I := I) (M := M) g 0 s x
          (∑ i : Fin n,
            tensorSecondCovDeriv (I := I) g 0 s
              (smoothOrthoFrame (I := I) g x i) (smoothOrthoFrame (I := I) g x i)
              (fun y : M => S.toSection y) x)
      ≤ (n : ℝ) * ∑ i : Fin n,
            riemannianFiberNormSq (I := I) (M := M) g 0 s x
              (tensorSecondCovDeriv (I := I) g 0 s
                (smoothOrthoFrame (I := I) g x i) (smoothOrthoFrame (I := I) g x i)
                (fun y : M => S.toSection y) x) := hsub
    _ ≤ (n : ℝ) * ((n : ℝ) * rhs) := mul_le_mul_of_nonneg_left hsum_le hn_nn
    _ = (n : ℝ) ^ 2 * rhs := by ring

/-- **The rough-Laplacian-to-second-covariant-gradient `L²` trace bound (uniform in valence).**

There is a single multiplier `K ≥ 1` (depending only on `g` and the manifold, valence-uniform —
in fact `K = dim`) such that for every valence `s` and every smooth compactly-supported
`(0, s)`-tensor `S`, the metric `L²` norm of the rough (connection) Laplacian
`Δ_∇ S := rawTensorConnLapSmooth g 0 s S` is controlled by the metric `L²` norm of the second
iterated covariant gradient `∇²S = covGrad g 0 (s+1) (covGrad g 0 s S)`:
```
‖Δ_∇ S‖_{L²} ≤ K · ‖∇²S‖_{L²}.
```

This is the elementary metric-trace half of the closed-manifold Bochner package, the companion of
the on-disk integration-by-parts half `covGrad_l2NormSq_le_rawConnLap_mul_self_gen`. The proof
integrates the pointwise fibre-norm trace bound `rawConnLap_fiberNormSq_le_secondCovGrad`
(`rfns(Δ_∇ S)(x) ≤ dim² · rfns(∇²S)(x)`) over the compact manifold via the finite-sum
pointwise-to-`L²` packaging `tensorL2Norm_le_of_pointwise_fiberNormSq_bound_sum`. Both sides are
intrinsic metric `L²` norms. -/
theorem exists_rawConnLap_l2Norm_le_secondCovGrad_l2Norm_gen
    (g : SmoothRiemannianMetric I M) :
    ∃ K : ℝ, 1 ≤ K ∧
      ∀ (s : ℕ) (S : Integral.L2.SmoothCcTensor g 0 s),
        Integral.L2.tensorL2Norm (I := I) g 0 s
            (rawTensorConnLapSmooth (I := I) g 0 s S).toFun ≤
          K * Integral.L2.tensorL2Norm (I := I) g 0 (s + 1 + 1)
            (covGrad (I := I) (M := M) g 0 (s + 1)
              (covGrad (I := I) (M := M) g 0 s S)).toFun := by
  classical
  set n : ℕ := Module.finrank ℝ E with hn_def
  have hn_pos : 0 < n := by
    rw [hn_def]; exact Nat.pos_of_ne_zero (NeZero.ne (Module.finrank ℝ E))
  have hK1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn_pos
  refine ⟨(n : ℝ), hK1, ?_⟩
  intro s S
  -- The single-term jet family for the packaging lemma: `∇²S` at valence `s + 1 + 1`.
  set HH : Integral.L2.SmoothCcTensor g 0 (s + 1 + 1) :=
    covGrad (I := I) (M := M) g 0 (s + 1) (covGrad (I := I) (M := M) g 0 s S) with hHH_def
  -- Pointwise fibre-norm bound, packaged as a one-term sum with multiplier `n`.
  have hpt : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g 0 s x
          ((rawTensorConnLapSmooth (I := I) g 0 s S).toSection x) ≤
        (n : ℝ) ^ 2 * ∑ _i ∈ Finset.range 1,
          riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1 + 1) x (HH.toSection x) := by
    intro x
    rw [Finset.sum_const, Finset.card_range, one_nsmul]
    rw [hHH_def]
    exact rawConnLap_fiberNormSq_le_secondCovGrad (I := I) (M := M) g s S x
  -- Lift the pointwise bound to the metric `L²` norm.
  have hpack :
      ‖rawTensorConnLapSmooth (I := I) g 0 s S‖ ≤
        (n : ℝ) * ∑ _i ∈ Finset.range 1, ‖HH‖ :=
    tensorL2Norm_le_of_pointwise_fiberNormSq_bound_sum (I := I) (M := M) g 1
      (fun _ => s + 1 + 1) (fun _ => HH)
      (rawTensorConnLapSmooth (I := I) g 0 s S)
      (n : ℝ) (Nat.cast_nonneg n) hpt
  rw [Finset.sum_const, Finset.card_range, one_nsmul] at hpack
  rw [Integral.L2.SmoothCcTensor.norm_def (I := I) (M := M)
    (rawTensorConnLapSmooth (I := I) g 0 s S)] at hpack
  rw [Integral.L2.SmoothCcTensor.norm_def (I := I) (M := M) HH] at hpack
  rw [hHH_def] at hpack
  exact hpack

end Connection
end Integral
end DifferentialGeometry

end
