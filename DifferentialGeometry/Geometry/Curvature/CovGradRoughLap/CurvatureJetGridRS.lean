import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.OrderSeparatedCurvatureJetRS

/-!
# The rank-`r` genuine curvature-jet grid of the order-`2` commutator defect

For a closed (compact, boundaryless) smooth Riemannian manifold `(M, g)` and a fixed contravariant
rank `r` this file homes the two genuinely-irreducible rank-`r` curvature-jet primitives of the
order-`2` rough-Laplacian / covariant-gradient commutator defect

```
Curv S := Δ_∇(∇S) − ∇(Δ_∇ S)
```

(`pointwiseTensorCurvRS g r s S`, a `(r, s + 1)`-tensor field; `∇S = covGrad g r s S`), each the
contravariant-rank-`r` lift of a rank-`0` curvature-jet node whose proof tower
(`FrozenFramePureRCurvatureTower`, `DiffCurvatureGenuineTower`) is stated *only* at contravariant
rank `0`.

* `GcurvSectionRS_gradedCurvJet` — the rank-`r` lift of the rank-`0` pure-Riemann genuine-section jet
  `GcurvSection_gradedCurvJet` (`OrderSeparatedCurvatureJet`): the concrete moving-centre pure-Riemann
  genuine curvature section `GcurvSectionRS g r s S` (the slot-`0` assembly of the *tensorial*
  moving-frame trace `∑ᵢ R(Bᵢ, ·)(∇_{Bᵢ} S)`, the `R(∇S)` contraction) is a **graded** curvature jet
  of `S` of lowest contracted order `1` and base width `1`.

* `exists_pointwiseTensorCurvRS_diffCurvAndRemainder_fullSum_gradedCurvJet` — the rank-`r`, **sound
  full-sum** lift of the rank-`0` combined differentiated-curvature-and-remainder jet split
  `exists_pointwiseTensorCurv_diffCurvAndRemainder_gradedCurvJet` (`OrderSeparatedCurvatureJet`),
  carrying the existential differentiated-curvature `(∇R) S` jet `Gcd` of shape `(0, 1)` and the
  moving-frame remainder `Grem` of the sound full-sum shape `(0, 3)` over the concrete pure-Riemann
  section `GcurvSectionRS g r s S` — **not** the false single-top-order shape `(2, 1)` (the
  per-direction moving-frame bracket trace is non-tensorial, so only the intrinsic full-sum window
  `0 … k + 2` is order-controlled).

Both are the genuine missing rank-`r` curvature content; the rank-`r` pure-Riemann / differentiated
grids are absent sorry-free below this file, so they are posited here as precise true children — the
two pieces from which the witnessed rank-`r` three-field base split
`pointwiseTensorCurvRS_directFullSum_baseSplit` (`CommutatorDefectFullSumJet`) is assembled. Consumers
transitively depend on `sorryAx`.

## Convention

Geometer convention `Δ_∇ = ∑ᵢ ∇²_{Bᵢ, Bᵢ}` (frame trace). All fibre norms are the intrinsic
Riemannian fibre norm `riemannianFiberNormSq`; `covGrad g r s` raises `(r, s) → (r, s + 1)` and
`iteratedCovGrad g r s j` is its `j`-fold iterate.
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
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

/-- **The rank-`r` pure-Riemann genuine-section graded curvature-jet grid (posited general-rank
curvature child).** The contravariant-rank-`r` lift of the rank-`0` pure-Riemann genuine-section jet
`GcurvSection_gradedCurvJet` (`OrderSeparatedCurvatureJet`, *sorry-free* via the frame-free
`FrozenFramePureRCurvatureTower`). For a closed smooth Riemannian manifold `(M, g)` and a fixed
contravariant rank `r` there is a valence/order-dependent nonnegative constant family
`c : ℕ → ℕ → ℝ` such that, at every covariant rank `s` and for every smooth compactly-supported
`(r, s)`-tensor `S`, the concrete moving-centre pure-Riemann genuine curvature section
`GcurvSectionRS g r s S` (the slot-`0` assembly of the *tensorial* moving-frame trace
`∑ᵢ R(Bᵢ, ·)(∇_{Bᵢ} S)`, the `R(∇S)` contraction) is a **graded** curvature jet of `S` of lowest
contracted order `1` and base width `1`:

```
rfns(∇^k (GcurvSectionRS g r s S))(x) ≤ (c s k)² · ∑_{i < 1 + k} rfns(∇^{i + 1} S)(x).
```

**Why this is TRUE.** This is the verbatim contravariant-rank-`r` mirror of the rank-`0` headline
`GcurvSection_gradedCurvJet`. The pure-Riemann genuine trace `∑ᵢ R(Bᵢ, ·)(∇_{Bᵢ} S)` is a genuine
`g`-metric trace (the frame index `Bᵢ` is contracted twice — in slot-`0` of the bundled curvature
operator `riemannOp (tensorCov g r s)` and as the covariant-gradient direction), so the section
`GcurvSectionRS g r s S` is the slot-`0` assembly of a *tensorial* contraction of the curvature
operator against `∇S`. Each of its own iterated covariant gradients `∇^k (GcurvSectionRS g r s S)` is,
by the iterated covariant Leibniz expansion, a sum of contractions of `∇^p R` (`p ≤ k`) against
`∇^{q + 1} S` (`q ≤ k`), contracted-order window `1 … 1 + k` — the `(p, w) = (1, 1)` graded shape, the
contraction entering the gradient field `∇S` at order `1`. Every curvature coefficient is absorbed
uniformly over the compact manifold into the per-order constant `(c s k)²` (carrying `‖∇^{≤ k} R‖_∞`,
finite by per-`k` compactness, via the rank-`r` analogue of the curvature sup
`exists_uniform_riemannianFiberNormSq_riemannOp_bound`). The rank-`r` pure-Riemann grid tower is
itself absent sorry-free below this file (only the rank-`0` `FrozenFramePureRCurvatureTower` headline
`exists_GcurvSection_iteratedCovGrad_grid_bound` is proven), so this rank-`r` grid is posited here as
the single precise true child. Consumers transitively depend on `sorryAx`.

**Non-vacuity.** With `c s 0 = 0` the bound forces `rfns(GcurvSectionRS g r s S)(x) = 0` at `k = 0`,
i.e. the pure-Riemann contraction `∑ᵢ R(Bᵢ, ·)(∇_{Bᵢ} S)` vanishes; *false* on a non-flat manifold
(`R ≠ 0`) for a non-parallel `S` (`∇S ≠ 0`) — the field `GcurvSectionRS g r s S` carries the genuine
pure-Riemann `R(∇S)` content (`genuineCurvPureRFibRS_contMDiff`, never the zero section). The constant
family is genuinely positive. -/
theorem GcurvSectionRS_gradedCurvJet (g : SmoothRiemannianMetric I M) (r : ℕ) :
    ∃ c : ℕ → ℕ → ℝ, (∀ s k, 0 ≤ c s k) ∧
      ∀ (s : ℕ) (S : SmoothCcTensor g r s),
        IsGradedCurvJetRS (I := I) (M := M) g S (c s) 1 1
          (GcurvSectionRS (I := I) (M := M) g r s S) := by
  -- The graded curvature-jet of the pure-Riemann section is exactly the rank-`r` pure-Riemann grid:
  -- `IsGradedCurvJetRS g S (c s) 1 1 (GcurvSectionRS g r s S)` unfolds to the grid bound (lowest order
  -- `p = 1`, base width `w = 1`, so the contracted-order window `∑_{i < 1 + k} rfns(∇^{i + 1} S)`).
  obtain ⟨c, hc_nn, hgrid⟩ := exists_GcurvSectionRS_iteratedCovGrad_grid_bound (I := I) (M := M) g r
  exact ⟨c, hc_nn, fun s S k x => hgrid s S k x⟩

/-- **The rank-`r` differentiated-curvature-and-remainder full-sum graded curvature-jet seed (posited
general-rank curvature child — the genuinely-missing upstream differentiated grid).** The
contravariant-rank-`r`, **sound full-sum** analogue of the rank-`0` combined split
`exists_pointwiseTensorCurv_diffCurvAndRemainder_gradedCurvJet` (`OrderSeparatedCurvatureJet`, itself a
posited `sorry` at rank `0`), the differentiated companion of the pure-Riemann grid
`exists_GcurvSectionRS_iteratedCovGrad_grid_bound`. For a closed smooth Riemannian manifold `(M, g)` and
a fixed contravariant rank `r` there is a valence/order-dependent nonnegative constant family
`c : ℕ → ℕ → ℝ` such that, at every covariant rank `s` and for every smooth compactly-supported
`(r, s)`-tensor `S`, the order-`2` commutator defect `Curv S := pointwiseTensorCurvRS g r s S` splits,
over the concrete pure-Riemann genuine section `GcurvSectionRS g r s S`, into a differentiated-curvature
genuine field `Gcd` and a moving-frame remainder field `Grem` — both smooth compactly-supported
`(r, s + 1)`-tensors carried **existentially** — with `Curv S = GcurvSectionRS g r s S + Gcd + Grem`,
`Gcd` a **graded** curvature jet of `S` of lowest order `0` and base width `1`, and `Grem` a **graded**
curvature jet of the **sound full-sum shape** lowest order `0` and base width `3`.

**Why this is TRUE — and why it is the FULL-SUM, not order-separated, shape.** This is the differentiated
companion of the pure-Riemann grid: where `exists_GcurvSectionRS_iteratedCovGrad_grid_bound` controls the
*all-order* iterated gradients of the pure-Riemann section `GcurvSectionRS g r s S` (the `R(∇S)`
contraction), this controls the *all-order* iterated gradients of the differentiated-curvature `(∇R) S`
field `Gcd` (each `∇^k Gcd` a sum of contractions of `∇^p R` (`p ≤ k + 1`) against `∇^q S` (`q ≤ k`),
the `(0, 1)` shape) and of the moving-frame remainder `Grem` (each `∇^k Grem` a curvature contraction of
`∇^{≤ k + 2} S`, the **full-sum** window `0 … k + 2`, shape `(0, 3)`). All curvature coefficients are
absorbed uniformly over the compact manifold into the per-order constant `(c s k)²` (carrying
`‖∇^{≤ k + 1} R‖_∞`, finite by per-`k` compactness). The **full-sum**, not the single top order `(2, 1)`:
the per-direction moving-frame bracket trace is non-tensorial in the direction (false term-by-term
through `smoothExtensionTangent`), so only the intrinsic full-sum window is order-controlled; the
differentiated-curvature and bracket fields are carried *existentially* (never per-direction
`smoothExtensionTangent`-curried). At rank `0` the differentiated grid is itself a posited `sorry`; at
rank `r` it is again the genuinely-irreducible rank-`r` differentiated curvature grid, absent sorry-free
below this file (the rank-`r` differentiated `(∇R)·` grid and iterated-Ricci remainder tower are absent,
and the rank-`0` grid engine `DiffBilinOp` is contravariant-rank-`0`-locked), so it is posited here as
the single precise true child — the differentiated companion grid from which the graded packaging
`exists_pointwiseTensorCurvRS_diffCurvAndRemainder_fullSum_gradedCurvJet` is read off. Consumers
transitively depend on `sorryAx`.

**Non-vacuity.** With `c s 0 = 0` the two bounds force `rfns(Gcd)(x) = rfns(Grem)(x) = 0` at `k = 0`,
making the split `Curv S = GcurvSectionRS g r s S` (the differentiated-curvature `(∇R) S` and
frame-bracket content vanish); *false* on a non-flat manifold where the differentiated-curvature
contraction (`∇R ≠ 0`) and the moving-frame bracket discrepancy are genuinely non-zero. The constant
family is genuinely positive. -/
theorem exists_pointwiseTensorCurvRS_diffCurvAndRemainder_fullSum_gradedCurvJet_seed
    (g : SmoothRiemannianMetric I M) (r : ℕ) :
    ∃ c : ℕ → ℕ → ℝ, (∀ s k, 0 ≤ c s k) ∧
      ∀ (s : ℕ) (S : SmoothCcTensor g r s),
        ∃ Gcd Grem : SmoothCcTensor g r (s + 1),
          pointwiseTensorCurvRS (I := I) (M := M) g r s S =
              GcurvSectionRS (I := I) (M := M) g r s S + Gcd + Grem ∧
          IsGradedCurvJetRS (I := I) (M := M) g S (c s) 0 1 Gcd ∧
          IsGradedCurvJetRS (I := I) (M := M) g S (c s) 0 3 Grem := by
  sorry

/-- **The rank-`r` combined differentiated-curvature-and-remainder full-sum graded curvature-jet split
(posited general-rank curvature child, the sound full-sum form).** The contravariant-rank-`r`,
**sound full-sum** lift of the rank-`0` combined split
`exists_pointwiseTensorCurv_diffCurvAndRemainder_gradedCurvJet` (`OrderSeparatedCurvatureJet`). For a
closed smooth Riemannian manifold `(M, g)` and a fixed contravariant rank `r` there is a
valence/order-dependent nonnegative constant family `c : ℕ → ℕ → ℝ` such that, at every covariant
rank `s` and for every smooth compactly-supported `(r, s)`-tensor `S`, the order-`2` commutator defect
`Curv S := pointwiseTensorCurvRS g r s S` splits, over the concrete pure-Riemann genuine section
`GcurvSectionRS g r s S` (the slot-`0` assembly of the *tensorial* moving-frame trace
`∑ᵢ R(Bᵢ, ·)(∇_{Bᵢ} S)`, the `R(∇S)` contraction), into a differentiated-curvature genuine field
`Gcd` and a moving-frame remainder field `Grem` — both smooth compactly-supported `(r, s + 1)`-tensors
carried **existentially** (never extension-curried):

```
Curv S = GcurvSectionRS g r s S + Gcd + Grem
```

with `Gcd` a **graded** curvature jet of `S` of lowest order `0` and base width `1`, and `Grem` a
**graded** curvature jet of the **sound full-sum shape** lowest order `0` and base width `3` (bounded
by the whole window `∇^{≤ k + 2} S`, NOT the false single-top-order shape `(2, 1)`):

```
rfns(∇^k Gcd)(x)  ≤ (c s k)² · ∑_{i < 1 + k} rfns(∇^{i + 0} S)(x),
rfns(∇^k Grem)(x) ≤ (c s k)² · ∑_{i < 3 + k} rfns(∇^{i + 0} S)(x).
```

**Why this is TRUE — and why it is the FULL-SUM, not order-separated, shape.** Pointwise `Curv S` is
the genuine third-order Bochner–Weitzenböck field: by the metric-trace reading of the rough Laplacian
`Δ_∇ = tr_g ∘ ∇²` (`rawTensorConnLap_eq_metricTrace2`, frame-free, rank-generic) the defect
`Δ_∇(∇S) − ∇(Δ_∇ S)` is the metric trace of the antisymmetrised second covariant derivative of `∇S`
after the outer `∇` is passed through the trace by metric compatibility (`metricTrace2_covDeriv_comm`,
rank-generic), which the third-order tensor Ricci identity
`secondCovDeriv_covGrad_antisymm_eq_riemannOp_gen` exhibits as a `riemannOp`-contraction of `(∇S, S)`,
lifted to the `(r, s)`-bundle through the slot-wise curvature formula `riemannSec_tensorCov_apply_eval`
(`TensorSlotwiseCurvatureRS`). Splitting that contraction into its pure-Riemann `R(∇S)` part (the
concrete `GcurvSectionRS g r s S`) and its differentiated-curvature `(∇R) S` part (the existential
`Gcd`, genuinely `rfns(S)`-order: each `∇^k Gcd` is a sum of contractions of `∇^p R` (`p ≤ k + 1`)
against `∇^q S` (`q ≤ k`), contracted-order window `0 … k`, the `(0, 1)` shape), the surviving
`Grem := Curv S − GcurvSectionRS g r s S − Gcd` is the moving-frame / frame-bracket discrepancy,
genuinely `∇²S`-order; each of its iterated gradients `∇^k Grem` is, after the iterated-Ricci
cancellation of the top `∇^{k + 3} S` terms, a curvature contraction of `∇^{≤ k + 2} S` — the
**full-sum** window `0 … k + 2` (shape `(0, 3)`). All curvature coefficients are absorbed uniformly
over the compact manifold into the per-order constant `(c s k)²` (carrying `‖∇^{≤ k + 1} R‖_∞`, finite
by per-`k` compactness, via the rank-`r` curvature / differentiated-curvature sups). The
**full-sum**, not the single top order `(2, 1)`: the per-direction moving-frame bracket trace is
non-tensorial in the direction (false term-by-term through `smoothExtensionTangent`), so only the
intrinsic full-sum window is order-controlled. The rank-`r` differentiated `(∇R)·` grid and the
rank-`r` iterated-Ricci remainder tower are absent sorry-free below this file (only the rank-`0`
`DiffCurvatureGenuineTower` / the rank-`0` order-separated split are proven), so this rank-`r` sound
full-sum combined split is posited here as the single precise true child. The differentiated-curvature
and bracket fields are carried *existentially* (never as per-direction `smoothExtensionTangent`-curried
sections): their moving-frame traces are non-tensorial in the direction. Consumers transitively depend
on `sorryAx`.

**Non-vacuity.** With `c s 0 = 0` the two bounds force `rfns(Gcd)(x) = rfns(Grem)(x) = 0` at `k = 0`,
making the split `Curv S = GcurvSectionRS g r s S` (the differentiated-curvature `(∇R) S` and
frame-bracket content vanish); *false* on a non-flat manifold where the differentiated-curvature
contraction (`∇R ≠ 0`) and the moving-frame bracket discrepancy are genuinely non-zero (the
moving-frame bracket discrepancy is carried explicitly — never asserted to vanish — throughout the
moving-frame tower). The constant family is genuinely positive. -/
theorem exists_pointwiseTensorCurvRS_diffCurvAndRemainder_fullSum_gradedCurvJet
    (g : SmoothRiemannianMetric I M) (r : ℕ) :
    ∃ c : ℕ → ℕ → ℝ, (∀ s k, 0 ≤ c s k) ∧
      ∀ (s : ℕ) (S : SmoothCcTensor g r s),
        ∃ Gcd Grem : SmoothCcTensor g r (s + 1),
          pointwiseTensorCurvRS (I := I) (M := M) g r s S =
              GcurvSectionRS (I := I) (M := M) g r s S + Gcd + Grem ∧
          IsGradedCurvJetRS (I := I) (M := M) g S (c s) 0 1 Gcd ∧
          IsGradedCurvJetRS (I := I) (M := M) g S (c s) 0 3 Grem := by
  -- The combined graded split is read off directly from the rank-`r` differentiated-curvature-and-
  -- remainder grid seed (the differentiated companion of the pure-Riemann grid): the seed carries the
  -- existential `Gcd`, `Grem`, the section split, and the two graded jets at the very shapes required.
  exact exists_pointwiseTensorCurvRS_diffCurvAndRemainder_fullSum_gradedCurvJet_seed (I := I) (M := M) g r

end Connection
end Integral
end DifferentialGeometry

end
