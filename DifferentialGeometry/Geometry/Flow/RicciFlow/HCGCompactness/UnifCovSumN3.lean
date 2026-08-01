import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.ConnDiffDeriv2Bound

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# The `∇₁³`-jet telescoping bound (UNIF item 6, the `N = 3` glue)

The `∇₁ᴺ`-jet telescoping bound `iterCovG1_le` (`UnifCovSumCross.lean`) is conditional on the
accumulator hypothesis `hAcc`, bounding `∇₂(telescAccum g₁ g₂ r T m)` at each level `m < N`.
`iterCovG1_two` discharges `hAcc` for `m < 2` (`m = 0`: the accumulator is `0`; `m = 1`: it is
`diffStep g₁ g₂ r T`, bounded by the a=1 atom `covStepDiff_of_jets`).  This leaf feeds the completed
a=2 atom `covStepDiff2_exists_const` (`ConnDiffDeriv2Bound.lean`) into the recursion, discharging
`hAcc` at `m = 2` and closing the unconditional `N = 3` case.

The `m = 2` reconciliation (`covStepAcc2_le`): unfolding `telescAccum 2` and splitting the inner
`∇₁ = ∇₂ + A` gives

```
∇₂(telescAccum 2)  =  ∇₂²(A ⋆ T)          -- the a=2 atom `covStepDiff2_exists_const` at s = r
                    + ∇₂(A ⋆ (A ⋆ T))     -- a=1 `covStepDiff_of_jets` at s = r+1, S = A ⋆ T
                    + ∇₂(A ⋆ ∇₂T)         -- a=1 `covStepDiff_of_jets` at s = r+1, S = ∇₂T
```

with the inner factors `|A ⋆ T|`, `|∇₂(A ⋆ T)|` folded by `diffStep_jet_one_le` and
`covStepDiff_of_jets` at `s = r`.  All three pieces land in the `∇₂`-jets `P₀, P₁, P₂` of `T`, so the
level-2 accumulator bound needs no `P₃` (the sharp range is `m + 1`, one below `hAcc`'s `m + 2`).

**Import direction.**  `ConnDiffDeriv2Bound` imports `UnifCovSumCross`, so this glue cannot live in
`UnifCovSumCross.lean`; `ConnDiffDeriv2Bound.lean` is at the 3000-line cap.  Hence this leaf, which
imports `ConnDiffDeriv2Bound` (and transitively the whole T-B tower).  The `iterCovG1_*` family lives
in `DifferentialGeometry.PDE.RicciFlow`, so the endpoints here do too.

## Main results

* `covStepAcc2_le` — the `hAcc` `m = 2` accumulator bound with a uniform existential constant:
  `|∇₂(telescAccum g₁ g₂ r T 2)|_{g₂} ≤ C · ∑_{k≤2} |∇₂ᵏT|_{g₂}` on `K`, under the metric-jet
  bundle (`Λ`-comparability; `∇g₂/g₁ ≤ Λ'`; `∇g₁, ∇²g₁, ∇³g₁ / g₂ ≤ Λ', Λ'', Λ'''`).
* `iterCovG1_three` — the unconditional `N = 3` telescoping endpoint:
  `|∇₁³T|_{g₂} ≤ C · ∑_{k≤3} |∇₂ᵏT|_{g₂}` on `K`, with `C` uniform in `T` and `x` (built from the
  `Dtower` recursion with `Racc 2` supplied by `covStepAcc2_le`).
* `hAcc_of_jets` — **FRONTIER (`sorry`)**: the general-`m` accumulator bound, the single remaining
  hypothesis for the unconditional general-`N` case (the a ≥ 3 campaign).

The three private helpers (`covStep_zero'`, `sqrt_normSq0S_zero`, `telescAccum_one`) are verbatim
re-derivations of `UnifCovSumCross.lean` privates (hoist candidates for `MetricCovDerivLinear.lean` /
`ProductMFoldNorm.lean`, pending planner hoist).
-/

noncomputable section

open Bundle Manifold Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff BigOperators
open DifferentialGeometry.HCGCompactness
open DifferentialGeometry.Integral.Connection

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [Module.Finite ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [T2Space M] [IsManifold I ∞ M] [SigmaCompactSpace M] [BoundarylessManifold I M]
variable [CompactSpace M] [I.Boundaryless]

/-- `covStep` of the zero field vanishes (`R`-linearity, via `covStep_add`).  Verbatim re-derivation
of the `UnifCovSumCross.lean` private helper (hoist candidate: `MetricCovDerivLinear.lean`). -/
private theorem covStep_zero' (gRef : SmoothRiemannianMetric I M) (s : ℕ) :
    covStep (I := I) gRef s 0 = 0 := by
  have h := covStep_add (I := I) gRef s 0 0
  rw [add_zero] at h
  have hc : covStep (I := I) gRef s 0 + covStep (I := I) gRef s 0 =
      covStep (I := I) gRef s 0 + 0 := by rw [add_zero]; exact h.symm
  exact add_left_cancel hc

/-- The fibre norm of the zero tensor vanishes.  Re-derivation of the `UnifCovSumCross.lean` private
helper through the public `exists_gOrthonormalBasis` (hoist candidate: `ProductMFoldNorm.lean`). -/
private theorem sqrt_normSq0S_zero (g : SmoothRiemannianMetric I M) (x : M) (s : ℕ) :
    Real.sqrt (normSq0S (I := I) g x s (0 : Tensor0SBundle.Tensor0SSpace s I x)) = 0 := by
  classical
  obtain ⟨basis, hON⟩ :=
    DifferentialGeometry.Integral.Connection.exists_gOrthonormalBasis (I := I) g x
  have hinv : MetricInverseInBasis_gen (I := I) g x basis
      (identityInvMetric (Idx := Fin (Module.finrank Real (TangentSpace I x)))) := by
    intro i j; constructor <;> simp [identityInvMetric, diagonalInvMetric, hON]
  rw [normSq0S_identity_eq_sum_sq (I := I) g x s basis hinv]
  rw [show (∑ slots : Fin s → Fin (Module.finrank Real (TangentSpace I x)),
      (component0S (I := I) basis (0 : Tensor0SBundle.Tensor0SSpace s I x) slots) ^ 2) = 0 from ?_]
  · exact Real.sqrt_zero
  · refine Finset.sum_eq_zero (fun slots _ => ?_)
    rw [component0S_apply]; simp

/-- The telescoping accumulator at level `1` is the single-step connection difference of `T`.
Verbatim re-derivation of the `UnifCovSumCross.lean` private helper. -/
private theorem telescAccum_one (g₁ g₂ : SmoothRiemannianMetric I M) (r : ℕ)
    (T : Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) r) :
    telescAccum (I := I) g₁ g₂ r T 1 = diffStep (I := I) g₁ g₂ r T := by
  have hunfold : telescAccum (I := I) g₁ g₂ r T 1
      = covStep (I := I) g₁ r (telescAccum (I := I) g₁ g₂ r T 0)
        + diffStep (I := I) g₁ g₂ r T := rfl
  rw [hunfold, show telescAccum (I := I) g₁ g₂ r T 0 = 0 from rfl, covStep_zero', zero_add]

/-- Explicit coefficient for the level-two telescoping accumulator. -/
noncomputable def covStepAcc2C (r : ℕ) (Λ Λ' Λ'' Λ''' : ℝ) : ℝ :=
  max 0 (covStepDiff2C (E := E) r Λ Λ' Λ'' Λ''' +
    (((r + 1 : ℕ) : ℝ) * Real.sqrt ((Module.finrank ℝ E : ℝ) ^ (r + 3)) *
      (3 / 2 * Λ ^ 4 * (Λ'' + Λ * Λ' ^ 2) +
        (3 / 2 : ℝ) * (Real.sqrt (Λ ^ 3) * Λ'))) *
      ((r : ℝ) * Real.sqrt ((Module.finrank ℝ E : ℝ) ^ (r + 1)) *
          ((3 / 2 : ℝ) * (Real.sqrt (Λ ^ 3) * Λ')) +
        (r : ℝ) * Real.sqrt ((Module.finrank ℝ E : ℝ) ^ (r + 2)) *
          (3 / 2 * Λ ^ 4 * (Λ'' + Λ * Λ' ^ 2) +
            (3 / 2 : ℝ) * (Real.sqrt (Λ ^ 3) * Λ')) + 1))

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 400000 in
/-- **The `hAcc` `m = 2` accumulator bound** (the a=2 glue).  The `g₂`-fibre norm of the base
covariant derivative of the level-2 telescoping accumulator is bounded on `K` by a single constant
`C` — uniform in the rank-`r` field `T` and in `x` — times the order-≤2 `∇₂`-jets of `T`:

```
|∇₂(telescAccum g₁ g₂ r T 2)|_{g₂} ≤ C · ∑_{k ∈ range 3} |iterCov g₂ r T k|_{g₂}.
```

This discharges `iterCovG1_le`'s hypothesis `hAcc` at `m = 2` (the sharp jet range is `m + 1 = 3`
terms, one below the `m + 2` that `hAcc` allows).  Route: `telescAccum 2` unfolds to
`∇₁(A ⋆ T) + A ⋆ ∇₂T`; splitting the inner `∇₁ = ∇₂ + A` and pushing `∇₂` through gives the three
pieces `∇₂²(A ⋆ T)` (the a=2 atom `covStepDiff2_exists_const`), `∇₂(A ⋆ (A ⋆ T))` and `∇₂(A ⋆ ∇₂T)`
(both the a=1 atom `covStepDiff_of_jets` at level `r + 1`), with the inner `|A ⋆ T|`-jets folded by
`diffStep_jet_one_le` and `covStepDiff_of_jets` at level `r`.  The metric jets carry the session-12
role asymmetry: `hjet` measures `∇g₂` against `g₁`, while `hJet1`/`hJet2`/`hJet3` measure
`∇g₁`/`∇²g₁`/`∇³g₁` against `g₂`. -/
theorem covStepAcc2_bound
    {K : Set M} (g₁ g₂ : SmoothRiemannianMetric I M) (r : ℕ)
    {Λ Λ' Λ'' Λ''' : ℝ}
    (hEq : MetricUniformEquivalentOn (I := I) K g₁ g₂ Λ)
    (hjet : MetricCovDerivOrderBoundOn (I := I) K 1 g₂ g₁ Λ')
    (hJet1 : MetricCovDerivOrderBoundOn (I := I) K 1 g₁ g₂ Λ')
    (hJet2 : MetricCovDerivOrderBoundOn (I := I) K 2 g₁ g₂ Λ'')
    (hJet3 : MetricCovDerivOrderBoundOn (I := I) K 3 g₁ g₂ Λ''') :
    ∀ (T : Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
        (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) r) (x : M), x ∈ K →
      Real.sqrt (normSq0S (I := I) g₂ x (r + 3)
          (covStep (I := I) g₂ (r + 2) (telescAccum (I := I) g₁ g₂ r T 2) x)) ≤
        covStepAcc2C (E := E) r Λ Λ' Λ'' Λ''' *
          ∑ k ∈ Finset.range 3,
            Real.sqrt (normSq0S (I := I) g₂ x (r + k) (iterCov (I := I) g₂ r T k x)) := by
  classical
  let C₂ : ℝ := covStepDiff2C (E := E) r Λ Λ' Λ'' Λ'''
  have hC₂nn : 0 ≤ C₂ := by
    dsimp [C₂, covStepDiff2C]
    exact le_max_left _ _
  have hC₂ := covStepDiff2_le (I := I) g₁ g₂ r
    (metricUniformEquivalentOn_symm (I := I) hEq) hJet1 hJet2 hJet3 hjet
  -- the committed a=1 constants (`covStepDiff_of_jets` at levels `r`, `r+1`; `diffStep_jet_one_le`)
  set CA0 : ℝ := (r : ℝ) * Real.sqrt ((Module.finrank ℝ E : ℝ) ^ (r + 2)) *
    (3 / 2 * Λ ^ 4 * (Λ'' + Λ * Λ' ^ 2) + (3 / 2 : ℝ) * (Real.sqrt (Λ ^ 3) * Λ')) with hCA0def
  set CA1 : ℝ := ((r + 1 : ℕ) : ℝ) * Real.sqrt ((Module.finrank ℝ E : ℝ) ^ (r + 3)) *
    (3 / 2 * Λ ^ 4 * (Λ'' + Λ * Λ' ^ 2) + (3 / 2 : ℝ) * (Real.sqrt (Λ ^ 3) * Λ')) with hCA1def
  set cs0 : ℝ := (r : ℝ) * Real.sqrt ((Module.finrank ℝ E : ℝ) ^ (r + 1)) *
    ((3 / 2 : ℝ) * (Real.sqrt (Λ ^ 3) * Λ')) with hcs0def
  intro T x hx
  -- Λ-nonnegativity at `x ∈ K` and nonnegativity of the constants
  have hLnn : (0 : ℝ) ≤ Λ := le_trans zero_le_one hEq.1
  have hL'nn : (0 : ℝ) ≤ Λ' := le_trans (Real.sqrt_nonneg _) (hjet x hx)
  have hL''nn : (0 : ℝ) ≤ Λ'' := le_trans (Real.sqrt_nonneg _) (hJet2 x hx)
  have hCA0nn : (0 : ℝ) ≤ CA0 := by rw [hCA0def]; positivity
  have hCA1nn : (0 : ℝ) ≤ CA1 := by rw [hCA1def]; positivity
  have hcs0nn : (0 : ℝ) ≤ cs0 := by rw [hcs0def]; positivity
  -- operator split: `∇₂(telescAccum 2) = ∇₂²(A⋆T) + ∇₂(A⋆(A⋆T)) + ∇₂(A⋆∇₂T)`
  have hsplit : covStep (I := I) g₂ (r + 2) (telescAccum (I := I) g₁ g₂ r T 2)
      = covStep (I := I) g₂ (r + 2)
            (covStep (I := I) g₂ (r + 1) (diffStep (I := I) g₁ g₂ r T))
        + covStep (I := I) g₂ (r + 2)
            (diffStep (I := I) g₁ g₂ (r + 1) (diffStep (I := I) g₁ g₂ r T))
        + covStep (I := I) g₂ (r + 2)
            (diffStep (I := I) g₁ g₂ (r + 1) (iterCov (I := I) g₂ r T 1)) := by
    have h2 : telescAccum (I := I) g₁ g₂ r T 2
        = covStep (I := I) g₁ (r + 1) (diffStep (I := I) g₁ g₂ r T)
          + diffStep (I := I) g₁ g₂ (r + 1) (iterCov (I := I) g₂ r T 1) := by
      have hu : telescAccum (I := I) g₁ g₂ r T 2
          = covStep (I := I) g₁ (r + 1) (telescAccum (I := I) g₁ g₂ r T 1)
            + diffStep (I := I) g₁ g₂ (r + 1) (iterCov (I := I) g₂ r T 1) := rfl
      rw [hu, telescAccum_one]
    have hg1 : covStep (I := I) g₁ (r + 1) (diffStep (I := I) g₁ g₂ r T)
        = covStep (I := I) g₂ (r + 1) (diffStep (I := I) g₁ g₂ r T)
          + diffStep (I := I) g₁ g₂ (r + 1) (diffStep (I := I) g₁ g₂ r T) := by
      simp only [diffStep]
      abel
    rw [h2, covStep_add, hg1, covStep_add]
  have hsplitx : covStep (I := I) g₂ (r + 2) (telescAccum (I := I) g₁ g₂ r T 2) x
      = covStep (I := I) g₂ (r + 2)
            (covStep (I := I) g₂ (r + 1) (diffStep (I := I) g₁ g₂ r T)) x
        + covStep (I := I) g₂ (r + 2)
            (diffStep (I := I) g₁ g₂ (r + 1) (diffStep (I := I) g₁ g₂ r T)) x
        + covStep (I := I) g₂ (r + 2)
            (diffStep (I := I) g₁ g₂ (r + 1) (iterCov (I := I) g₂ r T 1)) x := by
    rw [hsplit]; rfl
  -- `g₂`-orthonormal basis at `x` for the fibre triangle inequality
  obtain ⟨basis, hON⟩ :=
    DifferentialGeometry.Integral.Connection.exists_gOrthonormalBasis (I := I) g₂ x
  have hinv : MetricInverseInBasis_gen (I := I) g₂ x basis
      (identityInvMetric (Idx := Fin (Module.finrank Real (TangentSpace I x)))) := by
    intro i j; constructor <;> simp [identityInvMetric, diagonalInvMetric, hON]
  -- unfold the jet sum and fix the `iterCov g₂` currency
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]
  set p0 := Real.sqrt (normSq0S (I := I) g₂ x (r + 0) (iterCov (I := I) g₂ r T 0 x)) with hp0def
  set p1 := Real.sqrt (normSq0S (I := I) g₂ x (r + 1) (iterCov (I := I) g₂ r T 1 x)) with hp1def
  set p2 := Real.sqrt (normSq0S (I := I) g₂ x (r + 2) (iterCov (I := I) g₂ r T 2 x)) with hp2def
  have hp0nn : 0 ≤ p0 := Real.sqrt_nonneg _
  have hp1nn : 0 ≤ p1 := Real.sqrt_nonneg _
  have hp2nn : 0 ≤ p2 := Real.sqrt_nonneg _
  -- the three per-piece bounds, defeq-normalised into the `iterCov g₂` jet currency
  have hb1' : Real.sqrt (normSq0S (I := I) g₂ x (r + 3)
        (covStep (I := I) g₂ (r + 2)
          (covStep (I := I) g₂ (r + 1) (diffStep (I := I) g₁ g₂ r T)) x)) ≤
      C₂ * (p0 + p1 + p2) := hC₂ T x hx
  have hb2' : Real.sqrt (normSq0S (I := I) g₂ x (r + 3)
        (covStep (I := I) g₂ (r + 2)
          (diffStep (I := I) g₁ g₂ (r + 1) (diffStep (I := I) g₁ g₂ r T)) x)) ≤
      CA1 * (Real.sqrt (normSq0S (I := I) g₂ x (r + 1) (diffStep (I := I) g₁ g₂ r T x))
        + Real.sqrt (normSq0S (I := I) g₂ x (r + 2)
            (covStep (I := I) g₂ (r + 1) (diffStep (I := I) g₁ g₂ r T) x))) :=
    covStepDiff_of_jets (I := I) g₁ g₂ (r + 1) (diffStep (I := I) g₁ g₂ r T) x
      (metricUniformEquivalentOn_symm (I := I) hEq) hJet1 hJet2 hjet hx
  have hb3' : Real.sqrt (normSq0S (I := I) g₂ x (r + 3)
        (covStep (I := I) g₂ (r + 2)
          (diffStep (I := I) g₁ g₂ (r + 1) (iterCov (I := I) g₂ r T 1)) x)) ≤
      CA1 * (p1 + p2) :=
    covStepDiff_of_jets (I := I) g₁ g₂ (r + 1) (iterCov (I := I) g₂ r T 1) x
      (metricUniformEquivalentOn_symm (I := I) hEq) hJet1 hJet2 hjet hx
  -- fold the inner `A ⋆ T` jets of the middle piece into `p0, p1`
  have hb2a' : Real.sqrt (normSq0S (I := I) g₂ x (r + 1) (diffStep (I := I) g₁ g₂ r T x)) ≤
      cs0 * p0 :=
    diffStep_jet_one_le (I := I) g₁ g₂ r T hEq hjet hx
  have hb2b' : Real.sqrt (normSq0S (I := I) g₂ x (r + 2)
        (covStep (I := I) g₂ (r + 1) (diffStep (I := I) g₁ g₂ r T) x)) ≤
      CA0 * (p0 + p1) :=
    covStepDiff_of_jets (I := I) g₁ g₂ r T x
      (metricUniformEquivalentOn_symm (I := I) hEq) hJet1 hJet2 hjet hx
  have hb2'' : Real.sqrt (normSq0S (I := I) g₂ x (r + 3)
        (covStep (I := I) g₂ (r + 2)
          (diffStep (I := I) g₁ g₂ (r + 1) (diffStep (I := I) g₁ g₂ r T)) x)) ≤
      CA1 * (cs0 * p0 + CA0 * (p0 + p1)) :=
    le_trans hb2' (mul_le_mul_of_nonneg_left (add_le_add hb2a' hb2b') hCA1nn)
  -- abbreviate the three heavy fibre values as opaque locals so the fibre-norm triangle
  -- unifies against variables rather than the `covStep`/`diffStep` bodies (the
  -- `iterCovG1_le` taming idiom)
  set av := covStep (I := I) g₂ (r + 2)
    (covStep (I := I) g₂ (r + 1) (diffStep (I := I) g₁ g₂ r T)) x with hav
  set bv := covStep (I := I) g₂ (r + 2)
    (diffStep (I := I) g₁ g₂ (r + 1) (diffStep (I := I) g₁ g₂ r T)) x with hbv
  set cv := covStep (I := I) g₂ (r + 2)
    (diffStep (I := I) g₁ g₂ (r + 1) (iterCov (I := I) g₂ r T 1)) x with hcv
  clear_value av bv cv
  -- assemble
  have hSle : C₂ * (p0 + p1 + p2) + CA1 * (cs0 * p0 + CA0 * (p0 + p1)) + CA1 * (p1 + p2)
      ≤ (C₂ + CA1 * (cs0 + CA0 + 1)) * (p0 + p1 + p2) := by
    nlinarith [mul_nonneg (mul_nonneg hCA1nn hcs0nn) hp1nn,
      mul_nonneg (mul_nonneg hCA1nn hcs0nn) hp2nn,
      mul_nonneg (mul_nonneg hCA1nn hCA0nn) hp2nn,
      mul_nonneg hCA1nn hp0nn]
  have hfin : (C₂ + CA1 * (cs0 + CA0 + 1)) * (p0 + p1 + p2)
      ≤ max 0 (C₂ + CA1 * (cs0 + CA0 + 1)) * (p0 + p1 + p2) :=
    mul_le_mul_of_nonneg_right (le_max_right _ _)
      (add_nonneg (add_nonneg hp0nn hp1nn) hp2nn)
  calc Real.sqrt (normSq0S (I := I) g₂ x (r + 3)
        (covStep (I := I) g₂ (r + 2) (telescAccum (I := I) g₁ g₂ r T 2) x))
      ≤ Real.sqrt (normSq0S (I := I) g₂ x (r + 3) av)
          + Real.sqrt (normSq0S (I := I) g₂ x (r + 3) bv)
          + Real.sqrt (normSq0S (I := I) g₂ x (r + 3) cv) := by
        rw [hsplitx]
        refine le_trans (sqrt_normSq0S_add_le (I := I) g₂ (av + bv) cv basis hinv) ?_
        exact add_le_add (sqrt_normSq0S_add_le (I := I) g₂ av bv basis hinv) (le_refl _)
    _ ≤ C₂ * (p0 + p1 + p2) + CA1 * (cs0 * p0 + CA0 * (p0 + p1)) + CA1 * (p1 + p2) :=
        add_le_add (add_le_add hb1' hb2'') hb3'
    _ ≤ (C₂ + CA1 * (cs0 + CA0 + 1)) * (p0 + p1 + p2) := hSle
    _ ≤ max 0 (C₂ + CA1 * (cs0 + CA0 + 1)) * (p0 + p1 + p2) := hfin

/-- Compatibility wrapper for the explicit level-two accumulator bound. -/
theorem covStepAcc2_le
    {K : Set M} (g₁ g₂ : SmoothRiemannianMetric I M) (r : ℕ)
    {Λ Λ' Λ'' Λ''' : ℝ}
    (hEq : MetricUniformEquivalentOn (I := I) K g₁ g₂ Λ)
    (hjet : MetricCovDerivOrderBoundOn (I := I) K 1 g₂ g₁ Λ')
    (hJet1 : MetricCovDerivOrderBoundOn (I := I) K 1 g₁ g₂ Λ')
    (hJet2 : MetricCovDerivOrderBoundOn (I := I) K 2 g₁ g₂ Λ'')
    (hJet3 : MetricCovDerivOrderBoundOn (I := I) K 3 g₁ g₂ Λ''') :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (T : Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
          (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) r) (x : M), x ∈ K →
        Real.sqrt (normSq0S (I := I) g₂ x (r + 3)
            (covStep (I := I) g₂ (r + 2) (telescAccum (I := I) g₁ g₂ r T 2) x)) ≤
          C * ∑ k ∈ Finset.range 3,
            Real.sqrt (normSq0S (I := I) g₂ x (r + k) (iterCov (I := I) g₂ r T k x)) := by
  refine ⟨covStepAcc2C (E := E) r Λ Λ' Λ'' Λ''', ?_, ?_⟩
  · dsimp [covStepAcc2C]
    exact le_max_left _ _
  · exact covStepAcc2_bound (I := I) g₁ g₂ r hEq hjet hJet1 hJet2 hJet3

/-- Explicit coefficient for the third iterated-covariant-derivative transfer. -/
noncomputable def iterCovThreeC (r : ℕ) (Λ Λ' Λ'' Λ''' : ℝ) : ℝ :=
  max 0 (Dtower (Module.finrank ℝ E)
    ((3 / 2 : ℝ) * (Real.sqrt (Λ ^ 3) * Λ')) r
    (fun m => if m = 1 then
      (r : ℝ) * Real.sqrt ((Module.finrank ℝ E : ℝ) ^ (r + 2)) *
        (3 / 2 * Λ ^ 4 * (Λ'' + Λ * Λ' ^ 2) +
          (3 / 2 : ℝ) * (Real.sqrt (Λ ^ 3) * Λ'))
    else if m = 2 then covStepAcc2C (E := E) r Λ Λ' Λ'' Λ''' else 0) 3)

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 400000 in
/-- **The `∇₁³`-jet telescoping bound (brick T-B), unconditional `N = 3` endpoint.**

Under the metric-jet bundle (`Λ`-comparability of `g₁, g₂` on `K`; `∇g₂/g₁ ≤ Λ'`; `∇g₁, ∇²g₁,
∇³g₁ / g₂ ≤ Λ', Λ'', Λ'''`), the `g₂`-fibre norm of the third `∇₁`-iterated derivative of any
rank-`r` field `T` is controlled on `K` by a single constant — uniform in `T` and `x` — times the
`∇₂`-jets of `T` through order 3:

```
|∇₁³T|_{g₂} ≤ C · ∑_{k ∈ range 4} |iterCov g₂ r T k|_{g₂}.
```

This is the `N = 3` case of `iterCovG1_le`, with `hAcc` discharged outright: `m = 0, 1` as in
`iterCovG1_two`, and `m = 2` by the a=2 accumulator bound `covStepAcc2_le` (the
`covStepDiff2_exists_const` glue).  The constant is existential because the a=2 atom's is; it is
realised as the `Dtower` recursion with `Racc 1` the explicit a=1 constant and `Racc 2` the
`covStepAcc2_le` constant.  For `N ≥ 4` the remaining input is the general accumulator bound
`hAcc_of_jets` below. -/
theorem iterCovThree_le
    {K : Set M} (g₁ g₂ : SmoothRiemannianMetric I M) (r : ℕ)
    {Λ Λ' Λ'' Λ''' : ℝ}
    (hEq : MetricUniformEquivalentOn (I := I) K g₁ g₂ Λ)
    (hjet : MetricCovDerivOrderBoundOn (I := I) K 1 g₂ g₁ Λ')
    (hJet1 : MetricCovDerivOrderBoundOn (I := I) K 1 g₁ g₂ Λ')
    (hJet2 : MetricCovDerivOrderBoundOn (I := I) K 2 g₁ g₂ Λ'')
    (hJet3 : MetricCovDerivOrderBoundOn (I := I) K 3 g₁ g₂ Λ''') :
    ∀ (T : Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
        (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) r) (x : M), x ∈ K →
      Real.sqrt (normSq0S (I := I) g₂ x (r + 3) (iterCov (I := I) g₁ r T 3 x)) ≤
        iterCovThreeC (E := E) r Λ Λ' Λ'' Λ''' *
          ∑ k ∈ Finset.range 4,
            Real.sqrt (normSq0S (I := I) g₂ x (r + k) (iterCov (I := I) g₂ r T k x)) := by
  classical
  let C2acc : ℝ := covStepAcc2C (E := E) r Λ Λ' Λ'' Λ'''
  have hC2accnn : 0 ≤ C2acc := by
    dsimp [C2acc, covStepAcc2C]
    exact le_max_left _ _
  have hC2acc := covStepAcc2_bound (I := I) g₁ g₂ r
    hEq hjet hJet1 hJet2 hJet3
  intro T x hx
  have hLnn : (0 : ℝ) ≤ Λ := le_trans zero_le_one hEq.1
  have hL'nn : (0 : ℝ) ≤ Λ' := le_trans (Real.sqrt_nonneg _) (hjet x hx)
  have hL''nn : (0 : ℝ) ≤ Λ'' := le_trans (Real.sqrt_nonneg _) (hJet2 x hx)
  have hCA0nn : (0 : ℝ) ≤ (r : ℝ) * Real.sqrt ((Module.finrank ℝ E : ℝ) ^ (r + 2)) *
      (3 / 2 * Λ ^ 4 * (Λ'' + Λ * Λ' ^ 2) + (3 / 2 : ℝ) * (Real.sqrt (Λ ^ 3) * Λ')) := by
    positivity
  have hRnn : ∀ m : ℕ, (0 : ℝ) ≤ if m = 1 then
      (r : ℝ) * Real.sqrt ((Module.finrank ℝ E : ℝ) ^ (r + 2)) *
        (3 / 2 * Λ ^ 4 * (Λ'' + Λ * Λ' ^ 2) + (3 / 2 : ℝ) * (Real.sqrt (Λ ^ 3) * Λ'))
      else if m = 2 then C2acc else 0 := by
    intro m
    split
    · exact hCA0nn
    · split
      · exact hC2accnn
      · exact le_refl 0
  refine le_trans (iterCovG1_le (I := I) g₁ g₂ r T x
    (fun m => if m = 1 then
      (r : ℝ) * Real.sqrt ((Module.finrank ℝ E : ℝ) ^ (r + 2)) *
        (3 / 2 * Λ ^ 4 * (Λ'' + Λ * Λ' ^ 2) + (3 / 2 : ℝ) * (Real.sqrt (Λ ^ 3) * Λ'))
    else if m = 2 then C2acc else 0) hRnn hEq hjet hx 3 ?_) ?_
  · -- discharge `hAcc` for `m < 3`
    intro m hm
    interval_cases m
    · -- `m = 0`: the accumulator is `0`
      simp only [if_neg (by norm_num : (0 : ℕ) ≠ 1), if_neg (by norm_num : (0 : ℕ) ≠ 2), zero_mul]
      rw [show telescAccum (I := I) g₁ g₂ r T 0 = 0 from rfl, covStep_zero']
      simp only [ContMDiffSection.coe_zero, Pi.zero_apply, sqrt_normSq0S_zero, le_refl]
    · -- `m = 1`: the accumulator is `diffStep g₁ g₂ r T`; bound its `∇₂` by `covStepDiff_of_jets`
      simp only [reduceIte]
      rw [telescAccum_one (I := I) g₁ g₂ r T]
      refine le_trans (covStepDiff_of_jets (I := I) g₁ g₂ r T x
        (metricUniformEquivalentOn_symm (I := I) hEq) hJet1 hJet2 hjet hx) ?_
      rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]
      refine mul_le_mul_of_nonneg_left ?_ hCA0nn
      have hA : Real.sqrt (normSq0S (I := I) g₂ x r (T x))
          = Real.sqrt (normSq0S (I := I) g₂ x (r + 0) (iterCov (I := I) g₂ r T 0 x)) := rfl
      have hB : Real.sqrt (normSq0S (I := I) g₂ x (r + 1) (covStep (I := I) g₂ r T x))
          = Real.sqrt (normSq0S (I := I) g₂ x (r + 1) (iterCov (I := I) g₂ r T 1 x)) := rfl
      rw [hA, hB]
      exact le_add_of_nonneg_right (Real.sqrt_nonneg _)
    · -- `m = 2`: the a=2 accumulator bound `covStepAcc2_le`
      simp only [reduceIte]
      rw [Finset.sum_range_succ]
      exact le_trans (hC2acc T x hx)
        (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (Real.sqrt_nonneg _)) hC2accnn)
  · -- fold the `Dtower` constant into its `max 0` majorant
    exact mul_le_mul_of_nonneg_right (le_max_right _ _)
      (Finset.sum_nonneg fun k _ => Real.sqrt_nonneg _)

/-- Compatibility wrapper for the explicit third-jet transfer bound. -/
theorem iterCovG1_three
    {K : Set M} (g₁ g₂ : SmoothRiemannianMetric I M) (r : ℕ)
    {Λ Λ' Λ'' Λ''' : ℝ}
    (hEq : MetricUniformEquivalentOn (I := I) K g₁ g₂ Λ)
    (hjet : MetricCovDerivOrderBoundOn (I := I) K 1 g₂ g₁ Λ')
    (hJet1 : MetricCovDerivOrderBoundOn (I := I) K 1 g₁ g₂ Λ')
    (hJet2 : MetricCovDerivOrderBoundOn (I := I) K 2 g₁ g₂ Λ'')
    (hJet3 : MetricCovDerivOrderBoundOn (I := I) K 3 g₁ g₂ Λ''') :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (T : Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
          (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) r) (x : M), x ∈ K →
        Real.sqrt (normSq0S (I := I) g₂ x (r + 3) (iterCov (I := I) g₁ r T 3 x)) ≤
          C * ∑ k ∈ Finset.range 4,
            Real.sqrt (normSq0S (I := I) g₂ x (r + k) (iterCov (I := I) g₂ r T k x)) := by
  refine ⟨iterCovThreeC (E := E) r Λ Λ' Λ'' Λ''', ?_, ?_⟩
  · dsimp [iterCovThreeC]
    exact le_max_left _ _
  · exact iterCovThree_le (I := I) g₁ g₂ r hEq hjet hJet1 hJet2 hJet3

/-- **FRONTIER (`sorry`) — the general accumulator bound (the a ≥ 3 campaign).**

The general-`m` form of `covStepAcc2_le`: under `Λ`-comparability, the role-asymmetric first-order
jet `∇g₂/g₁ ≤ Λ'`, and `g₁`-jets against `g₂` through order `m + 1` (`hJets`), the base covariant
derivative of the level-`m` telescoping accumulator is bounded on `K` by a uniform constant times
the `∇₂`-jets of `T`:

```
|∇₂(telescAccum g₁ g₂ r T m)|_{g₂} ≤ C · ∑_{k ∈ range (m+2)} |iterCov g₂ r T k|_{g₂}.
```

This is exactly `iterCovG1_le`'s hypothesis `hAcc` at level `m` (with a `T, x`-uniform constant),
so proving it closes the unconditional general-`N` telescoping bound.  It is a THEOREM for `m ≤ 2`:
`m = 0` (accumulator `0`), `m = 1` (`covStepDiff_of_jets`), `m = 2` (`covStepAcc2_le`, where the
jet sum is even sharp at `range (m+1)`).  For `m ≥ 3` the expansion of `∇₂(telescAccum m)` produces
all words in `{∇₂, A}` of total weight `m + 1` with at least one `A`-factor: the needed atoms are
the a-fold base-Leibniz jets `∇₂ᵃ(A ⋆ ·)` for `a ≤ m` (the a=3+ siblings of
`covStepDiff2_exists_const`, each requiring `g₁`-jets through order `a + 1`) composed over the
lower-order accumulators — the honest multi-session frontier.  Stated here (sorry) as the single
remaining input; do not consume it downstream while the `sorry` stands. -/
theorem hAcc_of_jets
    {K : Set M} (g₁ g₂ : SmoothRiemannianMetric I M) (r m : ℕ)
    {Λ Λ' : ℝ} (Λs : ℕ → ℝ)
    (hEq : MetricUniformEquivalentOn (I := I) K g₁ g₂ Λ)
    (hjet : MetricCovDerivOrderBoundOn (I := I) K 1 g₂ g₁ Λ')
    (hJets : ∀ j, 1 ≤ j → j ≤ m + 1 → MetricCovDerivOrderBoundOn (I := I) K j g₁ g₂ (Λs j)) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (T : Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
          (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) r) (x : M), x ∈ K →
        Real.sqrt (normSq0S (I := I) g₂ x (r + m + 1)
            (covStep (I := I) g₂ (r + m) (telescAccum (I := I) g₁ g₂ r T m) x)) ≤
          C * ∑ k ∈ Finset.range (m + 2),
            Real.sqrt (normSq0S (I := I) g₂ x (r + k) (iterCov (I := I) g₂ r T k x)) := by
  sorry

end RicciFlow
end PDE
end DifferentialGeometry

end
