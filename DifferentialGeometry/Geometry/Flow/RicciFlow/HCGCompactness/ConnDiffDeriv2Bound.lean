import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.AllTimesBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.MetricCovDerivLinear

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# Order-2 connection-difference-derivative: the base-Leibniz jet atom (`hAcc`, m ≥ 2)

The `∇₁ᴺ`-jet telescoping bound `iterCovG1_le` (`HCGCompactness/UnifCovSumCross.lean`) is a proved
conditional theorem whose single named frontier is the accumulator hypothesis

```
hAcc m : √normSq0S(g₂, r+m+1, ∇₂(telescAccum g₁ g₂ r T m)) ≤ Racc m · ∑_{k≤m+1} √normSq0S(g₂, iterCov g₂ r T k)
```

`hAcc` is a theorem at `m = 0` (the accumulator is `0`) and `m = 1` (it is `diffStep g₁ g₂ r T`, so
its base derivative is the a=1 piece `covStepDiff_of_jets`).  For `m ≥ 2` the recursion
`telescAccum (m+1) = ∇₁(telescAccum m) + (∇₁−∇₂)(∇₂ᵐT)` forces a **second** base derivative of a
connection-difference step, e.g. at `m = 2`:

```
∇₂(telescAccum 2)  =  [∇₂(A ⋆ ∇₂T)]        -- a=1, covStepDiff_of_jets  (committed)
                    + [∇₂(A ⋆ (A ⋆ T))]     -- a=1, covStepDiff_of_jets  (committed, composition)
                    + [∇₂²(A ⋆ T)]           -- a=2, THIS FILE            (the single new atom)
```

with `A = Γ₁ − Γ₂ = connection difference`.  The only genuinely new mathematical content for
`m ≥ 2` is the **a=2 (and higher) base-Leibniz jet of a single connection-difference step**
`∇₂²(A ⋆ S) = covStep g₂ (covStep g₂ (diffStep g₁ g₂ s S))`, which this file isolates.  See
`ConnDiffDeriv2Bound.md` for the full route ruling, the `hAcc m ⇒ ∇₂^a A` reduction, and the honest
size estimate for the a ≥ 2 campaign.

Route (RULED IN — route (i) of the recon): the atom is bounded by iterating the differentiated Koszul
identity `connDiff_koszul_deriv` (`ChristoffelDiffKoszulDeriv.lean`, the a=1 identity landed for B2).
Differentiating it once more with the base connection `∇₂` keeps the right-hand side in `metricCovDeriv`
currency at order `a + 1 = 3`, giving the recursion
`|∇₂²A| ≲ |∇₂³g₁| + |∇₂²g₁|·|A| + |∇₂g₁|·|∇₂A|`, whose a=0 factor `|A|` is `lcDiff_norm_le` and whose
a=1 factor `|∇₂A|` is `covDerivConnDiff_gJet_le` (B2, committed).  This is why the metric-jet
hypotheses reach order `3` (one above the a=2 order) and carry the metric-role asymmetry
(`∇g₁ w.r.t. g₂` in `hJet1/hJet2/hJet3`, `∇g₂ w.r.t. g₁` in `hJet1'`, sharing `Λ'`).
-/

noncomputable section

open Bundle Manifold Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff BigOperators

namespace DifferentialGeometry
namespace HCGCompactness

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [Module.Finite ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [T2Space M] [IsManifold I ∞ M] [SigmaCompactSpace M] [BoundarylessManifold I M]
variable [CompactSpace M] [I.Boundaryless]

/-- **FRONTIER (`sorry`) — the a=2 base-Leibniz jet of a single connection-difference step.**

Under `Λ`-comparability of `g₁, g₂` on `K` and metric covariant-derivative bounds through **order 3**
(`Λ'`, `Λ''`, `Λ'''` for `∇g₁, ∇²g₁, ∇³g₁` measured against `g₂`; `Λ'` for `∇g₂` against `g₁` — the
metric-role asymmetry), the `g₂`-fibre norm of the **second** base covariant derivative of a single
connection-difference step `∇₂²(A ⋆ S) = covStep g₂ (covStep g₂ (diffStep g₁ g₂ s S))` is controlled at
every `x ∈ K` by a single constant `C₂` (uniform in the rank-`s` field `S` and in `x`) times the
order-≤2 jets of `S`:

```
√normSq0S(g₂, s+3, ∇₂²(A ⋆ S) x) ≤ C₂ · (|S x| + |∇₂S x| + |∇₂²S x|).
```

The constant is existential (it depends only on `Λ, Λ', Λ'', Λ''', finrank E, s`, not on `S` or `x`),
which is the honest state-before-prove interface: the a≥2 campaign has not yet pinned its explicit
polynomial, only its structure (order-3 metric jets, order-2 `S`-jets, role asymmetry).  A downstream
`hAcc`-facing consumer reads `Racc 2 := C₂`.

**What discharges the `sorry` (two ingredients, one genuinely new):**

1. THE FRONTIER — the a=2 differentiated Christoffel-difference Koszul identity `connDiff_koszul_deriv2`
   (not yet in the tree): differentiate the committed a=1 identity `connDiff_koszul_deriv`
   (`Geometry/Connection/LeviCivita/ChristoffelDiffKoszulDeriv.lean`) once more along a base direction
   with the metric-compatibility Leibniz.  Its RHS stays in `metricCovDeriv` currency at order 3
   (`∇₂³g₁` combos) plus `∇₂²g₁·A` and `∇₂g₁·∇₂A` correction terms.  This is a new
   differential-geometric identity of the same character and size as `connDiff_koszul_deriv`
   (~150–300 lines), plus its a=2 dual core (analogue of `ConnDiffDerivBound`'s `covDerivConnDiff_g1_le`)
   giving `|∇₂²A|`.  Comparability at orders 4/5 is already covered by the general-`s`
   `sqrt_normSq0S_comp` (`ConnDiffDerivBound.lean`).

2. MECHANICAL — the a=2 base-Leibniz operator identity `∇₂²(A ⋆ S) = (∇₂²A) ⋆ S + 2 (∇₂A) ⋆ (∇₂S)
   + A ⋆ (∇₂²S)` (the a=2 analogue of `diffStep_leibniz` in `MetricCovDerivLinear.lean`, pure `covStep`
   / `diffStep` operator algebra), then the fibre Cauchy–Schwarz product bound composing the a=0 atom
   `|A| ≲ √(Λ³)Λ'` (`lcDiff_norm_le`), the a=1 atom `|∇₂A| ≲ Λ⁴(Λ''+ΛΛ'²)`
   (`covDerivConnDiff_gJet_le`), and the a=2 atom `|∇₂²A|` from (1). -/
theorem covStepDiff2_exists_const
    {K : Set M} (g₁ g₂ : SmoothRiemannianMetric I M) (s : ℕ)
    {Λ Λ' Λ'' Λ''' : ℝ}
    (hEq : MetricUniformEquivalentOn (I := I) K g₂ g₁ Λ)
    (hJet1 : MetricCovDerivOrderBoundOn (I := I) K 1 g₁ g₂ Λ')
    (hJet2 : MetricCovDerivOrderBoundOn (I := I) K 2 g₁ g₂ Λ'')
    (hJet3 : MetricCovDerivOrderBoundOn (I := I) K 3 g₁ g₂ Λ''')
    (hJet1' : MetricCovDerivOrderBoundOn (I := I) K 1 g₂ g₁ Λ') :
    ∃ C₂ : ℝ, 0 ≤ C₂ ∧
      ∀ (S : Tensor0SBundle.Tensor0SField (𝕜 := ℝ) (E := E) (H := H)
            (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) s) (x : M), x ∈ K →
        Real.sqrt (normSq0S (I := I) g₂ x (s + 3)
            (covStep (I := I) g₂ (s + 2)
              (covStep (I := I) g₂ (s + 1) (diffStep (I := I) g₁ g₂ s S)) x)) ≤
          C₂ * (Real.sqrt (normSq0S (I := I) g₂ x s (S x))
            + Real.sqrt (normSq0S (I := I) g₂ x (s + 1) (covStep (I := I) g₂ s S x))
            + Real.sqrt (normSq0S (I := I) g₂ x (s + 2)
                (covStep (I := I) g₂ (s + 1) (covStep (I := I) g₂ s S) x))) := by
  sorry

end HCGCompactness
end DifferentialGeometry

end
