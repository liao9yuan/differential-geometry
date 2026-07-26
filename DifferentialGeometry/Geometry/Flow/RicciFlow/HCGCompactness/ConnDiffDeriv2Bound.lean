import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.AllTimesBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.MetricCovDerivLinear
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.ConnDiffDerivBound
import DifferentialGeometry.Geometry.Connection.LeviCivita.ChristoffelDiffKoszulDeriv2

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

/-- **The a=2 operator-form base-connection Leibniz split** (deliverable 2, operator form).

Expanding the second *base* covariant derivative of a single connection-difference step
`∇₂²(A ⋆ S) = covStep g₂ (covStep g₂ (diffStep g₁ g₂ s S))` by applying the committed base Leibniz
`diffStep_leibniz` (`MetricCovDerivLinear.lean`) twice regroups it, as pure `covStep`/`diffStep`
operator algebra, into

* the **`A ⋆ ∇₂²S` term** `diffStep g₁ g₂ (s+2) (covStep g₂ (s+1) (covStep g₂ s S))` (the single
  connection-difference of the twice-base-differentiated `S`), plus
* the **mixed commutator on `∇₂S`** `∇₂∇₁(∇₂S) − ∇₁∇₂(∇₂S)` (morally `(∇₂A) ⋆ ∇₂S`), plus
* the **base derivative of the mixed commutator on `S`** `∇₂(∇₂∇₁S − ∇₁∇₂S)` (morally
  `(∇₂²A) ⋆ S + (∇₂A) ⋆ ∇₂S`).

This is the structural backbone of the `covStepDiff2_exists_const` fibre assembly: the first term is
bounded by the a=0 connection-difference atom `|A| · |∇₂²S|`, the mixed commutator on `∇₂S` by the a=1
atom `|∇₂A| · |∇₂S|`, and the **only new frontier** is the fibre norm of the last term (its
`(∇₂²A) ⋆ S` part needs the a=2 connection-difference jet `∇₂²A`, i.e. the dual core below). The
identity itself carries no `[InnerProductSpace]`: it is `covStep`/`diffStep` additivity only. -/
theorem covStepDiff2_opLeibniz
    (g₁ g₂ : SmoothRiemannianMetric I M) (s : ℕ)
    (S : Tensor0SBundle.Tensor0SField (𝕜 := ℝ) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) s) :
    covStep (I := I) g₂ (s + 2)
        (covStep (I := I) g₂ (s + 1) (diffStep (I := I) g₁ g₂ s S))
      = diffStep (I := I) g₁ g₂ (s + 2)
          (covStep (I := I) g₂ (s + 1) (covStep (I := I) g₂ s S))
        + (covStep (I := I) g₂ (s + 2)
              (covStep (I := I) g₁ (s + 1) (covStep (I := I) g₂ s S))
            - covStep (I := I) g₁ (s + 2)
              (covStep (I := I) g₂ (s + 1) (covStep (I := I) g₂ s S)))
        + (covStep (I := I) g₂ (s + 2)
              (covStep (I := I) g₂ (s + 1) (covStep (I := I) g₁ s S))
            - covStep (I := I) g₂ (s + 2)
              (covStep (I := I) g₁ (s + 1) (covStep (I := I) g₂ s S))) := by
  rw [diffStep_leibniz (I := I) g₁ g₂ s S, covStep_add, covStep_sub,
    diffStep_leibniz (I := I) g₁ g₂ (s + 1) (covStep (I := I) g₂ s S)]

/-! ### Metric-jet currency bridges (orders 1–3)

The differentiated Koszul identity `connDiff_koszul_deriv2` outputs the metric jets of `g₁` in the
`totalNabla0S`/`nabla0SFun` currency: `field₁ = totalNabla0S 2 (LC g₂) (mtf g₁)` (`= ∇₂g₁`),
`field₂ = totalNabla0S 3 (LC g₂) field₁` (`= ∇₂²g₁`), and `nabla0SFun 4 (LC g₂) V field₂`
(`= ∇₂³g₁`).  These bridges identify each with the HCG `metricCovDeriv g₁ g₂ a` currency (order
`a = 1, 2, 3`), so the dual core can run its Cauchy–Schwarz in the `metricCovDeriv` currency that the
jet-bound hypotheses `MetricCovDerivOrderBoundOn K a g₁ g₂ Λ` are stated in.  Order-1/2 are the
re-derived siblings of `ConnDiffDerivBound`'s `private` `field_eq_mcd1`/`nabla3_eq_mcd2`; order-3 is
the new sibling the a=2 campaign needs. -/

/-- Currency bridge (order 1): `field₁ = totalNabla0S 2 (LC g₂) (mtf g₁) = metricCovDeriv g₁ g₂ 1`.
Re-derived sibling of `ConnDiffDerivBound.field_eq_mcd1` (private there). -/
theorem field1_eq_mcd1
    [VectorBundle ℝ E (TangentSpace I : M → Type _)]
    [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]
    (g₁ g₂ : SmoothRiemannianMetric I M) :
    (Tensor0SBundle.totalNabla0S (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 2
        (DifferentialGeometry.Integral.Connection.LeviCivita (I := I) g₂)
        (Tensor0SBundle.metricTensorField (I := I) g₁)
        (DifferentialGeometry.Integral.Connection.metricField_totalReg (I := I) g₁ g₂))
      = metricCovDeriv (I := I) g₁ g₂ 1 := by
  haveI : IsManifold I 1 M :=
    IsManifold.of_le (I := I) (M := M) (n := ∞) (by decide : (1 : WithTop ℕ∞) ≤ ∞)
  haveI : IsManifold I ((∞ : WithTop ℕ∞) + 1) M := by change IsManifold I ∞ M; infer_instance
  apply DFunLike.ext
  intro x
  rw [Tensor0SBundle.totalNabla0S_apply]
  exact (metricCovDerivStep_apply (I := I) g₂ 0
    (Tensor0SBundle.metricTensorField (I := I) g₁) x).symm

/-- Currency bridge (order 2): `field₂ = totalNabla0S 3 (LC g₂) field₁ = metricCovDeriv g₁ g₂ 2`. -/
theorem field2_eq_mcd2
    [VectorBundle ℝ E (TangentSpace I : M → Type _)]
    [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]
    (g₁ g₂ : SmoothRiemannianMetric I M) :
    (Tensor0SBundle.totalNabla0S (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 3
        (DifferentialGeometry.Integral.Connection.LeviCivita (I := I) g₂)
        (Tensor0SBundle.totalNabla0S (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 2
          (DifferentialGeometry.Integral.Connection.LeviCivita (I := I) g₂)
          (Tensor0SBundle.metricTensorField (I := I) g₁)
          (DifferentialGeometry.Integral.Connection.metricField_totalReg (I := I) g₁ g₂))
        (DifferentialGeometry.Integral.Connection.metricField_totalReg2 (I := I) g₁ g₂))
      = metricCovDeriv (I := I) g₁ g₂ 2 := by
  haveI : IsManifold I 1 M :=
    IsManifold.of_le (I := I) (M := M) (n := ∞) (by decide : (1 : WithTop ℕ∞) ≤ ∞)
  haveI : IsManifold I ((∞ : WithTop ℕ∞) + 1) M := by change IsManifold I ∞ M; infer_instance
  apply DFunLike.ext
  intro x
  rw [Tensor0SBundle.totalNabla0S_apply, field1_eq_mcd1 (I := I) g₁ g₂]
  exact (metricCovDerivStep_apply (I := I) g₂ 1 (metricCovDeriv (I := I) g₁ g₂ 1) x).symm

/-- Currency bridge (order 2, directional): `nabla0SFun 3 (LC g₂) W field₁` is `metricCovDeriv g₁ g₂ 2`
with the derivative direction `W x` in the leading slot.  Re-derived sibling of
`ConnDiffDerivBound.nabla3_eq_mcd2` (private there). -/
theorem nabla3_eq_mcd2
    [VectorBundle ℝ E (TangentSpace I : M → Type _)]
    [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]
    (g₁ g₂ : SmoothRiemannianMetric I M)
    (W : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _))
    (x : M) (slots : Fin 3 → TangentSpace I x) :
    Tensor0SBundle.nabla0SFun (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 3
        (DifferentialGeometry.Integral.Connection.LeviCivita (I := I) g₂) W
        (Tensor0SBundle.totalNabla0S (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 2
          (DifferentialGeometry.Integral.Connection.LeviCivita (I := I) g₂)
          (Tensor0SBundle.metricTensorField (I := I) g₁)
          (DifferentialGeometry.Integral.Connection.metricField_totalReg (I := I) g₁ g₂)) x slots
      = metricCovDeriv (I := I) g₁ g₂ 2 x (Fin.cons (W x) slots) := by
  rw [field1_eq_mcd1 (I := I) g₁ g₂,
    show metricCovDeriv (I := I) g₁ g₂ 2
        = metricCovDerivStep (I := I) g₂ 1 (metricCovDeriv (I := I) g₁ g₂ 1) from rfl,
    metricCovDerivStep_apply]
  exact (Tensor0SBundle.totalNabla0SFun_apply_section (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M)
    3 (DifferentialGeometry.Integral.Connection.LeviCivita (I := I) g₂) W
    (metricCovDeriv (I := I) g₁ g₂ 1) x slots).symm

/-- **Currency bridge (order 3, directional): the new a=2 sibling.**  The `∇₂³g₁` combo
`nabla0SFun 4 (LC g₂) V field₂` of `connDiff_koszul_deriv2`'s right-hand side is the third metric
covariant derivative `metricCovDeriv g₁ g₂ 3` with the derivative direction `V x` in the leading slot.
This is the order-3 analogue of `nabla3_eq_mcd2`; it puts the leading `∇₂³g₁` combos of the
twice-differentiated Koszul identity into the `metricCovDeriv 3` currency the a=2 dual core bounds. -/
theorem nabla4_eq_mcd3
    [VectorBundle ℝ E (TangentSpace I : M → Type _)]
    [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]
    (g₁ g₂ : SmoothRiemannianMetric I M)
    (V : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _))
    (x : M) (slots : Fin 4 → TangentSpace I x) :
    Tensor0SBundle.nabla0SFun (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 4
        (DifferentialGeometry.Integral.Connection.LeviCivita (I := I) g₂) V
        (Tensor0SBundle.totalNabla0S (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 3
          (DifferentialGeometry.Integral.Connection.LeviCivita (I := I) g₂)
          (Tensor0SBundle.totalNabla0S (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 2
            (DifferentialGeometry.Integral.Connection.LeviCivita (I := I) g₂)
            (Tensor0SBundle.metricTensorField (I := I) g₁)
            (DifferentialGeometry.Integral.Connection.metricField_totalReg (I := I) g₁ g₂))
          (DifferentialGeometry.Integral.Connection.metricField_totalReg2 (I := I) g₁ g₂)) x slots
      = metricCovDeriv (I := I) g₁ g₂ 3 x (Fin.cons (V x) slots) := by
  rw [field2_eq_mcd2 (I := I) g₁ g₂,
    show metricCovDeriv (I := I) g₁ g₂ 3
        = metricCovDerivStep (I := I) g₂ 2 (metricCovDeriv (I := I) g₁ g₂ 2) from rfl,
    metricCovDerivStep_apply]
  exact (Tensor0SBundle.totalNabla0SFun_apply_section (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M)
    4 (DifferentialGeometry.Integral.Connection.LeviCivita (I := I) g₂) V
    (metricCovDeriv (I := I) g₁ g₂ 2) x slots).symm

/-! ### The clean a=2 connection-difference jet `∇₂²A` (the dual-core target object)

`covDerivConnDiff2` is the a=2 analogue of `covDerivConnDiff` (`= ∇₂A`, the a=1 clean object): the
fully tensorial **second** base covariant derivative of the connection-difference tensor `A = Γ₁ − Γ₂`.
It is the output vector the a=2 dual core `covDConnDiff2_g1_le` (below, the remaining frontier)
bounds in `metricCovDeriv 3/2/1` currency.  See `ConnDiffDeriv2Bound.md` for the full dual-core route
(the clean Koszul-2 identity `2 g₁(covDerivConnDiff2, Z) = …` obtained from `connDiff_koszul_deriv2`
by absorbing the slot corrections, the verified `∇₂_V Z`-term cancellation, and the Cauchy–Schwarz
`abs_apply_le_sqrt_normSq0S` + division endgame mirroring the a=1 `covDerivConnDiff_g1_le`). -/

/-- **The clean second base covariant derivative of the connection-difference tensor** `∇₂²A`
(`A = Γ₁ − Γ₂`), the a=2 analogue of `covDerivConnDiff`.  Fully tensorial `(1,4)` form: the raw
`∇₂_V` of the a=1 field `p ↦ (∇₂A)(W; X, Y)(p)` minus the three input-slot Leibniz corrections that
make it a tensor,
`(∇₂²A)(V,W;X,Y) = ∇₂_V[(∇₂A)(W;X,Y)] − (∇₂A)(∇₂_V W;X,Y) − (∇₂A)(W;∇₂_V X,Y) − (∇₂A)(W;X,∇₂_V Y)`.

HOME DEBT: this is Curvature-layer content that canonically belongs next to `covDerivConnDiff` in
`Geometry/Curvature/CurvatureOperator/RicciConnDiffPalatini.lean`; it is placed in this HCG leaf only
because the a=2 campaign's editable set is here.  Promote upstream once the dual core assembles. -/
def covDerivConnDiff2 (g₂ g₁ : SmoothRiemannianMetric I M)
    (V W X Y : Π b : M, TangentSpace I b) (x : M) : TangentSpace I x :=
  DifferentialGeometry.Integral.Connection.covApply
      (DifferentialGeometry.Integral.Connection.LeviCivita (I := I) g₂) V
      (fun p => DifferentialGeometry.Integral.Connection.covDerivConnDiff (I := I) g₂ g₁ W X Y p) x
    - DifferentialGeometry.Integral.Connection.covDerivConnDiff (I := I) g₂ g₁
        (DifferentialGeometry.Integral.Connection.covApply
          (DifferentialGeometry.Integral.Connection.LeviCivita (I := I) g₂) V W) X Y x
    - DifferentialGeometry.Integral.Connection.covDerivConnDiff (I := I) g₂ g₁ W
        (DifferentialGeometry.Integral.Connection.covApply
          (DifferentialGeometry.Integral.Connection.LeviCivita (I := I) g₂) V X) Y x
    - DifferentialGeometry.Integral.Connection.covDerivConnDiff (I := I) g₂ g₁ W X
        (DifferentialGeometry.Integral.Connection.covApply
          (DifferentialGeometry.Integral.Connection.LeviCivita (I := I) g₂) V Y) x

/-- Unfolding of `covDerivConnDiff2` to its `covApply`/`covDerivConnDiff` definition. -/
theorem covDerivConnDiff2_eq (g₂ g₁ : SmoothRiemannianMetric I M)
    (V W X Y : Π b : M, TangentSpace I b) (x : M) :
    covDerivConnDiff2 (I := I) g₂ g₁ V W X Y x =
      DifferentialGeometry.Integral.Connection.covApply
          (DifferentialGeometry.Integral.Connection.LeviCivita (I := I) g₂) V
          (fun p => DifferentialGeometry.Integral.Connection.covDerivConnDiff (I := I) g₂ g₁ W X Y p)
          x
        - DifferentialGeometry.Integral.Connection.covDerivConnDiff (I := I) g₂ g₁
            (DifferentialGeometry.Integral.Connection.covApply
              (DifferentialGeometry.Integral.Connection.LeviCivita (I := I) g₂) V W) X Y x
        - DifferentialGeometry.Integral.Connection.covDerivConnDiff (I := I) g₂ g₁ W
            (DifferentialGeometry.Integral.Connection.covApply
              (DifferentialGeometry.Integral.Connection.LeviCivita (I := I) g₂) V X) Y x
        - DifferentialGeometry.Integral.Connection.covDerivConnDiff (I := I) g₂ g₁ W X
            (DifferentialGeometry.Integral.Connection.covApply
              (DifferentialGeometry.Integral.Connection.LeviCivita (I := I) g₂) V Y) x :=
  rfl

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
