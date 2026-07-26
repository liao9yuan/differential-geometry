import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.AllTimesBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.MetricCovDerivLinear
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.ConnDiffDerivBound
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.UnifCovSumCross
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

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
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

/-- Currency bridge (order 0, directional): `nabla0SFun 2 (LC g₂) W (mtf g₁)` is `metricCovDeriv g₁ g₂ 1`
with the derivative direction `W x` in the leading slot.  Order-1 analogue of `nabla3_eq_mcd2`; the
`∇₂g₁·A`/`∇₂g₁·∇₂A` quadratic slots of the differentiated Koszul identities land here. -/
theorem nabla2_eq_mcd1
    [VectorBundle ℝ E (TangentSpace I : M → Type _)]
    [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]
    (g₁ g₂ : SmoothRiemannianMetric I M)
    (W : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _))
    (x : M) (slots : Fin 2 → TangentSpace I x) :
    Tensor0SBundle.nabla0SFun (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 2
        (DifferentialGeometry.Integral.Connection.LeviCivita (I := I) g₂) W
        (Tensor0SBundle.metricTensorField (I := I) g₁) x slots
      = metricCovDeriv (I := I) g₁ g₂ 1 x (Fin.cons (W x) slots) :=
  (metricCovDeriv_one_apply_section (I := I) g₁ g₂ W x slots).symm

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

open DifferentialGeometry.Integral.Connection in
/-- **Section-smoothness of the a=1 connection-difference jet** `p ↦ covDerivConnDiff g₂ g₁ W X Y p`.
Assembled from `covApply_contMDiffOn` + `diffSec_contMDiff`:
`covDerivConnDiff = covApply(∇₂) W (diffSec X Y) − diffSec(∇₂_W X, Y) − diffSec(X, ∇₂_W Y)`.  Needed to
feed the a=1 output field as a smooth slot into `metric_leibniz_extDeriv` when differentiating the
master Koszul-2 pairing (the LHS of the clean identity).
HOME DEBT: canonical home is upstream next to `covDerivConnDiff` in `RicciConnDiffPalatini.lean`. -/
theorem covDerivConnDiff_contMDiff
    (g₂ g₁ : SmoothRiemannianMetric I M)
    (W X Y : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _)) :
    ContMDiff I (I.prod 𝓘(ℝ, E)) (∞ : WithTop ℕ∞)
      (T% (fun p => covDerivConnDiff (I := I) g₂ g₁
        (fun b => W b) (fun b => X b) (fun b => Y b) p)) := by
  haveI : CovariantDerivative.ContMDiffCovariantDerivative
      (LeviCivita (I := I) g₂) (∞ : WithTop ℕ∞) :=
    leviCivitaConnectionOfMetric_contMDiffCovariantDerivative (I := I) g₂
  haveI : CovariantDerivative.ContMDiffCovariantDerivative
      (LeviCivita (I := I) g₁) (∞ : WithTop ℕ∞) :=
    leviCivitaConnectionOfMetric_contMDiffCovariantDerivative (I := I) g₁
  have hcast : ∀ (S : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _)),
      ContMDiff I (I.prod 𝓘(ℝ, E)) ((∞ : WithTop ℕ∞) + 1) (T% (fun b => S b)) := by
    intro S
    rw [show ((∞ : WithTop ℕ∞) + 1) = (∞ : WithTop ℕ∞) from by rw [ENat.coe_top_add_one]]
    exact S.contMDiff
  have hDXY : ContMDiff I (I.prod 𝓘(ℝ, E)) (∞ : WithTop ℕ∞)
      (T% (diffSec (LeviCivita (I := I) g₂) (LeviCivita (I := I) g₁)
        (fun b => X b) (fun b => Y b))) :=
    diffSec_contMDiff (LeviCivita (I := I) g₂) (LeviCivita (I := I) g₁) X.contMDiff (hcast Y)
  have hDXYc : ContMDiff I (I.prod 𝓘(ℝ, E)) ((∞ : WithTop ℕ∞) + 1)
      (T% (diffSec (LeviCivita (I := I) g₂) (LeviCivita (I := I) g₁)
        (fun b => X b) (fun b => Y b))) := by
    rw [show ((∞ : WithTop ℕ∞) + 1) = (∞ : WithTop ℕ∞) from by rw [ENat.coe_top_add_one]]
    exact hDXY
  have hA : ContMDiffOn I (I.prod 𝓘(ℝ, E)) (∞ : WithTop ℕ∞)
      (T% (covApply (LeviCivita (I := I) g₂) (fun b => W b)
        (diffSec (LeviCivita (I := I) g₂) (LeviCivita (I := I) g₁)
          (fun b => X b) (fun b => Y b)))) Set.univ :=
    covApply_contMDiffOn (cov := LeviCivita (I := I) g₂) W.contMDiff hDXYc
  have hWX : ContMDiff I (I.prod 𝓘(ℝ, E)) (∞ : WithTop ℕ∞)
      (T% (covApply (LeviCivita (I := I) g₂) (fun b => W b) (fun b => X b))) :=
    contMDiffOn_univ.mp
      (covApply_contMDiffOn (cov := LeviCivita (I := I) g₂) W.contMDiff (hcast X))
  have hWY : ContMDiff I (I.prod 𝓘(ℝ, E)) (∞ : WithTop ℕ∞)
      (T% (covApply (LeviCivita (I := I) g₂) (fun b => W b) (fun b => Y b))) :=
    contMDiffOn_univ.mp
      (covApply_contMDiffOn (cov := LeviCivita (I := I) g₂) W.contMDiff (hcast Y))
  have hWYc : ContMDiff I (I.prod 𝓘(ℝ, E)) ((∞ : WithTop ℕ∞) + 1)
      (T% (covApply (LeviCivita (I := I) g₂) (fun b => W b) (fun b => Y b))) := by
    rw [show ((∞ : WithTop ℕ∞) + 1) = (∞ : WithTop ℕ∞) from by rw [ENat.coe_top_add_one]]
    exact hWY
  have hB : ContMDiff I (I.prod 𝓘(ℝ, E)) (∞ : WithTop ℕ∞)
      (T% (diffSec (LeviCivita (I := I) g₂) (LeviCivita (I := I) g₁)
        (covApply (LeviCivita (I := I) g₂) (fun b => W b) (fun b => X b)) (fun b => Y b))) :=
    diffSec_contMDiff (LeviCivita (I := I) g₂) (LeviCivita (I := I) g₁) hWX (hcast Y)
  have hC : ContMDiff I (I.prod 𝓘(ℝ, E)) (∞ : WithTop ℕ∞)
      (T% (diffSec (LeviCivita (I := I) g₂) (LeviCivita (I := I) g₁)
        (fun b => X b) (covApply (LeviCivita (I := I) g₂) (fun b => W b) (fun b => Y b)))) :=
    diffSec_contMDiff (LeviCivita (I := I) g₂) (LeviCivita (I := I) g₁) X.contMDiff hWYc
  rw [← contMDiffOn_univ]
  refine ((hA.sub_section hB.contMDiffOn).sub_section hC.contMDiffOn).congr (fun p _hp => ?_)
  rfl

/-! ### The clean a=2 Koszul identity + the dual core -/

open DifferentialGeometry.Integral.Connection in
/-- **The clean a=2 Christoffel-difference Koszul identity** (`Z` evaluated only, `metricCovDeriv`
currency).  Pairing the a=2 connection-difference jet `covDerivConnDiff2 = ∇₂²A` against `Z`:
```
2 g₁(∇₂²A(V,W;X,Y), Z)
  = ∇₂³g₁(V;W,X,Y,Z) + ∇₂³g₁(V;W,Y,X,Z) − ∇₂³g₁(V;W,Z,X,Y)
    − 2 ∇₂²g₁(V;W, A(Y,X), Z)
    − 2 ∇₂g₁(W; ∇₂A(V;X,Y), Z)
    − 2 ∇₂g₁(V; ∇₂A(W;X,Y), Z).
```
Obtained from the master `connDiff_koszul_deriv2` by the metric-compat Leibniz on the LHS pairing and
absorbing every slot correction (`∇₂_V W/X/Y/Z`) via the a=1 `connDiff_koszul_deriv` — all correction
terms cancel exactly, leaving these six survivors.  The two `∇₂g₁·∇₂A` terms carry the **clean** a=1
jet `covDerivConnDiff` (the raw `∇₂_V` of the connection-difference section reduces to it once the
`A(Y,∇₂_V X)` pieces cancel against the input-slot absorption).  Proved by the metric-compat Leibniz
on the LHS pairing, the master `connDiff_koszul_deriv2`, and the a=1 `connDiff_koszul_deriv` applied to
each of the four `∇₂_V`-slot corrections; every correction cancels, leaving the six survivors. -/
theorem koszul2_clean
    [VectorBundle ℝ E (TangentSpace I : M → Type _)]
    [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]
    (g₁ g₂ : SmoothRiemannianMetric I M)
    (V W X Y Z : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _))
    (x : M) :
    2 * g₁.inner x (covDerivConnDiff2 (I := I) g₂ g₁
        (fun b => V b) (fun b => W b) (fun b => X b) (fun b => Y b) x) (Z x)
      = metricCovDeriv (I := I) g₁ g₂ 3 x ![V x, W x, X x, Y x, Z x]
        + metricCovDeriv (I := I) g₁ g₂ 3 x ![V x, W x, Y x, X x, Z x]
        - metricCovDeriv (I := I) g₁ g₂ 3 x ![V x, W x, Z x, X x, Y x]
        - 2 * metricCovDeriv (I := I) g₁ g₂ 2 x
            ![V x, W x,
              CovariantDerivative.difference
                (DifferentialGeometry.Integral.Connection.LeviCivita (I := I) g₁)
                (DifferentialGeometry.Integral.Connection.LeviCivita (I := I) g₂) x (Y x) (X x),
              Z x]
        - 2 * metricCovDeriv (I := I) g₁ g₂ 1 x
            ![W x,
              DifferentialGeometry.Integral.Connection.covDerivConnDiff (I := I) g₂ g₁
                (fun b => V b) (fun b => X b) (fun b => Y b) x,
              Z x]
        - 2 * metricCovDeriv (I := I) g₁ g₂ 1 x
            ![V x,
              DifferentialGeometry.Integral.Connection.covDerivConnDiff (I := I) g₂ g₁
                (fun b => W b) (fun b => X b) (fun b => Y b) x,
              Z x] := by
  classical
  haveI : IsManifold I 1 M :=
    IsManifold.of_le (I := I) (M := M) (n := ∞) (by decide : (1 : WithTop ℕ∞) ≤ ∞)
  haveI : IsManifold I ((∞ : WithTop ℕ∞) + 1) M := by change IsManifold I ∞ M; infer_instance
  haveI hcov2 : CovariantDerivative.ContMDiffCovariantDerivative
      (LeviCivita (I := I) g₂) (∞ : WithTop ℕ∞) :=
    leviCivitaConnectionOfMetric_contMDiffCovariantDerivative (I := I) g₂
  -- Sections are `C^(∞+1)` since `∞ + 1 = ∞`.
  have hZcast : ∀ (S : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _)),
      ContMDiff I (I.prod 𝓘(ℝ, E)) ((∞ : WithTop ℕ∞) + 1) (T% (fun b => S b)) := by
    intro S
    rw [show ((∞ : WithTop ℕ∞) + 1) = (∞ : WithTop ℕ∞) from by rw [ENat.coe_top_add_one]]
    exact S.contMDiff
  -- Smoothness of the base covariant derivatives `∇₂_V S`.
  have hsmW : ContMDiff I (I.prod 𝓘(ℝ, E)) (∞ : WithTop ℕ∞)
      (T% (covApply (LeviCivita (I := I) g₂) (fun b => V b) (fun b => W b))) :=
    contMDiffOn_univ.mp (covApply_contMDiffOn (cov := LeviCivita (I := I) g₂) V.contMDiff (hZcast W))
  have hsmX : ContMDiff I (I.prod 𝓘(ℝ, E)) (∞ : WithTop ℕ∞)
      (T% (covApply (LeviCivita (I := I) g₂) (fun b => V b) (fun b => X b))) :=
    contMDiffOn_univ.mp (covApply_contMDiffOn (cov := LeviCivita (I := I) g₂) V.contMDiff (hZcast X))
  have hsmY : ContMDiff I (I.prod 𝓘(ℝ, E)) (∞ : WithTop ℕ∞)
      (T% (covApply (LeviCivita (I := I) g₂) (fun b => V b) (fun b => Y b))) :=
    contMDiffOn_univ.mp (covApply_contMDiffOn (cov := LeviCivita (I := I) g₂) V.contMDiff (hZcast Y))
  have hsmZ : ContMDiff I (I.prod 𝓘(ℝ, E)) (∞ : WithTop ℕ∞)
      (T% (covApply (LeviCivita (I := I) g₂) (fun b => V b) (fun b => Z b))) :=
    contMDiffOn_univ.mp (covApply_contMDiffOn (cov := LeviCivita (I := I) g₂) V.contMDiff (hZcast Z))
  set DVW : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _) :=
    ContMDiffSection.mk (covApply (LeviCivita (I := I) g₂) (fun b => V b) (fun b => W b)) hsmW
    with hDVWdef
  set DVX : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _) :=
    ContMDiffSection.mk (covApply (LeviCivita (I := I) g₂) (fun b => V b) (fun b => X b)) hsmX
    with hDVXdef
  set DVY : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _) :=
    ContMDiffSection.mk (covApply (LeviCivita (I := I) g₂) (fun b => V b) (fun b => Y b)) hsmY
    with hDVYdef
  set DVZ : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _) :=
    ContMDiffSection.mk (covApply (LeviCivita (I := I) g₂) (fun b => V b) (fun b => Z b)) hsmZ
    with hDVZdef
  set Qsec : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _) :=
    ContMDiffSection.mk
      (fun p => covDerivConnDiff (I := I) g₂ g₁ (fun b => W b) (fun b => X b) (fun b => Y b) p)
      (covDerivConnDiff_contMDiff (I := I) g₂ g₁ W X Y) with hQdef
  -- Value bridges (definitional): the packaged base derivatives are the master's `∇₂_V ·` forms.
  have hDVWval : DVW x = ((LeviCivita (I := I) g₂) (fun p => W p) x) (V x) := rfl
  have hDVXval : DVX x = ((LeviCivita (I := I) g₂) (fun p => X p) x) (V x) := rfl
  have hDVYval : DVY x = ((LeviCivita (I := I) g₂) (fun p => Y p) x) (V x) := rfl
  have hDVZval : DVZ x = ((LeviCivita (I := I) g₂) (fun p => Z p) x) (V x) := rfl
  have hQxval : Qsec x = covDerivConnDiff (I := I) g₂ g₁ W X Y x := rfl
  -- The A-section base derivative decomposes into the clean a=1 jet plus two `A(·,∇₂_V ·)` corrections.
  have hAvec : ((LeviCivita (I := I) g₂)
        (fun p => CovariantDerivative.difference (LeviCivita (I := I) g₁)
          (LeviCivita (I := I) g₂) p (Y p) (X p)) x) (V x)
      = covDerivConnDiff (I := I) g₂ g₁ V X Y x
        + CovariantDerivative.difference (LeviCivita (I := I) g₁) (LeviCivita (I := I) g₂) x (Y x)
            (((LeviCivita (I := I) g₂) (fun p => X p) x) (V x))
        + CovariantDerivative.difference (LeviCivita (I := I) g₁) (LeviCivita (I := I) g₂) x
            (((LeviCivita (I := I) g₂) (fun p => Y p) x) (V x)) (X x) := by
    have hcd : covDerivConnDiff (I := I) g₂ g₁ V X Y x
        = ((LeviCivita (I := I) g₂)
            (fun p => CovariantDerivative.difference (LeviCivita (I := I) g₁)
              (LeviCivita (I := I) g₂) p (Y p) (X p)) x) (V x)
          - CovariantDerivative.difference (LeviCivita (I := I) g₁) (LeviCivita (I := I) g₂) x (Y x)
              (((LeviCivita (I := I) g₂) (fun p => X p) x) (V x))
          - CovariantDerivative.difference (LeviCivita (I := I) g₁) (LeviCivita (I := I) g₂) x
              (((LeviCivita (I := I) g₂) (fun p => Y p) x) (V x)) (X x) := rfl
    rw [hcd]; abel
  -- Slot-1 additivity of the first metric jet (three summands).
  have hmcd1_add3 : ∀ (a b c d e : TangentSpace I x),
      metricCovDeriv (I := I) g₁ g₂ 1 x ![a, b + c + d, e]
        = metricCovDeriv (I := I) g₁ g₂ 1 x ![a, b, e]
          + metricCovDeriv (I := I) g₁ g₂ 1 x ![a, c, e]
          + metricCovDeriv (I := I) g₁ g₂ 1 x ![a, d, e] := by
    intro a b c d e
    have e1 : ∀ v : TangentSpace I x,
        (![a, v, e] : Fin 3 → TangentSpace I x) = Function.update ![a, b, e] 1 v := by
      intro v; funext i; fin_cases i <;> simp
    rw [e1 (b + c + d),
      Tensor0SBundle.Tensor0SSpace.map_update_add (metricCovDeriv (I := I) g₁ g₂ 1 x) ![a, b, e] 1
        (b + c) d,
      Tensor0SBundle.Tensor0SSpace.map_update_add (metricCovDeriv (I := I) g₁ g₂ 1 x) ![a, b, e] 1
        b c, ← e1 b, ← e1 c, ← e1 d]
  -- Metric bilinearity (subtraction in the first slot).
  have g_sub : ∀ (a b : TangentSpace I x),
      g₁.inner x (a - b) (Z x) = g₁.inner x a (Z x) - g₁.inner x b (Z x) := by
    intro a b; rw [map_sub (g₁.inner x), ContinuousLinearMap.sub_apply]
  -- `Fin.cons`/`![·]` normalisers.
  have hcons3 : ∀ (a b c : TangentSpace I x),
      Fin.cons a (![b, c] : Fin 2 → TangentSpace I x) = (![a, b, c] : Fin 3 → TangentSpace I x) := by
    intro a b c; funext i; fin_cases i <;> rfl
  have hcons4 : ∀ (a b c d : TangentSpace I x),
      Fin.cons a (![b, c, d] : Fin 3 → TangentSpace I x)
        = (![a, b, c, d] : Fin 4 → TangentSpace I x) := by
    intro a b c d; funext i; fin_cases i <;> rfl
  have hcons5 : ∀ (a b c d e : TangentSpace I x),
      Fin.cons a (![b, c, d, e] : Fin 4 → TangentSpace I x)
        = (![a, b, c, d, e] : Fin 5 → TangentSpace I x) := by
    intro a b c d e; funext i; fin_cases i <;> rfl
  -- `Function.update` normalisers on explicit tuples.
  have hup4_0 : ∀ (v a b c d : TangentSpace I x),
      Function.update (![a, b, c, d] : Fin 4 → TangentSpace I x) 0 v = ![v, b, c, d] := by
    intro v a b c d; funext i; fin_cases i <;> simp
  have hup4_1 : ∀ (v a b c d : TangentSpace I x),
      Function.update (![a, b, c, d] : Fin 4 → TangentSpace I x) 1 v = ![a, v, c, d] := by
    intro v a b c d; funext i; fin_cases i <;> simp
  have hup4_2 : ∀ (v a b c d : TangentSpace I x),
      Function.update (![a, b, c, d] : Fin 4 → TangentSpace I x) 2 v = ![a, b, v, d] := by
    intro v a b c d; funext i; fin_cases i <;> simp
  have hup4_3 : ∀ (v a b c d : TangentSpace I x),
      Function.update (![a, b, c, d] : Fin 4 → TangentSpace I x) 3 v = ![a, b, c, v] := by
    intro v a b c d; funext i; fin_cases i <;> simp
  have hup2_0 : ∀ (v a b : TangentSpace I x),
      Function.update (![a, b] : Fin 2 → TangentSpace I x) 0 v = ![v, b] := by
    intro v a b; funext i; fin_cases i <;> simp
  have hup2_1 : ∀ (v a b : TangentSpace I x),
      Function.update (![a, b] : Fin 2 → TangentSpace I x) 1 v = ![a, v] := by
    intro v a b; funext i; fin_cases i <;> simp
  -- Section-tuple evaluations at `x`.
  have e4x : ∀ (a b c d : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _)),
      (fun i : Fin 4 => ((![a, b, c, d] : Fin 4 → ContMDiffSection I E (∞ : WithTop ℕ∞)
        (TangentSpace I : M → Type _)) i) x) = ![a x, b x, c x, d x] := by
    intro a b c d; funext i; fin_cases i <;> rfl
  have e2x : ∀ (a b : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _)),
      (fun i : Fin 2 => ((![a, b] : Fin 2 → ContMDiffSection I E (∞ : WithTop ℕ∞)
        (TangentSpace I : M → Type _)) i) x) = ![a x, b x] := by
    intro a b; funext i; fin_cases i <;> rfl
  -- The master differentiated identity, the four a=1 Koszul identities, and the LHS Leibniz.
  have hmaster := connDiff_koszul_deriv2 (I := I) g₁ g₂ V W X Y Z x
  have hkW := connDiff_koszul_deriv (I := I) g₁ g₂ DVW X Y Z x
  have hkX := connDiff_koszul_deriv (I := I) g₁ g₂ W DVX Y Z x
  have hkY := connDiff_koszul_deriv (I := I) g₁ g₂ W X DVY Z x
  have hkZ := connDiff_koszul_deriv (I := I) g₁ g₂ W X Y DVZ x
  -- Expand the master LHS by metric-compatibility Leibniz (factor 2 pulled out).
  have hLHSfun : (fun p => g₁.inner p (Qsec p) (Z p))
      = (fun p => Tensor0SBundle.metricTensorField (I := I) g₁ p
          (fun c : Fin 2 => (![Qsec, Z] c) p)) := by
    funext p
    rw [Tensor0SBundle.metricTensorField_apply]
    simp [Matrix.cons_val_zero, Matrix.cons_val_one]
  have hQZdiff : MDifferentiableAt I 𝓘(ℝ, ℝ) (fun p => g₁.inner p (Qsec p) (Z p)) x := by
    rw [hLHSfun]
    exact (Tensor0SBundle.tensor0SField_eval_smooth_slots_contMDiffAt (𝕜 := ℝ) (E := E) (H := H)
      (I := I) (M := M) (Tensor0SBundle.metricTensorField (I := I) g₁) ![Qsec, Z] x).mdifferentiableAt
      (by simp)
  have hLeib := metric_leibniz_extDeriv (I := I) g₁ g₂ ![Qsec, Z] V x
  rw [← hLHSfun] at hLeib
  rw [show (fun p : M => 2 * g₁.inner p
        (covDerivConnDiff (I := I) g₂ g₁ (fun b => W b) (fun b => X b) (fun b => Y b) p) (Z p))
      = (fun p : M => 2 * g₁.inner p (Qsec p) (Z p)) from rfl,
    extDerivFun_const_mul I (2 : ℝ) hQZdiff] at hmaster
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul] at hmaster
  rw [hLeib] at hmaster
  -- Currency normalisation: everything to `metricCovDeriv` currency.
  simp only [nabla4_eq_mcd3, nabla3_eq_mcd2, nabla2_eq_mcd1] at hmaster hkW hkX hkY hkZ
  simp only [field2_eq_mcd2] at hmaster
  simp only [field1_eq_mcd1] at hmaster
  -- Expand sums / updates / matrix evaluations; normalise `∇₂_V ·` and `Fin.cons`.
  simp only [Fin.sum_univ_four, Fin.sum_univ_two, e4x, e2x, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons, Matrix.cons_val_three, hup4_0, hup4_1,
    hup4_2, hup4_3, hup2_0, hup2_1, hcons3, hcons4, hcons5, Tensor0SBundle.metricTensorField_apply,
    hDVWval, hDVXval, hDVYval, hDVZval, hQxval] at hmaster hkW hkX hkY hkZ
  -- Split the master's `∇₂_V(A-section)` correction into the clean jet + the two `A(·,∇₂_V·)` pieces.
  rw [hAvec, hmcd1_add3] at hmaster
  -- Unfold the a=2 jet; split the pairing by bilinearity.
  have hcdc2 : covDerivConnDiff2 (I := I) g₂ g₁
        (fun b => V b) (fun b => W b) (fun b => X b) (fun b => Y b) x
      = ((LeviCivita (I := I) g₂) (fun p => Qsec p) x) (V x)
        - covDerivConnDiff (I := I) g₂ g₁ DVW X Y x
        - covDerivConnDiff (I := I) g₂ g₁ W DVX Y x
        - covDerivConnDiff (I := I) g₂ g₁ W X DVY x := by
    rw [covDerivConnDiff2_eq]; rfl
  rw [hcdc2, g_sub, g_sub, g_sub,
    show covDerivConnDiff (I := I) g₂ g₁ (fun b => V b) (fun b => X b) (fun b => Y b) x
      = covDerivConnDiff (I := I) g₂ g₁ V X Y x from rfl,
    show covDerivConnDiff (I := I) g₂ g₁ (fun b => W b) (fun b => X b) (fun b => Y b) x
      = covDerivConnDiff (I := I) g₂ g₁ W X Y x from rfl]
  linarith [hmaster, hkW, hkX, hkY, hkZ]

open DifferentialGeometry.Integral.Connection
  (smoothExtensionTangent smoothExtensionTangent_eq smoothExtensionTangent_contMDiff
    leviCivitaConnectionOfMetric exists_gOrthonormalBasis) in
open DifferentialGeometry.Analysis.Laplacian (metric_inner_self_nonneg) in
set_option maxHeartbeats 1600000 in
set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in
/-- **The a=2 dual core.**  Pairing the clean a=2 Koszul identity `koszul2_clean` against the output
vector `B₂ = ∇₂²A(v',v;w,u)` bounds the `g₁`-length of the second connection-difference jet by the
order-3/2/1 metric covariant derivatives of `g₁` and the a≤1 connection-difference atoms, all in the
`g₁` fibre.  The two `∇₂A`-vector slots of `koszul2_clean` are re-expanded by the a=1 dual core
`covDerivConnDiff_g1_le` (constant `CA1 = 3/2·M₂ + M₁·NA`); the `A`-slot by `connDiffVec_norm_le`;
then the pairing is divided by `|B₂|` (B2's step-(7) trick).  a=2 analogue of
`ConnDiffDerivBound.covDerivConnDiff_g1_le`. -/
theorem covDConnDiff2_g1_le
    [VectorBundle ℝ E (TangentSpace I : M → Type _)]
    [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]
    (g₂ g₁ : SmoothRiemannianMetric I M) (x : M) (v' v w u : TangentSpace I x) :
    Real.sqrt (g₁.inner x
        (covDerivConnDiff2 (I := I) g₂ g₁
          (smoothExtensionTangent (I := I) x v') (smoothExtensionTangent (I := I) x v)
          (smoothExtensionTangent (I := I) x w) (smoothExtensionTangent (I := I) x u) x)
        (covDerivConnDiff2 (I := I) g₂ g₁
          (smoothExtensionTangent (I := I) x v') (smoothExtensionTangent (I := I) x v)
          (smoothExtensionTangent (I := I) x w) (smoothExtensionTangent (I := I) x u) x)) ≤
      (3 / 2 * Real.sqrt (Tensor0SBundle.normSq0S (I := I) g₁ x 5
            (metricCovDeriv (I := I) g₁ g₂ 3 x))
        + Real.sqrt (Tensor0SBundle.normSq0S (I := I) g₁ x 4 (metricCovDeriv (I := I) g₁ g₂ 2 x))
            * Real.sqrt (Tensor0SBundle.normSqRS (I := I) (g := g₁) (x := x) 1 2
                (Tensor0SBundle.connectionDifferenceTensorAt (I := I)
                  (leviCivitaConnectionOfMetric (I := I) g₁)
                  (leviCivitaConnectionOfMetric (I := I) g₂) x))
        + 2 * Real.sqrt (Tensor0SBundle.normSq0S (I := I) g₁ x 3 (metricCovDeriv (I := I) g₁ g₂ 1 x))
            * (3 / 2 * Real.sqrt (Tensor0SBundle.normSq0S (I := I) g₁ x 4
                  (metricCovDeriv (I := I) g₁ g₂ 2 x))
              + Real.sqrt (Tensor0SBundle.normSq0S (I := I) g₁ x 3 (metricCovDeriv (I := I) g₁ g₂ 1 x))
                  * Real.sqrt (Tensor0SBundle.normSqRS (I := I) (g := g₁) (x := x) 1 2
                      (Tensor0SBundle.connectionDifferenceTensorAt (I := I)
                        (leviCivitaConnectionOfMetric (I := I) g₁)
                        (leviCivitaConnectionOfMetric (I := I) g₂) x)))) *
        Real.sqrt (g₁.inner x v' v') * Real.sqrt (g₁.inner x v v) *
          Real.sqrt (g₁.inner x w w) * Real.sqrt (g₁.inner x u u) := by
  classical
  haveI : IsManifold I 1 M :=
    IsManifold.of_le (I := I) (M := M) (n := ∞) (by decide : (1 : WithTop ℕ∞) ≤ ∞)
  haveI : IsManifold I (1 + 1) M :=
    IsManifold.of_le (I := I) (M := M) (n := ∞) (by decide : ((1 : WithTop ℕ∞) + 1) ≤ ∞)
  obtain ⟨basis, hON⟩ := exists_gOrthonormalBasis (I := I) g₁ x
  set NA : ℝ := Real.sqrt (Tensor0SBundle.normSqRS (I := I) (g := g₁) (x := x) 1 2
    (Tensor0SBundle.connectionDifferenceTensorAt (I := I)
      (leviCivitaConnectionOfMetric (I := I) g₁)
      (leviCivitaConnectionOfMetric (I := I) g₂) x)) with hNAdef
  set M1 : ℝ := Real.sqrt (Tensor0SBundle.normSq0S (I := I) g₁ x 3
    (metricCovDeriv (I := I) g₁ g₂ 1 x)) with hM1def
  set M2 : ℝ := Real.sqrt (Tensor0SBundle.normSq0S (I := I) g₁ x 4
    (metricCovDeriv (I := I) g₁ g₂ 2 x)) with hM2def
  set M3 : ℝ := Real.sqrt (Tensor0SBundle.normSq0S (I := I) g₁ x 5
    (metricCovDeriv (I := I) g₁ g₂ 3 x)) with hM3def
  set B2 : TangentSpace I x :=
    covDerivConnDiff2 (I := I) g₂ g₁
      (smoothExtensionTangent (I := I) x v') (smoothExtensionTangent (I := I) x v)
      (smoothExtensionTangent (I := I) x w) (smoothExtensionTangent (I := I) x u) x with hB2def
  set Vsec : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _) :=
    ContMDiffSection.mk (smoothExtensionTangent (I := I) x v')
      (smoothExtensionTangent_contMDiff (I := I) x v') with hVsec
  set Wsec : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _) :=
    ContMDiffSection.mk (smoothExtensionTangent (I := I) x v)
      (smoothExtensionTangent_contMDiff (I := I) x v) with hWsec
  set Xsec : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _) :=
    ContMDiffSection.mk (smoothExtensionTangent (I := I) x w)
      (smoothExtensionTangent_contMDiff (I := I) x w) with hXsec
  set Ysec : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _) :=
    ContMDiffSection.mk (smoothExtensionTangent (I := I) x u)
      (smoothExtensionTangent_contMDiff (I := I) x u) with hYsec
  set Zsec : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _) :=
    ContMDiffSection.mk (smoothExtensionTangent (I := I) x B2)
      (smoothExtensionTangent_contMDiff (I := I) x B2) with hZsec
  have hVx : Vsec x = v' := smoothExtensionTangent_eq (I := I) x v'
  have hWx : Wsec x = v := smoothExtensionTangent_eq (I := I) x v
  have hXx : Xsec x = w := smoothExtensionTangent_eq (I := I) x w
  have hYx : Ysec x = u := smoothExtensionTangent_eq (I := I) x u
  have hZx : Zsec x = B2 := smoothExtensionTangent_eq (I := I) x B2
  have hAbr2 : covDerivConnDiff2 (I := I) g₂ g₁
      (fun b => Vsec b) (fun b => Wsec b) (fun b => Xsec b) (fun b => Ysec b) x = B2 := by
    rw [hB2def]; rfl
  have hkos := koszul2_clean (I := I) g₁ g₂ Vsec Wsec Xsec Ysec Zsec x
  rw [hAbr2, hVx, hWx, hXx, hYx, hZx] at hkos
  -- the two ∇₂A vectors
  set D5 : TangentSpace I x :=
    DifferentialGeometry.Integral.Connection.covDerivConnDiff (I := I) g₂ g₁
      (fun b => Vsec b) (fun b => Xsec b) (fun b => Ysec b) x with hD5def
  set D6 : TangentSpace I x :=
    DifferentialGeometry.Integral.Connection.covDerivConnDiff (I := I) g₂ g₁
      (fun b => Wsec b) (fun b => Xsec b) (fun b => Ysec b) x with hD6def
  set Avec : TangentSpace I x :=
    CovariantDerivative.difference
      (DifferentialGeometry.Integral.Connection.LeviCivita (I := I) g₁)
      (DifferentialGeometry.Integral.Connection.LeviCivita (I := I) g₂) x u w with hAvec
  -- make the heavy `covDerivConnDiff2`/`covDerivConnDiff`/`difference` vectors opaque (heartbeats)
  clear_value B2 D5 D6 Avec
  -- Cauchy–Schwarz at the internal `g₁`-orthonormal basis, ranks 5/4/3.
  have hcs5 : ∀ a b c d e : TangentSpace I x,
      |metricCovDeriv (I := I) g₁ g₂ 3 x ![a, b, c, d, e]| ≤
        M3 * (Real.sqrt (g₁.inner x a a) * Real.sqrt (g₁.inner x b b) *
          Real.sqrt (g₁.inner x c c) * Real.sqrt (g₁.inner x d d) * Real.sqrt (g₁.inner x e e)) := by
    intro a b c d e
    have h := Tensor0SBundle.abs_apply_le_sqrt_normSq0S (I := I) g₁ x 5 basis hON
      (metricCovDeriv (I := I) g₁ g₂ 3 x) ![a, b, c, d, e]
    rw [hM3def]
    refine le_trans h (le_of_eq ?_)
    congr 1
    change (∏ i : Fin 5, Real.sqrt (g₁.inner x (![a, b, c, d, e] i) (![a, b, c, d, e] i))) = _
    simp [Fin.prod_univ_five]
  have hcs4 : ∀ a b c d : TangentSpace I x,
      |metricCovDeriv (I := I) g₁ g₂ 2 x ![a, b, c, d]| ≤
        M2 * (Real.sqrt (g₁.inner x a a) * Real.sqrt (g₁.inner x b b) *
          Real.sqrt (g₁.inner x c c) * Real.sqrt (g₁.inner x d d)) := by
    intro a b c d
    have h := Tensor0SBundle.abs_apply_le_sqrt_normSq0S (I := I) g₁ x 4 basis hON
      (metricCovDeriv (I := I) g₁ g₂ 2 x) ![a, b, c, d]
    rw [hM2def]
    refine le_trans h (le_of_eq ?_)
    congr 1
    change (∏ i : Fin 4, Real.sqrt (g₁.inner x (![a, b, c, d] i) (![a, b, c, d] i))) = _
    simp [Fin.prod_univ_four]
  have hcs3 : ∀ a b c : TangentSpace I x,
      |metricCovDeriv (I := I) g₁ g₂ 1 x ![a, b, c]| ≤
        M1 * (Real.sqrt (g₁.inner x a a) * Real.sqrt (g₁.inner x b b) *
          Real.sqrt (g₁.inner x c c)) := by
    intro a b c
    have h := Tensor0SBundle.abs_apply_le_sqrt_normSq0S (I := I) g₁ x 3 basis hON
      (metricCovDeriv (I := I) g₁ g₂ 1 x) ![a, b, c]
    rw [hM1def]
    refine le_trans h (le_of_eq ?_)
    congr 1
    change (∏ i : Fin 3, Real.sqrt (g₁.inner x (![a, b, c] i) (![a, b, c] i))) = _
    simp [Fin.prod_univ_three]
  -- the a≤1 atom bounds on the fibre norms of `Avec`, `D5`, `D6`
  have hSA : Real.sqrt (g₁.inner x Avec Avec) ≤
      NA * Real.sqrt (g₁.inner x w w) * Real.sqrt (g₁.inner x u u) := by
    rw [hAvec, hNAdef]
    exact Tensor0SBundle.connDiffVec_norm_le (I := I) g₁
      (leviCivitaConnectionOfMetric (I := I) g₁)
      (leviCivitaConnectionOfMetric (I := I) g₂) w u
  have hSD5 : Real.sqrt (g₁.inner x D5 D5) ≤
      (3 / 2 * M2 + M1 * NA) *
        Real.sqrt (g₁.inner x v' v') * Real.sqrt (g₁.inner x w w) * Real.sqrt (g₁.inner x u u) := by
    rw [hD5def, hM2def, hM1def, hNAdef]
    exact DifferentialGeometry.Geometry.Curvature.covDerivConnDiff_g1_le (I := I) g₂ g₁ x v' w u
  have hSD6 : Real.sqrt (g₁.inner x D6 D6) ≤
      (3 / 2 * M2 + M1 * NA) *
        Real.sqrt (g₁.inner x v v) * Real.sqrt (g₁.inner x w w) * Real.sqrt (g₁.inner x u u) := by
    rw [hD6def, hM2def, hM1def, hNAdef]
    exact DifferentialGeometry.Geometry.Curvature.covDerivConnDiff_g1_le (I := I) g₂ g₁ x v w u
  -- squared length of `B₂`
  have hBB_nn : 0 ≤ g₁.inner x B2 B2 := metric_inner_self_nonneg (I := I) (M := M) g₁ x B2
  have hBBsq : g₁.inner x B2 B2 = Real.sqrt (g₁.inner x B2 B2) ^ 2 := (Real.sq_sqrt hBB_nn).symm
  rw [hBBsq] at hkos
  -- combined product bounds (CS composed with the atom bounds); vector norms kept literal
  have hM1nn : (0:ℝ) ≤ M1 := hM1def ▸ Real.sqrt_nonneg _
  have hM2nn : (0:ℝ) ≤ M2 := hM2def ▸ Real.sqrt_nonneg _
  have hM3nn : (0:ℝ) ≤ M3 := hM3def ▸ Real.sqrt_nonneg _
  have hNAnn : (0:ℝ) ≤ NA := hNAdef ▸ Real.sqrt_nonneg _
  have hSBnn : (0:ℝ) ≤ Real.sqrt (g₁.inner x B2 B2) := Real.sqrt_nonneg _
  -- three mcd3 combos
  have hT1 := hcs5 v' v w u B2
  have hT2 := hcs5 v' v u w B2
  have hT3 := hcs5 v' v B2 w u
  -- mcd2 · A term (CS composed with the a=0 atom bound `hSA`)
  have hTA : |metricCovDeriv (I := I) g₁ g₂ 2 x ![v', v, Avec, B2]| ≤
      M2 * NA * (Real.sqrt (g₁.inner x v' v') * Real.sqrt (g₁.inner x v v) *
        Real.sqrt (g₁.inner x w w) * Real.sqrt (g₁.inner x u u) *
          Real.sqrt (g₁.inner x B2 B2)) := by
    refine le_trans (hcs4 v' v Avec B2) ?_
    have hpre : (0:ℝ) ≤ M2 * Real.sqrt (g₁.inner x v' v') * Real.sqrt (g₁.inner x v v) *
        Real.sqrt (g₁.inner x B2 B2) :=
      mul_nonneg (mul_nonneg (mul_nonneg hM2nn (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _))
        (Real.sqrt_nonneg _)
    nlinarith [mul_le_mul_of_nonneg_left hSA hpre, hM2nn, hNAnn,
      Real.sqrt_nonneg (g₁.inner x Avec Avec), Real.sqrt_nonneg (g₁.inner x v' v'),
      Real.sqrt_nonneg (g₁.inner x v v), Real.sqrt_nonneg (g₁.inner x w w),
      Real.sqrt_nonneg (g₁.inner x u u), Real.sqrt_nonneg (g₁.inner x B2 B2)]
  -- mcd1 · D5 term (CS composed with the a=1 atom bound `hSD5`)
  have hTD5 : |metricCovDeriv (I := I) g₁ g₂ 1 x ![v, D5, B2]| ≤
      M1 * (3 / 2 * M2 + M1 * NA) * (Real.sqrt (g₁.inner x v' v') * Real.sqrt (g₁.inner x v v) *
        Real.sqrt (g₁.inner x w w) * Real.sqrt (g₁.inner x u u) *
          Real.sqrt (g₁.inner x B2 B2)) := by
    refine le_trans (hcs3 v D5 B2) ?_
    have hpre : (0:ℝ) ≤ M1 * Real.sqrt (g₁.inner x v v) * Real.sqrt (g₁.inner x B2 B2) :=
      mul_nonneg (mul_nonneg hM1nn (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)
    nlinarith [mul_le_mul_of_nonneg_left hSD5 hpre, hM1nn, hM2nn, hNAnn,
      Real.sqrt_nonneg (g₁.inner x D5 D5), Real.sqrt_nonneg (g₁.inner x v' v'),
      Real.sqrt_nonneg (g₁.inner x v v), Real.sqrt_nonneg (g₁.inner x w w),
      Real.sqrt_nonneg (g₁.inner x u u), Real.sqrt_nonneg (g₁.inner x B2 B2)]
  -- mcd1 · D6 term (CS composed with the a=1 atom bound `hSD6`)
  have hTD6 : |metricCovDeriv (I := I) g₁ g₂ 1 x ![v', D6, B2]| ≤
      M1 * (3 / 2 * M2 + M1 * NA) * (Real.sqrt (g₁.inner x v' v') * Real.sqrt (g₁.inner x v v) *
        Real.sqrt (g₁.inner x w w) * Real.sqrt (g₁.inner x u u) *
          Real.sqrt (g₁.inner x B2 B2)) := by
    refine le_trans (hcs3 v' D6 B2) ?_
    have hpre : (0:ℝ) ≤ M1 * Real.sqrt (g₁.inner x v' v') * Real.sqrt (g₁.inner x B2 B2) :=
      mul_nonneg (mul_nonneg hM1nn (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)
    nlinarith [mul_le_mul_of_nonneg_left hSD6 hpre, hM1nn, hM2nn, hNAnn,
      Real.sqrt_nonneg (g₁.inner x D6 D6), Real.sqrt_nonneg (g₁.inner x v' v'),
      Real.sqrt_nonneg (g₁.inner x v v), Real.sqrt_nonneg (g₁.inner x w w),
      Real.sqrt_nonneg (g₁.inner x u u), Real.sqrt_nonneg (g₁.inner x B2 B2)]
  -- absolute-value bounds feeding the pairing
  have habs1 := le_abs_self (metricCovDeriv (I := I) g₁ g₂ 3 x ![v', v, w, u, B2])
  have habs2 := le_abs_self (metricCovDeriv (I := I) g₁ g₂ 3 x ![v', v, u, w, B2])
  have habs3 := neg_le_abs (metricCovDeriv (I := I) g₁ g₂ 3 x ![v', v, B2, w, u])
  have habsA := neg_le_abs (metricCovDeriv (I := I) g₁ g₂ 2 x ![v', v, Avec, B2])
  have habsD5 := neg_le_abs (metricCovDeriv (I := I) g₁ g₂ 1 x ![v, D5, B2])
  have habsD6 := neg_le_abs (metricCovDeriv (I := I) g₁ g₂ 1 x ![v', D6, B2])
  rcases eq_or_lt_of_le hSBnn with hSB0 | hSBpos
  · rw [← hSB0]
    have hcoef : (0:ℝ) ≤ 3 / 2 * M3 + M2 * NA + 2 * M1 * (3 / 2 * M2 + M1 * NA) := by
      have hca : (0:ℝ) ≤ 3 / 2 * M2 + M1 * NA := by nlinarith [hM2nn, mul_nonneg hM1nn hNAnn]
      nlinarith [hM3nn, mul_nonneg hM2nn hNAnn, mul_nonneg hM1nn hca]
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hcoef (Real.sqrt_nonneg _))
      (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)
  · have hmul : Real.sqrt (g₁.inner x B2 B2) * (2 * Real.sqrt (g₁.inner x B2 B2)) ≤
        Real.sqrt (g₁.inner x B2 B2) *
          ((3 * M3 + 2 * (M2 * NA) + 4 * (M1 * (3 / 2 * M2 + M1 * NA))) *
            (Real.sqrt (g₁.inner x v' v') * Real.sqrt (g₁.inner x v v) *
              Real.sqrt (g₁.inner x w w) * Real.sqrt (g₁.inner x u u))) := by
      nlinarith [hkos, hT1, hT2, hT3, hTA, hTD5, hTD6,
        habs1, habs2, habs3, habsA, habsD5, habsD6,
        Real.sqrt_nonneg (g₁.inner x B2 B2), Real.sqrt_nonneg (g₁.inner x v' v'),
        Real.sqrt_nonneg (g₁.inner x v v), Real.sqrt_nonneg (g₁.inner x w w),
        Real.sqrt_nonneg (g₁.inner x u u), hM1nn, hM2nn, hM3nn, hNAnn]
    have hdiv := le_of_mul_le_mul_left hmul hSBpos
    nlinarith [hdiv]

/-! ### The evaluated a=2 base-Leibniz core `covStep2_diffStep_eval` (`∇₂²(A ⋆ S)`)

The reusable eval identity feeding the `covStepDiff2_mixedComm_le` norm bridge, built one order up
from `diffStep_leibniz_eval` (`MetricCovDerivLinear.lean`).  Session 1 delivers the correct-by-
construction outer **peel** (`covStep2_diffStep_peel`) and the fully-resolved **T1 branch**
(`covStep2_diffStep_branch1`, materialising `covDerivConnDiff2`).  See `ConnDiffDeriv2Bound.md §0`
(session 7/8) for the session-2 frontier: the T2 branch (`∇₂²S` + `covDerivConnDiff`), the
`H`-correction sum, and the final `∇₂²S`-cancellation assembly. -/

open DifferentialGeometry.Integral.Connection in
set_option maxHeartbeats 1600000 in
set_option linter.unusedSectionVars false in
/-- **The a=2 connection-difference-derivative bound in the metric-jet currency** (the
`g₂`-currency pointwise atom, session 14).  Under uniform metric equivalence
`MetricUniformEquivalentOn K g₂ g₁ Λ` and the exact-order metric covariant-derivative bounds
`Λ', Λ'', Λ'''` (orders 1–3 of `∇g₁` against `g₂`), the output vector of
`covDerivConnDiff2 g₂ g₁ (ext v') (ext v) (ext w) (ext u) x` obeys the `g₂`-quadratic estimate with
constant `CA₂ = (3/2)·Λ⁵·Λ''' + (9/2)·Λ⁶·Λ'·Λ'' + 3·Λ⁷·Λ'³`.  a=2 sibling of
`Geometry.Curvature.covDerivConnDiff_gJet_le`, obtained from the dual core `covDConnDiff2_g1_le` by
the rank-3/4/5 fibre conversions `sqrt_normSq0S_comp`, the a=0 Koszul conversion
(`diff_le_covOne_basis_ref_lc`), and vector comparability on the output and the four input slots. -/
theorem covDConnDiff2_gJet_le
    [VectorBundle ℝ E (TangentSpace I : M → Type _)]
    [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]
    {K : Set M} {g₂ g₁ : SmoothRiemannianMetric I M} {Λ Λ' Λ'' Λ''' : ℝ}
    (hEq : MetricUniformEquivalentOn (I := I) K g₂ g₁ Λ)
    (hJet1 : MetricCovDerivOrderBoundOn (I := I) K 1 g₁ g₂ Λ')
    (hJet2 : MetricCovDerivOrderBoundOn (I := I) K 2 g₁ g₂ Λ'')
    (hJet3 : MetricCovDerivOrderBoundOn (I := I) K 3 g₁ g₂ Λ''')
    {x : M} (hx : x ∈ K) (v' v w u : TangentSpace I x) :
    Real.sqrt (g₂.inner x
        (covDerivConnDiff2 (I := I) g₂ g₁
          (smoothExtensionTangent (I := I) x v') (smoothExtensionTangent (I := I) x v)
          (smoothExtensionTangent (I := I) x w) (smoothExtensionTangent (I := I) x u) x)
        (covDerivConnDiff2 (I := I) g₂ g₁
          (smoothExtensionTangent (I := I) x v') (smoothExtensionTangent (I := I) x v)
          (smoothExtensionTangent (I := I) x w) (smoothExtensionTangent (I := I) x u) x)) ≤
      (3 / 2 * Λ ^ 5 * Λ''' + 9 / 2 * Λ ^ 6 * Λ' * Λ'' + 3 * Λ ^ 7 * Λ' ^ 3) *
        Real.sqrt (g₂.inner x v' v') * Real.sqrt (g₂.inner x v v) *
          Real.sqrt (g₂.inner x w w) * Real.sqrt (g₂.inner x u u) := by
  classical
  have hL1 : (1 : ℝ) ≤ Λ := hEq.1
  have hL0 : (0 : ℝ) < Λ := lt_of_lt_of_le zero_lt_one hL1
  have hLnn : (0 : ℝ) ≤ Λ := le_of_lt hL0
  have hJ1 : metricCovDerivNorm (I := I) 1 g₁ g₂ x ≤ Λ' := hJet1 x hx
  have hJ2 : metricCovDerivNorm (I := I) 2 g₁ g₂ x ≤ Λ'' := hJet2 x hx
  have hJ3 : metricCovDerivNorm (I := I) 3 g₁ g₂ x ≤ Λ''' := hJet3 x hx
  have hL'nn : (0 : ℝ) ≤ Λ' := le_trans (Real.sqrt_nonneg _) hJ1
  have hL''nn : (0 : ℝ) ≤ Λ'' := le_trans (Real.sqrt_nonneg _) hJ2
  have hL'''nn : (0 : ℝ) ≤ Λ''' := le_trans (Real.sqrt_nonneg _) hJ3
  have hs2 : Real.sqrt Λ ^ 2 = Λ := Real.sq_sqrt hLnn
  have hs3 : Real.sqrt (Λ ^ 3) = Λ * Real.sqrt Λ := by
    rw [show Λ ^ 3 = Λ ^ 2 * Λ by ring, Real.sqrt_mul (by positivity), Real.sqrt_sq hLnn]
  have hs4 : Real.sqrt (Λ ^ 4) = Λ ^ 2 := by
    rw [show Λ ^ 4 = (Λ ^ 2) ^ 2 by ring, Real.sqrt_sq (by positivity)]
  have hs5 : Real.sqrt (Λ ^ 5) = Λ ^ 2 * Real.sqrt Λ := by
    rw [show Λ ^ 5 = (Λ ^ 2) ^ 2 * Λ by ring, Real.sqrt_mul (by positivity),
      Real.sqrt_sq (by positivity)]
  -- the dual core, in the `g₁` fibre
  have hcore := covDConnDiff2_g1_le (I := I) g₂ g₁ x v' v w u
  -- metric jets, converted from the `g₂` to the `g₁` fibre
  have hM3 : Real.sqrt (Tensor0SBundle.normSq0S (I := I) g₁ x 5
      (metricCovDeriv (I := I) g₁ g₂ 3 x)) ≤ Λ ^ 2 * Real.sqrt Λ * Λ''' := by
    have hcomp := DifferentialGeometry.Geometry.Curvature.sqrt_normSq0S_comp (I := I) hEq hx 5
      (metricCovDeriv (I := I) g₁ g₂ 3 x)
    rw [hs5] at hcomp
    refine le_trans hcomp ?_
    exact mul_le_mul_of_nonneg_left (show Real.sqrt (Tensor0SBundle.normSq0S (I := I) g₂ x 5
        (metricCovDeriv (I := I) g₁ g₂ 3 x)) ≤ Λ''' from hJ3)
      (mul_nonneg (by positivity) (Real.sqrt_nonneg _))
  have hM2 : Real.sqrt (Tensor0SBundle.normSq0S (I := I) g₁ x 4
      (metricCovDeriv (I := I) g₁ g₂ 2 x)) ≤ Λ ^ 2 * Λ'' := by
    have hcomp := DifferentialGeometry.Geometry.Curvature.sqrt_normSq0S_comp (I := I) hEq hx 4
      (metricCovDeriv (I := I) g₁ g₂ 2 x)
    rw [hs4] at hcomp
    refine le_trans hcomp ?_
    exact mul_le_mul_of_nonneg_left (show Real.sqrt (Tensor0SBundle.normSq0S (I := I) g₂ x 4
        (metricCovDeriv (I := I) g₁ g₂ 2 x)) ≤ Λ'' from hJ2) (by positivity)
  have hM1 : Real.sqrt (Tensor0SBundle.normSq0S (I := I) g₁ x 3
      (metricCovDeriv (I := I) g₁ g₂ 1 x)) ≤ Λ * Real.sqrt Λ * Λ' := by
    have hcomp := DifferentialGeometry.Geometry.Curvature.sqrt_normSq0S_comp (I := I) hEq hx 3
      (metricCovDeriv (I := I) g₁ g₂ 1 x)
    rw [hs3] at hcomp
    refine le_trans hcomp ?_
    exact mul_le_mul_of_nonneg_left (show Real.sqrt (Tensor0SBundle.normSq0S (I := I) g₂ x 3
        (metricCovDeriv (I := I) g₁ g₂ 1 x)) ≤ Λ' from hJ1)
      (mul_nonneg hLnn (Real.sqrt_nonneg _))
  have hNA : Real.sqrt (Tensor0SBundle.normSqRS (I := I) (g := g₁) (x := x) 1 2
        (Tensor0SBundle.connectionDifferenceTensorAt (I := I)
          (leviCivitaConnectionOfMetric (I := I) g₁)
          (leviCivitaConnectionOfMetric (I := I) g₂) x)) ≤ 3 / 2 * (Λ * Real.sqrt Λ * Λ') := by
    obtain ⟨_, basis₁, hhinv₁, _, _, _⟩ :=
      exists_diagInv_of_metricUniformEquivalentOn (I := I)
        (metricUniformEquivalentOn_symm (I := I) hEq) hx
    have h := diff_le_covOne_basis_ref_lc (I := I) g₁ g₂ hx Λ hEq basis₁ hhinv₁
    rw [hs3] at h
    refine le_trans h ?_
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hJ1 (mul_nonneg hLnn (Real.sqrt_nonneg _)))
      (by norm_num : (0 : ℝ) ≤ 3 / 2)
  -- shorten the fibre norms
  set M3 := Real.sqrt (Tensor0SBundle.normSq0S (I := I) g₁ x 5
    (metricCovDeriv (I := I) g₁ g₂ 3 x)) with hM3def
  set M2 := Real.sqrt (Tensor0SBundle.normSq0S (I := I) g₁ x 4
    (metricCovDeriv (I := I) g₁ g₂ 2 x)) with hM2def
  set M1 := Real.sqrt (Tensor0SBundle.normSq0S (I := I) g₁ x 3
    (metricCovDeriv (I := I) g₁ g₂ 1 x)) with hM1def
  set NA := Real.sqrt (Tensor0SBundle.normSqRS (I := I) (g := g₁) (x := x) 1 2
    (Tensor0SBundle.connectionDifferenceTensorAt (I := I)
      (leviCivitaConnectionOfMetric (I := I) g₁)
      (leviCivitaConnectionOfMetric (I := I) g₂) x)) with hNAdef
  have hM3nn : (0 : ℝ) ≤ M3 := Real.sqrt_nonneg _
  have hM2nn : (0 : ℝ) ≤ M2 := Real.sqrt_nonneg _
  have hM1nn : (0 : ℝ) ≤ M1 := Real.sqrt_nonneg _
  have hNAnn : (0 : ℝ) ≤ NA := Real.sqrt_nonneg _
  clear_value M3 M2 M1 NA
  have hc1nn : (0 : ℝ) ≤ Λ * Real.sqrt Λ * Λ' :=
    mul_nonneg (mul_nonneg hLnn (Real.sqrt_nonneg _)) hL'nn
  have hc2nn : (0 : ℝ) ≤ Λ ^ 2 * Λ'' := mul_nonneg (by positivity) hL''nn
  have hc3nn : (0 : ℝ) ≤ 3 / 2 * (Λ * Real.sqrt Λ * Λ') :=
    mul_nonneg (by norm_num) hc1nn
  -- clean product bounds
  have hp1 : M2 * NA ≤ 3 / 2 * (Λ ^ 3 * Real.sqrt Λ * Λ' * Λ'') := by
    have h := mul_le_mul hM2 hNA hNAnn hc2nn
    refine le_trans h (le_of_eq ?_)
    ring
  have hp2 : M1 * M2 ≤ Λ ^ 3 * Real.sqrt Λ * Λ' * Λ'' := by
    have h := mul_le_mul hM1 hM2 hM2nn hc1nn
    refine le_trans h (le_of_eq ?_)
    ring
  have hp3 : M1 * (M1 * NA) ≤ 3 / 2 * (Λ ^ 4 * Real.sqrt Λ * Λ' ^ 3) := by
    have h := mul_le_mul hM1 (mul_le_mul hM1 hNA hNAnn hc1nn)
      (mul_nonneg hM1nn hNAnn) hc1nn
    refine le_trans h (le_of_eq ?_)
    linear_combination (3 / 2 * Λ ^ 3 * Λ' ^ 3 * Real.sqrt Λ) * hs2
  have hexp : 2 * M1 * (3 / 2 * M2 + M1 * NA) = 3 * (M1 * M2) + 2 * (M1 * (M1 * NA)) := by
    ring
  have hbr : 3 / 2 * M3 + M2 * NA + 2 * M1 * (3 / 2 * M2 + M1 * NA) ≤
      Real.sqrt Λ * (3 / 2 * Λ ^ 2 * Λ''' + 9 / 2 * Λ ^ 3 * Λ' * Λ'' + 3 * Λ ^ 4 * Λ' ^ 3) := by
    nlinarith [hM3, hp1, hp2, hp3, hexp]
  have hbrnn : (0 : ℝ) ≤ 3 / 2 * M3 + M2 * NA + 2 * M1 * (3 / 2 * M2 + M1 * NA) :=
    add_nonneg (add_nonneg (by linarith) (mul_nonneg hM2nn hNAnn))
      (mul_nonneg (by linarith) (add_nonneg (by linarith) (mul_nonneg hM1nn hNAnn)))
  -- vector comparability
  set B2 : TangentSpace I x :=
    covDerivConnDiff2 (I := I) g₂ g₁
      (smoothExtensionTangent (I := I) x v') (smoothExtensionTangent (I := I) x v)
      (smoothExtensionTangent (I := I) x w) (smoothExtensionTangent (I := I) x u) x with hB2def
  clear_value B2
  have hvec : ∀ z : TangentSpace I x,
      Real.sqrt (g₁.inner x z z) ≤ Real.sqrt Λ * Real.sqrt (g₂.inner x z z) := by
    intro z
    calc Real.sqrt (g₁.inner x z z) ≤ Real.sqrt (Λ * g₂.inner x z z) :=
          Real.sqrt_le_sqrt (hEq.2 x hx z).2
      _ = Real.sqrt Λ * Real.sqrt (g₂.inner x z z) := Real.sqrt_mul hLnn _
  have hBcomp : Real.sqrt (g₂.inner x B2 B2) ≤ Real.sqrt Λ * Real.sqrt (g₁.inner x B2 B2) := by
    have h := (hEq.2 x hx B2).1
    have h' : g₂.inner x B2 B2 ≤ Λ * g₁.inner x B2 B2 := by
      have h2 := mul_le_mul_of_nonneg_left h hLnn
      rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hL0), one_mul] at h2
      exact h2
    calc Real.sqrt (g₂.inner x B2 B2) ≤ Real.sqrt (Λ * g₁.inner x B2 B2) := Real.sqrt_le_sqrt h'
      _ = Real.sqrt Λ * Real.sqrt (g₁.inner x B2 B2) := Real.sqrt_mul hLnn _
  have hv4 : Real.sqrt (g₁.inner x v' v') * Real.sqrt (g₁.inner x v v) *
        Real.sqrt (g₁.inner x w w) * Real.sqrt (g₁.inner x u u) ≤
      Real.sqrt Λ * Real.sqrt (g₂.inner x v' v') * (Real.sqrt Λ * Real.sqrt (g₂.inner x v v)) *
        (Real.sqrt Λ * Real.sqrt (g₂.inner x w w)) *
          (Real.sqrt Λ * Real.sqrt (g₂.inner x u u)) := by
    have p1 : Real.sqrt (g₁.inner x v' v') * Real.sqrt (g₁.inner x v v) ≤
        Real.sqrt Λ * Real.sqrt (g₂.inner x v' v') *
          (Real.sqrt Λ * Real.sqrt (g₂.inner x v v)) :=
      mul_le_mul (hvec v') (hvec v) (Real.sqrt_nonneg _) (by positivity)
    have p2 : Real.sqrt (g₁.inner x v' v') * Real.sqrt (g₁.inner x v v) *
          Real.sqrt (g₁.inner x w w) ≤
        Real.sqrt Λ * Real.sqrt (g₂.inner x v' v') * (Real.sqrt Λ * Real.sqrt (g₂.inner x v v)) *
          (Real.sqrt Λ * Real.sqrt (g₂.inner x w w)) :=
      mul_le_mul p1 (hvec w) (Real.sqrt_nonneg _) (by positivity)
    exact mul_le_mul p2 (hvec u) (Real.sqrt_nonneg _) (by positivity)
  have hfin : Real.sqrt (g₁.inner x B2 B2) ≤
      Real.sqrt Λ * (3 / 2 * Λ ^ 2 * Λ''' + 9 / 2 * Λ ^ 3 * Λ' * Λ'' + 3 * Λ ^ 4 * Λ' ^ 3) *
        (Real.sqrt Λ * Real.sqrt (g₂.inner x v' v') *
          (Real.sqrt Λ * Real.sqrt (g₂.inner x v v)) *
          (Real.sqrt Λ * Real.sqrt (g₂.inner x w w)) *
          (Real.sqrt Λ * Real.sqrt (g₂.inner x u u))) := by
    refine le_trans hcore ?_
    have h1 := mul_le_mul_of_nonneg_left hv4 hbrnn
    have h2 := mul_le_mul_of_nonneg_right hbr
      (show (0 : ℝ) ≤ Real.sqrt Λ * Real.sqrt (g₂.inner x v' v') *
          (Real.sqrt Λ * Real.sqrt (g₂.inner x v v)) *
          (Real.sqrt Λ * Real.sqrt (g₂.inner x w w)) *
          (Real.sqrt Λ * Real.sqrt (g₂.inner x u u)) by positivity)
    nlinarith [h1, h2]
  calc Real.sqrt (g₂.inner x B2 B2)
      ≤ Real.sqrt Λ * Real.sqrt (g₁.inner x B2 B2) := hBcomp
    _ ≤ Real.sqrt Λ *
          (Real.sqrt Λ * (3 / 2 * Λ ^ 2 * Λ''' + 9 / 2 * Λ ^ 3 * Λ' * Λ'' + 3 * Λ ^ 4 * Λ' ^ 3) *
            (Real.sqrt Λ * Real.sqrt (g₂.inner x v' v') *
              (Real.sqrt Λ * Real.sqrt (g₂.inner x v v)) *
              (Real.sqrt Λ * Real.sqrt (g₂.inner x w w)) *
              (Real.sqrt Λ * Real.sqrt (g₂.inner x u u)))) :=
        mul_le_mul_of_nonneg_left hfin (Real.sqrt_nonneg _)
    _ = (3 / 2 * Λ ^ 5 * Λ''' + 9 / 2 * Λ ^ 6 * Λ' * Λ'' + 3 * Λ ^ 7 * Λ' ^ 3) *
          Real.sqrt (g₂.inner x v' v') * Real.sqrt (g₂.inner x v v) *
            Real.sqrt (g₂.inner x w w) * Real.sqrt (g₂.inner x u u) := by
        linear_combination ((3 / 2 * Λ ^ 2 * Λ''' + 9 / 2 * Λ ^ 3 * Λ' * Λ'' +
            3 * Λ ^ 4 * Λ' ^ 3) *
          (Real.sqrt Λ ^ 4 + Real.sqrt Λ ^ 2 * Λ + Λ ^ 2) *
          (Real.sqrt (g₂.inner x v' v') * Real.sqrt (g₂.inner x v v) *
            Real.sqrt (g₂.inner x w w) * Real.sqrt (g₂.inner x u u))) * hs2

open DifferentialGeometry.Integral.Connection in
/-- **The outer peel of the a=2 base-Leibniz eval `∇₂²(A ⋆ S)`** (session-1 core,
correct-by-construction).  Evaluating the second base covariant derivative of a single
connection-difference step `∇₂²(A ⋆ S) = covStep g₂ (s+2)(covStep g₂ (s+1)(diffStep g₁ g₂ s S))` on
`Fin.cons (U x)(Fin.cons (W x)(Fin.cons (V x)(Vslots·x)))` peels the outer `covStep g₂` by
`covStep_eval_smooth_slots` (field `H = covStep g₂ (s+1)(diffStep S)`, derivative `U`), then rewrites
the inner scalar field `y ↦ H y (…)` pointwise by `diffStep_leibniz_eval` into the two
diffStep-Leibniz sums: **T1**, the `covDerivConnDiff`-insertion (`∇₂A ⋆ S`) sum, and **T2**, the
`A`-insertion (`A ⋆ ∇₂S`) sum.  The remaining `H`-connection-correction sum
(`covStep g₂ (s+1)(diffStep S)` on the `∇₂_U`-updated slots) is left unevaluated, to be resolved by
`diffStep_leibniz_eval` one level down in the next session.  This is the reusable scaffold that the
branch lemmas differentiate; no differentiability hypothesis is needed (the exterior-derivative
linearity split is deferred to the branch layer). -/
theorem covStep2_diffStep_peel
    (g₁ g₂ : SmoothRiemannianMetric I M) (s : Nat)
    (S : Tensor0SBundle.Tensor0SField (𝕜 := ℝ) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) s)
    (U W V : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (Vslots : Fin s -> ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _))
    (x : M) :
    covStep (I := I) g₂ (s + 2)
        (covStep (I := I) g₂ (s + 1) (diffStep (I := I) g₁ g₂ s S)) x
        (Fin.cons (U x) (Fin.cons (W x) (Fin.cons (V x) (fun a : Fin s => Vslots a x))))
      = extDerivFun (I := I)
            (fun y : M =>
              (-∑ a : Fin s, (S y) (Function.update (fun b : Fin s => Vslots b y) a
                  (covDerivConnDiff (I := I) g₂ g₁
                    (fun z => W z) (fun z => V z) (fun z => Vslots a z) y)))
              - ∑ a : Fin s, covStep (I := I) g₂ s S y
                  (Fin.cons (W y) (Function.update (fun b : Fin s => Vslots b y) a
                    ((CovariantDerivative.difference
                        (leviCivitaConnectionOfMetric (I := I) g₁)
                        (leviCivitaConnectionOfMetric (I := I) g₂) y
                        (Vslots a y)) (V y))))) x (U x)
        - ∑ q : Fin (s + 2),
            (covStep (I := I) g₂ (s + 1) (diffStep (I := I) g₁ g₂ s S)) x
              (Function.update
                (fun b : Fin (s + 2) =>
                  (Fin.cons W (Fin.cons V Vslots) :
                    Fin (s + 2) → ContMDiffSection I E (∞ : WithTop ℕ∞)
                      (TangentSpace I : M -> Type _)) b x) q
                ((leviCivitaConnectionOfMetric (I := I) g₂
                    (fun y : M =>
                      (Fin.cons W (Fin.cons V Vslots) :
                        Fin (s + 2) → ContMDiffSection I E (∞ : WithTop ℕ∞)
                          (TangentSpace I : M -> Type _)) q y) x) (U x))) := by
  classical
  haveI : IsManifold I 1 M :=
    IsManifold.of_le (I := I) (M := M) (n := ∞) (by decide : (1 : WithTop ℕ∞) ≤ ∞)
  haveI : IsManifold I 2 M :=
    IsManifold.of_le (I := I) (M := M) (n := ∞) (by decide : (2 : WithTop ℕ∞) ≤ ∞)
  haveI : IsManifold I ((∞ : WithTop ℕ∞) + 1) M := by
    change IsManifold I ∞ M
    infer_instance
  haveI : IsManifold I (1 + 1) M :=
    IsManifold.of_le (I := I) (M := M) (n := ∞)
      (by decide : ((1 : WithTop ℕ∞) + 1) ≤ ∞)
  haveI : ContMDiffVectorBundle 1 E (TangentSpace I : M -> Type _) I :=
    TangentBundle.contMDiffVectorBundle (I := I) (M := M) (n := 1)
  set RR : Fin (s + 2) → ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _) := Fin.cons W (Fin.cons V Vslots) with hRRdef
  have hRRpt : ∀ y : M, (fun q : Fin (s + 2) => RR q y)
      = Fin.cons (W y) (Fin.cons (V y) (fun a : Fin s => Vslots a y)) := by
    intro y
    funext q
    refine Fin.cases ?_ (fun i => ?_) q
    · simp [hRRdef]
    · refine Fin.cases ?_ (fun j => ?_) i <;> simp [hRRdef]
  rw [show Fin.cons (W x) (Fin.cons (V x) (fun a : Fin s => Vslots a x))
        = (fun q : Fin (s + 2) => RR q x) from (hRRpt x).symm,
    covStep_eval_smooth_slots (I := I) g₂ (s + 2)
      (covStep (I := I) g₂ (s + 1) (diffStep (I := I) g₁ g₂ s S)) U RR x]
  have hInner :
      (fun y : M => (covStep (I := I) g₂ (s + 1) (diffStep (I := I) g₁ g₂ s S)) y
          (fun q : Fin (s + 2) => RR q y))
        = (fun y : M =>
            (-∑ a : Fin s, (S y) (Function.update (fun b : Fin s => Vslots b y) a
                (covDerivConnDiff (I := I) g₂ g₁
                  (fun z => W z) (fun z => V z) (fun z => Vslots a z) y)))
            - ∑ a : Fin s, covStep (I := I) g₂ s S y
                (Fin.cons (W y) (Function.update (fun b : Fin s => Vslots b y) a
                  ((CovariantDerivative.difference
                      (leviCivitaConnectionOfMetric (I := I) g₁)
                      (leviCivitaConnectionOfMetric (I := I) g₂) y
                      (Vslots a y)) (V y))))) := by
    funext y
    rw [hRRpt y]
    exact diffStep_leibniz_eval (I := I) g₁ g₂ s S W V Vslots y
  rw [hInner]

open DifferentialGeometry.Integral.Connection in
/-- **The T1 branch of the a=2 base-Leibniz eval, per slot** (session-1 core).  Differentiates the
`covDerivConnDiff`-insertion summand `y ↦ (S y)(update (Vslots·y) a (∇₂A(W;V,Vslots a) y))` (one slot
`a` of the `T1` sum peeled by `covStep2_diffStep_peel`) by `covStep_eval_smooth_slots` (field `S`,
derivative `U`), then **materialises `covDerivConnDiff2`** on the diagonal via `covDerivConnDiff2_eq`
(its definition is exactly `∇₂_U(∇₂A-section) − 3` covariant slot corrections, smoothness supplied by
`covDerivConnDiff_contMDiff`).  The three branches: the leading `∇₂S`-into-`∇₂A` term, the diagonal
`∇₂²A` insertion (`covDerivConnDiff2` plus its three `covDerivConnDiff` corrections), and the
off-diagonal `∇₂_U(Vslots b)` insertions.  Summing over `a` and combining with the T2 branch and the
`H`-correction sum is the session-2 assembly. -/
theorem covStep2_diffStep_branch1
    (g₁ g₂ : SmoothRiemannianMetric I M) (s : Nat)
    (S : Tensor0SBundle.Tensor0SField (𝕜 := ℝ) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) s)
    (U W V : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (Vslots : Fin s -> ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _))
    (a : Fin s) (x : M) :
    extDerivFun (I := I)
        (fun y : M => (S y) (Function.update (fun b : Fin s => Vslots b y) a
          (covDerivConnDiff (I := I) g₂ g₁
            (fun z => W z) (fun z => V z) (fun z => Vslots a z) y))) x (U x)
      = covStep (I := I) g₂ s S x
          (Fin.cons (U x) (Function.update (fun b : Fin s => Vslots b x) a
            (covDerivConnDiff (I := I) g₂ g₁
              (fun z => W z) (fun z => V z) (fun z => Vslots a z) x)))
        + (S x) (Function.update (fun b : Fin s => Vslots b x) a
            (covDerivConnDiff2 (I := I) g₂ g₁
                (fun z => U z) (fun z => W z) (fun z => V z) (fun z => Vslots a z) x
              + covDerivConnDiff (I := I) g₂ g₁
                  (covApply (LeviCivita (I := I) g₂) (fun z => U z) (fun z => W z))
                  (fun z => V z) (fun z => Vslots a z) x
              + covDerivConnDiff (I := I) g₂ g₁ (fun z => W z)
                  (covApply (LeviCivita (I := I) g₂) (fun z => U z) (fun z => V z))
                  (fun z => Vslots a z) x
              + covDerivConnDiff (I := I) g₂ g₁ (fun z => W z) (fun z => V z)
                  (covApply (LeviCivita (I := I) g₂) (fun z => U z) (fun z => Vslots a z)) x))
        + ∑ b ∈ Finset.univ.erase a, (S x) (Function.update
            (Function.update (fun c : Fin s => Vslots c x) a
              (covDerivConnDiff (I := I) g₂ g₁
                (fun z => W z) (fun z => V z) (fun z => Vslots a z) x)) b
            ((leviCivitaConnectionOfMetric (I := I) g₂
                (fun y : M => Vslots b y) x) (U x))) := by
  classical
  haveI : IsManifold I 1 M :=
    IsManifold.of_le (I := I) (M := M) (n := ∞) (by decide : (1 : WithTop ℕ∞) ≤ ∞)
  haveI : IsManifold I 2 M :=
    IsManifold.of_le (I := I) (M := M) (n := ∞) (by decide : (2 : WithTop ℕ∞) ≤ ∞)
  haveI : IsManifold I ((∞ : WithTop ℕ∞) + 1) M := by
    change IsManifold I ∞ M
    infer_instance
  haveI : IsManifold I (1 + 1) M :=
    IsManifold.of_le (I := I) (M := M) (n := ∞)
      (by decide : ((1 : WithTop ℕ∞) + 1) ≤ ∞)
  haveI : ContMDiffVectorBundle 1 E (TangentSpace I : M -> Type _) I :=
    TangentBundle.contMDiffVectorBundle (I := I) (M := M) (n := 1)
  haveI hcov₁ : CovariantDerivative.ContMDiffCovariantDerivative
      (leviCivitaConnectionOfMetric (I := I) g₁) (∞ : WithTop ℕ∞) :=
    leviCivitaConnectionOfMetric_contMDiffCovariantDerivative (I := I) g₁
  haveI hcov₂ : CovariantDerivative.ContMDiffCovariantDerivative
      (leviCivitaConnectionOfMetric (I := I) g₂) (∞ : WithTop ℕ∞) :=
    leviCivitaConnectionOfMetric_contMDiffCovariantDerivative (I := I) g₂
  set CDCsec : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _) :=
    ContMDiffSection.mk
      (fun p => covDerivConnDiff (I := I) g₂ g₁
        (fun z => W z) (fun z => V z) (fun z => Vslots a z) p)
      (covDerivConnDiff_contMDiff (I := I) g₂ g₁ W V (Vslots a)) with hCDCdef
  set σ : Fin s → ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _) :=
    Function.update Vslots a CDCsec with hσdef
  have hCDCcoe : ∀ p : M, (CDCsec) p
      = covDerivConnDiff (I := I) g₂ g₁
          (fun z => W z) (fun z => V z) (fun z => Vslots a z) p := by
    intro p
    rw [hCDCdef]
    rfl
  have hσeval : ∀ y : M, (fun b : Fin s => (σ b) y)
      = Function.update (fun b : Fin s => Vslots b y) a
          (covDerivConnDiff (I := I) g₂ g₁
            (fun z => W z) (fun z => V z) (fun z => Vslots a z) y) := by
    intro y
    funext b
    rcases eq_or_ne b a with hb | hb
    · subst hb
      simp only [hσdef, Function.update_self]
      exact hCDCcoe y
    · simp only [hσdef, Function.update_of_ne hb]
  have hInnerFun : (fun y : M => (S y) (Function.update (fun b : Fin s => Vslots b y) a
        (covDerivConnDiff (I := I) g₂ g₁
          (fun z => W z) (fun z => V z) (fun z => Vslots a z) y)))
      = (fun y : M => (S y) (fun b : Fin s => (σ b) y)) := by
    funext y
    rw [hσeval y]
  rw [hInnerFun]
  have hpeel := covStep_eval_smooth_slots (I := I) g₂ s S U σ x
  have hpeel' : extDerivFun (I := I) (fun y : M => (S y) (fun b : Fin s => (σ b) y)) x (U x)
      = covStep (I := I) g₂ s S x (Fin.cons (U x) (fun b : Fin s => (σ b) x))
        + ∑ q : Fin s, (S x) (Function.update (fun b : Fin s => (σ b) x) q
            ((leviCivitaConnectionOfMetric (I := I) g₂ (fun y : M => (σ q) y) x) (U x))) := by
    rw [hpeel]
    ring
  have hσa : (fun y : M => (σ a) y)
      = (fun p : M => covDerivConnDiff (I := I) g₂ g₁
          (fun z => W z) (fun z => V z) (fun z => Vslots a z) p) := by
    funext y
    simp only [hσdef, Function.update_self]
    exact hCDCcoe y
  have hdiag : (leviCivitaConnectionOfMetric (I := I) g₂ (fun y : M => (σ a) y) x) (U x)
      = covDerivConnDiff2 (I := I) g₂ g₁
          (fun z => U z) (fun z => W z) (fun z => V z) (fun z => Vslots a z) x
        + covDerivConnDiff (I := I) g₂ g₁
            (covApply (LeviCivita (I := I) g₂) (fun z => U z) (fun z => W z))
            (fun z => V z) (fun z => Vslots a z) x
        + covDerivConnDiff (I := I) g₂ g₁ (fun z => W z)
            (covApply (LeviCivita (I := I) g₂) (fun z => U z) (fun z => V z))
            (fun z => Vslots a z) x
        + covDerivConnDiff (I := I) g₂ g₁ (fun z => W z) (fun z => V z)
            (covApply (LeviCivita (I := I) g₂) (fun z => U z) (fun z => Vslots a z)) x := by
    rw [hσa, covDerivConnDiff2_eq]
    simp only [covApply, LeviCivita_eq_leviCivitaConnectionOfMetric]
    abel
  have hoff : (∑ b ∈ Finset.univ.erase a, (S x) (Function.update
        (Function.update (fun c : Fin s => Vslots c x) a
          (covDerivConnDiff (I := I) g₂ g₁
            (fun z => W z) (fun z => V z) (fun z => Vslots a z) x)) b
        ((leviCivitaConnectionOfMetric (I := I) g₂ (fun y : M => (σ b) y) x) (U x))))
      = ∑ b ∈ Finset.univ.erase a, (S x) (Function.update
          (Function.update (fun c : Fin s => Vslots c x) a
            (covDerivConnDiff (I := I) g₂ g₁
              (fun z => W z) (fun z => V z) (fun z => Vslots a z) x)) b
          ((leviCivitaConnectionOfMetric (I := I) g₂ (fun y : M => Vslots b y) x) (U x))) := by
    refine Finset.sum_congr rfl (fun b hb => ?_)
    have hbne : (fun y : M => (σ b) y) = (fun y : M => Vslots b y) := by
      funext y
      simp only [hσdef, Function.update_of_ne (Finset.ne_of_mem_erase hb)]
    rw [hbne]
  rw [hpeel', hσeval x, ← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ a),
    Function.update_idem, hdiag, hoff]
  abel

open DifferentialGeometry.Integral.Connection in
/-- **The T2 branch of the a=2 base-Leibniz eval, per slot** (session-2 core).  Differentiates the
`A`-insertion summand `y ↦ (∇₂S) y (cons (W y)(update (Vslots·y) a (A_y(Vslots a, V))))` (one slot `a`
of the `T2` sum peeled by `covStep2_diffStep_peel`, field `∇₂S = covStep g₂ s S`, rank `s+1`) by
`covStep_eval_smooth_slots` (derivative `U`).  Four branches: the leading **`∇₂²S`** term, the `p=0`
`∇₂_U W`-into-`W` insertion, the diagonal **`covDerivConnDiff`** branch (`∇₂_U(A(Vslots a,V))` expanded
by the connection-difference product rule into `covDerivConnDiff g₂ g₁ U V (Vslots a)` plus two
`A ⋆ ∇₂` corrections), and the off-diagonal `∇₂_U(Vslots b)` insertions.  Together with
`covStep2_diffStep_branch1` this fully resolves `−extDerivFun T1 − extDerivFun T2`; the `∇₂²S`
cancellation against `PieceB` is the session-3 assembly. -/
theorem covStep2_diffStep_branch2
    (g₁ g₂ : SmoothRiemannianMetric I M) (s : Nat)
    (S : Tensor0SBundle.Tensor0SField (𝕜 := ℝ) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) s)
    (U W V : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (Vslots : Fin s -> ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _))
    (a : Fin s) (x : M) :
    extDerivFun (I := I)
        (fun y : M => covStep (I := I) g₂ s S y
          (Fin.cons (W y) (Function.update (fun b : Fin s => Vslots b y) a
            ((CovariantDerivative.difference
                (leviCivitaConnectionOfMetric (I := I) g₁)
                (leviCivitaConnectionOfMetric (I := I) g₂) y
                (Vslots a y)) (V y))))) x (U x)
      = covStep (I := I) g₂ (s + 1) (covStep (I := I) g₂ s S) x
          (Fin.cons (U x) (Fin.cons (W x) (Function.update (fun b : Fin s => Vslots b x) a
            ((CovariantDerivative.difference
                (leviCivitaConnectionOfMetric (I := I) g₁)
                (leviCivitaConnectionOfMetric (I := I) g₂) x
                (Vslots a x)) (V x)))))
        + covStep (I := I) g₂ s S x
            (Fin.cons ((leviCivitaConnectionOfMetric (I := I) g₂ (fun y : M => W y) x) (U x))
              (Function.update (fun b : Fin s => Vslots b x) a
                ((CovariantDerivative.difference
                    (leviCivitaConnectionOfMetric (I := I) g₁)
                    (leviCivitaConnectionOfMetric (I := I) g₂) x
                    (Vslots a x)) (V x))))
        + covStep (I := I) g₂ s S x
            (Fin.cons (W x) (Function.update (fun b : Fin s => Vslots b x) a
              (covDerivConnDiff (I := I) g₂ g₁
                  (fun z => U z) (fun z => V z) (fun z => Vslots a z) x
                + (CovariantDerivative.difference
                    (leviCivitaConnectionOfMetric (I := I) g₁)
                    (leviCivitaConnectionOfMetric (I := I) g₂) x (Vslots a x))
                    ((leviCivitaConnectionOfMetric (I := I) g₂ (fun y : M => V y) x) (U x))
                + (CovariantDerivative.difference
                    (leviCivitaConnectionOfMetric (I := I) g₁)
                    (leviCivitaConnectionOfMetric (I := I) g₂) x
                    ((leviCivitaConnectionOfMetric (I := I) g₂ (fun y : M => Vslots a y) x) (U x)))
                    (V x))))
        + ∑ b ∈ Finset.univ.erase a, covStep (I := I) g₂ s S x
            (Fin.cons (W x) (Function.update
              (Function.update (fun c : Fin s => Vslots c x) a
                ((CovariantDerivative.difference
                    (leviCivitaConnectionOfMetric (I := I) g₁)
                    (leviCivitaConnectionOfMetric (I := I) g₂) x
                    (Vslots a x)) (V x))) b
              ((leviCivitaConnectionOfMetric (I := I) g₂ (fun y : M => Vslots b y) x) (U x)))) := by
  classical
  haveI : IsManifold I 1 M :=
    IsManifold.of_le (I := I) (M := M) (n := ∞) (by decide : (1 : WithTop ℕ∞) ≤ ∞)
  haveI : IsManifold I 2 M :=
    IsManifold.of_le (I := I) (M := M) (n := ∞) (by decide : (2 : WithTop ℕ∞) ≤ ∞)
  haveI : IsManifold I ((∞ : WithTop ℕ∞) + 1) M := by
    change IsManifold I ∞ M
    infer_instance
  haveI : IsManifold I (1 + 1) M :=
    IsManifold.of_le (I := I) (M := M) (n := ∞)
      (by decide : ((1 : WithTop ℕ∞) + 1) ≤ ∞)
  haveI : ContMDiffVectorBundle 1 E (TangentSpace I : M -> Type _) I :=
    TangentBundle.contMDiffVectorBundle (I := I) (M := M) (n := 1)
  haveI hcov₁ : CovariantDerivative.ContMDiffCovariantDerivative
      (leviCivitaConnectionOfMetric (I := I) g₁) (∞ : WithTop ℕ∞) :=
    leviCivitaConnectionOfMetric_contMDiffCovariantDerivative (I := I) g₁
  haveI hcov₂ : CovariantDerivative.ContMDiffCovariantDerivative
      (leviCivitaConnectionOfMetric (I := I) g₂) (∞ : WithTop ℕ∞) :=
    leviCivitaConnectionOfMetric_contMDiffCovariantDerivative (I := I) g₂
  set Asec : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _) :=
    ContMDiffSection.mk
      (diffSec (leviCivitaConnectionOfMetric (I := I) g₂)
        (leviCivitaConnectionOfMetric (I := I) g₁) (fun y : M => V y) (fun y : M => Vslots a y))
      (diffSec_contMDiff (leviCivitaConnectionOfMetric (I := I) g₂)
        (leviCivitaConnectionOfMetric (I := I) g₁) V.contMDiff
        (by simpa using (Vslots a).contMDiff)) with hAsecdef
  set ρ : Fin (s + 1) → ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _) :=
    Fin.cons W (Function.update Vslots a Asec) with hρdef
  have hAcoe : ∀ y : M, (Asec) y
      = (CovariantDerivative.difference
          (leviCivitaConnectionOfMetric (I := I) g₁)
          (leviCivitaConnectionOfMetric (I := I) g₂) y (Vslots a y)) (V y) := by
    intro y
    rw [hAsecdef]
    rfl
  have hρpt : ∀ y : M, (fun p : Fin (s + 1) => (ρ p) y)
      = Fin.cons (W y) (Function.update (fun b : Fin s => Vslots b y) a
          ((CovariantDerivative.difference
              (leviCivitaConnectionOfMetric (I := I) g₁)
              (leviCivitaConnectionOfMetric (I := I) g₂) y (Vslots a y)) (V y))) := by
    intro y
    funext p
    refine Fin.cases ?_ (fun i => ?_) p
    · simp only [hρdef, Fin.cons_zero]
    · rcases eq_or_ne i a with hi | hi
      · subst hi
        simp only [hρdef, Fin.cons_succ, Function.update_self]
        exact hAcoe y
      · simp only [hρdef, Fin.cons_succ, Function.update_of_ne hi]
  have hInnerFun : (fun y : M => covStep (I := I) g₂ s S y
        (Fin.cons (W y) (Function.update (fun b : Fin s => Vslots b y) a
          ((CovariantDerivative.difference
              (leviCivitaConnectionOfMetric (I := I) g₁)
              (leviCivitaConnectionOfMetric (I := I) g₂) y
              (Vslots a y)) (V y)))))
      = (fun y : M => covStep (I := I) g₂ s S y (fun p : Fin (s + 1) => (ρ p) y)) := by
    funext y
    rw [hρpt y]
  rw [hInnerFun]
  have hpeel := covStep_eval_smooth_slots (I := I) g₂ (s + 1) (covStep (I := I) g₂ s S) U ρ x
  have hpeel' : extDerivFun (I := I)
        (fun y : M => covStep (I := I) g₂ s S y (fun p : Fin (s + 1) => (ρ p) y)) x (U x)
      = covStep (I := I) g₂ (s + 1) (covStep (I := I) g₂ s S) x
          (Fin.cons (U x) (fun p : Fin (s + 1) => (ρ p) x))
        + ∑ p : Fin (s + 1), (covStep (I := I) g₂ s S x) (Function.update
            (fun b : Fin (s + 1) => (ρ b) x) p
            ((leviCivitaConnectionOfMetric (I := I) g₂ (fun y : M => (ρ p) y) x) (U x))) := by
    rw [hpeel]
    ring
  have hfact : (leviCivitaConnectionOfMetric (I := I) g₂ (fun y : M => (Asec) y) x) (U x)
      = covDerivConnDiff (I := I) g₂ g₁
          (fun z => U z) (fun z => V z) (fun z => Vslots a z) x
        + (CovariantDerivative.difference
            (leviCivitaConnectionOfMetric (I := I) g₁)
            (leviCivitaConnectionOfMetric (I := I) g₂) x (Vslots a x))
            ((leviCivitaConnectionOfMetric (I := I) g₂ (fun y : M => V y) x) (U x))
        + (CovariantDerivative.difference
            (leviCivitaConnectionOfMetric (I := I) g₁)
            (leviCivitaConnectionOfMetric (I := I) g₂) x
            ((leviCivitaConnectionOfMetric (I := I) g₂ (fun y : M => Vslots a y) x) (U x)))
            (V x) := by
    rw [covDerivConnDiff_eq]
    simp only [covDerivDiff, covApply, hAsecdef, ContMDiffSection.coeFn_mk,
      LeviCivita_eq_leviCivitaConnectionOfMetric]
    abel
  have hρ0 : (fun y : M => (ρ (0 : Fin (s + 1))) y) = (fun y : M => W y) := by
    funext y
    simp only [hρdef, Fin.cons_zero]
  have hoff : (∑ i ∈ Finset.univ.erase a, (covStep (I := I) g₂ s S x) (Fin.cons (W x)
        (Function.update (Function.update (fun c : Fin s => Vslots c x) a
            ((CovariantDerivative.difference
                (leviCivitaConnectionOfMetric (I := I) g₁)
                (leviCivitaConnectionOfMetric (I := I) g₂) x (Vslots a x)) (V x))) i
          ((leviCivitaConnectionOfMetric (I := I) g₂ (fun y : M => (ρ i.succ) y) x) (U x)))))
      = ∑ i ∈ Finset.univ.erase a, (covStep (I := I) g₂ s S x) (Fin.cons (W x)
          (Function.update (Function.update (fun c : Fin s => Vslots c x) a
              ((CovariantDerivative.difference
                  (leviCivitaConnectionOfMetric (I := I) g₁)
                  (leviCivitaConnectionOfMetric (I := I) g₂) x (Vslots a x)) (V x))) i
            ((leviCivitaConnectionOfMetric (I := I) g₂ (fun y : M => Vslots i y) x) (U x)))) := by
    refine Finset.sum_congr rfl (fun i hi => ?_)
    have hine : (fun y : M => (ρ i.succ) y) = (fun y : M => Vslots i y) := by
      funext y
      simp only [hρdef, Fin.cons_succ, Function.update_of_ne (Finset.ne_of_mem_erase hi)]
    rw [hine]
  rw [hpeel', hρpt x, Fin.sum_univ_succ]
  simp only [Fin.update_cons_zero, ← Fin.cons_update, hρ0]
  rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ a)]
  have hρa : (fun y : M => (ρ a.succ) y) = (fun y : M => (Asec) y) := by
    funext y
    simp only [hρdef, Fin.cons_succ, Function.update_self]
  rw [Function.update_idem, hρa, hfact, hoff]
  abel

set_option backward.isDefEq.respectTransparency false in
open DifferentialGeometry.Integral.Connection in
/-- **Differentiability of the T1 summand** at `x`: the scalar field
`y ↦ (S y)(update (Vslots·y) a (∇₂A(W;V,Vslots a) y))` is `MDifferentiableAt` (the `covDerivConnDiff`
slot is a smooth section by `covDerivConnDiff_contMDiff`).  Feeds the exterior-derivative linearity
split `covStep2_diffStep_split`.  Needs `backward.isDefEq.respectTransparency false` for the
`Tensor0SModel`-`NormedSpace` synthesis in `contMDiffAt_section_apply_gen` (the IPS-file remedy). -/
theorem covStep2_branch1_mdiff
    (g₁ g₂ : SmoothRiemannianMetric I M) (s : Nat)
    (S : Tensor0SBundle.Tensor0SField (𝕜 := ℝ) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) s)
    (U W V : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (Vslots : Fin s -> ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _))
    (a : Fin s) (x : M) :
    MDifferentiableAt I 𝓘(ℝ, ℝ)
      (fun y : M => (S y) (Function.update (fun b : Fin s => Vslots b y) a
        (covDerivConnDiff (I := I) g₂ g₁
          (fun z => W z) (fun z => V z) (fun z => Vslots a z) y))) x := by
  classical
  haveI : IsManifold I 1 M :=
    IsManifold.of_le (I := I) (M := M) (n := ∞) (by decide : (1 : WithTop ℕ∞) ≤ ∞)
  haveI : IsManifold I 2 M :=
    IsManifold.of_le (I := I) (M := M) (n := ∞) (by decide : (2 : WithTop ℕ∞) ≤ ∞)
  haveI : IsManifold I ((∞ : WithTop ℕ∞) + 1) M := by
    change IsManifold I ∞ M
    infer_instance
  haveI : IsManifold I (1 + 1) M :=
    IsManifold.of_le (I := I) (M := M) (n := ∞)
      (by decide : ((1 : WithTop ℕ∞) + 1) ≤ ∞)
  haveI : ContMDiffVectorBundle 1 E (TangentSpace I : M -> Type _) I :=
    TangentBundle.contMDiffVectorBundle (I := I) (M := M) (n := 1)
  haveI hcov₁ : CovariantDerivative.ContMDiffCovariantDerivative
      (leviCivitaConnectionOfMetric (I := I) g₁) (∞ : WithTop ℕ∞) :=
    leviCivitaConnectionOfMetric_contMDiffCovariantDerivative (I := I) g₁
  haveI hcov₂ : CovariantDerivative.ContMDiffCovariantDerivative
      (leviCivitaConnectionOfMetric (I := I) g₂) (∞ : WithTop ℕ∞) :=
    leviCivitaConnectionOfMetric_contMDiffCovariantDerivative (I := I) g₂
  set CDCsec : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _) :=
    ContMDiffSection.mk
      (fun p => covDerivConnDiff (I := I) g₂ g₁
        (fun z => W z) (fun z => V z) (fun z => Vslots a z) p)
      (covDerivConnDiff_contMDiff (I := I) g₂ g₁ W V (Vslots a)) with hCDCdef
  set σ : Fin s → ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _) :=
    Function.update Vslots a CDCsec with hσdef
  have hCDCcoe : ∀ p : M, (CDCsec) p
      = covDerivConnDiff (I := I) g₂ g₁
          (fun z => W z) (fun z => V z) (fun z => Vslots a z) p := by
    intro p
    rw [hCDCdef]
    rfl
  have hσeval : ∀ y : M, (fun b : Fin s => (σ b) y)
      = Function.update (fun b : Fin s => Vslots b y) a
          (covDerivConnDiff (I := I) g₂ g₁
            (fun z => W z) (fun z => V z) (fun z => Vslots a z) y) := by
    intro y
    funext b
    rcases eq_or_ne b a with hb | hb
    · subst hb
      simp only [hσdef, Function.update_self]
      exact hCDCcoe y
    · simp only [hσdef, Function.update_of_ne hb]
  have hEq : (fun y : M => (S y) (Function.update (fun b : Fin s => Vslots b y) a
        (covDerivConnDiff (I := I) g₂ g₁
          (fun z => W z) (fun z => V z) (fun z => Vslots a z) y)))
      = (fun y : M => (S y) (fun b : Fin s => (σ b) y)) := by
    funext y
    rw [hσeval y]
  rw [hEq]
  have hS := (S.contMDiff x).of_le (le_refl (∞ : WithTop ℕ∞))
  have hEval := TensorMultilinear.contMDiffAt_section_apply_gen (I := I) (M := M) (n := s) (x₀ := x)
    (T := fun y : M => S y) hS (v := fun b : Fin s => fun y : M => (σ b) y)
    (hv := fun b => ((σ b).contMDiff.contMDiffAt))
  have hSAt : ContMDiffAt I 𝓘(ℝ, ℝ) (∞ : WithTop ℕ∞)
      (fun y : M => (S y) (fun b : Fin s => (σ b) y)) x := by
    simpa [Tensor0SBundle.Tensor0SSpace.toModel,
      Tensor0SBundle.tensor0SSpace_continuousLinearEquiv_apply] using hEval
  exact hSAt.mdifferentiableAt (by simp)

set_option backward.isDefEq.respectTransparency false in
open DifferentialGeometry.Integral.Connection in
/-- **Differentiability of the T2 summand** at `x`: the scalar field
`y ↦ (∇₂S) y (cons (W y)(update (Vslots·y) a (A_y(Vslots a,V))))` is `MDifferentiableAt` (the field
`∇₂S = covStep g₂ s S` and the `A`-insertion slot `diffSec` are smooth).  Feeds
`covStep2_diffStep_split`.  Same `respectTransparency false` remedy as `covStep2_branch1_mdiff`. -/
theorem covStep2_branch2_mdiff
    (g₁ g₂ : SmoothRiemannianMetric I M) (s : Nat)
    (S : Tensor0SBundle.Tensor0SField (𝕜 := ℝ) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) s)
    (U W V : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (Vslots : Fin s -> ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _))
    (a : Fin s) (x : M) :
    MDifferentiableAt I 𝓘(ℝ, ℝ)
      (fun y : M => covStep (I := I) g₂ s S y
        (Fin.cons (W y) (Function.update (fun b : Fin s => Vslots b y) a
          ((CovariantDerivative.difference
              (leviCivitaConnectionOfMetric (I := I) g₁)
              (leviCivitaConnectionOfMetric (I := I) g₂) y
              (Vslots a y)) (V y))))) x := by
  classical
  haveI : IsManifold I 1 M :=
    IsManifold.of_le (I := I) (M := M) (n := ∞) (by decide : (1 : WithTop ℕ∞) ≤ ∞)
  haveI : IsManifold I 2 M :=
    IsManifold.of_le (I := I) (M := M) (n := ∞) (by decide : (2 : WithTop ℕ∞) ≤ ∞)
  haveI : IsManifold I ((∞ : WithTop ℕ∞) + 1) M := by
    change IsManifold I ∞ M
    infer_instance
  haveI : IsManifold I (1 + 1) M :=
    IsManifold.of_le (I := I) (M := M) (n := ∞)
      (by decide : ((1 : WithTop ℕ∞) + 1) ≤ ∞)
  haveI : ContMDiffVectorBundle 1 E (TangentSpace I : M -> Type _) I :=
    TangentBundle.contMDiffVectorBundle (I := I) (M := M) (n := 1)
  haveI hcov₁ : CovariantDerivative.ContMDiffCovariantDerivative
      (leviCivitaConnectionOfMetric (I := I) g₁) (∞ : WithTop ℕ∞) :=
    leviCivitaConnectionOfMetric_contMDiffCovariantDerivative (I := I) g₁
  haveI hcov₂ : CovariantDerivative.ContMDiffCovariantDerivative
      (leviCivitaConnectionOfMetric (I := I) g₂) (∞ : WithTop ℕ∞) :=
    leviCivitaConnectionOfMetric_contMDiffCovariantDerivative (I := I) g₂
  set Asec : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _) :=
    ContMDiffSection.mk
      (diffSec (leviCivitaConnectionOfMetric (I := I) g₂)
        (leviCivitaConnectionOfMetric (I := I) g₁) (fun y : M => V y) (fun y : M => Vslots a y))
      (diffSec_contMDiff (leviCivitaConnectionOfMetric (I := I) g₂)
        (leviCivitaConnectionOfMetric (I := I) g₁) V.contMDiff
        (by simpa using (Vslots a).contMDiff)) with hAsecdef
  set ρ : Fin (s + 1) → ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _) :=
    Fin.cons W (Function.update Vslots a Asec) with hρdef
  have hAcoe : ∀ y : M, (Asec) y
      = (CovariantDerivative.difference
          (leviCivitaConnectionOfMetric (I := I) g₁)
          (leviCivitaConnectionOfMetric (I := I) g₂) y (Vslots a y)) (V y) := by
    intro y
    rw [hAsecdef]
    rfl
  have hρpt : ∀ y : M, (fun p : Fin (s + 1) => (ρ p) y)
      = Fin.cons (W y) (Function.update (fun b : Fin s => Vslots b y) a
          ((CovariantDerivative.difference
              (leviCivitaConnectionOfMetric (I := I) g₁)
              (leviCivitaConnectionOfMetric (I := I) g₂) y (Vslots a y)) (V y))) := by
    intro y
    funext p
    refine Fin.cases ?_ (fun i => ?_) p
    · simp only [hρdef, Fin.cons_zero]
    · rcases eq_or_ne i a with hi | hi
      · subst hi
        simp only [hρdef, Fin.cons_succ, Function.update_self]
        exact hAcoe y
      · simp only [hρdef, Fin.cons_succ, Function.update_of_ne hi]
  have hEq : (fun y : M => covStep (I := I) g₂ s S y
        (Fin.cons (W y) (Function.update (fun b : Fin s => Vslots b y) a
          ((CovariantDerivative.difference
              (leviCivitaConnectionOfMetric (I := I) g₁)
              (leviCivitaConnectionOfMetric (I := I) g₂) y
              (Vslots a y)) (V y)))))
      = (fun y : M => covStep (I := I) g₂ s S y (fun p : Fin (s + 1) => (ρ p) y)) := by
    funext y
    rw [hρpt y]
  rw [hEq]
  have hS := ((covStep (I := I) g₂ s S).contMDiff x).of_le (le_refl (∞ : WithTop ℕ∞))
  have hEval := TensorMultilinear.contMDiffAt_section_apply_gen (I := I) (M := M) (n := s + 1) (x₀ := x)
    (T := fun y : M => covStep (I := I) g₂ s S y) hS (v := fun p : Fin (s + 1) => fun y : M => (ρ p) y)
    (hv := fun p => ((ρ p).contMDiff.contMDiffAt))
  have hSAt : ContMDiffAt I 𝓘(ℝ, ℝ) (∞ : WithTop ℕ∞)
      (fun y : M => covStep (I := I) g₂ s S y (fun p : Fin (s + 1) => (ρ p) y)) x := by
    simpa [Tensor0SBundle.Tensor0SSpace.toModel,
      Tensor0SBundle.tensor0SSpace_continuousLinearEquiv_apply] using hEval
  exact hSAt.mdifferentiableAt (by simp)

open DifferentialGeometry.Integral.Connection in
/-- **The exterior-derivative linearity split of the peel's inner scalar field** (session-2 glue).
Splits `extDerivFun (−T1 − T2)` (the single `extDerivFun` kept by `covStep2_diffStep_peel`) into the
per-slot sums `−∑ₐ extDerivFun T1ₐ − ∑ₐ extDerivFun T2ₐ`, using `extDerivFun` additivity
(`extDerivFun_sub_at`, `extDerivFun_neg_at`, `extDerivFun_finset_sum_at`) with the summand
differentiability `covStep2_branch1_mdiff`/`covStep2_branch2_mdiff`.  Composing `covStep2_diffStep_peel`
with this and then `covStep2_diffStep_branch1`/`branch2` per slot expands `PieceA` up to the
`H`-correction sum. -/
theorem covStep2_diffStep_split
    (g₁ g₂ : SmoothRiemannianMetric I M) (s : Nat)
    (S : Tensor0SBundle.Tensor0SField (𝕜 := ℝ) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) s)
    (U W V : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (Vslots : Fin s -> ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _))
    (x : M) :
    extDerivFun (I := I)
        (fun y : M =>
          (-∑ a : Fin s, (S y) (Function.update (fun b : Fin s => Vslots b y) a
              (covDerivConnDiff (I := I) g₂ g₁
                (fun z => W z) (fun z => V z) (fun z => Vslots a z) y)))
          - ∑ a : Fin s, covStep (I := I) g₂ s S y
              (Fin.cons (W y) (Function.update (fun b : Fin s => Vslots b y) a
                ((CovariantDerivative.difference
                    (leviCivitaConnectionOfMetric (I := I) g₁)
                    (leviCivitaConnectionOfMetric (I := I) g₂) y
                    (Vslots a y)) (V y))))) x (U x)
      = (-∑ a : Fin s, extDerivFun (I := I)
            (fun y : M => (S y) (Function.update (fun b : Fin s => Vslots b y) a
              (covDerivConnDiff (I := I) g₂ g₁
                (fun z => W z) (fun z => V z) (fun z => Vslots a z) y))) x (U x))
        - ∑ a : Fin s, extDerivFun (I := I)
            (fun y : M => covStep (I := I) g₂ s S y
              (Fin.cons (W y) (Function.update (fun b : Fin s => Vslots b y) a
                ((CovariantDerivative.difference
                    (leviCivitaConnectionOfMetric (I := I) g₁)
                    (leviCivitaConnectionOfMetric (I := I) g₂) y
                    (Vslots a y)) (V y))))) x (U x) := by
  classical
  have hT1 : ∀ a : Fin s, MDifferentiableAt I 𝓘(ℝ, ℝ)
      (fun y : M => (S y) (Function.update (fun b : Fin s => Vslots b y) a
        (covDerivConnDiff (I := I) g₂ g₁
          (fun z => W z) (fun z => V z) (fun z => Vslots a z) y))) x :=
    fun a => covStep2_branch1_mdiff (I := I) g₁ g₂ s S U W V Vslots a x
  have hT2 : ∀ a : Fin s, MDifferentiableAt I 𝓘(ℝ, ℝ)
      (fun y : M => covStep (I := I) g₂ s S y
        (Fin.cons (W y) (Function.update (fun b : Fin s => Vslots b y) a
          ((CovariantDerivative.difference
              (leviCivitaConnectionOfMetric (I := I) g₁)
              (leviCivitaConnectionOfMetric (I := I) g₂) y
              (Vslots a y)) (V y))))) x :=
    fun a => covStep2_branch2_mdiff (I := I) g₁ g₂ s S U W V Vslots a x
  have hsum2 : (fun y : M => ∑ a : Fin s, covStep (I := I) g₂ s S y
        (Fin.cons (W y) (Function.update (fun b : Fin s => Vslots b y) a
          ((CovariantDerivative.difference
              (leviCivitaConnectionOfMetric (I := I) g₁)
              (leviCivitaConnectionOfMetric (I := I) g₂) y
              (Vslots a y)) (V y)))))
      = Finset.univ.sum (fun a : Fin s => fun y : M => covStep (I := I) g₂ s S y
          (Fin.cons (W y) (Function.update (fun b : Fin s => Vslots b y) a
            ((CovariantDerivative.difference
                (leviCivitaConnectionOfMetric (I := I) g₁)
                (leviCivitaConnectionOfMetric (I := I) g₂) y
                (Vslots a y)) (V y))))) := by
    funext y
    simp only [Finset.sum_apply]
  have hf1 : MDifferentiableAt I 𝓘(ℝ, ℝ)
      (fun y : M => ∑ a : Fin s, (S y) (Function.update (fun b : Fin s => Vslots b y) a
        (covDerivConnDiff (I := I) g₂ g₁
          (fun z => W z) (fun z => V z) (fun z => Vslots a z) y))) x := by
    rw [show (fun y : M => ∑ a : Fin s, (S y) (Function.update (fun b : Fin s => Vslots b y) a
          (covDerivConnDiff (I := I) g₂ g₁
            (fun z => W z) (fun z => V z) (fun z => Vslots a z) y)))
        = Finset.univ.sum (fun a : Fin s => fun y : M => (S y)
            (Function.update (fun b : Fin s => Vslots b y) a
              (covDerivConnDiff (I := I) g₂ g₁
                (fun z => W z) (fun z => V z) (fun z => Vslots a z) y))) from by
        funext y; simp only [Finset.sum_apply]]
    exact mdiffAt_finset_sum (I := I) Finset.univ _ (fun a _ => hT1 a)
  have hf2 : MDifferentiableAt I 𝓘(ℝ, ℝ)
      (fun y : M => ∑ a : Fin s, covStep (I := I) g₂ s S y
        (Fin.cons (W y) (Function.update (fun b : Fin s => Vslots b y) a
          ((CovariantDerivative.difference
              (leviCivitaConnectionOfMetric (I := I) g₁)
              (leviCivitaConnectionOfMetric (I := I) g₂) y
              (Vslots a y)) (V y))))) x := by
    rw [hsum2]
    exact mdiffAt_finset_sum (I := I) Finset.univ _ (fun a _ => hT2 a)
  have e1 : extDerivFun (I := I)
        (fun y : M => -∑ a : Fin s, (S y) (Function.update (fun b : Fin s => Vslots b y) a
          (covDerivConnDiff (I := I) g₂ g₁
            (fun z => W z) (fun z => V z) (fun z => Vslots a z) y))) x (U x)
      = -∑ a : Fin s, extDerivFun (I := I)
          (fun y : M => (S y) (Function.update (fun b : Fin s => Vslots b y) a
            (covDerivConnDiff (I := I) g₂ g₁
              (fun z => W z) (fun z => V z) (fun z => Vslots a z) y))) x (U x) := by
    have hneg : (fun y : M => -∑ a : Fin s, (S y) (Function.update (fun b : Fin s => Vslots b y) a
          (covDerivConnDiff (I := I) g₂ g₁
            (fun z => W z) (fun z => V z) (fun z => Vslots a z) y)))
        = (fun y : M => -(Finset.univ.sum (fun a : Fin s => fun y' : M => (S y')
            (Function.update (fun b : Fin s => Vslots b y') a
              (covDerivConnDiff (I := I) g₂ g₁
                (fun z => W z) (fun z => V z) (fun z => Vslots a z) y'))) y)) := by
      funext y
      simp only [Finset.sum_apply]
    rw [hneg,
      extDerivFun_neg_at (I := I) (U x)
        (mdiffAt_finset_sum (I := I) Finset.univ _ (fun a _ => hT1 a)),
      extDerivFun_finset_sum_at (I := I) Finset.univ _ (U x) (fun a _ => hT1 a)]
  have e2 : extDerivFun (I := I)
        (fun y : M => ∑ a : Fin s, covStep (I := I) g₂ s S y
          (Fin.cons (W y) (Function.update (fun b : Fin s => Vslots b y) a
            ((CovariantDerivative.difference
                (leviCivitaConnectionOfMetric (I := I) g₁)
                (leviCivitaConnectionOfMetric (I := I) g₂) y
                (Vslots a y)) (V y))))) x (U x)
      = ∑ a : Fin s, extDerivFun (I := I)
          (fun y : M => covStep (I := I) g₂ s S y
            (Fin.cons (W y) (Function.update (fun b : Fin s => Vslots b y) a
              ((CovariantDerivative.difference
                  (leviCivitaConnectionOfMetric (I := I) g₁)
                  (leviCivitaConnectionOfMetric (I := I) g₂) y
                  (Vslots a y)) (V y))))) x (U x) := by
    rw [hsum2, extDerivFun_finset_sum_at (I := I) Finset.univ _ (U x) (fun a _ => hT2 a)]
  have hsub : extDerivFun (I := I)
        (fun y : M =>
          (-∑ a : Fin s, (S y) (Function.update (fun b : Fin s => Vslots b y) a
              (covDerivConnDiff (I := I) g₂ g₁
                (fun z => W z) (fun z => V z) (fun z => Vslots a z) y)))
          - ∑ a : Fin s, covStep (I := I) g₂ s S y
              (Fin.cons (W y) (Function.update (fun b : Fin s => Vslots b y) a
                ((CovariantDerivative.difference
                    (leviCivitaConnectionOfMetric (I := I) g₁)
                    (leviCivitaConnectionOfMetric (I := I) g₂) y
                    (Vslots a y)) (V y))))) x (U x)
      = extDerivFun (I := I)
            (fun y : M => -∑ a : Fin s, (S y) (Function.update (fun b : Fin s => Vslots b y) a
              (covDerivConnDiff (I := I) g₂ g₁
                (fun z => W z) (fun z => V z) (fun z => Vslots a z) y))) x (U x)
        - extDerivFun (I := I)
            (fun y : M => ∑ a : Fin s, covStep (I := I) g₂ s S y
              (Fin.cons (W y) (Function.update (fun b : Fin s => Vslots b y) a
                ((CovariantDerivative.difference
                    (leviCivitaConnectionOfMetric (I := I) g₁)
                    (leviCivitaConnectionOfMetric (I := I) g₂) y
                    (Vslots a y)) (V y))))) x (U x) :=
    extDerivFun_sub_at (I := I) (U x) hf1.neg hf2
  rw [hsub, e1, e2]

open DifferentialGeometry.Integral.Connection in
/-- **The H-correction (OC) sum split** (session-4 core, correct-by-construction).  Splits the
`covStep2_diffStep_peel` connection-correction sum
`∑_{q:Fin(s+2)} H x (update (RR·x) q (∇₂_U(RR q)))` (`H = covStep g₂ (s+1)(diffStep S)`,
`RR = cons W (cons V Vslots)`) by `Fin.sum_univ_succ`×2 into the three `∇₂_U`-updated-tuple
`H`-applications, each in the `Fin.cons`-`Fin.cons` form that `diffStep_leibniz_eval` consumes:

* `q=0`: `∇₂_U W` in the derivative slot,
* `q=1`: `∇₂_U V` in the first covariant slot,
* `q=succ·succ a₀` (summed over `a₀`): `∇₂_U(Vslots a₀)` in the `a₀`-th covariant slot.

Value-level (no proof-local sections): each `∇₂_U ·` is the tangent value
`(∇₂ ·)(U x) = (leviCiv g₂ (fun z => · z) x) (U x)`.  Applying `diffStep_leibniz_eval` per term
(packaging `∇₂_U W`/`∇₂_U V`/`∇₂_U(Vslots a₀)` as `covApply` sections one level down) evaluates each
`H`-application into its two `diffStep`-Leibniz sums — the remaining step to the full OC eval. -/
theorem covStep2_diffStep_OCsplit
    (g₁ g₂ : SmoothRiemannianMetric I M) (s : Nat)
    (S : Tensor0SBundle.Tensor0SField (𝕜 := ℝ) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) s)
    (U W V : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (Vslots : Fin s -> ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _))
    (x : M) :
    (∑ q : Fin (s + 2),
        (covStep (I := I) g₂ (s + 1) (diffStep (I := I) g₁ g₂ s S)) x
          (Function.update
            (fun b : Fin (s + 2) =>
              (Fin.cons W (Fin.cons V Vslots) :
                Fin (s + 2) → ContMDiffSection I E (∞ : WithTop ℕ∞)
                  (TangentSpace I : M -> Type _)) b x) q
            ((leviCivitaConnectionOfMetric (I := I) g₂
                (fun y : M =>
                  (Fin.cons W (Fin.cons V Vslots) :
                    Fin (s + 2) → ContMDiffSection I E (∞ : WithTop ℕ∞)
                      (TangentSpace I : M -> Type _)) q y) x) (U x))))
      = (covStep (I := I) g₂ (s + 1) (diffStep (I := I) g₁ g₂ s S)) x
          (Fin.cons ((leviCivitaConnectionOfMetric (I := I) g₂ (fun z => W z) x) (U x))
            (Fin.cons (V x) (fun a : Fin s => Vslots a x)))
        + (covStep (I := I) g₂ (s + 1) (diffStep (I := I) g₁ g₂ s S)) x
            (Fin.cons (W x)
              (Fin.cons ((leviCivitaConnectionOfMetric (I := I) g₂ (fun z => V z) x) (U x))
                (fun a : Fin s => Vslots a x)))
        + ∑ a₀ : Fin s, (covStep (I := I) g₂ (s + 1) (diffStep (I := I) g₁ g₂ s S)) x
            (Fin.cons (W x)
              (Fin.cons (V x)
                (Function.update (fun b : Fin s => Vslots b x) a₀
                  ((leviCivitaConnectionOfMetric (I := I) g₂ (fun z => Vslots a₀ z) x) (U x))))) := by
  classical
  set RR : Fin (s + 2) → ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _) := Fin.cons W (Fin.cons V Vslots) with hRRdef
  have hRR0 : (fun y : M => (RR 0) y) = (fun y : M => W y) := by
    simp only [hRRdef, Fin.cons_zero]
  have hRR1 : (fun y : M => (RR (Fin.succ 0)) y) = (fun y : M => V y) := by
    simp only [hRRdef, Fin.cons_succ, Fin.cons_zero]
  have hRRss : ∀ a₀ : Fin s, (fun y : M => (RR (Fin.succ (Fin.succ a₀))) y)
      = (fun y : M => Vslots a₀ y) := by
    intro a₀
    simp only [hRRdef, Fin.cons_succ]
  have hRRptx : (fun b : Fin (s + 2) => (RR b) x)
      = Fin.cons (W x) (Fin.cons (V x) (fun a : Fin s => Vslots a x)) := by
    funext b
    refine Fin.cases ?_ (fun i => ?_) b
    · simp only [hRRdef, Fin.cons_zero]
    · refine Fin.cases ?_ (fun j => ?_) i <;> simp only [hRRdef, Fin.cons_succ, Fin.cons_zero]
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
  simp only [hRRptx, hRR0, hRR1, hRRss, Fin.update_cons_zero, ← Fin.cons_update]
  ring

open DifferentialGeometry.Integral.Connection in
/-- **The `q = 0` H-correction eval** (session-14).  `diffStep_leibniz_eval` applied to the first
`covStep2_diffStep_OCsplit` term: the derivative slot carries `∇₂_U W`, packaged as the `covApply`
section.  The `∇₂A`-insertion sum materialises `covDerivConnDiff` with first argument
`covApply (LeviCivita g₂) U W` — verbatim the second summand of `covStep2_diffStep_branch1`'s
diagonal, and the `A`-insertion sum is verbatim `covStep2_diffStep_branch2`'s `p = 0` term; both
cancel pairwise in the clean `covStep2_diffStep_eval` assembly. -/
theorem covStep2_OC_q0
    (g₁ g₂ : SmoothRiemannianMetric I M) (s : Nat)
    (S : Tensor0SBundle.Tensor0SField (𝕜 := ℝ) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) s)
    (U W V : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (Vslots : Fin s -> ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _))
    (x : M) :
    (covStep (I := I) g₂ (s + 1) (diffStep (I := I) g₁ g₂ s S)) x
        (Fin.cons ((leviCivitaConnectionOfMetric (I := I) g₂ (fun z => W z) x) (U x))
          (Fin.cons (V x) (fun a : Fin s => Vslots a x)))
      = (-∑ a : Fin s, (S x) (Function.update (fun b : Fin s => Vslots b x) a
            (covDerivConnDiff (I := I) g₂ g₁
              (covApply (LeviCivita (I := I) g₂) (fun z => U z) (fun z => W z))
              (fun z => V z) (fun z => Vslots a z) x)))
        - ∑ a : Fin s, covStep (I := I) g₂ s S x
            (Fin.cons ((leviCivitaConnectionOfMetric (I := I) g₂ (fun z => W z) x) (U x))
              (Function.update (fun b : Fin s => Vslots b x) a
                ((CovariantDerivative.difference
                    (leviCivitaConnectionOfMetric (I := I) g₁)
                    (leviCivitaConnectionOfMetric (I := I) g₂) x
                    (Vslots a x)) (V x)))) := by
  classical
  haveI : IsManifold I 1 M :=
    IsManifold.of_le (I := I) (M := M) (n := ∞) (by decide : (1 : WithTop ℕ∞) ≤ ∞)
  haveI : IsManifold I 2 M :=
    IsManifold.of_le (I := I) (M := M) (n := ∞) (by decide : (2 : WithTop ℕ∞) ≤ ∞)
  haveI : IsManifold I ((∞ : WithTop ℕ∞) + 1) M := by
    change IsManifold I ∞ M
    infer_instance
  haveI : IsManifold I (1 + 1) M :=
    IsManifold.of_le (I := I) (M := M) (n := ∞)
      (by decide : ((1 : WithTop ℕ∞) + 1) ≤ ∞)
  haveI : ContMDiffVectorBundle 1 E (TangentSpace I : M -> Type _) I :=
    TangentBundle.contMDiffVectorBundle (I := I) (M := M) (n := 1)
  haveI hcov₂ : CovariantDerivative.ContMDiffCovariantDerivative
      (LeviCivita (I := I) g₂) (∞ : WithTop ℕ∞) :=
    leviCivitaConnectionOfMetric_contMDiffCovariantDerivative (I := I) g₂
  have hcast : ∀ (P : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _)),
      ContMDiff I (I.prod 𝓘(ℝ, E)) ((∞ : WithTop ℕ∞) + 1) (T% (fun b => P b)) := by
    intro P
    rw [show ((∞ : WithTop ℕ∞) + 1) = (∞ : WithTop ℕ∞) from by rw [ENat.coe_top_add_one]]
    exact P.contMDiff
  set NW : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _) :=
    ContMDiffSection.mk
      (covApply (LeviCivita (I := I) g₂) (fun z => U z) (fun z => W z))
      (contMDiffOn_univ.mp
        (covApply_contMDiffOn (cov := LeviCivita (I := I) g₂) U.contMDiff (hcast W))) with hNWdef
  have hNWfun : (fun y : M => NW y)
      = covApply (LeviCivita (I := I) g₂) (fun z => U z) (fun z => W z) := by
    rw [hNWdef]
    rfl
  have hNWx : NW x = (leviCivitaConnectionOfMetric (I := I) g₂ (fun z => W z) x) (U x) := by
    rw [hNWdef]
    rfl
  have key := diffStep_leibniz_eval (I := I) g₁ g₂ s S NW V Vslots x
  rw [hNWfun, hNWx] at key
  exact key

open DifferentialGeometry.Integral.Connection in
/-- **The `q = 1` H-correction eval** (session-14).  `diffStep_leibniz_eval` applied to the second
`covStep2_diffStep_OCsplit` term: the first covariant slot carries `∇₂_U V`, packaged as the
`covApply` section.  The `∇₂A`-insertion sum materialises `covDerivConnDiff` with second argument
`covApply (LeviCivita g₂) U V` — verbatim the third summand of `covStep2_diffStep_branch1`'s
diagonal, and the `A`-insertion sum is verbatim `covStep2_diffStep_branch2`'s diagonal
`A(Vslots a, ∇₂_U V)` piece; both cancel pairwise in the clean assembly. -/
theorem covStep2_OC_q1
    (g₁ g₂ : SmoothRiemannianMetric I M) (s : Nat)
    (S : Tensor0SBundle.Tensor0SField (𝕜 := ℝ) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) s)
    (U W V : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (Vslots : Fin s -> ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _))
    (x : M) :
    (covStep (I := I) g₂ (s + 1) (diffStep (I := I) g₁ g₂ s S)) x
        (Fin.cons (W x)
          (Fin.cons ((leviCivitaConnectionOfMetric (I := I) g₂ (fun z => V z) x) (U x))
            (fun a : Fin s => Vslots a x)))
      = (-∑ a : Fin s, (S x) (Function.update (fun b : Fin s => Vslots b x) a
            (covDerivConnDiff (I := I) g₂ g₁ (fun z => W z)
              (covApply (LeviCivita (I := I) g₂) (fun z => U z) (fun z => V z))
              (fun z => Vslots a z) x)))
        - ∑ a : Fin s, covStep (I := I) g₂ s S x
            (Fin.cons (W x)
              (Function.update (fun b : Fin s => Vslots b x) a
                ((CovariantDerivative.difference
                    (leviCivitaConnectionOfMetric (I := I) g₁)
                    (leviCivitaConnectionOfMetric (I := I) g₂) x
                    (Vslots a x))
                  ((leviCivitaConnectionOfMetric (I := I) g₂ (fun z => V z) x) (U x))))) := by
  classical
  haveI : IsManifold I 1 M :=
    IsManifold.of_le (I := I) (M := M) (n := ∞) (by decide : (1 : WithTop ℕ∞) ≤ ∞)
  haveI : IsManifold I 2 M :=
    IsManifold.of_le (I := I) (M := M) (n := ∞) (by decide : (2 : WithTop ℕ∞) ≤ ∞)
  haveI : IsManifold I ((∞ : WithTop ℕ∞) + 1) M := by
    change IsManifold I ∞ M
    infer_instance
  haveI : IsManifold I (1 + 1) M :=
    IsManifold.of_le (I := I) (M := M) (n := ∞)
      (by decide : ((1 : WithTop ℕ∞) + 1) ≤ ∞)
  haveI : ContMDiffVectorBundle 1 E (TangentSpace I : M -> Type _) I :=
    TangentBundle.contMDiffVectorBundle (I := I) (M := M) (n := 1)
  haveI hcov₂ : CovariantDerivative.ContMDiffCovariantDerivative
      (LeviCivita (I := I) g₂) (∞ : WithTop ℕ∞) :=
    leviCivitaConnectionOfMetric_contMDiffCovariantDerivative (I := I) g₂
  have hcast : ∀ (P : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _)),
      ContMDiff I (I.prod 𝓘(ℝ, E)) ((∞ : WithTop ℕ∞) + 1) (T% (fun b => P b)) := by
    intro P
    rw [show ((∞ : WithTop ℕ∞) + 1) = (∞ : WithTop ℕ∞) from by rw [ENat.coe_top_add_one]]
    exact P.contMDiff
  set NV : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _) :=
    ContMDiffSection.mk
      (covApply (LeviCivita (I := I) g₂) (fun z => U z) (fun z => V z))
      (contMDiffOn_univ.mp
        (covApply_contMDiffOn (cov := LeviCivita (I := I) g₂) U.contMDiff (hcast V))) with hNVdef
  have hNVfun : (fun y : M => NV y)
      = covApply (LeviCivita (I := I) g₂) (fun z => U z) (fun z => V z) := by
    rw [hNVdef]
    rfl
  have hNVx : NV x = (leviCivitaConnectionOfMetric (I := I) g₂ (fun z => V z) x) (U x) := by
    rw [hNVdef]
    rfl
  have key := diffStep_leibniz_eval (I := I) g₁ g₂ s S W NV Vslots x
  rw [hNVfun, hNVx] at key
  exact key

open DifferentialGeometry.Integral.Connection in
/-- **The interior (`q = a₀.succ.succ`) H-correction eval** (session-14).  `diffStep_leibniz_eval`
applied to an interior `covStep2_diffStep_OCsplit` term: the `a₀`-th covariant slot carries
`∇₂_U (Vslots a₀)` (packaged as the `covApply` section), inserted through the section-level
`Function.update Vslots a₀`.  The output sums are split into the diagonal `a = a₀` term (where the
`covApply` section survives inside `covDerivConnDiff` / the connection difference — verbatim the
fourth summand of `covStep2_diffStep_branch1`'s diagonal resp. `covStep2_diffStep_branch2`'s
`A(∇₂_U(Vslots a₀), V)` piece) and the off-diagonal `a ≠ a₀` sums (verbatim the branch off-diagonal
sums after the `Function.update_comm`/`Finset.sum_comm'` pair swap). -/
theorem covStep2_OC_int
    (g₁ g₂ : SmoothRiemannianMetric I M) (s : Nat)
    (S : Tensor0SBundle.Tensor0SField (𝕜 := ℝ) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) s)
    (U W V : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (Vslots : Fin s -> ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _))
    (a₀ : Fin s) (x : M) :
    (covStep (I := I) g₂ (s + 1) (diffStep (I := I) g₁ g₂ s S)) x
        (Fin.cons (W x)
          (Fin.cons (V x)
            (Function.update (fun b : Fin s => Vslots b x) a₀
              ((leviCivitaConnectionOfMetric (I := I) g₂ (fun z => Vslots a₀ z) x) (U x)))))
      = (-((S x) (Function.update (fun b : Fin s => Vslots b x) a₀
              (covDerivConnDiff (I := I) g₂ g₁ (fun z => W z) (fun z => V z)
                (covApply (LeviCivita (I := I) g₂) (fun z => U z) (fun z => Vslots a₀ z)) x))
            + ∑ a ∈ Finset.univ.erase a₀, (S x) (Function.update
                (Function.update (fun c : Fin s => Vslots c x) a₀
                  ((leviCivitaConnectionOfMetric (I := I) g₂ (fun z => Vslots a₀ z) x) (U x))) a
                (covDerivConnDiff (I := I) g₂ g₁
                  (fun z => W z) (fun z => V z) (fun z => Vslots a z) x))))
        - (covStep (I := I) g₂ s S x
              (Fin.cons (W x) (Function.update (fun b : Fin s => Vslots b x) a₀
                ((CovariantDerivative.difference
                    (leviCivitaConnectionOfMetric (I := I) g₁)
                    (leviCivitaConnectionOfMetric (I := I) g₂) x
                    ((leviCivitaConnectionOfMetric (I := I) g₂ (fun z => Vslots a₀ z) x) (U x)))
                  (V x))))
            + ∑ a ∈ Finset.univ.erase a₀, covStep (I := I) g₂ s S x
                (Fin.cons (W x) (Function.update
                  (Function.update (fun c : Fin s => Vslots c x) a₀
                    ((leviCivitaConnectionOfMetric (I := I) g₂ (fun z => Vslots a₀ z) x) (U x))) a
                  ((CovariantDerivative.difference
                      (leviCivitaConnectionOfMetric (I := I) g₁)
                      (leviCivitaConnectionOfMetric (I := I) g₂) x
                      (Vslots a x)) (V x))))) := by
  classical
  haveI : IsManifold I 1 M :=
    IsManifold.of_le (I := I) (M := M) (n := ∞) (by decide : (1 : WithTop ℕ∞) ≤ ∞)
  haveI : IsManifold I 2 M :=
    IsManifold.of_le (I := I) (M := M) (n := ∞) (by decide : (2 : WithTop ℕ∞) ≤ ∞)
  haveI : IsManifold I ((∞ : WithTop ℕ∞) + 1) M := by
    change IsManifold I ∞ M
    infer_instance
  haveI : IsManifold I (1 + 1) M :=
    IsManifold.of_le (I := I) (M := M) (n := ∞)
      (by decide : ((1 : WithTop ℕ∞) + 1) ≤ ∞)
  haveI : ContMDiffVectorBundle 1 E (TangentSpace I : M -> Type _) I :=
    TangentBundle.contMDiffVectorBundle (I := I) (M := M) (n := 1)
  haveI hcov₂ : CovariantDerivative.ContMDiffCovariantDerivative
      (LeviCivita (I := I) g₂) (∞ : WithTop ℕ∞) :=
    leviCivitaConnectionOfMetric_contMDiffCovariantDerivative (I := I) g₂
  have hcast : ∀ (P : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _)),
      ContMDiff I (I.prod 𝓘(ℝ, E)) ((∞ : WithTop ℕ∞) + 1) (T% (fun b => P b)) := by
    intro P
    rw [show ((∞ : WithTop ℕ∞) + 1) = (∞ : WithTop ℕ∞) from by rw [ENat.coe_top_add_one]]
    exact P.contMDiff
  set NS : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _) :=
    ContMDiffSection.mk
      (covApply (LeviCivita (I := I) g₂) (fun z => U z) (fun z => Vslots a₀ z))
      (contMDiffOn_univ.mp
        (covApply_contMDiffOn (cov := LeviCivita (I := I) g₂) U.contMDiff
          (hcast (Vslots a₀)))) with hNSdef
  set σ : Fin s → ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _) :=
    Function.update Vslots a₀ NS with hσdef
  have hNSx : NS x
      = (leviCivitaConnectionOfMetric (I := I) g₂ (fun z => Vslots a₀ z) x) (U x) := by
    rw [hNSdef]
    rfl
  have hσx : (fun b : Fin s => σ b x)
      = Function.update (fun b : Fin s => Vslots b x) a₀
          ((leviCivitaConnectionOfMetric (I := I) g₂ (fun z => Vslots a₀ z) x) (U x)) := by
    funext b
    rcases eq_or_ne b a₀ with hb | hb
    · subst hb
      simp only [hσdef, Function.update_self]
      exact hNSx
    · simp only [hσdef, Function.update_of_ne hb]
  have hσa₀ : (fun y : M => σ a₀ y)
      = covApply (LeviCivita (I := I) g₂) (fun z => U z) (fun z => Vslots a₀ z) := by
    funext y
    simp only [hσdef, Function.update_self]
    rw [hNSdef]
    rfl
  have hσa₀x : σ a₀ x
      = (leviCivitaConnectionOfMetric (I := I) g₂ (fun z => Vslots a₀ z) x) (U x) := by
    simp only [hσdef, Function.update_self]
    exact hNSx
  have key := diffStep_leibniz_eval (I := I) g₁ g₂ s S W V σ x
  rw [hσx] at key
  rw [key]
  have hs1 : (∑ a : Fin s, (S x) (Function.update
        (Function.update (fun b : Fin s => Vslots b x) a₀
          ((leviCivitaConnectionOfMetric (I := I) g₂ (fun z => Vslots a₀ z) x) (U x))) a
        (covDerivConnDiff (I := I) g₂ g₁
          (fun y => W y) (fun y => V y) (fun y => σ a y) x)))
      = (S x) (Function.update (fun b : Fin s => Vslots b x) a₀
            (covDerivConnDiff (I := I) g₂ g₁ (fun z => W z) (fun z => V z)
              (covApply (LeviCivita (I := I) g₂) (fun z => U z) (fun z => Vslots a₀ z)) x))
        + ∑ a ∈ Finset.univ.erase a₀, (S x) (Function.update
            (Function.update (fun c : Fin s => Vslots c x) a₀
              ((leviCivitaConnectionOfMetric (I := I) g₂ (fun z => Vslots a₀ z) x) (U x))) a
            (covDerivConnDiff (I := I) g₂ g₁
              (fun z => W z) (fun z => V z) (fun z => Vslots a z) x)) := by
    rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ a₀), hσa₀,
      Function.update_idem]
    refine congrArg _ (Finset.sum_congr rfl (fun a ha => ?_))
    rw [show (fun y : M => σ a y) = (fun y : M => Vslots a y) from by
      funext y
      simp only [hσdef, Function.update_of_ne (Finset.ne_of_mem_erase ha)]]
  have hs2 : (∑ a : Fin s, covStep (I := I) g₂ s S x
        (Fin.cons (W x) (Function.update
          (Function.update (fun b : Fin s => Vslots b x) a₀
            ((leviCivitaConnectionOfMetric (I := I) g₂ (fun z => Vslots a₀ z) x) (U x))) a
          ((CovariantDerivative.difference
              (leviCivitaConnectionOfMetric (I := I) g₁)
              (leviCivitaConnectionOfMetric (I := I) g₂) x
              (σ a x)) (V x)))))
      = covStep (I := I) g₂ s S x
            (Fin.cons (W x) (Function.update (fun b : Fin s => Vslots b x) a₀
              ((CovariantDerivative.difference
                  (leviCivitaConnectionOfMetric (I := I) g₁)
                  (leviCivitaConnectionOfMetric (I := I) g₂) x
                  ((leviCivitaConnectionOfMetric (I := I) g₂ (fun z => Vslots a₀ z) x) (U x)))
                (V x))))
        + ∑ a ∈ Finset.univ.erase a₀, covStep (I := I) g₂ s S x
            (Fin.cons (W x) (Function.update
              (Function.update (fun c : Fin s => Vslots c x) a₀
                ((leviCivitaConnectionOfMetric (I := I) g₂ (fun z => Vslots a₀ z) x) (U x))) a
              ((CovariantDerivative.difference
                  (leviCivitaConnectionOfMetric (I := I) g₁)
                  (leviCivitaConnectionOfMetric (I := I) g₂) x
                  (Vslots a x)) (V x)))) := by
    rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ a₀), hσa₀x,
      Function.update_idem]
    refine congrArg _ (Finset.sum_congr rfl (fun a ha => ?_))
    rw [show σ a x = Vslots a x from by
      simp only [hσdef, Function.update_of_ne (Finset.ne_of_mem_erase ha)]]
  rw [hs1, hs2]

open DifferentialGeometry.Integral.Connection in
/-- **The PieceB eval** (session-14): `diffStep_leibniz_eval` at rank `s + 1` on the field `∇₂S`,
with derivative direction `U` and connection-difference direction `W`.  This is the second half of
`covStep2_mixedComm_eval_sub`: the `∇₂A`-insertion sum inserts `covDerivConnDiff g₂ g₁ U W ·` into
each of the `s + 1` slots of `∇₂S`, and the `A`-insertion sum — the **retained** `A ⋆ ∇₂²S` family
(coordinator ruling №33; no cancellation) — inserts the connection difference into each slot of
`∇₂²S`, to be bounded by the a=0 atom times `|∇₂²S|`. -/
theorem covStep2_pieceB_eval
    (g₁ g₂ : SmoothRiemannianMetric I M) (s : Nat)
    (S : Tensor0SBundle.Tensor0SField (𝕜 := ℝ) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) s)
    (U W V : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (Vslots : Fin s -> ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _))
    (x : M) :
    covStep (I := I) g₂ (s + 2)
        (diffStep (I := I) g₁ g₂ (s + 1) (covStep (I := I) g₂ s S)) x
        (Fin.cons (U x) (Fin.cons (W x) (Fin.cons (V x) (fun a : Fin s => Vslots a x))))
      = (-∑ j : Fin (s + 1), (covStep (I := I) g₂ s S x)
            (Function.update (Fin.cons (V x) (fun b : Fin s => Vslots b x)) j
              (covDerivConnDiff (I := I) g₂ g₁ (fun z => U z) (fun z => W z)
                (fun z => (Fin.cons V Vslots :
                  Fin (s + 1) → ContMDiffSection I E (∞ : WithTop ℕ∞)
                    (TangentSpace I : M -> Type _)) j z) x)))
        - ∑ j : Fin (s + 1), covStep (I := I) g₂ (s + 1) (covStep (I := I) g₂ s S) x
            (Fin.cons (U x)
              (Function.update (Fin.cons (V x) (fun b : Fin s => Vslots b x)) j
                ((CovariantDerivative.difference
                    (leviCivitaConnectionOfMetric (I := I) g₁)
                    (leviCivitaConnectionOfMetric (I := I) g₂) x
                    ((Fin.cons V Vslots :
                      Fin (s + 1) → ContMDiffSection I E (∞ : WithTop ℕ∞)
                        (TangentSpace I : M -> Type _)) j x)) (W x)))) := by
  classical
  set VV : Fin (s + 1) → ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _) := Fin.cons V Vslots with hVVdef
  have hVVx : (fun b : Fin (s + 1) => VV b x)
      = Fin.cons (V x) (fun b : Fin s => Vslots b x) := by
    funext b
    refine Fin.cases ?_ (fun i => ?_) b
    · simp only [hVVdef, Fin.cons_zero]
    · simp only [hVVdef, Fin.cons_succ]
  have key := diffStep_leibniz_eval (I := I) g₁ g₂ (s + 1)
    (covStep (I := I) g₂ s S) U W VV x
  rw [hVVx] at key
  exact key

set_option maxHeartbeats 800000 in
open DifferentialGeometry.Integral.Connection in
/-- **The clean full eval of `PieceA = ∇₂²(A ⋆ S)`** (session-14; the reusable a=2 core named by the
session-7 recon).  Composing `covStep2_diffStep_peel ▸ split ▸ branch1/branch2 ▸ OCsplit ▸ OC per-term`
and cancelling every `∇₂`-of-section correction (the `q=0`/`q=1`/diagonal corrections pairwise against
the branch diagonals, the off-diagonal double sums via `Finset.sum_comm'` + `Function.update_comm`)
leaves the value-honest a=2 Leibniz expansion — four families:

* the **`∇₂²A ⋆ S`** family: `covDerivConnDiff2 (U, W; V, Vslots a)` inserted into each slot of `S`;
* two **`∇₂A ⋆ ∇₂S`** families: `covDerivConnDiff (W; V, Vslots a)` into `∇₂S` with leading `U`, and
  `covDerivConnDiff (U; V, Vslots a)` into `∇₂S` with leading `W`;
* the **`A ⋆ ∇₂²S`** family (retained per ruling №33): the connection difference `A(Vslots a, V)`
  inserted into each original slot of `∇₂²S` with leading `U, W`.

Every right-hand vector is tensorial (value-level), so the identity feeds the per-slot Cauchy–Schwarz
of `covStepDiff2_mixedComm_le` directly. -/
theorem covStep2_diffStep_eval
    (g₁ g₂ : SmoothRiemannianMetric I M) (s : Nat)
    (S : Tensor0SBundle.Tensor0SField (𝕜 := ℝ) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) s)
    (U W V : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (Vslots : Fin s -> ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _))
    (x : M) :
    covStep (I := I) g₂ (s + 2)
        (covStep (I := I) g₂ (s + 1) (diffStep (I := I) g₁ g₂ s S)) x
        (Fin.cons (U x) (Fin.cons (W x) (Fin.cons (V x) (fun a : Fin s => Vslots a x))))
      = (-∑ a : Fin s, (S x) (Function.update (fun b : Fin s => Vslots b x) a
            (covDerivConnDiff2 (I := I) g₂ g₁
              (fun z => U z) (fun z => W z) (fun z => V z) (fun z => Vslots a z) x)))
        - ∑ a : Fin s, covStep (I := I) g₂ s S x
            (Fin.cons (U x) (Function.update (fun b : Fin s => Vslots b x) a
              (covDerivConnDiff (I := I) g₂ g₁
                (fun z => W z) (fun z => V z) (fun z => Vslots a z) x)))
        - ∑ a : Fin s, covStep (I := I) g₂ s S x
            (Fin.cons (W x) (Function.update (fun b : Fin s => Vslots b x) a
              (covDerivConnDiff (I := I) g₂ g₁
                (fun z => U z) (fun z => V z) (fun z => Vslots a z) x)))
        - ∑ a : Fin s, covStep (I := I) g₂ (s + 1) (covStep (I := I) g₂ s S) x
            (Fin.cons (U x) (Fin.cons (W x) (Function.update (fun b : Fin s => Vslots b x) a
              ((CovariantDerivative.difference
                  (leviCivitaConnectionOfMetric (I := I) g₁)
                  (leviCivitaConnectionOfMetric (I := I) g₂) x
                  (Vslots a x)) (V x))))) := by
  classical
  -- Slot-additivity split of the branch1 diagonal (`cdc2 + three corrections`).
  have hsplitS : (∑ a : Fin s, (S x) (Function.update (fun b : Fin s => Vslots b x) a
        (covDerivConnDiff2 (I := I) g₂ g₁
            (fun z => U z) (fun z => W z) (fun z => V z) (fun z => Vslots a z) x
          + covDerivConnDiff (I := I) g₂ g₁
              (covApply (LeviCivita (I := I) g₂) (fun z => U z) (fun z => W z))
              (fun z => V z) (fun z => Vslots a z) x
          + covDerivConnDiff (I := I) g₂ g₁ (fun z => W z)
              (covApply (LeviCivita (I := I) g₂) (fun z => U z) (fun z => V z))
              (fun z => Vslots a z) x
          + covDerivConnDiff (I := I) g₂ g₁ (fun z => W z) (fun z => V z)
              (covApply (LeviCivita (I := I) g₂) (fun z => U z) (fun z => Vslots a z)) x)))
      = (∑ a : Fin s, (S x) (Function.update (fun b : Fin s => Vslots b x) a
            (covDerivConnDiff2 (I := I) g₂ g₁
              (fun z => U z) (fun z => W z) (fun z => V z) (fun z => Vslots a z) x)))
        + (∑ a : Fin s, (S x) (Function.update (fun b : Fin s => Vslots b x) a
            (covDerivConnDiff (I := I) g₂ g₁
              (covApply (LeviCivita (I := I) g₂) (fun z => U z) (fun z => W z))
              (fun z => V z) (fun z => Vslots a z) x)))
        + (∑ a : Fin s, (S x) (Function.update (fun b : Fin s => Vslots b x) a
            (covDerivConnDiff (I := I) g₂ g₁ (fun z => W z)
              (covApply (LeviCivita (I := I) g₂) (fun z => U z) (fun z => V z))
              (fun z => Vslots a z) x)))
        + (∑ a : Fin s, (S x) (Function.update (fun b : Fin s => Vslots b x) a
            (covDerivConnDiff (I := I) g₂ g₁ (fun z => W z) (fun z => V z)
              (covApply (LeviCivita (I := I) g₂) (fun z => U z) (fun z => Vslots a z)) x))) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [Tensor0SBundle.Tensor0SSpace.map_update_add,
      Tensor0SBundle.Tensor0SSpace.map_update_add,
      Tensor0SBundle.Tensor0SSpace.map_update_add]
  -- Slot-additivity split of the branch2 diagonal (`cdc(U,V,·) + two A-corrections`).
  have hsplitD : (∑ a : Fin s, covStep (I := I) g₂ s S x
        (Fin.cons (W x) (Function.update (fun b : Fin s => Vslots b x) a
          (covDerivConnDiff (I := I) g₂ g₁
              (fun z => U z) (fun z => V z) (fun z => Vslots a z) x
            + (CovariantDerivative.difference
                (leviCivitaConnectionOfMetric (I := I) g₁)
                (leviCivitaConnectionOfMetric (I := I) g₂) x (Vslots a x))
                ((leviCivitaConnectionOfMetric (I := I) g₂ (fun y : M => V y) x) (U x))
            + (CovariantDerivative.difference
                (leviCivitaConnectionOfMetric (I := I) g₁)
                (leviCivitaConnectionOfMetric (I := I) g₂) x
                ((leviCivitaConnectionOfMetric (I := I) g₂ (fun y : M => Vslots a y) x) (U x)))
                (V x)))))
      = (∑ a : Fin s, covStep (I := I) g₂ s S x
            (Fin.cons (W x) (Function.update (fun b : Fin s => Vslots b x) a
              (covDerivConnDiff (I := I) g₂ g₁
                (fun z => U z) (fun z => V z) (fun z => Vslots a z) x))))
        + (∑ a : Fin s, covStep (I := I) g₂ s S x
            (Fin.cons (W x) (Function.update (fun b : Fin s => Vslots b x) a
              ((CovariantDerivative.difference
                  (leviCivitaConnectionOfMetric (I := I) g₁)
                  (leviCivitaConnectionOfMetric (I := I) g₂) x (Vslots a x))
                ((leviCivitaConnectionOfMetric (I := I) g₂ (fun y : M => V y) x) (U x))))))
        + (∑ a : Fin s, covStep (I := I) g₂ s S x
            (Fin.cons (W x) (Function.update (fun b : Fin s => Vslots b x) a
              ((CovariantDerivative.difference
                  (leviCivitaConnectionOfMetric (I := I) g₁)
                  (leviCivitaConnectionOfMetric (I := I) g₂) x
                  ((leviCivitaConnectionOfMetric (I := I) g₂ (fun y : M => Vslots a y) x) (U x)))
                (V x))))) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [Fin.cons_update, Tensor0SBundle.Tensor0SSpace.map_update_add,
      Tensor0SBundle.Tensor0SSpace.map_update_add]
    simp only [← Fin.cons_update]
  -- Pair swap: the interior `∇₂_U`-correction double sum equals the branch1 off-diagonal double sum.
  have hFub1 : (∑ a₀ : Fin s, ∑ a ∈ Finset.univ.erase a₀, (S x) (Function.update
        (Function.update (fun c : Fin s => Vslots c x) a₀
          ((leviCivitaConnectionOfMetric (I := I) g₂ (fun z => Vslots a₀ z) x) (U x))) a
        (covDerivConnDiff (I := I) g₂ g₁
          (fun z => W z) (fun z => V z) (fun z => Vslots a z) x)))
      = ∑ a : Fin s, ∑ b ∈ Finset.univ.erase a, (S x) (Function.update
          (Function.update (fun c : Fin s => Vslots c x) a
            (covDerivConnDiff (I := I) g₂ g₁
              (fun z => W z) (fun z => V z) (fun z => Vslots a z) x)) b
          ((leviCivitaConnectionOfMetric (I := I) g₂ (fun y : M => Vslots b y) x) (U x))) := by
    rw [Finset.sum_comm' (s := Finset.univ) (t := fun a₀ : Fin s => Finset.univ.erase a₀)
      (t' := Finset.univ) (s' := fun a : Fin s => Finset.univ.erase a)
      (h := fun p q => by
        simp only [Finset.mem_univ, Finset.mem_erase, true_and, and_true]
        exact ⟨Ne.symm, Ne.symm⟩)]
    refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun a₀ ha₀ => ?_))
    rw [Function.update_comm (Finset.ne_of_mem_erase ha₀)]
  -- Pair swap: the interior `A`-correction double sum equals the branch2 off-diagonal double sum.
  have hFub2 : (∑ a₀ : Fin s, ∑ a ∈ Finset.univ.erase a₀, covStep (I := I) g₂ s S x
        (Fin.cons (W x) (Function.update
          (Function.update (fun c : Fin s => Vslots c x) a₀
            ((leviCivitaConnectionOfMetric (I := I) g₂ (fun z => Vslots a₀ z) x) (U x))) a
          ((CovariantDerivative.difference
              (leviCivitaConnectionOfMetric (I := I) g₁)
              (leviCivitaConnectionOfMetric (I := I) g₂) x
              (Vslots a x)) (V x)))))
      = ∑ a : Fin s, ∑ b ∈ Finset.univ.erase a, covStep (I := I) g₂ s S x
          (Fin.cons (W x) (Function.update
            (Function.update (fun c : Fin s => Vslots c x) a
              ((CovariantDerivative.difference
                  (leviCivitaConnectionOfMetric (I := I) g₁)
                  (leviCivitaConnectionOfMetric (I := I) g₂) x
                  (Vslots a x)) (V x))) b
            ((leviCivitaConnectionOfMetric (I := I) g₂ (fun y : M => Vslots b y) x) (U x)))) := by
    rw [Finset.sum_comm' (s := Finset.univ) (t := fun a₀ : Fin s => Finset.univ.erase a₀)
      (t' := Finset.univ) (s' := fun a : Fin s => Finset.univ.erase a)
      (h := fun p q => by
        simp only [Finset.mem_univ, Finset.mem_erase, true_and, and_true]
        exact ⟨Ne.symm, Ne.symm⟩)]
    refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun a₀ ha₀ => ?_))
    rw [Function.update_comm (Finset.ne_of_mem_erase ha₀)]
  -- Expansion chain: peel, linearity split, OC split, and the five per-term evals.
  rw [covStep2_diffStep_peel (I := I) g₁ g₂ s S U W V Vslots x,
    covStep2_diffStep_split (I := I) g₁ g₂ s S U W V Vslots x,
    covStep2_diffStep_OCsplit (I := I) g₁ g₂ s S U W V Vslots x,
    covStep2_OC_q0 (I := I) g₁ g₂ s S U W V Vslots x,
    covStep2_OC_q1 (I := I) g₁ g₂ s S U W V Vslots x]
  simp only [covStep2_OC_int (I := I) g₁ g₂ s S U W V Vslots,
    covStep2_diffStep_branch1 (I := I) g₁ g₂ s S U W V Vslots,
    covStep2_diffStep_branch2 (I := I) g₁ g₂ s S U W V Vslots]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_neg_distrib]
  rw [hsplitS, hsplitD, hFub1, hFub2]
  abel

open DifferentialGeometry.Integral.Connection in
/-- **Rank-`0` vanishing of the single connection-difference step** (session-12 witness).  For a
scalar (rank-`0`) field `S`, the connection-difference step `A ⋆ S = diffStep g₁ g₂ 0 S` is identically
zero: `diffStep_eval` inserts the derivative direction into the *empty* tuple of covariant slots, an
empty sum.  This is the base case exposing that `∇₂(mixedComm S)` is genuinely order-`2` in `S`: at
`s = 0`, `∇₂²(A⋆S) = 0`, so the committed operator split `∇₂²(A⋆S) = ∇₂(A⋆∇₂S) + ∇₂(mixedComm S)`
(`covStepDiff2_exists_const.hop`) forces `∇₂(mixedComm S) = −∇₂(A⋆∇₂S)`, whose fibre norm is the
committed a=1 atom `covStepDiff_of_jets` applied at level `1` to `∇₂S` — bounded by `|∇₂S| + |∇₂²S|`,
*genuinely involving* the second jet `|∇₂²S|`.  Hence any bound on `∇₂(mixedComm S)` that omits
`|∇₂²S|` from its right-hand side (as `covStepDiff2_mixedComm_le` currently does) is false; the `∇₂²S`
terms of `∇₂(mixedComm S)` do **not** cancel. -/
theorem diffStep_rank0_eq_zero
    (g₁ g₂ : SmoothRiemannianMetric I M)
    (S : Tensor0SBundle.Tensor0SField (𝕜 := ℝ) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 0) :
    diffStep (I := I) g₁ g₂ 0 S = 0 := by
  refine DFunLike.ext _ _ (fun x => ?_)
  refine tensor0SSpace_ext 1 x (fun v => ?_)
  have hev := diffStep_eval (I := I) g₁ g₂ 0 S x (v 0) (Fin.tail v)
  rw [Fin.cons_self_tail] at hev
  rw [hev]
  simp

/-- **The operator split of `∇₂(mixedComm S)` into `PieceA − PieceB`** (session-13 backbone).  The base
derivative of the a=1 mixed commutator equals the second base-Leibniz jet `PieceA = ∇₂²(A⋆S)` minus the
base-Leibniz jet of `∇₂S`, `PieceB = ∇₂(A⋆∇₂S)`:
`∇₂(∇₂∇₁S − ∇₁∇₂S) = covStep g₂ (covStep g₂ (diffStep g₁ g₂ S)) − covStep g₂ (diffStep g₁ g₂ (∇₂S))`.
Pure `covStep`/`diffStep` operator algebra (`diffStep_leibniz` + `covStep_sub`).  This is the field-level
backbone the eval-level `∇₂(mixedComm S)` assembly rewrites through: `PieceB` is the committed a=1 atom
(`covStepDiff_of_jets` at level `s+1`, which carries `|∇₂²S|`), and `PieceA` is expanded by the
session-8–11 chain (`covStep2_diffStep_peel/split/branch1/branch2/OCsplit`). -/
theorem covStep2_mixedComm_split
    (g₁ g₂ : SmoothRiemannianMetric I M) (s : ℕ)
    (S : Tensor0SBundle.Tensor0SField (𝕜 := ℝ) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) s) :
    covStep (I := I) g₂ (s + 2)
        (covStep (I := I) g₂ (s + 1) (covStep (I := I) g₁ s S)
          - covStep (I := I) g₁ (s + 1) (covStep (I := I) g₂ s S))
      = covStep (I := I) g₂ (s + 2)
          (covStep (I := I) g₂ (s + 1) (diffStep (I := I) g₁ g₂ s S))
        - covStep (I := I) g₂ (s + 2)
          (diffStep (I := I) g₁ g₂ (s + 1) (covStep (I := I) g₂ s S)) := by
  rw [← covStep_sub]
  congr 1
  rw [diffStep_leibniz (I := I) g₁ g₂ s S]
  abel

set_option backward.isDefEq.respectTransparency false in
open DifferentialGeometry.Integral.Connection in
/-- **Eval-level split of `∇₂(mixedComm S)`** (session-13, the assembly's Step 1).  Evaluating
`covStep2_mixedComm_split` on `Fin.cons (U x) (Fin.cons (W x) (Fin.cons (V x) (Vslots · x)))` gives the
pointwise `∇₂(mixedComm S) x [·] = PieceA x [·] − PieceB x [·]` (via the definitional fibre-subtraction
eval).  The norm Cauchy–Schwarz then expands `PieceA = ∇₂²(A⋆S)` by the
`covStep2_diffStep_peel ▸ split ▸ branch1/branch2 ▸ OCsplit` chain and `PieceB = ∇₂(A⋆∇₂S)` by
`diffStep_leibniz_eval` at rank `s+1` — the latter's `A ⋆ ∇₂²S` sum KEPT (no cancellation), bounded by
the committed a=0 atom scaled by `|∇₂²S|`. -/
theorem covStep2_mixedComm_eval_sub
    (g₁ g₂ : SmoothRiemannianMetric I M) (s : ℕ)
    (S : Tensor0SBundle.Tensor0SField (𝕜 := ℝ) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) s)
    (U W V : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (Vslots : Fin s -> ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _))
    (x : M) :
    covStep (I := I) g₂ (s + 2)
        (covStep (I := I) g₂ (s + 1) (covStep (I := I) g₁ s S)
          - covStep (I := I) g₁ (s + 1) (covStep (I := I) g₂ s S)) x
        (Fin.cons (U x) (Fin.cons (W x) (Fin.cons (V x) (fun a : Fin s => Vslots a x))))
      = covStep (I := I) g₂ (s + 2)
            (covStep (I := I) g₂ (s + 1) (diffStep (I := I) g₁ g₂ s S)) x
            (Fin.cons (U x) (Fin.cons (W x) (Fin.cons (V x) (fun a : Fin s => Vslots a x))))
        - covStep (I := I) g₂ (s + 2)
            (diffStep (I := I) g₁ g₂ (s + 1) (covStep (I := I) g₂ s S)) x
            (Fin.cons (U x) (Fin.cons (W x) (Fin.cons (V x) (fun a : Fin s => Vslots a x)))) := by
  rw [covStep2_mixedComm_split (I := I) g₁ g₂ s S, ContMDiffSection.coe_sub, Pi.sub_apply,
    Tensor0SSpace.sub_apply]

open DifferentialGeometry.Integral.Connection in
/-- **The full eval identity for `∇₂(mixedComm S)`** (session-14; the evaluated a=2 mixed-commutator
Leibniz, the identity feeding `covStepDiff2_mixedComm_le`).  Composing `covStep2_mixedComm_eval_sub`
with the clean PieceA eval `covStep2_diffStep_eval` and the PieceB eval `covStep2_pieceB_eval` gives
the six value-honest families:

* **`∇₂²A ⋆ S`**: `covDerivConnDiff2 (U, W; V, Vslots a)` into each slot of `S`
  (⟵ dual core `covDConnDiff2_g1_le`);
* **`∇₂A ⋆ ∇₂S`** (three families): `covDerivConnDiff (W; V, ·)` into `∇₂S` with leading `U`,
  `covDerivConnDiff (U; V, ·)` into `∇₂S` with leading `W`, and — from `PieceB` — `covDerivConnDiff
  (U; W, ·)` into every slot of `∇₂S` (⟵ `covDerivConnDiff_gJet_le`);
* **`A ⋆ ∇₂²S`** (two families, RETAINED per coordinator ruling №33 — no cancellation):
  `A(Vslots a, V)` into the original slots of `∇₂²S` with leading `U, W`, and — from `PieceB` —
  `A(·, W)` into every slot of `∇₂²S` with leading `U` (⟵ `lcDiff_norm_le` × `|∇₂²S|`). -/
theorem covStep2_mixedComm_eval
    (g₁ g₂ : SmoothRiemannianMetric I M) (s : ℕ)
    (S : Tensor0SBundle.Tensor0SField (𝕜 := ℝ) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) s)
    (U W V : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (Vslots : Fin s -> ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _))
    (x : M) :
    covStep (I := I) g₂ (s + 2)
        (covStep (I := I) g₂ (s + 1) (covStep (I := I) g₁ s S)
          - covStep (I := I) g₁ (s + 1) (covStep (I := I) g₂ s S)) x
        (Fin.cons (U x) (Fin.cons (W x) (Fin.cons (V x) (fun a : Fin s => Vslots a x))))
      = (-∑ a : Fin s, (S x) (Function.update (fun b : Fin s => Vslots b x) a
            (covDerivConnDiff2 (I := I) g₂ g₁
              (fun z => U z) (fun z => W z) (fun z => V z) (fun z => Vslots a z) x)))
        - ∑ a : Fin s, covStep (I := I) g₂ s S x
            (Fin.cons (U x) (Function.update (fun b : Fin s => Vslots b x) a
              (covDerivConnDiff (I := I) g₂ g₁
                (fun z => W z) (fun z => V z) (fun z => Vslots a z) x)))
        - ∑ a : Fin s, covStep (I := I) g₂ s S x
            (Fin.cons (W x) (Function.update (fun b : Fin s => Vslots b x) a
              (covDerivConnDiff (I := I) g₂ g₁
                (fun z => U z) (fun z => V z) (fun z => Vslots a z) x)))
        - ∑ a : Fin s, covStep (I := I) g₂ (s + 1) (covStep (I := I) g₂ s S) x
            (Fin.cons (U x) (Fin.cons (W x) (Function.update (fun b : Fin s => Vslots b x) a
              ((CovariantDerivative.difference
                  (leviCivitaConnectionOfMetric (I := I) g₁)
                  (leviCivitaConnectionOfMetric (I := I) g₂) x
                  (Vslots a x)) (V x)))))
        + ∑ j : Fin (s + 1), (covStep (I := I) g₂ s S x)
            (Function.update (Fin.cons (V x) (fun b : Fin s => Vslots b x)) j
              (covDerivConnDiff (I := I) g₂ g₁ (fun z => U z) (fun z => W z)
                (fun z => (Fin.cons V Vslots :
                  Fin (s + 1) → ContMDiffSection I E (∞ : WithTop ℕ∞)
                    (TangentSpace I : M -> Type _)) j z) x))
        + ∑ j : Fin (s + 1), covStep (I := I) g₂ (s + 1) (covStep (I := I) g₂ s S) x
            (Fin.cons (U x)
              (Function.update (Fin.cons (V x) (fun b : Fin s => Vslots b x)) j
                ((CovariantDerivative.difference
                    (leviCivitaConnectionOfMetric (I := I) g₁)
                    (leviCivitaConnectionOfMetric (I := I) g₂) x
                    ((Fin.cons V Vslots :
                      Fin (s + 1) → ContMDiffSection I E (∞ : WithTop ℕ∞)
                        (TangentSpace I : M -> Type _)) j x)) (W x)))) := by
  rw [covStep2_mixedComm_eval_sub (I := I) g₁ g₂ s S U W V Vslots x,
    covStep2_diffStep_eval (I := I) g₁ g₂ s S U W V Vslots x,
    covStep2_pieceB_eval (I := I) g₁ g₂ s S U W V Vslots x]
  abel

open DifferentialGeometry.Integral.Connection in
set_option maxHeartbeats 1600000 in
/-- **The a=2 mixed-commutator fibre-realization bridge (PROVED, session 14 — the LAST a=2 piece).**
The `g₂`-fibre norm of the base derivative of the a=1 mixed commutator
`∇₂(∇₂∇₁S − ∇₁∇₂S) = covStep g₂ (covStep g₂ (covStep g₁ S) − covStep g₁ (covStep g₂ S))` — the `Term C`
of `covStepDiff2_opLeibniz` — bounded by the order-≤2 jets of `S`.

**Statement correction (session-12/13, coordinator ruling №33).**  `mixedComm S` is order-`1` in `S`
(NOT `(∇₂A)⋆S`; the Leibniz `A⋆∇₂S` contracts over the original `s` slots, while `diffStep_leibniz`'s
`mixedComm := ∇₂(A⋆S) − diffStep(∇₂S)` subtracts `A` over all `s+1` slots — see `diffStep_rank0_eq_zero`
and `ConnDiffDeriv2Bound.md §0 s.12`).  Hence `∇₂(mixedComm S)` genuinely carries a `∇₂²S` term
(`A ⋆ ∇₂²S`), and the right-hand side MUST include `|∇₂²S|` — the earlier "cancelled `∇₂²S` / order-≤1"
form was false.  `covStepDiff2_exists_const` (the sole consumer) already has room for this: its own
right-hand side carries the `|∇₂²S|` term, and its `nlinarith` closes with the strengthened bound.

**Route (as proved, session 14).**  The evaluated a=2 mixed-commutator Leibniz
`covStep2_mixedComm_eval` expands `∇₂(mixedComm S)(tuple)` into six value-honest families: a
`covDerivConnDiff2`-insertion sum into `S` (`∇₂²A`), three `covDerivConnDiff`-insertion sums into
`∇₂S` (`∇₂A`), and two retained `A ⋆ ∇₂²S`-insertion sums (NO cancellation, ruling №33).  Then
per-slot Cauchy–Schwarz at a `g₂`-orthonormal frame against the `g₂`-currency atoms
`covDConnDiff2_gJet_le` (`∇₂²A`, constant `CA₂`), `covDerivConnDiff_gJet_le` (`∇₂A`, constant
`CA₁`), and the a=0 atom `connDiffVec_norm_le` converted through the `g₁` fibre (`A`, constant
`(3/2)·Λ³·Λ'`), assembled by `normSq0S_le_card_of_component_bound`.  The role-swapped jet `∇g₂/g₁`
is NOT needed: the `A`-atom runs entirely in the `g₁` tensor norm plus metric comparability. -/
theorem covStepDiff2_mixedComm_le
    {K : Set M} (g₁ g₂ : SmoothRiemannianMetric I M) (s : ℕ)
    {Λ Λ' Λ'' Λ''' : ℝ}
    (hEq : MetricUniformEquivalentOn (I := I) K g₂ g₁ Λ)
    (hJet1 : MetricCovDerivOrderBoundOn (I := I) K 1 g₁ g₂ Λ')
    (hJet2 : MetricCovDerivOrderBoundOn (I := I) K 2 g₁ g₂ Λ'')
    (hJet3 : MetricCovDerivOrderBoundOn (I := I) K 3 g₁ g₂ Λ''') :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (S : Tensor0SBundle.Tensor0SField (𝕜 := ℝ) (E := E) (H := H)
            (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) s) (x : M), x ∈ K →
        Real.sqrt (normSq0S (I := I) g₂ x (s + 3)
            (covStep (I := I) g₂ (s + 2)
              (covStep (I := I) g₂ (s + 1) (covStep (I := I) g₁ s S)
                - covStep (I := I) g₁ (s + 1) (covStep (I := I) g₂ s S)) x)) ≤
          C * (Real.sqrt (normSq0S (I := I) g₂ x s (S x))
            + Real.sqrt (normSq0S (I := I) g₂ x (s + 1) (covStep (I := I) g₂ s S x))
            + Real.sqrt (normSq0S (I := I) g₂ x (s + 2)
                (covStep (I := I) g₂ (s + 1) (covStep (I := I) g₂ s S) x))) := by
  classical
  haveI : IsManifold I 1 M :=
    IsManifold.of_le (I := I) (M := M) (n := ∞) (by decide : (1 : WithTop ℕ∞) ≤ ∞)
  haveI : IsManifold I 2 M :=
    IsManifold.of_le (I := I) (M := M) (n := ∞) (by decide : (2 : WithTop ℕ∞) ≤ ∞)
  haveI : IsManifold I ((∞ : WithTop ℕ∞) + 1) M := by
    change IsManifold I ∞ M
    infer_instance
  haveI : IsManifold I (1 + 1) M :=
    IsManifold.of_le (I := I) (M := M) (n := ∞)
      (by decide : ((1 : WithTop ℕ∞) + 1) ≤ ∞)
  haveI : ContMDiffVectorBundle 1 E (TangentSpace I : M -> Type _) I :=
    TangentBundle.contMDiffVectorBundle (I := I) (M := M) (n := 1)
  -- the three x-uniform per-slot constants
  set CA2 : ℝ := 3 / 2 * Λ ^ 5 * Λ''' + 9 / 2 * Λ ^ 6 * Λ' * Λ'' + 3 * Λ ^ 7 * Λ' ^ 3 with hCA2def
  set CA1 : ℝ := 3 / 2 * Λ ^ 4 * (Λ'' + Λ * Λ' ^ 2) with hCA1def
  set NAb : ℝ := 3 / 2 * Λ ^ 3 * Λ' with hNAbdef
  refine ⟨max 0 (Real.sqrt ((Module.finrank ℝ E : ℝ) ^ (s + 3)) *
      ((s : ℝ) * CA2 + (3 * (s : ℝ) + 1) * CA1 + (2 * (s : ℝ) + 1) * NAb)),
    le_max_left _ _, ?_⟩
  intro S x hx
  -- sign facts (available at `x ∈ K`)
  have hL1 : (1 : ℝ) ≤ Λ := hEq.1
  have hLnn : (0 : ℝ) ≤ Λ := le_trans zero_le_one hL1
  have hL'nn : (0 : ℝ) ≤ Λ' := le_trans (Real.sqrt_nonneg _) (hJet1 x hx)
  have hL''nn : (0 : ℝ) ≤ Λ'' := le_trans (Real.sqrt_nonneg _) (hJet2 x hx)
  have hL'''nn : (0 : ℝ) ≤ Λ''' := le_trans (Real.sqrt_nonneg _) (hJet3 x hx)
  have hs2 : Real.sqrt Λ ^ 2 = Λ := Real.sq_sqrt hLnn
  have hCA2nn : (0 : ℝ) ≤ CA2 := by
    rw [hCA2def]
    have h1 : (0 : ℝ) ≤ Λ ^ 5 * Λ''' := mul_nonneg (by positivity) hL'''nn
    have h2 : (0 : ℝ) ≤ Λ ^ 6 * Λ' * Λ'' := mul_nonneg (mul_nonneg (by positivity) hL'nn) hL''nn
    have h3 : (0 : ℝ) ≤ Λ ^ 7 * Λ' ^ 3 := mul_nonneg (by positivity) (pow_nonneg hL'nn 3)
    nlinarith [h1, h2, h3]
  have hCA1nn : (0 : ℝ) ≤ CA1 := by
    rw [hCA1def]
    exact mul_nonneg (mul_nonneg (by norm_num) (by positivity))
      (add_nonneg hL''nn (mul_nonneg hLnn (sq_nonneg Λ')))
  have hNAbnn : (0 : ℝ) ≤ NAb := by
    rw [hNAbdef]
    exact mul_nonneg (mul_nonneg (by norm_num) (by positivity)) hL'nn
  -- `g₂`-orthonormal basis at `x`
  obtain ⟨basis, hON⟩ :=
    DifferentialGeometry.Integral.Connection.exists_gOrthonormalBasis (I := I) g₂ x
  have hbnorm : ∀ i, Real.sqrt (g₂.inner x (basis i) (basis i)) = 1 := by
    intro i; rw [hON i i]; simp
  have hinv : MetricInverseInBasis_gen (I := I) g₂ x basis
      (identityInvMetric (Idx := Fin (Module.finrank Real (TangentSpace I x)))) := by
    intro i j; constructor <;> simp [identityInvMetric, diagonalInvMetric, hON]
  -- the `S`-jet fibre norms
  set NS := Real.sqrt (normSq0S (I := I) g₂ x s (S x)) with hNSdef
  set N1 := Real.sqrt (normSq0S (I := I) g₂ x (s + 1) (covStep (I := I) g₂ s S x)) with hN1def
  set N2 := Real.sqrt (normSq0S (I := I) g₂ x (s + 2)
    (covStep (I := I) g₂ (s + 1) (covStep (I := I) g₂ s S) x)) with hN2def
  have hNSnn : (0 : ℝ) ≤ NS := Real.sqrt_nonneg _
  have hN1nn : (0 : ℝ) ≤ N1 := Real.sqrt_nonneg _
  have hN2nn : (0 : ℝ) ≤ N2 := Real.sqrt_nonneg _
  -- pointwise atoms at `x`
  have hA2 := fun (v' v w u : TangentSpace I x) =>
    covDConnDiff2_gJet_le (I := I) hEq hJet1 hJet2 hJet3 hx v' v w u
  have hA1 := fun (v w u : TangentSpace I x) =>
    DifferentialGeometry.Geometry.Curvature.covDerivConnDiff_gJet_le (I := I)
      hEq hJet1 hJet2 hx v w u
  -- the a=0 atom, `g₂`-vector currency (via the `g₁` tensor norm plus comparability)
  have hvec : ∀ z : TangentSpace I x,
      Real.sqrt (g₁.inner x z z) ≤ Real.sqrt Λ * Real.sqrt (g₂.inner x z z) := by
    intro z
    calc Real.sqrt (g₁.inner x z z) ≤ Real.sqrt (Λ * g₂.inner x z z) :=
          Real.sqrt_le_sqrt (hEq.2 x hx z).2
      _ = Real.sqrt Λ * Real.sqrt (g₂.inner x z z) := Real.sqrt_mul hLnn _
  have hout : ∀ z : TangentSpace I x,
      Real.sqrt (g₂.inner x z z) ≤ Real.sqrt Λ * Real.sqrt (g₁.inner x z z) := by
    intro z
    have h := (hEq.2 x hx z).1
    have h' : g₂.inner x z z ≤ Λ * g₁.inner x z z := by
      have h2 := mul_le_mul_of_nonneg_left h hLnn
      rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt (lt_of_lt_of_le zero_lt_one hL1)), one_mul] at h2
      exact h2
    calc Real.sqrt (g₂.inner x z z) ≤ Real.sqrt (Λ * g₁.inner x z z) := Real.sqrt_le_sqrt h'
      _ = Real.sqrt Λ * Real.sqrt (g₁.inner x z z) := Real.sqrt_mul hLnn _
  have hNAg1 : Real.sqrt (Tensor0SBundle.normSqRS (I := I) (g := g₁) (x := x) 1 2
        (Tensor0SBundle.connectionDifferenceTensorAt (I := I)
          (leviCivitaConnectionOfMetric (I := I) g₁)
          (leviCivitaConnectionOfMetric (I := I) g₂) x)) ≤
      3 / 2 * (Λ * Real.sqrt Λ * Λ') := by
    obtain ⟨_, basis₁, hhinv₁, _, _, _⟩ :=
      exists_diagInv_of_metricUniformEquivalentOn (I := I)
        (metricUniformEquivalentOn_symm (I := I) hEq) hx
    have h := diff_le_covOne_basis_ref_lc (I := I) g₁ g₂ hx Λ hEq basis₁ hhinv₁
    rw [show Real.sqrt (Λ ^ 3) = Λ * Real.sqrt Λ from by
      rw [show Λ ^ 3 = Λ ^ 2 * Λ by ring, Real.sqrt_mul (by positivity),
        Real.sqrt_sq hLnn]] at h
    refine le_trans h ?_
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left (hJet1 x hx) (mul_nonneg hLnn (Real.sqrt_nonneg _)))
      (by norm_num : (0 : ℝ) ≤ 3 / 2)
  have hA0 : ∀ (Yv Xv : TangentSpace I x),
      Real.sqrt (g₂.inner x
          ((CovariantDerivative.difference
              (leviCivitaConnectionOfMetric (I := I) g₁)
              (leviCivitaConnectionOfMetric (I := I) g₂) x Yv) Xv)
          ((CovariantDerivative.difference
              (leviCivitaConnectionOfMetric (I := I) g₁)
              (leviCivitaConnectionOfMetric (I := I) g₂) x Yv) Xv)) ≤
        NAb * Real.sqrt (g₂.inner x Xv Xv) * Real.sqrt (g₂.inner x Yv Yv) := by
    intro Yv Xv
    have hg1 := connDiffVec_norm_le (I := I) g₁
      (leviCivitaConnectionOfMetric (I := I) g₁)
      (leviCivitaConnectionOfMetric (I := I) g₂) Xv Yv
    have hstep1 : Real.sqrt (g₁.inner x
          ((CovariantDerivative.difference
              (leviCivitaConnectionOfMetric (I := I) g₁)
              (leviCivitaConnectionOfMetric (I := I) g₂) x Yv) Xv)
          ((CovariantDerivative.difference
              (leviCivitaConnectionOfMetric (I := I) g₁)
              (leviCivitaConnectionOfMetric (I := I) g₂) x Yv) Xv)) ≤
        3 / 2 * (Λ * Real.sqrt Λ * Λ') *
          (Real.sqrt Λ * Real.sqrt (g₂.inner x Xv Xv)) *
          (Real.sqrt Λ * Real.sqrt (g₂.inner x Yv Yv)) := by
      refine le_trans hg1 ?_
      have hmono1 : Real.sqrt (Tensor0SBundle.normSqRS (I := I) (g := g₁) (x := x) 1 2
            (Tensor0SBundle.connectionDifferenceTensorAt (I := I)
              (leviCivitaConnectionOfMetric (I := I) g₁)
              (leviCivitaConnectionOfMetric (I := I) g₂) x)) *
            Real.sqrt (g₁.inner x Xv Xv) * Real.sqrt (g₁.inner x Yv Yv) ≤
          3 / 2 * (Λ * Real.sqrt Λ * Λ') *
            (Real.sqrt Λ * Real.sqrt (g₂.inner x Xv Xv)) *
            (Real.sqrt Λ * Real.sqrt (g₂.inner x Yv Yv)) := by
        have p1 := mul_le_mul (mul_le_mul hNAg1 (hvec Xv) (Real.sqrt_nonneg _)
          (by positivity)) (hvec Yv) (Real.sqrt_nonneg _) (by positivity)
        exact p1
      exact hmono1
    calc Real.sqrt (g₂.inner x
          ((CovariantDerivative.difference
              (leviCivitaConnectionOfMetric (I := I) g₁)
              (leviCivitaConnectionOfMetric (I := I) g₂) x Yv) Xv)
          ((CovariantDerivative.difference
              (leviCivitaConnectionOfMetric (I := I) g₁)
              (leviCivitaConnectionOfMetric (I := I) g₂) x Yv) Xv))
        ≤ Real.sqrt Λ * Real.sqrt (g₁.inner x
            ((CovariantDerivative.difference
                (leviCivitaConnectionOfMetric (I := I) g₁)
                (leviCivitaConnectionOfMetric (I := I) g₂) x Yv) Xv)
            ((CovariantDerivative.difference
                (leviCivitaConnectionOfMetric (I := I) g₁)
                (leviCivitaConnectionOfMetric (I := I) g₂) x Yv) Xv)) := hout _
      _ ≤ Real.sqrt Λ * (3 / 2 * (Λ * Real.sqrt Λ * Λ') *
            (Real.sqrt Λ * Real.sqrt (g₂.inner x Xv Xv)) *
            (Real.sqrt Λ * Real.sqrt (g₂.inner x Yv Yv))) :=
          mul_le_mul_of_nonneg_left hstep1 (Real.sqrt_nonneg _)
      _ = NAb * Real.sqrt (g₂.inner x Xv Xv) * Real.sqrt (g₂.inner x Yv Yv) := by
          rw [hNAbdef]
          linear_combination (3 / 2 * Λ' * (Real.sqrt Λ ^ 2 + Λ) *
            (Real.sqrt (g₂.inner x Xv Xv) * Real.sqrt (g₂.inner x Yv Yv)) * Λ) * hs2
  -- the single-slot Cauchy–Schwarz helper
  have habs : ∀ (r : ℕ)
      (T : Tensor0SBundle.Tensor0SSpace (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) r x)
      (tup : Fin r → TangentSpace I x) (j : Fin r),
      (∀ b : Fin r, b ≠ j → Real.sqrt (g₂.inner x (tup b) (tup b)) = 1) →
      |T tup| ≤ Real.sqrt (normSq0S (I := I) g₂ x r T) *
        Real.sqrt (g₂.inner x (tup j) (tup j)) := by
    intro r T tup j hb
    have hcs := Tensor0SBundle.abs_apply_le_sqrt_normSq0S (I := I) g₂ x r basis hON T tup
    rwa [Finset.prod_eq_single j (fun b _ hbj => hb b hbj)
      (fun hj => absurd (Finset.mem_univ j) hj)] at hcs
  -- the per-component bound
  set B : ℝ := (s : ℝ) * (NS * CA2) + (3 * (s : ℝ) + 1) * (N1 * CA1) +
    (2 * (s : ℝ) + 1) * (N2 * NAb) with hBdef
  have hBnn : (0 : ℝ) ≤ B := by
    rw [hBdef]
    have b1 : (0 : ℝ) ≤ (s : ℝ) * (NS * CA2) :=
      mul_nonneg (by positivity) (mul_nonneg hNSnn hCA2nn)
    have b2 : (0 : ℝ) ≤ (3 * (s : ℝ) + 1) * (N1 * CA1) :=
      mul_nonneg (by positivity) (mul_nonneg hN1nn hCA1nn)
    have b3 : (0 : ℝ) ≤ (2 * (s : ℝ) + 1) * (N2 * NAb) :=
      mul_nonneg (by positivity) (mul_nonneg hN2nn hNAbnn)
    linarith
  have hcomp : ∀ φ : Fin (s + 3) → Fin (Module.finrank Real (TangentSpace I x)),
      |Tensor0SBundle.component0S (I := I) basis
        (covStep (I := I) g₂ (s + 2)
          (covStep (I := I) g₂ (s + 1) (covStep (I := I) g₁ s S)
            - covStep (I := I) g₁ (s + 1) (covStep (I := I) g₂ s S)) x) φ| ≤ B := by
    intro φ
    rw [Tensor0SBundle.component0S_apply]
    -- basis-vector extension sections
    set Usec : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _) :=
      ContMDiffSection.mk (smoothExtensionTangent (I := I) x (basis (φ 0)))
        (smoothExtensionTangent_contMDiff (I := I) x (basis (φ 0))) with hUsec
    set Wsec : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _) :=
      ContMDiffSection.mk (smoothExtensionTangent (I := I) x (basis (φ (Fin.succ 0))))
        (smoothExtensionTangent_contMDiff (I := I) x (basis (φ (Fin.succ 0)))) with hWsec
    set Vsec : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _) :=
      ContMDiffSection.mk
        (smoothExtensionTangent (I := I) x (basis (φ (Fin.succ (Fin.succ 0)))))
        (smoothExtensionTangent_contMDiff (I := I) x
          (basis (φ (Fin.succ (Fin.succ 0))))) with hVsec
    set Zsec : Fin s → ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _) :=
      fun a => ContMDiffSection.mk
        (smoothExtensionTangent (I := I) x (basis (φ a.succ.succ.succ)))
        (smoothExtensionTangent_contMDiff (I := I) x (basis (φ a.succ.succ.succ))) with hZsec
    have hUval : Usec x = basis (φ 0) := smoothExtensionTangent_eq (I := I) x _
    have hWval : Wsec x = basis (φ (Fin.succ 0)) := smoothExtensionTangent_eq (I := I) x _
    have hVval : Vsec x = basis (φ (Fin.succ (Fin.succ 0))) :=
      smoothExtensionTangent_eq (I := I) x _
    have hZval : ∀ a : Fin s, Zsec a x = basis (φ a.succ.succ.succ) :=
      fun a => smoothExtensionTangent_eq (I := I) x _
    have hnU : Real.sqrt (g₂.inner x (Usec x) (Usec x)) = 1 := by rw [hUval]; exact hbnorm _
    have hnW : Real.sqrt (g₂.inner x (Wsec x) (Wsec x)) = 1 := by rw [hWval]; exact hbnorm _
    have hnV : Real.sqrt (g₂.inner x (Vsec x) (Vsec x)) = 1 := by rw [hVval]; exact hbnorm _
    have hnZ : ∀ a : Fin s, Real.sqrt (g₂.inner x (Zsec a x) (Zsec a x)) = 1 :=
      fun a => by rw [hZval a]; exact hbnorm _
    have htuple : (fun j : Fin (s + 3) => basis (φ j)) =
        Fin.cons (Usec x) (Fin.cons (Wsec x)
          (Fin.cons (Vsec x) (fun a : Fin s => Zsec a x))) := by
      funext j
      refine Fin.cases ?_ (fun i => ?_) j
      · exact hUval.symm
      · refine Fin.cases ?_ (fun k => ?_) i
        · exact hWval.symm
        · refine Fin.cases ?_ (fun a => ?_) k
          · exact hVval.symm
          · exact (hZval a).symm
    rw [htuple, covStep2_mixedComm_eval (I := I) g₁ g₂ s S Usec Wsec Vsec Zsec x]
    -- family (I): `∇₂²A` into `S`
    have hI : ∀ a : Fin s, |(S x) (Function.update (fun b : Fin s => Zsec b x) a
        (covDerivConnDiff2 (I := I) g₂ g₁
          (fun z => Usec z) (fun z => Wsec z) (fun z => Vsec z) (fun z => Zsec a z) x))| ≤
        NS * CA2 := by
      intro a
      have hb := habs s (S x)
        (Function.update (fun b : Fin s => Zsec b x) a
          (covDerivConnDiff2 (I := I) g₂ g₁
            (fun z => Usec z) (fun z => Wsec z) (fun z => Vsec z) (fun z => Zsec a z) x)) a
        (fun b hbne => by rw [Function.update_of_ne hbne]; exact hnZ b)
      rw [Function.update_self, ← hNSdef] at hb
      refine le_trans hb (mul_le_mul_of_nonneg_left ?_ hNSnn)
      rw [hCA2def]
      have h := hA2 (basis (φ 0)) (basis (φ (Fin.succ 0))) (basis (φ (Fin.succ (Fin.succ 0))))
        (basis (φ a.succ.succ.succ))
      rw [hbnorm (φ 0), hbnorm (φ (Fin.succ 0)), hbnorm (φ (Fin.succ (Fin.succ 0))),
        hbnorm (φ a.succ.succ.succ), mul_one, mul_one, mul_one, mul_one] at h
      exact h
    -- family (II): `∇₂A(W;V,·)` into `∇₂S`, leading `U`
    have hII : ∀ a : Fin s, |covStep (I := I) g₂ s S x
        (Fin.cons (Usec x) (Function.update (fun b : Fin s => Zsec b x) a
          (covDerivConnDiff (I := I) g₂ g₁
            (fun z => Wsec z) (fun z => Vsec z) (fun z => Zsec a z) x)))| ≤ N1 * CA1 := by
      intro a
      set tup : Fin (s + 1) → TangentSpace I x :=
        Fin.cons (Usec x) (Function.update (fun b : Fin s => Zsec b x) a
          (covDerivConnDiff (I := I) g₂ g₁
            (fun z => Wsec z) (fun z => Vsec z) (fun z => Zsec a z) x)) with htup
      have hbase : ∀ b : Fin (s + 1), b ≠ Fin.succ a →
          Real.sqrt (g₂.inner x (tup b) (tup b)) = 1 := by
        intro b
        refine Fin.cases ?_ (fun c => ?_) b
        · intro _
          rw [htup, Fin.cons_zero]
          exact hnU
        · intro hbne
          have hca : c ≠ a := fun h => hbne (by rw [h])
          rw [htup, Fin.cons_succ, Function.update_of_ne hca]
          exact hnZ c
      have hb := habs (s + 1) (covStep (I := I) g₂ s S x) tup (Fin.succ a) hbase
      have htupj : tup (Fin.succ a) = covDerivConnDiff (I := I) g₂ g₁
          (fun z => Wsec z) (fun z => Vsec z) (fun z => Zsec a z) x := by
        rw [htup, Fin.cons_succ, Function.update_self]
      rw [htupj, ← hN1def] at hb
      refine le_trans hb (mul_le_mul_of_nonneg_left ?_ hN1nn)
      rw [hCA1def]
      have h := hA1 (basis (φ (Fin.succ 0))) (basis (φ (Fin.succ (Fin.succ 0))))
        (basis (φ a.succ.succ.succ))
      rw [hbnorm (φ (Fin.succ 0)), hbnorm (φ (Fin.succ (Fin.succ 0))),
        hbnorm (φ a.succ.succ.succ), mul_one, mul_one, mul_one] at h
      exact h
    -- family (III): `∇₂A(U;V,·)` into `∇₂S`, leading `W`
    have hIII : ∀ a : Fin s, |covStep (I := I) g₂ s S x
        (Fin.cons (Wsec x) (Function.update (fun b : Fin s => Zsec b x) a
          (covDerivConnDiff (I := I) g₂ g₁
            (fun z => Usec z) (fun z => Vsec z) (fun z => Zsec a z) x)))| ≤ N1 * CA1 := by
      intro a
      set tup : Fin (s + 1) → TangentSpace I x :=
        Fin.cons (Wsec x) (Function.update (fun b : Fin s => Zsec b x) a
          (covDerivConnDiff (I := I) g₂ g₁
            (fun z => Usec z) (fun z => Vsec z) (fun z => Zsec a z) x)) with htup
      have hbase : ∀ b : Fin (s + 1), b ≠ Fin.succ a →
          Real.sqrt (g₂.inner x (tup b) (tup b)) = 1 := by
        intro b
        refine Fin.cases ?_ (fun c => ?_) b
        · intro _
          rw [htup, Fin.cons_zero]
          exact hnW
        · intro hbne
          have hca : c ≠ a := fun h => hbne (by rw [h])
          rw [htup, Fin.cons_succ, Function.update_of_ne hca]
          exact hnZ c
      have hb := habs (s + 1) (covStep (I := I) g₂ s S x) tup (Fin.succ a) hbase
      have htupj : tup (Fin.succ a) = covDerivConnDiff (I := I) g₂ g₁
          (fun z => Usec z) (fun z => Vsec z) (fun z => Zsec a z) x := by
        rw [htup, Fin.cons_succ, Function.update_self]
      rw [htupj, ← hN1def] at hb
      refine le_trans hb (mul_le_mul_of_nonneg_left ?_ hN1nn)
      rw [hCA1def]
      have h := hA1 (basis (φ 0)) (basis (φ (Fin.succ (Fin.succ 0))))
        (basis (φ a.succ.succ.succ))
      rw [hbnorm (φ 0), hbnorm (φ (Fin.succ (Fin.succ 0))),
        hbnorm (φ a.succ.succ.succ), mul_one, mul_one, mul_one] at h
      exact h
    -- family (V): `A(·,V)` into `∇₂²S`, leading `U, W`
    have hV : ∀ a : Fin s, |covStep (I := I) g₂ (s + 1) (covStep (I := I) g₂ s S) x
        (Fin.cons (Usec x) (Fin.cons (Wsec x) (Function.update (fun b : Fin s => Zsec b x) a
          ((CovariantDerivative.difference
              (leviCivitaConnectionOfMetric (I := I) g₁)
              (leviCivitaConnectionOfMetric (I := I) g₂) x
              (Zsec a x)) (Vsec x)))))| ≤ N2 * NAb := by
      intro a
      set tup : Fin (s + 2) → TangentSpace I x :=
        Fin.cons (Usec x) (Fin.cons (Wsec x) (Function.update (fun b : Fin s => Zsec b x) a
          ((CovariantDerivative.difference
              (leviCivitaConnectionOfMetric (I := I) g₁)
              (leviCivitaConnectionOfMetric (I := I) g₂) x
              (Zsec a x)) (Vsec x)))) with htup
      have hbase : ∀ b : Fin (s + 2), b ≠ Fin.succ (Fin.succ a) →
          Real.sqrt (g₂.inner x (tup b) (tup b)) = 1 := by
        intro b
        refine Fin.cases ?_ (fun c => ?_) b
        · intro _
          rw [htup, Fin.cons_zero]
          exact hnU
        · refine Fin.cases ?_ (fun d => ?_) c
          · intro _
            rw [htup, Fin.cons_succ, Fin.cons_zero]
            exact hnW
          · intro hbne
            have hda : d ≠ a := fun h => hbne (by rw [h])
            rw [htup, Fin.cons_succ, Fin.cons_succ, Function.update_of_ne hda]
            exact hnZ d
      have hb := habs (s + 2) (covStep (I := I) g₂ (s + 1) (covStep (I := I) g₂ s S) x) tup
        (Fin.succ (Fin.succ a)) hbase
      have htupj : tup (Fin.succ (Fin.succ a)) =
          (CovariantDerivative.difference
            (leviCivitaConnectionOfMetric (I := I) g₁)
            (leviCivitaConnectionOfMetric (I := I) g₂) x
            (Zsec a x)) (Vsec x) := by
        rw [htup, Fin.cons_succ, Fin.cons_succ, Function.update_self]
      rw [htupj, ← hN2def] at hb
      refine le_trans hb (mul_le_mul_of_nonneg_left ?_ hN2nn)
      have h := hA0 (Zsec a x) (Vsec x)
      rw [hnV, hnZ a, mul_one, mul_one] at h
      exact h
    -- family (IV): `∇₂A(U;W,·)` into every slot of `∇₂S` (from `PieceB`)
    have hIV : ∀ j : Fin (s + 1), |(covStep (I := I) g₂ s S x)
        (Function.update (Fin.cons (Vsec x) (fun b : Fin s => Zsec b x)) j
          (covDerivConnDiff (I := I) g₂ g₁ (fun z => Usec z) (fun z => Wsec z)
            (fun z => (Fin.cons Vsec Zsec :
              Fin (s + 1) → ContMDiffSection I E (∞ : WithTop ℕ∞)
                (TangentSpace I : M -> Type _)) j z) x))| ≤ N1 * CA1 := by
      intro j
      set tup : Fin (s + 1) → TangentSpace I x :=
        Function.update (Fin.cons (Vsec x) (fun b : Fin s => Zsec b x)) j
          (covDerivConnDiff (I := I) g₂ g₁ (fun z => Usec z) (fun z => Wsec z)
            (fun z => (Fin.cons Vsec Zsec :
              Fin (s + 1) → ContMDiffSection I E (∞ : WithTop ℕ∞)
                (TangentSpace I : M -> Type _)) j z) x) with htup
      have hbase : ∀ b : Fin (s + 1), b ≠ j →
          Real.sqrt (g₂.inner x (tup b) (tup b)) = 1 := by
        intro b hbj
        rw [htup, Function.update_of_ne hbj]
        refine Fin.cases ?_ (fun c => ?_) b
        · rw [Fin.cons_zero]
          exact hnV
        · rw [Fin.cons_succ]
          exact hnZ c
      have hb := habs (s + 1) (covStep (I := I) g₂ s S x) tup j hbase
      have htupj : tup j = covDerivConnDiff (I := I) g₂ g₁
          (fun z => Usec z) (fun z => Wsec z)
          (fun z => (Fin.cons Vsec Zsec :
            Fin (s + 1) → ContMDiffSection I E (∞ : WithTop ℕ∞)
              (TangentSpace I : M -> Type _)) j z) x := by
        rw [htup, Function.update_self]
      rw [htupj, ← hN1def] at hb
      refine le_trans hb (mul_le_mul_of_nonneg_left ?_ hN1nn)
      rw [hCA1def]
      refine Fin.cases ?_ (fun c => ?_) j
      · have h := hA1 (basis (φ 0)) (basis (φ (Fin.succ 0)))
          (basis (φ (Fin.succ (Fin.succ 0))))
        rw [hbnorm (φ 0), hbnorm (φ (Fin.succ 0)), hbnorm (φ (Fin.succ (Fin.succ 0))),
          mul_one, mul_one, mul_one] at h
        exact h
      · have h := hA1 (basis (φ 0)) (basis (φ (Fin.succ 0))) (basis (φ c.succ.succ.succ))
        rw [hbnorm (φ 0), hbnorm (φ (Fin.succ 0)), hbnorm (φ c.succ.succ.succ),
          mul_one, mul_one, mul_one] at h
        exact h
    -- family (VI): `A(·,W)` into every slot of `∇₂²S` (from `PieceB`)
    have hnVV : ∀ j : Fin (s + 1),
        Real.sqrt (g₂.inner x
          ((Fin.cons Vsec Zsec :
            Fin (s + 1) → ContMDiffSection I E (∞ : WithTop ℕ∞)
              (TangentSpace I : M -> Type _)) j x)
          ((Fin.cons Vsec Zsec :
            Fin (s + 1) → ContMDiffSection I E (∞ : WithTop ℕ∞)
              (TangentSpace I : M -> Type _)) j x)) = 1 := by
      intro j
      refine Fin.cases ?_ (fun c => ?_) j
      · rw [Fin.cons_zero]
        exact hnV
      · rw [Fin.cons_succ]
        exact hnZ c
    have hVI : ∀ j : Fin (s + 1), |covStep (I := I) g₂ (s + 1) (covStep (I := I) g₂ s S) x
        (Fin.cons (Usec x)
          (Function.update (Fin.cons (Vsec x) (fun b : Fin s => Zsec b x)) j
            ((CovariantDerivative.difference
                (leviCivitaConnectionOfMetric (I := I) g₁)
                (leviCivitaConnectionOfMetric (I := I) g₂) x
                ((Fin.cons Vsec Zsec :
                  Fin (s + 1) → ContMDiffSection I E (∞ : WithTop ℕ∞)
                    (TangentSpace I : M -> Type _)) j x)) (Wsec x))))| ≤ N2 * NAb := by
      intro j
      set tup : Fin (s + 2) → TangentSpace I x :=
        Fin.cons (Usec x)
          (Function.update (Fin.cons (Vsec x) (fun b : Fin s => Zsec b x)) j
            ((CovariantDerivative.difference
                (leviCivitaConnectionOfMetric (I := I) g₁)
                (leviCivitaConnectionOfMetric (I := I) g₂) x
                ((Fin.cons Vsec Zsec :
                  Fin (s + 1) → ContMDiffSection I E (∞ : WithTop ℕ∞)
                    (TangentSpace I : M -> Type _)) j x)) (Wsec x))) with htup
      have hbase : ∀ b : Fin (s + 2), b ≠ Fin.succ j →
          Real.sqrt (g₂.inner x (tup b) (tup b)) = 1 := by
        intro b
        refine Fin.cases ?_ (fun c => ?_) b
        · intro _
          rw [htup, Fin.cons_zero]
          exact hnU
        · intro hbne
          have hcj : c ≠ j := fun h => hbne (by rw [h])
          rw [htup, Fin.cons_succ, Function.update_of_ne hcj]
          refine Fin.cases ?_ (fun d => ?_) c
          · rw [Fin.cons_zero]
            exact hnV
          · rw [Fin.cons_succ]
            exact hnZ d
      have hb := habs (s + 2) (covStep (I := I) g₂ (s + 1) (covStep (I := I) g₂ s S) x) tup
        (Fin.succ j) hbase
      have htupj : tup (Fin.succ j) =
          (CovariantDerivative.difference
            (leviCivitaConnectionOfMetric (I := I) g₁)
            (leviCivitaConnectionOfMetric (I := I) g₂) x
            ((Fin.cons Vsec Zsec :
              Fin (s + 1) → ContMDiffSection I E (∞ : WithTop ℕ∞)
                (TangentSpace I : M -> Type _)) j x)) (Wsec x) := by
        rw [htup, Fin.cons_succ, Function.update_self]
      rw [htupj, ← hN2def] at hb
      refine le_trans hb (mul_le_mul_of_nonneg_left ?_ hN2nn)
      have h := hA0 ((Fin.cons Vsec Zsec :
        Fin (s + 1) → ContMDiffSection I E (∞ : WithTop ℕ∞)
          (TangentSpace I : M -> Type _)) j x) (Wsec x)
      rw [hnW, hnVV j, mul_one, mul_one] at h
      exact h
    -- assemble the six families
    have habs_sub : ∀ p q : ℝ, |p - q| ≤ |p| + |q| := by
      intro p q
      calc |p - q| = |p + -q| := by rw [sub_eq_add_neg]
        _ ≤ |p| + |-q| := abs_add_le _ _
        _ = |p| + |q| := by rw [abs_neg]
    have h6 : ∀ A B' C' D' E' F' : ℝ,
        |A - B' - C' - D' + E' + F'| ≤ |A| + |B'| + |C'| + |D'| + |E'| + |F'| := by
      intro A B' C' D' E' F'
      have h1 : |A - B' - C' - D' + E' + F'| ≤ |A - B' - C' - D' + E'| + |F'| :=
        abs_add_le _ _
      have h2 : |A - B' - C' - D' + E'| ≤ |A - B' - C' - D'| + |E'| := abs_add_le _ _
      have h3 : |A - B' - C' - D'| ≤ |A - B' - C'| + |D'| := habs_sub _ _
      have h4 : |A - B' - C'| ≤ |A - B'| + |C'| := habs_sub _ _
      have h5 : |A - B'| ≤ |A| + |B'| := habs_sub _ _
      linarith
    have esum : ∀ {r : ℕ} (f : Fin r → ℝ) (c : ℝ), (∀ a, |f a| ≤ c) →
        |∑ a, f a| ≤ (r : ℝ) * c := by
      intro r f c hf
      calc |∑ a, f a| ≤ ∑ a, |f a| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _a : Fin r, c := Finset.sum_le_sum (fun a _ => hf a)
        _ = (r : ℝ) * c := by
            simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    refine le_trans (h6 _ _ _ _ _ _) ?_
    rw [abs_neg]
    refine le_trans (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add
      (esum _ _ hI) (esum _ _ hII)) (esum _ _ hIII)) (esum _ _ hV)) (esum _ _ hIV))
      (esum _ _ hVI)) ?_
    rw [hBdef]
    refine le_of_eq ?_
    push_cast
    ring
  -- component bound → fibre-norm bound
  have hcard := Tensor0SBundle.normSq0S_le_card_of_component_bound (I := I) g₂ x (s + 3) basis hinv
    (covStep (I := I) g₂ (s + 2)
      (covStep (I := I) g₂ (s + 1) (covStep (I := I) g₁ s S)
        - covStep (I := I) g₁ (s + 1) (covStep (I := I) g₂ s S)) x) B hBnn hcomp
  have hcard_eq :
      (Fintype.card (Fin (s + 3) → Fin (Module.finrank Real (TangentSpace I x))) : ℝ)
        = (Module.finrank ℝ E : ℝ) ^ (s + 3) := by
    rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
    push_cast
    rfl
  have hstep : B ≤ ((s : ℝ) * CA2 + (3 * (s : ℝ) + 1) * CA1 + (2 * (s : ℝ) + 1) * NAb) *
      (NS + N1 + N2) := by
    rw [hBdef]
    have hc1 : (0 : ℝ) ≤ (s : ℝ) * CA2 := mul_nonneg (by positivity) hCA2nn
    have hc2 : (0 : ℝ) ≤ (3 * (s : ℝ) + 1) * CA1 := mul_nonneg (by positivity) hCA1nn
    have hc3 : (0 : ℝ) ≤ (2 * (s : ℝ) + 1) * NAb := mul_nonneg (by positivity) hNAbnn
    nlinarith [mul_nonneg hc1 (add_nonneg hN1nn hN2nn),
      mul_nonneg hc2 (add_nonneg hNSnn hN2nn),
      mul_nonneg hc3 (add_nonneg hNSnn hN1nn)]
  calc Real.sqrt (normSq0S (I := I) g₂ x (s + 3)
        (covStep (I := I) g₂ (s + 2)
          (covStep (I := I) g₂ (s + 1) (covStep (I := I) g₁ s S)
            - covStep (I := I) g₁ (s + 1) (covStep (I := I) g₂ s S)) x))
      ≤ Real.sqrt
          ((Fintype.card (Fin (s + 3) → Fin (Module.finrank Real (TangentSpace I x))) : ℝ)
            * B ^ 2) := Real.sqrt_le_sqrt hcard
    _ = Real.sqrt ((Module.finrank ℝ E : ℝ) ^ (s + 3)) * B := by
        rw [hcard_eq, Real.sqrt_mul (by positivity), Real.sqrt_sq hBnn]
    _ ≤ Real.sqrt ((Module.finrank ℝ E : ℝ) ^ (s + 3)) *
          (((s : ℝ) * CA2 + (3 * (s : ℝ) + 1) * CA1 + (2 * (s : ℝ) + 1) * NAb) *
            (NS + N1 + N2)) :=
        mul_le_mul_of_nonneg_left hstep (Real.sqrt_nonneg _)
    _ ≤ max 0 (Real.sqrt ((Module.finrank ℝ E : ℝ) ^ (s + 3)) *
          ((s : ℝ) * CA2 + (3 * (s : ℝ) + 1) * CA1 + (2 * (s : ℝ) + 1) * NAb)) *
          (NS + N1 + N2) := by
        rw [← mul_assoc]
        exact mul_le_mul_of_nonneg_right (le_max_right 0 _)
          (add_nonneg (add_nonneg hNSnn hN1nn) hN2nn)

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

**PROVED sorry-free (session 14).**  The full a=2 fibre assembly is discharged from committed
pieces plus the (now proved) bridge:
`covStep g₂ (covStep g₂ (diffStep g₁ g₂ s S))` splits, by `diffStep_leibniz` (applied to `S`) and
`covStep_add`, into
`covStep g₂ (diffStep g₁ g₂ (s+1) (covStep g₂ s S))` (the a=1 base-Leibniz jet of `∇₂S`, bounded by the
committed `covStepDiff_of_jets` at level `s+1`) plus `∇₂(mixedComm S)` (the a=2 mixed commutator,
bounded by `covStepDiff2_mixedComm_le` through the full eval identity `covStep2_mixedComm_eval`).
The two fibre norms combine by the triangle inequality `sqrt_normSq0S_add_le`; the constant is
`max 0 (K₁ + C_bridge)`, uniform in `S, x`.  A downstream `hAcc`-facing consumer reads
`Racc 2 := C₂`, `hRnn 2 := ·.1` directly. -/
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
  classical
  haveI : IsManifold I 1 M :=
    IsManifold.of_le (I := I) (M := M) (n := ∞) (by decide : (1 : WithTop ℕ∞) ≤ ∞)
  haveI : IsManifold I (1 + 1) M :=
    IsManifold.of_le (I := I) (M := M) (n := ∞) (by decide : ((1 : WithTop ℕ∞) + 1) ≤ ∞)
  obtain ⟨Cbr, hCbr_nn, hCbr⟩ :=
    covStepDiff2_mixedComm_le (I := I) g₁ g₂ s hEq hJet1 hJet2 hJet3
  -- The committed-atom constant of `covStepDiff_of_jets` at level `s+1`.
  set K1 : ℝ := ((s + 1 : ℕ) : ℝ) * Real.sqrt ((Module.finrank ℝ E : ℝ) ^ (s + 3)) *
    (3 / 2 * Λ ^ 4 * (Λ'' + Λ * Λ' ^ 2) + 3 / 2 * (Real.sqrt (Λ ^ 3) * Λ')) with hK1def
  refine ⟨max 0 (K1 + Cbr), le_max_left _ _, ?_⟩
  intro S x hx
  -- Λ-nonnegativity at `x ∈ K` and nonnegativity of `K1`.
  have hLnn : (0 : ℝ) ≤ Λ := le_trans zero_le_one hEq.1
  have hL'nn : (0 : ℝ) ≤ Λ' := le_trans (Real.sqrt_nonneg _) (hJet1 x hx)
  have hL''nn : (0 : ℝ) ≤ Λ'' := le_trans (Real.sqrt_nonneg _) (hJet2 x hx)
  have hK1nn : 0 ≤ K1 := by
    have hP : 0 ≤ 3 / 2 * Λ ^ 4 * (Λ'' + Λ * Λ' ^ 2) + 3 / 2 * (Real.sqrt (Λ ^ 3) * Λ') := by
      have h1 : 0 ≤ Λ ^ 4 := by positivity
      nlinarith [hL''nn, hL'nn, hLnn, h1, mul_nonneg hLnn (sq_nonneg Λ'),
        mul_nonneg (Real.sqrt_nonneg (Λ ^ 3)) hL'nn]
    rw [hK1def]
    exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Real.sqrt_nonneg _)) hP
  -- Operator split: `∇₂²(A⋆S) = piece1 + piece2` (a=1 jet of `∇₂S` plus the mixed commutator).
  have hop : covStep (I := I) g₂ (s + 2)
        (covStep (I := I) g₂ (s + 1) (diffStep (I := I) g₁ g₂ s S))
      = covStep (I := I) g₂ (s + 2)
          (diffStep (I := I) g₁ g₂ (s + 1) (covStep (I := I) g₂ s S))
        + covStep (I := I) g₂ (s + 2)
          (covStep (I := I) g₂ (s + 1) (covStep (I := I) g₁ s S)
            - covStep (I := I) g₁ (s + 1) (covStep (I := I) g₂ s S)) := by
    rw [diffStep_leibniz (I := I) g₁ g₂ s S, covStep_add]
  have hFx : (covStep (I := I) g₂ (s + 2)
        (covStep (I := I) g₂ (s + 1) (diffStep (I := I) g₁ g₂ s S))) x
      = (covStep (I := I) g₂ (s + 2)
          (diffStep (I := I) g₁ g₂ (s + 1) (covStep (I := I) g₂ s S))) x
        + (covStep (I := I) g₂ (s + 2)
          (covStep (I := I) g₂ (s + 1) (covStep (I := I) g₁ s S)
            - covStep (I := I) g₁ (s + 1) (covStep (I := I) g₂ s S))) x := by
    rw [hop]; rfl
  -- `g₂`-orthonormal basis at `x` for the fibre triangle inequality.
  obtain ⟨basis, hON⟩ :=
    DifferentialGeometry.Integral.Connection.exists_gOrthonormalBasis (I := I) g₂ x
  have hinv : MetricInverseInBasis_gen (I := I) g₂ x basis
      (identityInvMetric (Idx := Fin (Module.finrank Real (TangentSpace I x)))) := by
    intro i j; constructor <;> simp [identityInvMetric, diagonalInvMetric, hON]
  -- Committed a=1 jet bound on `piece1` (`covStepDiff_of_jets` at level `s+1`, `S := ∇₂S`).
  have hp1 := DifferentialGeometry.PDE.RicciFlow.covStepDiff_of_jets (I := I) g₁ g₂ (s + 1)
    (covStep (I := I) g₂ s S) x hEq hJet1 hJet2 hJet1' hx
  simp only [show s + 1 + 2 = s + 3 from rfl, ← hK1def] at hp1
  -- Bridge bound on `piece2`.
  have hp2 := hCbr S x hx
  -- Assemble by the triangle inequality.
  set a : ℝ := Real.sqrt (normSq0S (I := I) g₂ x s (S x)) with hadef
  set b : ℝ := Real.sqrt (normSq0S (I := I) g₂ x (s + 1) (covStep (I := I) g₂ s S x)) with hbdef
  set c : ℝ := Real.sqrt (normSq0S (I := I) g₂ x (s + 2)
    (covStep (I := I) g₂ (s + 1) (covStep (I := I) g₂ s S) x)) with hcdef
  have ha : 0 ≤ a := Real.sqrt_nonneg _
  have hb : 0 ≤ b := Real.sqrt_nonneg _
  have hc : 0 ≤ c := Real.sqrt_nonneg _
  rw [hFx]
  refine le_trans (sqrt_normSq0S_add_le (I := I) g₂ _ _ basis hinv) ?_
  refine le_trans (add_le_add hp1 hp2) ?_
  nlinarith [mul_nonneg hK1nn ha, mul_nonneg hCbr_nn hc,
    mul_nonneg (sub_nonneg.mpr (le_max_right 0 (K1 + Cbr)))
      (add_nonneg (add_nonneg ha hb) hc), ha, hb, hc, hK1nn, hCbr_nn]

end HCGCompactness
end DifferentialGeometry

end
