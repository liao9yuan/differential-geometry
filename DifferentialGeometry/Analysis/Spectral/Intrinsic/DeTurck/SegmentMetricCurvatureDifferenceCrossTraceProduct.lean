import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.SegmentMetricCurvatureDifferenceOpDecomposition
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.LoweredConnectionDifferenceCovariantDerivative
import DifferentialGeometry.Geometry.Connection.ConnectionDifferenceFieldJets
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.DeTurckCartanRfnsBilinearProduct
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.CometricDoubleTraceField

/-! # The Cross section as a cometric double-double-trace of a lowered connection-difference product

For a closed (compact, boundaryless) smooth Riemannian manifold `(M, g₀)` modelled on a real
inner-product space `E`, this file lifts the **pointwise** order-zero Cross fibre identity
`ricciDiffQuad_modelTrace_eq_crossEndoTrace`
(`SegmentMetricCurvatureDifferenceOpDecomposition.lean`) — which re-expresses the model-basis trace of
the quadratic `connDiffField ∘ connDiffField` summand as the difference of the two cross-endomorphism
traces — to a **section-level** identity: the genuine quadratic Cross section `crossSection g₀ g₁ g₂`
(a `SmoothCcTensor g₀ 0 2`) is a `g₀`-cometric **double** trace, applied **twice**
(`(0, 6) → (0, 4) → (0, 2)`), of a fixed slot-permutation of the bare fibrewise model tensor-product
**difference** of the two endpoints' `g₀`-lowered connection differences.

## The structural bridge SUB2 consumes

`crossSection`'s fibre value is `-2` times the model-basis trace of the antisymmetrised
connection-difference∧connection-difference summand difference
`ricciDiffQuadSummand g₀ g₁ − ricciDiffQuadSummand g₀ g₂`
(`ricciNeg2SectionDiffCrossEval`, `crossSection_toModel_apply`).  By the pointwise model-trace bridge
that summand's trace is `tr(crossEndoTerm1 gₖ) − tr(crossEndoTerm2 gₖ)` per metric arm
(`ricciDiffQuad_modelTrace_eq_crossEndoTrace`), where
`crossEndoTermᵢ gₖ` are the two `connDiffField gₖ g₀ ∘ connDiffField gₖ g₀` compositions.  Each
canonical endomorphism trace is, by the inverse-metric sharp duality `inverseMetricSharpFib_inner`
(`⟨♯ b^k, u⟩_{g₀} = (finBasis).repr u k`), a `g₀`-cometric double contraction of two slots of the bare
product `loweredConnDiffSection gₖ g₀ ⊗ loweredConnDiffSection gₖ g₀` (the `(0, 6)`-section whose fibre
is `⟨D_k b₁ a₁, c₁⟩ · ⟨D_k b₂ a₂, c₂⟩`): the composition `D_k ∘ D_k` binds the *output* index of the
inner factor against an *input* index of the outer factor, and the trace binds the *output* index of
the outer factor against its remaining input index — exactly **two** `g₀⁻¹` contractions.  Placing the
contracted slot-pairs into the two leading double-trace positions through a fixed `Fin 6` permutation,
the two endomorphism traces become two `(0, 6) → (0, 2)` cometric double-double-traces of the two
slot-permutations `crossTracePerm1`, `crossTracePerm2` of the product.

The two-arm (over `g₁`, `g₂`) bilinear difference collapses the per-metric products onto the bare
cross-product **difference** `crossProductDiff g₀ g₁ g₂ := bareProd g₀ 3 3 L₁ L₁ − bareProd g₀ 3 3
L₂ L₂` (`L_k := loweredConnDiffSection gₖ g₀`), the carrier on which the quadratic-engine diagonal
product grid `RfnsBilinearProduct.exists_rfns_iteratedCovGrad_prod_diagGrid_le` fires.  The headline
`crossSection_eq_cometricDoubleDoubleTrace_loweredProductDiff` exhibits

```
crossSection g₀ g₁ g₂ = (-2 : ℝ) • ( DDtr(perm crossTracePerm1 crossProductDiff)
                                       − DDtr(perm crossTracePerm2 crossProductDiff) ),
```

where `DDtr := appCc (cometricDoubleTraceField g₀ 2) ∘ appCc (cometricDoubleTraceField g₀ 4)` is the
twice-applied `g₀`-cometric double trace.  This is the curvature-half analogue of the gauge-half
quadratic-trace carriers in `DeTurckCartanQuadraticTraceProduct.lean`, and the order-zero Cross
companion of the once-differentiated linear identity
`linearSection_eq_ricciModelTrace42_loweredConnDiffSub`
(`SegmentMetricCurvatureDifferenceCovJet.lean`).

**Non-vacuity.**  At `g₁ = g₂` the lowered connection differences coincide (`L₁ = L₂`), so the bare
cross-product difference vanishes (`crossProductDiff_self`) and the double-double-trace of `0` is `0`
(`crossSection_self_toModel` matches `0 = -2 • (0 − 0)`); the identity is degenerate-correct.  NO free
quantifier dropped (the right-hand side depends on exactly `g₀, g₁, g₂`, the same as the left), NO
value-bounded operator shape, NO `toHs` mass, NO spectral-nonlinearity, NO Weyl dependence. -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

open Bundle Manifold Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff BigOperators

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow
namespace IntrinsicSpectral
namespace DeTurck

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

/-- **The bare cross-product difference of the two endpoints' lowered connection differences.**  The
bare fibrewise model tensor-product **difference**
`bareProd g₀ 3 3 L₁ L₁ − bareProd g₀ 3 3 L₂ L₂` with `L_k := loweredConnDiffSection gₖ g₀`, a
`(0, 6)`-section.  The genuine non-vacuous quadratic carrier of the order-zero Cross part: each
single-metric arm `bareProd L_k L_k` is the bare product whose fibre is the product of two lowered
connection-difference pairings, and the two-arm difference carries the connection-difference
**difference** `L₁ − L₂` against the endpoints.  Frame-free (the tensor-product map carries no
metric).  **Vanishes at `g₁ = g₂`** (`L₁ = L₂`, so it is `bareProd L₂ L₂ − bareProd L₂ L₂ = 0`,
`crossProductDiff_self`). -/
def crossProductDiff (g₀ g₁ g₂ : SmoothRiemannianMetric I M) :
    Integral.L2.SmoothCcTensor g₀ 0 6 :=
  Integral.Connection.bareProd (I := I) g₀ 3 3 (a := 0) (b := 0)
      (DeTurck.loweredConnDiffSection (I := I) g₁ g₀)
      (DeTurck.loweredConnDiffSection (I := I) g₁ g₀)
    - Integral.Connection.bareProd (I := I) g₀ 3 3 (a := 0) (b := 0)
      (DeTurck.loweredConnDiffSection (I := I) g₂ g₀)
      (DeTurck.loweredConnDiffSection (I := I) g₂ g₀)

set_option linter.unusedSectionVars false in
/-- **The bare cross-product difference vanishes when the metrics coincide.**  At `g₁ = g₂` the two
single-metric arms are identical, so the difference is `0`.  The non-vacuity certificate (it genuinely
tracks the connection-difference difference, not a constant). -/
theorem crossProductDiff_self (g₀ g : SmoothRiemannianMetric I M) :
    crossProductDiff (I := I) g₀ g g = 0 := by
  rw [crossProductDiff, sub_self]

/-- **The twice-applied `g₀`-cometric double trace `(0, 6) → (0, 4) → (0, 2)`.**  The double cometric
trace `appCc (cometricDoubleTraceField g₀ 2)` of the double cometric trace
`appCc (cometricDoubleTraceField g₀ 4)` of a `(0, 6)`-section, each application contracting the two
leading covariant slots against the cometric `g₀⁻¹`.  A `(0, 2)`-section. -/
def cometricDoubleDoubleTrace (g₀ : SmoothRiemannianMetric I M)
    (P : Integral.L2.SmoothCcTensor g₀ 0 6) : Integral.L2.SmoothCcTensor g₀ 0 2 :=
  Integral.Connection.appCc (I := I) (M := M) g₀ 4 2 (cometricDoubleTraceField (I := I) g₀ 2)
    (Integral.Connection.appCc (I := I) (M := M) g₀ 6 4 (cometricDoubleTraceField (I := I) g₀ 4) P)

set_option linter.unusedSectionVars false in
/-- **The twice-applied double trace is `ℝ`-additive over a section difference.**  Both `g₀`-cometric
traces are `ℝ`-linear (operator-field action, additive in the contracted section), so the composition
distributes over a difference.  Used to split the bare cross-product **difference** arm-by-arm. -/
theorem cometricDoubleDoubleTrace_sub (g₀ : SmoothRiemannianMetric I M)
    (P Q : Integral.L2.SmoothCcTensor g₀ 0 6) :
    cometricDoubleDoubleTrace (I := I) g₀ (P - Q) =
      cometricDoubleDoubleTrace (I := I) g₀ P - cometricDoubleDoubleTrace (I := I) g₀ Q := by
  have hinner : Integral.Connection.appCc (I := I) (M := M) g₀ 6 4
        (cometricDoubleTraceField (I := I) g₀ 4) (P - Q) =
      Integral.Connection.appCc (I := I) (M := M) g₀ 6 4
          (cometricDoubleTraceField (I := I) g₀ 4) P
        - Integral.Connection.appCc (I := I) (M := M) g₀ 6 4
          (cometricDoubleTraceField (I := I) g₀ 4) Q := by
    rw [sub_eq_add_neg, sub_eq_add_neg,
      ← Integral.Connection.appCcRS_zero_eq_appCc (I := I) (M := M) g₀ 6 4
        (cometricDoubleTraceField (I := I) g₀ 4) (P + -Q),
      Integral.Connection.appCcRS_add_right (I := I) (M := M) g₀ 0 6 4,
      show (-Q) = (-1 : ℝ) • Q by rw [neg_one_smul],
      Integral.Connection.appCcRS_smul_right, neg_one_smul,
      Integral.Connection.appCcRS_zero_eq_appCc, Integral.Connection.appCcRS_zero_eq_appCc]
  rw [cometricDoubleDoubleTrace, cometricDoubleDoubleTrace, cometricDoubleDoubleTrace, hinner,
    sub_eq_add_neg, sub_eq_add_neg,
    ← Integral.Connection.appCcRS_zero_eq_appCc (I := I) (M := M) g₀ 4 2
      (cometricDoubleTraceField (I := I) g₀ 2) _,
    Integral.Connection.appCcRS_add_right (I := I) (M := M) g₀ 0 4 2,
    show (-(Integral.Connection.appCc (I := I) (M := M) g₀ 6 4
        (cometricDoubleTraceField (I := I) g₀ 4) Q)) =
      (-1 : ℝ) • (Integral.Connection.appCc (I := I) (M := M) g₀ 6 4
        (cometricDoubleTraceField (I := I) g₀ 4) Q) by rw [neg_one_smul],
    Integral.Connection.appCcRS_smul_right, neg_one_smul,
    Integral.Connection.appCcRS_zero_eq_appCc, Integral.Connection.appCcRS_zero_eq_appCc]

set_option linter.unusedSectionVars false in
/-- **The unit-evaluated model value of the twice-applied `g₀`-cometric double trace.**  Reading the
`(0, 2)`-section `cometricDoubleDoubleTrace g₀ P` at the unit `(0, 0)`-tensor and a tangent pair
`(v, w)` is the nested model cometric double trace of `P`'s unit model:
```
toModel((DDtr g₀ P).toSection x unit) ![v, w]
  = ∑_{j} ∑_{k} toModel(P.toSection x unit)
      (♯b^k, b_k, ♯b^j, b_j, v, w),
```
with `b_k := finBasis k`, `b^k := cDualBasis k`, `♯ := cometricLmodel g₀ x` (the outer trace sums over
`j` and lands its pair at the slots freed by the inner trace, which runs first and sums over `k`; so
the inner `k`-pair leads, the outer `j`-pair follows, then the free `(v, w)`).  The unit-evaluated form
of the composed operator-field action, read through `appCc_toSection`, `cometricDoubleTraceField_toSection`,
`cometricDoubleTraceFib_toModel`, and `modelDoubleTrace_apply` applied twice (the reflexive rank casts
are identities). -/
theorem cometricDoubleDoubleTrace_unitModel_apply (g₀ : SmoothRiemannianMetric I M)
    (P : Integral.L2.SmoothCcTensor g₀ 0 6) (x : M) (v w : TangentSpace I x) :
    Tensor0SBundle.Tensor0SSpace.toModel
        ((cometricDoubleDoubleTrace (I := I) g₀ P).toSection x
          (ContinuousMultilinearMap.constOfIsEmpty ℝ
            (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ))) ![v, w] =
      ∑ j : Fin (Module.finrank ℝ E), ∑ k : Fin (Module.finrank ℝ E),
        Tensor0SBundle.Tensor0SSpace.toModel
          ((P.toSection x) (ContinuousMultilinearMap.constOfIsEmpty ℝ
            (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ)))
          (Fin.cons (cometricLmodel (I := I) g₀ x
              (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                ((Module.finBasis ℝ E).cDualBasis k)))
            (Fin.cons ((Module.finBasis ℝ E) k)
              (Fin.cons (cometricLmodel (I := I) g₀ x
                  (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                    ((Module.finBasis ℝ E).cDualBasis j)))
                (Fin.cons ((Module.finBasis ℝ E) j) ![(v : E), (w : E)])))) := by
  classical
  -- Unfold the outer trace at the unit: `(DDtr P) unit = field₂ (innerTrace P unit)`.
  rw [cometricDoubleDoubleTrace, Integral.Connection.appCc_toSection,
    ContinuousLinearMap.comp_apply, cometricDoubleTraceField_toSection,
    cometricDoubleTraceFib_toModel,
    modelDoubleTrace_apply (E := E) 2 (cometricLmodel (I := I) g₀ x)
      (Tensor0SBundle.Tensor0SSpace.toModel
        ((Integral.Connection.appCc (I := I) (M := M) g₀ 6 4
            (cometricDoubleTraceField (I := I) g₀ 4) P).toSection x
          (ContinuousMultilinearMap.constOfIsEmpty ℝ
            (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ)))) ![(v : E), (w : E)]]
  -- Per outer index `j`, read the inner trace at the unit as a model double trace of `P`'s unit model.
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Integral.Connection.appCc_toSection, ContinuousLinearMap.comp_apply,
    cometricDoubleTraceField_toSection, cometricDoubleTraceFib_toModel,
    modelDoubleTrace_apply (E := E) (2 + 2) (cometricLmodel (I := I) g₀ x)
      (Tensor0SBundle.Tensor0SSpace.toModel
        ((P.toSection x) (ContinuousMultilinearMap.constOfIsEmpty ℝ
          (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ))))
      (Fin.cons (cometricLmodel (I := I) g₀ x
          (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
            ((Module.finBasis ℝ E).cDualBasis j)))
        (Fin.cons ((Module.finBasis ℝ E) j) ![(v : E), (w : E)]))]

/-! ### Fibre-algebra collapse helpers (sharp duality)

The two cometric contractions of the double-double-trace collapse against the connection-difference
factors through the inverse-metric sharp duality `⟨♯ b^k, u⟩_{g₀} = (finBasis).repr u k`
(`cometricLmodel_dualBasis_inner`). -/

set_option linter.unusedSectionVars false in
/-- **The cometric-raised dual-basis covector pairs as the coordinate functional** (file-local replica
of the same-named private lemma in `CometricDoubleTraceField.lean` / `LoweredConnectionDifference…`).
`g₀(♯ b^k, u) = (finBasis).repr u k`, the inverse-metric sharp duality on the model dual basis,
through `inverseMetricSharpFib_inner` and `model_covectorOfCLM`. -/
private theorem cometricLmodel_dualBasis_inner (g₀ : SmoothRiemannianMetric I M) (x : M)
    (k : Fin (Module.finrank ℝ E)) (u : TangentSpace I x) :
    g₀.inner x (cometricLmodel (I := I) g₀ x
        (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
          ((Module.finBasis ℝ E).cDualBasis k))) u =
      (Module.finBasis ℝ E).repr (u : E) k := by
  have h1 : cometricLmodel (I := I) g₀ x
        (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
          ((Module.finBasis ℝ E).cDualBasis k)) =
      inverseMetricSharpFib (I := I) g₀ x
        ((Tensor0SBundle.tensor0SSpace_continuousLinearEquiv (𝕜 := ℝ) (I := I) 1 x).symm
          (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
            ((Module.finBasis ℝ E).cDualBasis k))) := rfl
  rw [h1, inverseMetricSharpFib_inner (I := I) g₀ x _ u, cotangentToDualLinear_apply,
    cotangentToDual_apply]
  have h2 : (((Tensor0SBundle.tensor0SSpace_continuousLinearEquiv (𝕜 := ℝ) (I := I) 1 x).symm
        (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
          ((Module.finBasis ℝ E).cDualBasis k))) (fun _ : Fin 1 => u) : ℝ) =
      Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
        ((Module.finBasis ℝ E).cDualBasis k) (fun _ : Fin 1 => (u : E)) := rfl
  rw [h2, Tensor0SBundle.model_covectorOfCLM_apply]
  rw [show ((Module.finBasis ℝ E).cDualBasis k) =
      LinearMap.toContinuousLinearMap ((Module.finBasis ℝ E).coord k) from by
    rw [Module.Basis.cDualBasis, Module.Basis.map_apply]
    congr 1
    exact congrFun (Module.Basis.coe_dualBasis (Module.finBasis ℝ E)) k]
  rw [LinearMap.coe_toContinuousLinearMap', Module.Basis.coord_apply]

set_option linter.unusedSectionVars false in
/-- **Nondegeneracy of the metric (left-extensionality).**  Two tangent vectors with equal `g₀`-pairing
against every test vector are equal: the metric is positive definite (`g₀.pos`), so a nonzero
difference would pair positively with itself. -/
private theorem inner_ext_left (g₀ : SmoothRiemannianMetric I M) (x : M) {a b : TangentSpace I x}
    (h : ∀ u : TangentSpace I x, g₀.inner x a u = g₀.inner x b u) : a = b := by
  by_contra hne
  have hd : a - b ≠ 0 := sub_ne_zero.mpr hne
  have hpos : 0 < g₀.inner x (a - b) (a - b) := g₀.pos x (a - b) hd
  have hexpand : g₀.inner x (a - b) (a - b) =
      g₀.inner x a (a - b) - g₀.inner x b (a - b) := by
    have := (g₀.inner x).map_sub a b
    have happ := congrArg (fun (φ : TangentSpace I x →L[ℝ] ℝ) => φ (a - b)) this
    simpa only [ContinuousLinearMap.sub_apply] using happ
  have hzero : g₀.inner x (a - b) (a - b) = 0 := by
    rw [hexpand, h (a - b)]; ring
  rw [hzero] at hpos
  exact lt_irrefl 0 hpos

set_option linter.unusedSectionVars false in
/-- **The sharp-pair reconstruction of a tangent vector.**  Summing the `g₀`-pairings of a vector `Y`
against the model basis, weighted by the cometric-raised dual basis, reconstructs `Y`:
`∑_k g₀(Y, b_k) · ♯ b^k = Y` (`b_k := finBasis k`, `b^k := cDualBasis k`, `♯ := cometricLmodel g₀ x`).
Proved by the sharp duality `⟨♯ b^k, u⟩ = repr(u)_k` paired against an arbitrary `u`. -/
private theorem sum_inner_basis_smul_sharp_eq (g₀ : SmoothRiemannianMetric I M) (x : M)
    (Y : TangentSpace I x) :
    ∑ k : Fin (Module.finrank ℝ E),
        g₀.inner x Y ((Module.finBasis ℝ E) k) •
          cometricLmodel (I := I) g₀ x
            (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
              ((Module.finBasis ℝ E).cDualBasis k)) = Y := by
  classical
  -- It suffices to check the `g₀`-pairing against an arbitrary `u` (the metric is nondegenerate).
  refine inner_ext_left (I := I) g₀ x (fun u => ?_)
  rw [map_sum]
  simp only [ContinuousLinearMap.coe_sum', Finset.sum_apply, map_smul]
  have hsharp : ∀ k : Fin (Module.finrank ℝ E),
      g₀.inner x (cometricLmodel (I := I) g₀ x
          (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
            ((Module.finBasis ℝ E).cDualBasis k))) u =
        (Module.finBasis ℝ E).repr (u : E) k :=
    fun k => cometricLmodel_dualBasis_inner (I := I) g₀ x k u
  calc ∑ k : Fin (Module.finrank ℝ E),
        g₀.inner x Y ((Module.finBasis ℝ E) k) *
          g₀.inner x (cometricLmodel (I := I) g₀ x
            (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
              ((Module.finBasis ℝ E).cDualBasis k))) u
      = ∑ k : Fin (Module.finrank ℝ E),
          g₀.inner x Y (((Module.finBasis ℝ E).repr (u : E) k) • (Module.finBasis ℝ E) k) := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [hsharp k, map_smul, smul_eq_mul]; ring
    _ = g₀.inner x Y (∑ k : Fin (Module.finrank ℝ E),
          ((Module.finBasis ℝ E).repr (u : E) k) • (Module.finBasis ℝ E) k) := by
        rw [map_sum]
    _ = g₀.inner x Y u := by
        rw [(Module.finBasis ℝ E).sum_repr (u : E)]

set_option linter.unusedSectionVars false in
/-- **The sharp-pair trace of a tangent endomorphism.**  The diagonal `g₀`-pairing of an endomorphism
`F` against the dual pair `(F b_k, ♯ b^k)` is the basis-free trace of `F`:
`∑_k g₀(F b_k, ♯ b^k) = tr F`.  The dual pair `♯ b^k` carries the sharp duality
`⟨♯ b^k, u⟩ = repr(u)_k`, so this is `sum_inner_dualPair_apply_eq_sum_chartBasis_repr` flipped, read
back to the basis-free trace `trace_eq_sum_basis_repr`. -/
private theorem sum_inner_apply_sharp_eq_trace (g₀ : SmoothRiemannianMetric I M) (x : M)
    (F : TangentSpace I x →L[ℝ] TangentSpace I x) :
    ∑ k : Fin (Module.finrank ℝ E),
        g₀.inner x (F ((Module.finBasis ℝ E) k))
          (cometricLmodel (I := I) g₀ x
            (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
              ((Module.finBasis ℝ E).cDualBasis k))) =
      LinearMap.trace ℝ (TangentSpace I x) (F : TangentSpace I x →ₗ[ℝ] TangentSpace I x) := by
  classical
  have hP : ∀ (k : Fin (Module.finrank ℝ E)) (u : TangentSpace I x),
      g₀.inner x (cometricLmodel (I := I) g₀ x
          (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
            ((Module.finBasis ℝ E).cDualBasis k))) u =
        (Module.finBasis ℝ E).repr (u : E) k :=
    fun k u => cometricLmodel_dualBasis_inner (I := I) g₀ x k u
  -- Flip each summand `g₀(F b_k, ♯ b^k) = g₀(♯ b^k, F b_k)`, then reduce to the basis trace.
  calc ∑ k : Fin (Module.finrank ℝ E),
        g₀.inner x (F ((Module.finBasis ℝ E) k))
          (cometricLmodel (I := I) g₀ x
            (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
              ((Module.finBasis ℝ E).cDualBasis k)))
      = ∑ k : Fin (Module.finrank ℝ E),
          (Module.finBasis ℝ E).repr (F ((Module.finBasis ℝ E) k) : E) k := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [g₀.symm x (F ((Module.finBasis ℝ E) k)) _, hP k]
    _ = LinearMap.trace ℝ (TangentSpace I x) (F : TangentSpace I x →ₗ[ℝ] TangentSpace I x) :=
        (Integral.Connection.trace_eq_sum_basis_repr (I := I) (M := M) x
          (Module.finBasis ℝ E) F).symm

/-! ### The bare-product unit read and the slot-permutation read patterns -/

set_option linter.unusedSectionVars false in
/-- **The unit value of `bareProd g₀ 3 3 S T`** reads the model product of the two factor units.  The
rank cast `castRankCc_db g₀ 0 (h : 6 = 6)` is reflexive (both ranks reduce to `6`), so the rank-cast
bare product evaluates exactly as `bareTensorProdSection`; through `bareTensorProdSection_unitModel`
and `modelProduct_apply` the value on `y` is `bareUnitModel S (y ∘ castAdd) · bareUnitModel T
(y ∘ natAdd)`. -/
private theorem bareProd33_unitModel_apply (g₀ : SmoothRiemannianMetric I M)
    (S T : Integral.L2.SmoothCcTensor g₀ 0 3) (x : M) (y : Fin 6 → E) :
    Tensor0SBundle.Tensor0SSpace.toModel
        ((Integral.Connection.bareProd (I := I) g₀ 3 3 (a := 0) (b := 0) S T).toSection x
          (ContinuousMultilinearMap.constOfIsEmpty ℝ
            (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ))) y =
      Integral.Connection.bareUnitModel (I := I) g₀ S x (y ∘ Fin.castAdd 3) *
        Integral.Connection.bareUnitModel (I := I) g₀ T x (y ∘ Fin.natAdd 3) := by
  have hcast : (Integral.Connection.bareProd (I := I) g₀ 3 3 (a := 0) (b := 0) S T).toSection x
        (ContinuousMultilinearMap.constOfIsEmpty ℝ
          (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ)) =
      (Integral.Connection.bareTensorProdSection (I := I) g₀ S T).toSection x
        (ContinuousMultilinearMap.constOfIsEmpty ℝ
          (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ)) := rfl
  rw [hcast, Integral.Connection.bareTensorProdSection_unitModel,
    Bundle.continuousMultilinearMap.modelProduct_apply]

/-- **The first cross trace permutation** `(0 4)(1 5 2)` of `Fin 6` — image map `[4, 5, 1, 3, 0, 2]`
(`0 ↦ 4, 1 ↦ 5, 2 ↦ 1, 3 ↦ 3, 4 ↦ 0, 5 ↦ 2`).  It carries the first cross-endomorphism trace
bookkeeping: it sends the bare product's two factor blocks so that the double-double-trace's two
cometric pairs land on the `crossEndoTerm1` contraction slots. -/
def crossTracePerm1 : Equiv.Perm (Fin 6) := c[(0 : Fin 6), 4] * c[(1 : Fin 6), 5, 2]

/-- **The second cross trace permutation** `(0 3 4)(1 5 2)` of `Fin 6` — image map `[3, 5, 1, 4, 0, 2]`
(`0 ↦ 3, 1 ↦ 5, 2 ↦ 1, 3 ↦ 4, 4 ↦ 0, 5 ↦ 2`).  It carries the second cross-endomorphism trace
bookkeeping. -/
def crossTracePerm2 : Equiv.Perm (Fin 6) := c[(0 : Fin 6), 3, 4] * c[(1 : Fin 6), 5, 2]

set_option linter.unusedSectionVars false in
/-- **Reading the six-slot product tuple through `crossTracePerm1`.**  Composing
`(y₀, y₁, y₂, y₃, y₄, y₅)` along `crossTracePerm1` (image map `[4, 5, 1, 3, 0, 2]`) yields
`(y₄, y₅, y₁, y₃, y₀, y₂)` — the first cross trace pattern: the inner-`k` pair `(y₀, y₁) = (♯b^k, b_k)`
splits between the second factor's contravariant-output slot and the first factor's covariant-output
slot, likewise the outer-`j` pair `(y₂, y₃)`; the free pair `(y₄, y₅) = (v, w)` becomes the first
factor's two leading inputs. -/
private theorem consTuple6_read_crossPerm1 (y₀ y₁ y₂ y₃ y₄ y₅ : E) :
    (fun p => (Fin.cons y₀ (Fin.cons y₁ (Fin.cons y₂ (Fin.cons y₃ ![y₄, y₅]))) : Fin 6 → E)
        (crossTracePerm1 p)) =
      Fin.cons y₄ (Fin.cons y₅ (Fin.cons y₁ ![y₃, y₀, y₂])) := by
  have hp : ∀ p : Fin 6, crossTracePerm1 p = (![4, 5, 1, 3, 0, 2] : Fin 6 → Fin 6) p := by
    decide
  funext p
  rw [hp p]
  fin_cases p <;> rfl

set_option linter.unusedSectionVars false in
/-- **Reading the six-slot product tuple through `crossTracePerm2`.**  Composing
`(y₀, y₁, y₂, y₃, y₄, y₅)` along `crossTracePerm2` (image map `[3, 5, 1, 4, 0, 2]`) yields
`(y₃, y₅, y₁, y₄, y₀, y₂)` — the second cross trace pattern, carrying the `crossEndoTerm2` slot
bookkeeping. -/
private theorem consTuple6_read_crossPerm2 (y₀ y₁ y₂ y₃ y₄ y₅ : E) :
    (fun p => (Fin.cons y₀ (Fin.cons y₁ (Fin.cons y₂ (Fin.cons y₃ ![y₄, y₅]))) : Fin 6 → E)
        (crossTracePerm2 p)) =
      Fin.cons y₃ (Fin.cons y₅ (Fin.cons y₁ ![y₄, y₀, y₂])) := by
  have hp : ∀ p : Fin 6, crossTracePerm2 p = (![3, 5, 1, 4, 0, 2] : Fin 6 → Fin 6) p := by
    decide
  funext p
  rw [hp p]
  fin_cases p <;> rfl

/-! ### The per-metric cross-endomorphism trace identities -/

set_option linter.unusedSectionVars false in
/-- **The first cross-endomorphism trace as a cometric double-double-trace of the single-metric lowered
product.**  For a single metric `gₖ` (write `L := loweredConnDiffSection gₖ g₀`,
`D := connDiff gₖ g₀ x`), the fibre value at `(v, w)` of the double-double-trace of `crossTracePerm1`
of the bare product `L ⊗ L` is the canonical trace of the first cross endomorphism
`crossEndoTerm1 g₀ gₖ x v w = (u ↦ D (D w v) u)`:
```
toModel((DDtr (perm crossTracePerm1 (bareProd 3 3 L L))).toSection x unit) ![v, w]
  = tr(crossEndoTerm1 g₀ gₖ x v w).
```
The double-double-trace expands (`cometricDoubleDoubleTrace_unitModel_apply`) into the nested sum over
`(j, k)` of `P`'s unit model on `(♯b^k, b_k, ♯b^j, b_j, v, w)`; the slot permutation reads this through
`crossTracePerm1` (`consTuple6_read_crossPerm1`) onto the product `L(v, w, b_k) · L(b_j, ♯b^k, ♯b^j)`
(`bareProd33_unitModel_apply`, `loweredConnDiffSection_toModel_apply`); the inner `k`-sum reconstructs
`D w v` in the second factor's leading input (`sum_inner_basis_smul_sharp_eq`), and the outer `j`-sum is
the basis-free trace (`sum_inner_apply_sharp_eq_trace`). -/
private theorem doubleDoubleTrace_perm1_loweredProd_eq_crossEndoTerm1_trace
    (g₀ gₖ : SmoothRiemannianMetric I M) (x : M) (v w : TangentSpace I x) :
    Tensor0SBundle.Tensor0SSpace.toModel
        ((cometricDoubleDoubleTrace (I := I) g₀
            (DeTurck.permuteCcTensor (I := I) g₀ crossTracePerm1
              (Integral.Connection.bareProd (I := I) g₀ 3 3 (a := 0) (b := 0)
                (DeTurck.loweredConnDiffSection (I := I) gₖ g₀)
                (DeTurck.loweredConnDiffSection (I := I) gₖ g₀)))).toSection x
          (ContinuousMultilinearMap.constOfIsEmpty ℝ
            (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ))) ![v, w] =
      LinearMap.trace ℝ (TangentSpace I x)
        (crossEndoTerm1 (I := I) g₀ gₖ x v w : TangentSpace I x →ₗ[ℝ] TangentSpace I x) := by
  classical
  set L := DeTurck.loweredConnDiffSection (I := I) gₖ g₀ with hL
  set P := Integral.Connection.bareProd (I := I) g₀ 3 3 (a := 0) (b := 0) L L with hP
  -- Expand the double-double-trace at the unit.
  rw [cometricDoubleDoubleTrace_unitModel_apply (I := I) g₀
    (DeTurck.permuteCcTensor (I := I) g₀ crossTracePerm1 P) x v w]
  -- The permuted product's unit model reads `P`'s unit model through `crossTracePerm1`.
  have hperm : ∀ (a b c d e f : E),
      Tensor0SBundle.Tensor0SSpace.toModel
          ((DeTurck.permuteCcTensor (I := I) g₀ crossTracePerm1 P).toSection x
            (ContinuousMultilinearMap.constOfIsEmpty ℝ
              (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ)))
          ![a, b, c, d, e, f] =
        Tensor0SBundle.Tensor0SSpace.toModel
          (P.toSection x (ContinuousMultilinearMap.constOfIsEmpty ℝ
            (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ)))
          ![e, f, b, d, a, c] := by
    intro a b c d e f
    have h := DeTurck.permuteCcTensor_unitModel (I := I) g₀ crossTracePerm1 P x
    have h' : Tensor0SBundle.Tensor0SSpace.toModel
          ((DeTurck.permuteCcTensor (I := I) g₀ crossTracePerm1 P).toSection x
            (ContinuousMultilinearMap.constOfIsEmpty ℝ
              (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ))) =
        ContinuousMultilinearMap.domDomCongr crossTracePerm1
          (Tensor0SBundle.Tensor0SSpace.toModel
            (P.toSection x (ContinuousMultilinearMap.constOfIsEmpty ℝ
              (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ)))) := h
    rw [h', ContinuousMultilinearMap.domDomCongr_apply]
    congr 1
    have := consTuple6_read_crossPerm1 (E := E) a b c d e f
    simpa using this
  -- `P`'s unit model is the model product of the two `L`-unit models; each `L`-value is a `g₀`-pairing.
  have hval : ∀ (a b c d e f : E),
      Tensor0SBundle.Tensor0SSpace.toModel
          (P.toSection x (ContinuousMultilinearMap.constOfIsEmpty ℝ
            (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ))) ![a, b, c, d, e, f] =
        g₀.inner x (DeTurck.connDiff (I := I) gₖ g₀ x b a) c *
          g₀.inner x (DeTurck.connDiff (I := I) gₖ g₀ x e d) f := by
    intro a b c d e f
    rw [hP, bareProd33_unitModel_apply (I := I) g₀ L L x ![a, b, c, d, e, f]]
    have hcast : (![a, b, c, d, e, f] : Fin 6 → E) ∘ Fin.castAdd 3 = ![a, b, c] := by
      funext i; fin_cases i <;> rfl
    have hnat : (![a, b, c, d, e, f] : Fin 6 → E) ∘ Fin.natAdd 3 = ![d, e, f] := by
      funext i; fin_cases i <;> rfl
    rw [hcast, hnat, hL]
    rw [show Integral.Connection.bareUnitModel (I := I) g₀
          (DeTurck.loweredConnDiffSection (I := I) gₖ g₀) x ![a, b, c] =
        Tensor0SBundle.Tensor0SSpace.toModel
          ((DeTurck.loweredConnDiffSection (I := I) gₖ g₀).toSection x
            (ContinuousMultilinearMap.constOfIsEmpty ℝ
              (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ))) ![a, b, c] from rfl,
      show Integral.Connection.bareUnitModel (I := I) g₀
          (DeTurck.loweredConnDiffSection (I := I) gₖ g₀) x ![d, e, f] =
        Tensor0SBundle.Tensor0SSpace.toModel
          ((DeTurck.loweredConnDiffSection (I := I) gₖ g₀).toSection x
            (ContinuousMultilinearMap.constOfIsEmpty ℝ
              (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ))) ![d, e, f] from rfl,
      DeTurck.loweredConnDiffSection_toModel_apply (I := I) gₖ g₀ x a b c,
      DeTurck.loweredConnDiffSection_toModel_apply (I := I) gₖ g₀ x d e f]
  -- Combine the permutation read and the product value inside the `(j, k)` double sum.
  have hsummand : ∀ j k : Fin (Module.finrank ℝ E),
      Tensor0SBundle.Tensor0SSpace.toModel
          ((DeTurck.permuteCcTensor (I := I) g₀ crossTracePerm1 P).toSection x
            (ContinuousMultilinearMap.constOfIsEmpty ℝ
              (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ)))
          (Fin.cons (cometricLmodel (I := I) g₀ x
              (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                ((Module.finBasis ℝ E).cDualBasis k)))
            (Fin.cons ((Module.finBasis ℝ E) k)
              (Fin.cons (cometricLmodel (I := I) g₀ x
                  (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                    ((Module.finBasis ℝ E).cDualBasis j)))
                (Fin.cons ((Module.finBasis ℝ E) j) ![(v : E), (w : E)])))) =
        g₀.inner x (DeTurck.connDiff (I := I) gₖ g₀ x w v) ((Module.finBasis ℝ E) k) *
          g₀.inner x (DeTurck.connDiff (I := I) gₖ g₀ x
              (cometricLmodel (I := I) g₀ x
                (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                  ((Module.finBasis ℝ E).cDualBasis k)))
              ((Module.finBasis ℝ E) j))
            (cometricLmodel (I := I) g₀ x
              (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                ((Module.finBasis ℝ E).cDualBasis j))) := by
    intro j k
    rw [show (Fin.cons (cometricLmodel (I := I) g₀ x
            (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
              ((Module.finBasis ℝ E).cDualBasis k)))
          (Fin.cons ((Module.finBasis ℝ E) k)
            (Fin.cons (cometricLmodel (I := I) g₀ x
                (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                  ((Module.finBasis ℝ E).cDualBasis j)))
              (Fin.cons ((Module.finBasis ℝ E) j) ![(v : E), (w : E)]))) :
            Fin 6 → E) =
        ![(cometricLmodel (I := I) g₀ x
            (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
              ((Module.finBasis ℝ E).cDualBasis k))),
          ((Module.finBasis ℝ E) k),
          (cometricLmodel (I := I) g₀ x
            (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
              ((Module.finBasis ℝ E).cDualBasis j))),
          ((Module.finBasis ℝ E) j), (v : E), (w : E)] from by
        funext i; fin_cases i <;> rfl,
      hperm, hval]
  rw [Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun k _ => hsummand j k))]
  -- Collapse the inner `k`-sum: it reconstructs `connDiff w v` in the second factor's leading input.
  have hinner : ∀ j : Fin (Module.finrank ℝ E),
      ∑ k : Fin (Module.finrank ℝ E),
          g₀.inner x (DeTurck.connDiff (I := I) gₖ g₀ x w v) ((Module.finBasis ℝ E) k) *
            g₀.inner x (DeTurck.connDiff (I := I) gₖ g₀ x
                (cometricLmodel (I := I) g₀ x
                  (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                    ((Module.finBasis ℝ E).cDualBasis k)))
                ((Module.finBasis ℝ E) j))
              (cometricLmodel (I := I) g₀ x
                (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                  ((Module.finBasis ℝ E).cDualBasis j))) =
        g₀.inner x (DeTurck.connDiff (I := I) gₖ g₀ x
            (DeTurck.connDiff (I := I) gₖ g₀ x w v) ((Module.finBasis ℝ E) j))
          (cometricLmodel (I := I) g₀ x
            (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
              ((Module.finBasis ℝ E).cDualBasis j))) := by
    intro j
    -- Expand the RHS's inner `connDiff w v` as `∑_k ⟨connDiff w v, b_k⟩ • ♯b^k`, then push linearity.
    rw [show DeTurck.connDiff (I := I) gₖ g₀ x
            (DeTurck.connDiff (I := I) gₖ g₀ x w v) ((Module.finBasis ℝ E) j) =
          DeTurck.connDiff (I := I) gₖ g₀ x
            (∑ k : Fin (Module.finrank ℝ E),
              g₀.inner x (DeTurck.connDiff (I := I) gₖ g₀ x w v) ((Module.finBasis ℝ E) k) •
                cometricLmodel (I := I) g₀ x
                  (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                    ((Module.finBasis ℝ E).cDualBasis k)))
            ((Module.finBasis ℝ E) j) from by
        rw [sum_inner_basis_smul_sharp_eq (I := I) g₀ x
          (DeTurck.connDiff (I := I) gₖ g₀ x w v)]]
    rw [_root_.map_sum (DeTurck.connDiff (I := I) gₖ g₀ x),
      ContinuousLinearMap.sum_apply,
      _root_.map_sum (g₀.inner x), ContinuousLinearMap.coe_sum',
      Finset.sum_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smul, ContinuousLinearMap.smul_apply, map_smul, ContinuousLinearMap.smul_apply,
      smul_eq_mul]
  rw [Finset.sum_congr rfl (fun j _ => hinner j)]
  -- Identify the second-factor leading input as `crossEndoTerm1`, then read the outer `j`-sum as a trace.
  have hcross : ∀ j : Fin (Module.finrank ℝ E),
      DeTurck.connDiff (I := I) gₖ g₀ x
          (DeTurck.connDiff (I := I) gₖ g₀ x w v) ((Module.finBasis ℝ E) j) =
        crossEndoTerm1 (I := I) g₀ gₖ x v w ((Module.finBasis ℝ E) j) := by
    intro j
    simp only [crossEndoTerm1_apply, DeTurck.connDiffField_apply]
  rw [Finset.sum_congr rfl (fun j _ => by rw [hcross j])]
  exact sum_inner_apply_sharp_eq_trace (I := I) g₀ x (crossEndoTerm1 (I := I) g₀ gₖ x v w)

set_option linter.unusedSectionVars false in
/-- **The second cross-endomorphism trace as a cometric double-double-trace of the single-metric lowered
product.**  For a single metric `gₖ` (write `L := loweredConnDiffSection gₖ g₀`,
`D := connDiff gₖ g₀ x`), the fibre value at `(v, w)` of the double-double-trace of `crossTracePerm2`
of the bare product `L ⊗ L` is the canonical trace of the second cross endomorphism
`crossEndoTerm2 g₀ gₖ x v w = (u ↦ D (D w u) v)`:
```
toModel((DDtr (perm crossTracePerm2 (bareProd 3 3 L L))).toSection x unit) ![v, w]
  = tr(crossEndoTerm2 g₀ gₖ x v w).
```
Identical reduction to `doubleDoubleTrace_perm1_loweredProd_eq_crossEndoTerm1_trace` through the second
read pattern `consTuple6_read_crossPerm2` (which lands the trace index `b_j` inside the first factor's
input slot), the inner `k`-sum reconstruction (`sum_inner_basis_smul_sharp_eq`), and the basis-free
trace (`sum_inner_apply_sharp_eq_trace`). -/
private theorem doubleDoubleTrace_perm2_loweredProd_eq_crossEndoTerm2_trace
    (g₀ gₖ : SmoothRiemannianMetric I M) (x : M) (v w : TangentSpace I x) :
    Tensor0SBundle.Tensor0SSpace.toModel
        ((cometricDoubleDoubleTrace (I := I) g₀
            (DeTurck.permuteCcTensor (I := I) g₀ crossTracePerm2
              (Integral.Connection.bareProd (I := I) g₀ 3 3 (a := 0) (b := 0)
                (DeTurck.loweredConnDiffSection (I := I) gₖ g₀)
                (DeTurck.loweredConnDiffSection (I := I) gₖ g₀)))).toSection x
          (ContinuousMultilinearMap.constOfIsEmpty ℝ
            (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ))) ![v, w] =
      LinearMap.trace ℝ (TangentSpace I x)
        (crossEndoTerm2 (I := I) g₀ gₖ x v w : TangentSpace I x →ₗ[ℝ] TangentSpace I x) := by
  classical
  set L := DeTurck.loweredConnDiffSection (I := I) gₖ g₀ with hL
  set P := Integral.Connection.bareProd (I := I) g₀ 3 3 (a := 0) (b := 0) L L with hP
  rw [cometricDoubleDoubleTrace_unitModel_apply (I := I) g₀
    (DeTurck.permuteCcTensor (I := I) g₀ crossTracePerm2 P) x v w]
  have hperm : ∀ (a b c d e f : E),
      Tensor0SBundle.Tensor0SSpace.toModel
          ((DeTurck.permuteCcTensor (I := I) g₀ crossTracePerm2 P).toSection x
            (ContinuousMultilinearMap.constOfIsEmpty ℝ
              (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ)))
          ![a, b, c, d, e, f] =
        Tensor0SBundle.Tensor0SSpace.toModel
          (P.toSection x (ContinuousMultilinearMap.constOfIsEmpty ℝ
            (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ)))
          ![d, f, b, e, a, c] := by
    intro a b c d e f
    have h := DeTurck.permuteCcTensor_unitModel (I := I) g₀ crossTracePerm2 P x
    have h' : Tensor0SBundle.Tensor0SSpace.toModel
          ((DeTurck.permuteCcTensor (I := I) g₀ crossTracePerm2 P).toSection x
            (ContinuousMultilinearMap.constOfIsEmpty ℝ
              (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ))) =
        ContinuousMultilinearMap.domDomCongr crossTracePerm2
          (Tensor0SBundle.Tensor0SSpace.toModel
            (P.toSection x (ContinuousMultilinearMap.constOfIsEmpty ℝ
              (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ)))) := h
    rw [h', ContinuousMultilinearMap.domDomCongr_apply]
    congr 1
    have := consTuple6_read_crossPerm2 (E := E) a b c d e f
    simpa using this
  have hval : ∀ (a b c d e f : E),
      Tensor0SBundle.Tensor0SSpace.toModel
          (P.toSection x (ContinuousMultilinearMap.constOfIsEmpty ℝ
            (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ))) ![a, b, c, d, e, f] =
        g₀.inner x (DeTurck.connDiff (I := I) gₖ g₀ x b a) c *
          g₀.inner x (DeTurck.connDiff (I := I) gₖ g₀ x e d) f := by
    intro a b c d e f
    rw [hP, bareProd33_unitModel_apply (I := I) g₀ L L x ![a, b, c, d, e, f]]
    have hcast : (![a, b, c, d, e, f] : Fin 6 → E) ∘ Fin.castAdd 3 = ![a, b, c] := by
      funext i; fin_cases i <;> rfl
    have hnat : (![a, b, c, d, e, f] : Fin 6 → E) ∘ Fin.natAdd 3 = ![d, e, f] := by
      funext i; fin_cases i <;> rfl
    rw [hcast, hnat, hL]
    rw [show Integral.Connection.bareUnitModel (I := I) g₀
          (DeTurck.loweredConnDiffSection (I := I) gₖ g₀) x ![a, b, c] =
        Tensor0SBundle.Tensor0SSpace.toModel
          ((DeTurck.loweredConnDiffSection (I := I) gₖ g₀).toSection x
            (ContinuousMultilinearMap.constOfIsEmpty ℝ
              (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ))) ![a, b, c] from rfl,
      show Integral.Connection.bareUnitModel (I := I) g₀
          (DeTurck.loweredConnDiffSection (I := I) gₖ g₀) x ![d, e, f] =
        Tensor0SBundle.Tensor0SSpace.toModel
          ((DeTurck.loweredConnDiffSection (I := I) gₖ g₀).toSection x
            (ContinuousMultilinearMap.constOfIsEmpty ℝ
              (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ))) ![d, e, f] from rfl,
      DeTurck.loweredConnDiffSection_toModel_apply (I := I) gₖ g₀ x a b c,
      DeTurck.loweredConnDiffSection_toModel_apply (I := I) gₖ g₀ x d e f]
  have hsummand : ∀ j k : Fin (Module.finrank ℝ E),
      Tensor0SBundle.Tensor0SSpace.toModel
          ((DeTurck.permuteCcTensor (I := I) g₀ crossTracePerm2 P).toSection x
            (ContinuousMultilinearMap.constOfIsEmpty ℝ
              (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ)))
          (Fin.cons (cometricLmodel (I := I) g₀ x
              (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                ((Module.finBasis ℝ E).cDualBasis k)))
            (Fin.cons ((Module.finBasis ℝ E) k)
              (Fin.cons (cometricLmodel (I := I) g₀ x
                  (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                    ((Module.finBasis ℝ E).cDualBasis j)))
                (Fin.cons ((Module.finBasis ℝ E) j) ![(v : E), (w : E)])))) =
        g₀.inner x (DeTurck.connDiff (I := I) gₖ g₀ x w ((Module.finBasis ℝ E) j))
            ((Module.finBasis ℝ E) k) *
          g₀.inner x (DeTurck.connDiff (I := I) gₖ g₀ x
              (cometricLmodel (I := I) g₀ x
                (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                  ((Module.finBasis ℝ E).cDualBasis k))) v)
            (cometricLmodel (I := I) g₀ x
              (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                ((Module.finBasis ℝ E).cDualBasis j))) := by
    intro j k
    rw [show (Fin.cons (cometricLmodel (I := I) g₀ x
            (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
              ((Module.finBasis ℝ E).cDualBasis k)))
          (Fin.cons ((Module.finBasis ℝ E) k)
            (Fin.cons (cometricLmodel (I := I) g₀ x
                (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                  ((Module.finBasis ℝ E).cDualBasis j)))
              (Fin.cons ((Module.finBasis ℝ E) j) ![(v : E), (w : E)]))) :
            Fin 6 → E) =
        ![(cometricLmodel (I := I) g₀ x
            (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
              ((Module.finBasis ℝ E).cDualBasis k))),
          ((Module.finBasis ℝ E) k),
          (cometricLmodel (I := I) g₀ x
            (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
              ((Module.finBasis ℝ E).cDualBasis j))),
          ((Module.finBasis ℝ E) j), (v : E), (w : E)] from by
        funext i; fin_cases i <;> rfl,
      hperm, hval]
  rw [Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun k _ => hsummand j k))]
  have hinner : ∀ j : Fin (Module.finrank ℝ E),
      ∑ k : Fin (Module.finrank ℝ E),
          g₀.inner x (DeTurck.connDiff (I := I) gₖ g₀ x w ((Module.finBasis ℝ E) j))
              ((Module.finBasis ℝ E) k) *
            g₀.inner x (DeTurck.connDiff (I := I) gₖ g₀ x
                (cometricLmodel (I := I) g₀ x
                  (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                    ((Module.finBasis ℝ E).cDualBasis k))) v)
              (cometricLmodel (I := I) g₀ x
                (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                  ((Module.finBasis ℝ E).cDualBasis j))) =
        g₀.inner x (DeTurck.connDiff (I := I) gₖ g₀ x
            (DeTurck.connDiff (I := I) gₖ g₀ x w ((Module.finBasis ℝ E) j)) v)
          (cometricLmodel (I := I) g₀ x
            (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
              ((Module.finBasis ℝ E).cDualBasis j))) := by
    intro j
    rw [show DeTurck.connDiff (I := I) gₖ g₀ x
            (DeTurck.connDiff (I := I) gₖ g₀ x w ((Module.finBasis ℝ E) j)) v =
          DeTurck.connDiff (I := I) gₖ g₀ x
            (∑ k : Fin (Module.finrank ℝ E),
              g₀.inner x (DeTurck.connDiff (I := I) gₖ g₀ x w ((Module.finBasis ℝ E) j))
                  ((Module.finBasis ℝ E) k) •
                cometricLmodel (I := I) g₀ x
                  (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                    ((Module.finBasis ℝ E).cDualBasis k))) v from by
        rw [sum_inner_basis_smul_sharp_eq (I := I) g₀ x
          (DeTurck.connDiff (I := I) gₖ g₀ x w ((Module.finBasis ℝ E) j))]]
    rw [_root_.map_sum (DeTurck.connDiff (I := I) gₖ g₀ x), ContinuousLinearMap.sum_apply,
      _root_.map_sum (g₀.inner x), ContinuousLinearMap.coe_sum', Finset.sum_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smul, ContinuousLinearMap.smul_apply, map_smul,
      ContinuousLinearMap.smul_apply, smul_eq_mul]
  rw [Finset.sum_congr rfl (fun j _ => hinner j)]
  have hcross : ∀ j : Fin (Module.finrank ℝ E),
      DeTurck.connDiff (I := I) gₖ g₀ x
          (DeTurck.connDiff (I := I) gₖ g₀ x w ((Module.finBasis ℝ E) j)) v =
        crossEndoTerm2 (I := I) g₀ gₖ x v w ((Module.finBasis ℝ E) j) := by
    intro j
    simp only [crossEndoTerm2_apply, DeTurck.connDiffField_apply]
  rw [Finset.sum_congr rfl (fun j _ => by rw [hcross j])]
  exact sum_inner_apply_sharp_eq_trace (I := I) g₀ x (crossEndoTerm2 (I := I) g₀ gₖ x v w)

/-! ### The section-level structural bridge -/

set_option linter.unusedSectionVars false in
/-- **Slot permutation distributes over a section difference** (file-local; the on-disk version is
private to `SegmentMetricCurvatureDifferenceCovJet.lean`, which imports this file).  `permuteCcTensor
g₀ σ` is a fibrewise slot reindexing, hence additive; its unit model is the `domDomCongr σ` of the
operand's (`permuteCcTensor_unitModel`), and `domDomCongr` is `ℝ`-linear. -/
private theorem permuteCcTensor_sub_local (g₀ : SmoothRiemannianMetric I M) {s : ℕ}
    (σ : Equiv.Perm (Fin s)) (A B : Integral.L2.SmoothCcTensor g₀ 0 s) :
    DeTurck.permuteCcTensor (I := I) g₀ σ (A - B) =
      DeTurck.permuteCcTensor (I := I) g₀ σ A - DeTurck.permuteCcTensor (I := I) g₀ σ B := by
  classical
  apply Integral.L2.SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply DifferentialGeometry.PDE.DeTurck.tensor0s_ext_unitZero (I := I) (M := M) (s := s)
  apply Tensor0SBundle.Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro m
  beta_reduce
  have hL : Tensor0SBundle.Tensor0SSpace.toModel
        ((DeTurck.permuteCcTensor (I := I) g₀ σ (A - B)).toSection x
          (Integral.Connection.unitZeroSec (I := I) (M := M) x)) =
      ContinuousMultilinearMap.domDomCongr σ
        (Tensor0SBundle.Tensor0SSpace.toModel ((A - B).toSection x
          (Integral.Connection.unitZeroSec (I := I) (M := M) x))) :=
    DeTurck.permuteCcTensor_unitModel (I := I) g₀ σ (A - B) x
  have hA : Tensor0SBundle.Tensor0SSpace.toModel
        ((DeTurck.permuteCcTensor (I := I) g₀ σ A).toSection x
          (Integral.Connection.unitZeroSec (I := I) (M := M) x)) =
      ContinuousMultilinearMap.domDomCongr σ
        (Tensor0SBundle.Tensor0SSpace.toModel (A.toSection x
          (Integral.Connection.unitZeroSec (I := I) (M := M) x))) :=
    DeTurck.permuteCcTensor_unitModel (I := I) g₀ σ A x
  have hB : Tensor0SBundle.Tensor0SSpace.toModel
        ((DeTurck.permuteCcTensor (I := I) g₀ σ B).toSection x
          (Integral.Connection.unitZeroSec (I := I) (M := M) x)) =
      ContinuousMultilinearMap.domDomCongr σ
        (Tensor0SBundle.Tensor0SSpace.toModel (B.toSection x
          (Integral.Connection.unitZeroSec (I := I) (M := M) x))) :=
    DeTurck.permuteCcTensor_unitModel (I := I) g₀ σ B x
  have hsubval : (A - B).toSection x = A.toSection x - B.toSection x := by
    rw [Integral.L2.SmoothCcTensor.toSection_sub, ContMDiffSection.coe_sub, Pi.sub_apply]
  have hsubval' : ((DeTurck.permuteCcTensor (I := I) g₀ σ A
        - DeTurck.permuteCcTensor (I := I) g₀ σ B)).toSection x =
      (DeTurck.permuteCcTensor (I := I) g₀ σ A).toSection x
        - (DeTurck.permuteCcTensor (I := I) g₀ σ B).toSection x := by
    rw [Integral.L2.SmoothCcTensor.toSection_sub, ContMDiffSection.coe_sub, Pi.sub_apply]
  calc Tensor0SBundle.Tensor0SSpace.toModel
        ((DeTurck.permuteCcTensor (I := I) g₀ σ (A - B)).toSection x
          (Integral.Connection.unitZeroSec (I := I) (M := M) x)) m
      = (ContinuousMultilinearMap.domDomCongr σ
          (Tensor0SBundle.Tensor0SSpace.toModel ((A - B).toSection x
            (Integral.Connection.unitZeroSec (I := I) (M := M) x)))) m := by rw [hL]
    _ = (ContinuousMultilinearMap.domDomCongr σ
            (Tensor0SBundle.Tensor0SSpace.toModel (A.toSection x
              (Integral.Connection.unitZeroSec (I := I) (M := M) x)))) m
          - (ContinuousMultilinearMap.domDomCongr σ
            (Tensor0SBundle.Tensor0SSpace.toModel (B.toSection x
              (Integral.Connection.unitZeroSec (I := I) (M := M) x)))) m := by
        rw [hsubval]; rfl
    _ = Tensor0SBundle.Tensor0SSpace.toModel
          ((DeTurck.permuteCcTensor (I := I) g₀ σ A).toSection x
            (Integral.Connection.unitZeroSec (I := I) (M := M) x)) m
          - Tensor0SBundle.Tensor0SSpace.toModel
          ((DeTurck.permuteCcTensor (I := I) g₀ σ B).toSection x
            (Integral.Connection.unitZeroSec (I := I) (M := M) x)) m := by
        rw [hA, hB]
    _ = Tensor0SBundle.Tensor0SSpace.toModel
          ((DeTurck.permuteCcTensor (I := I) g₀ σ A
            - DeTurck.permuteCcTensor (I := I) g₀ σ B).toSection x
            (Integral.Connection.unitZeroSec (I := I) (M := M) x)) m := by
        rw [hsubval']; rfl

set_option linter.unusedSectionVars false in
/-- **The Cross section as a cometric double-double-trace of the lowered connection-difference product
difference** (the section-level structural bridge consumed by SUB2).  The quadratic-in-difference Cross
section `crossSection g₀ g₁ g₂` is the `−2`-scaled antisymmetrised slot-permuted pair of cometric
double-double-traces of the bare cross-product difference `crossProductDiff g₀ g₁ g₂`:
```
crossSection g₀ g₁ g₂
  = (-2 : ℝ) • ( cometricDoubleDoubleTrace g₀ (permuteCcTensor g₀ crossTracePerm1 (crossProductDiff g₀ g₁ g₂))
               − cometricDoubleDoubleTrace g₀ (permuteCcTensor g₀ crossTracePerm2 (crossProductDiff g₀ g₁ g₂)) ).
```

**Decomposition.**  By unit-extensionality (`tensor0s_ext_unitZero`) it suffices to match the two fibre
values at the unit `(0, 0)`-tensor and an arbitrary tangent pair `(v, w)`.  The left side is the
order-zero Cross term `ricciNeg2SectionDiffCrossEval = -2 (crossBilinSingle g₁ − crossBilinSingle g₂)`
(`crossSection_toModel_apply`, `crossBilin_apply_eq_crossEval`, `crossBilin_apply`), each
`crossBilinSingle gₖ` the difference `tr(crossEndoTerm1 gₖ) − tr(crossEndoTerm2 gₖ)`.  The right side
distributes the double-double-trace and the slot permutation over the bare-product difference
(`cometricDoubleDoubleTrace_sub`, `permuteCcTensor_sub_local`), and each single-metric arm is identified
through `doubleDoubleTrace_perm1_loweredProd_eq_crossEndoTerm1_trace` /
`doubleDoubleTrace_perm2_loweredProd_eq_crossEndoTerm2_trace`.  The two readings agree by `ring`. -/
theorem crossSection_eq_cometricDoubleDoubleTrace_loweredProductDiff
    (g₀ g₁ g₂ : SmoothRiemannianMetric I M) :
    crossSection (I := I) g₀ g₁ g₂ =
      (-2 : ℝ) •
        (cometricDoubleDoubleTrace (I := I) g₀
            (DeTurck.permuteCcTensor (I := I) g₀ crossTracePerm1
              (crossProductDiff (I := I) g₀ g₁ g₂))
          - cometricDoubleDoubleTrace (I := I) g₀
            (DeTurck.permuteCcTensor (I := I) g₀ crossTracePerm2
              (crossProductDiff (I := I) g₀ g₁ g₂))) := by
  classical
  apply Integral.L2.SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply DifferentialGeometry.PDE.DeTurck.tensor0s_ext_unitZero (I := I) (M := M) (s := 2)
  apply Tensor0SBundle.Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro p
  beta_reduce
  have hunit : (Integral.Connection.unitZeroSec (I := I) (M := M) x :
        Tensor0SBundle.Tensor0SSpace 0 I x) =
      ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ) := rfl
  rw [hunit]
  have hpair : (![p 0, p 1] : Fin 2 → TangentSpace I x) = p := by
    funext i; fin_cases i <;> rfl
  -- LHS fibre = `-2 (crossBilinSingle g₁ − crossBilinSingle g₂)` (the order-zero Cross term).
  rw [← hpair, crossSection_toModel_apply (I := I) g₀ g₁ g₂ x (p 0) (p 1),
    ← crossBilin_apply_eq_crossEval (I := I) g₀ g₁ g₂ x (p 0) (p 1), crossBilin_apply,
    crossBilinSingle_apply, crossBilinSingle_apply]
  -- RHS fibre: distribute the double-double-trace and permutation over the bare-product difference.
  set L₁ := DeTurck.loweredConnDiffSection (I := I) g₁ g₀ with hL₁
  set L₂ := DeTurck.loweredConnDiffSection (I := I) g₂ g₀ with hL₂
  have hsplit : ∀ (σ : Equiv.Perm (Fin 6)),
      cometricDoubleDoubleTrace (I := I) g₀
          (DeTurck.permuteCcTensor (I := I) g₀ σ (crossProductDiff (I := I) g₀ g₁ g₂)) =
        cometricDoubleDoubleTrace (I := I) g₀
            (DeTurck.permuteCcTensor (I := I) g₀ σ
              (Integral.Connection.bareProd (I := I) g₀ 3 3 (a := 0) (b := 0) L₁ L₁))
          - cometricDoubleDoubleTrace (I := I) g₀
            (DeTurck.permuteCcTensor (I := I) g₀ σ
              (Integral.Connection.bareProd (I := I) g₀ 3 3 (a := 0) (b := 0) L₂ L₂)) := by
    intro σ
    rw [crossProductDiff, ← hL₁, ← hL₂, permuteCcTensor_sub_local, cometricDoubleDoubleTrace_sub]
  -- The fibre value of the `-2`-scaled difference of the two trace pairs.
  have hsmul : Tensor0SBundle.Tensor0SSpace.toModel
        (((-2 : ℝ) •
          (cometricDoubleDoubleTrace (I := I) g₀
              (DeTurck.permuteCcTensor (I := I) g₀ crossTracePerm1
                (crossProductDiff (I := I) g₀ g₁ g₂))
            - cometricDoubleDoubleTrace (I := I) g₀
              (DeTurck.permuteCcTensor (I := I) g₀ crossTracePerm2
                (crossProductDiff (I := I) g₀ g₁ g₂)))).toSection x
          (ContinuousMultilinearMap.constOfIsEmpty ℝ
            (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ))) ![(p 0 : TangentSpace I x), p 1] =
      (-2 : ℝ) * (Tensor0SBundle.Tensor0SSpace.toModel
          ((cometricDoubleDoubleTrace (I := I) g₀
              (DeTurck.permuteCcTensor (I := I) g₀ crossTracePerm1
                (crossProductDiff (I := I) g₀ g₁ g₂))).toSection x
            (ContinuousMultilinearMap.constOfIsEmpty ℝ
              (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ))) ![(p 0 : TangentSpace I x), p 1]
        - Tensor0SBundle.Tensor0SSpace.toModel
          ((cometricDoubleDoubleTrace (I := I) g₀
              (DeTurck.permuteCcTensor (I := I) g₀ crossTracePerm2
                (crossProductDiff (I := I) g₀ g₁ g₂))).toSection x
            (ContinuousMultilinearMap.constOfIsEmpty ℝ
              (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ))) ![(p 0 : TangentSpace I x), p 1]) := by
    have h1 : (((-2 : ℝ) •
          (cometricDoubleDoubleTrace (I := I) g₀
              (DeTurck.permuteCcTensor (I := I) g₀ crossTracePerm1
                (crossProductDiff (I := I) g₀ g₁ g₂))
            - cometricDoubleDoubleTrace (I := I) g₀
              (DeTurck.permuteCcTensor (I := I) g₀ crossTracePerm2
                (crossProductDiff (I := I) g₀ g₁ g₂)))).toSection x) =
        (-2 : ℝ) • ((cometricDoubleDoubleTrace (I := I) g₀
              (DeTurck.permuteCcTensor (I := I) g₀ crossTracePerm1
                (crossProductDiff (I := I) g₀ g₁ g₂))).toSection x
          - (cometricDoubleDoubleTrace (I := I) g₀
              (DeTurck.permuteCcTensor (I := I) g₀ crossTracePerm2
                (crossProductDiff (I := I) g₀ g₁ g₂))).toSection x) := by
      rw [Integral.L2.SmoothCcTensor.toSection_smul, ContMDiffSection.coe_smul, Pi.smul_apply,
        Integral.L2.SmoothCcTensor.toSection_sub, ContMDiffSection.coe_sub, Pi.sub_apply]
    rw [h1]; rfl
  rw [hsmul, hsplit crossTracePerm1, hsplit crossTracePerm2]
  -- Each single-metric arm reads as a cross-endomorphism trace.
  rw [show (![(p 0 : TangentSpace I x), p 1] : Fin 2 → TangentSpace I x) =
      ![(p 0 : TangentSpace I x), (p 1 : TangentSpace I x)] from rfl]
  have ht11 := doubleDoubleTrace_perm1_loweredProd_eq_crossEndoTerm1_trace
    (I := I) g₀ g₁ x (p 0) (p 1)
  have ht12 := doubleDoubleTrace_perm1_loweredProd_eq_crossEndoTerm1_trace
    (I := I) g₀ g₂ x (p 0) (p 1)
  have ht21 := doubleDoubleTrace_perm2_loweredProd_eq_crossEndoTerm2_trace
    (I := I) g₀ g₁ x (p 0) (p 1)
  have ht22 := doubleDoubleTrace_perm2_loweredProd_eq_crossEndoTerm2_trace
    (I := I) g₀ g₂ x (p 0) (p 1)
  rw [hL₁, hL₂] at *
  -- Distribute `toModel` over the section differences, then identify each arm.
  have hdist : ∀ (A B : Integral.L2.SmoothCcTensor g₀ 0 2),
      Tensor0SBundle.Tensor0SSpace.toModel ((A - B).toSection x
          (ContinuousMultilinearMap.constOfIsEmpty ℝ
            (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ))) ![(p 0 : TangentSpace I x), p 1] =
        Tensor0SBundle.Tensor0SSpace.toModel (A.toSection x
            (ContinuousMultilinearMap.constOfIsEmpty ℝ
              (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ))) ![(p 0 : TangentSpace I x), p 1]
          - Tensor0SBundle.Tensor0SSpace.toModel (B.toSection x
            (ContinuousMultilinearMap.constOfIsEmpty ℝ
              (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ))) ![(p 0 : TangentSpace I x), p 1] :=
    fun A B => by
      rw [Integral.L2.SmoothCcTensor.toSection_sub, ContMDiffSection.coe_sub, Pi.sub_apply,
        ContinuousLinearMap.sub_apply, Tensor0SBundle.Tensor0SSpace.toModel_sub,
        ContinuousMultilinearMap.sub_apply]
  rw [hdist _ _, hdist _ _, ht11, ht12, ht21, ht22]
  ring

end DeTurck
end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry
