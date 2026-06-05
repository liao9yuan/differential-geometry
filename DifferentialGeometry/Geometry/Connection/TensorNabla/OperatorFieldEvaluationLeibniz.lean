import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.MetricContractionLeibnizGrid

/-! # The operator-field evaluation covariant Leibniz and the per-order curvature-operator envelope

For a closed (compact, boundaryless) smooth Riemannian manifold `(M, g)` modelled on a real
inner-product space `E`, this file builds — piece by piece — the operator-field telescoping that powers
the per-order section-proportional fibre envelope for a recursively-differentiated *fibrewise curvature*
operator family, the single deep analytic primitive consumed by the two concrete curvature towers
through `exists_proportional_recCurvDiffOp_perOrderEnvelope`
(`Analysis/Spectral/Tensor/CovGrad/IteratedDiffOpProportionalBound`).

## The shape and why the envelope is true

A recursive covariant-Leibniz-remainder family `op p r` (the `p`-times covariantly differentiated
operator at covariant rank `r`, sending a smooth compactly-supported `(0, r)`-tensor section to a smooth
`(0, r + p)`-tensor section) whose

* order-`0` base is a *fibrewise* curvature operator (`IsOrderZeroCurvFactor`: `ℝ`-linear in the
  section value, value-local), and whose
* single-step covariant Leibniz is the exact remainder identity (`hcovGrad_op`,
  `∇(op p r W) = op (p+1) r W + (rank-cast) op p (r+1)(∇W)`),

telescopes: writing `L₀` for the order-`0` fibrewise operator field (`op 0 r W (x) = L₀ x (W x)`,
extracted from the value-locality + `ℝ`-linearity fingerprint), the input section's derivative `∇W`
produced by `∇(op p r W)` is cancelled exactly by the rank-cast lower-order term `op p (r + 1)(∇W)`, so
`op p r W (x) = Lᵖ x (W x)` for a fibrewise operator field `Lᵖ = ∇ᵖ L₀` that does not differentiate `W`.
Because `L₀` is built from `g` and the smooth Riemann curvature `R`, each `Lᵖ` is a *smooth* fibrewise
operator whose squared fibre-operator norm is *continuous* in the base point and hence uniformly bounded
on the compact `M`, giving the per-order section-proportional fibre bound
`rfns(op p r W)(x) ≤ kappa p r · rfns(W)(x)`.

## The pieces

* **P1** `op_zero_value_homogeneous` (**proved**) — the value-level homogeneity bridge that upgrades the
  pointwise `ℝ`-linearity of the order-`0` base to `C^∞(M, ℝ)`-linearity (a smooth scalar contributes
  only its value at the point, by value-locality); the bridge that makes the order-`0` operator field
  extraction (`ofLinearMapSection`) applicable.
* **P4** `riemannianFiberNormSq_clm_apply_le` (**posited**) — the fibrewise Cauchy–Schwarz
  `rfns(φ v) ≤ Cφ · rfns(v)` for a fibrewise continuous-linear operator `φ` between tensor fibres.
* **P2/P3/P5** `op_perOrder_factorisation_continuous` (**posited**) — the telescoping factorisation
  `op p r W (x) = Lᵖ x (W x)` packaged with a *continuous* per-point fibre constant controlling the
  fibrewise operator (the deep core; the recursion's cast-cancellation through the Hom-evaluation
  Leibniz on the operator-field bundle `Hom(T⁰_r, T⁰_{r+p})`, plus smoothness of the iterated
  curvature-operator field `∇ᵖ L₀`).
* **P6** the per-order envelope `exists_proportional_recCurvDiffOp_perOrderEnvelope` is assembled
  here, **non-`sorry`**, from `op_perOrder_factorisation_continuous` by the standard
  continuous-on-compact-`M` supremum (the established `(isCompact_univ).image · |>.bddAbove` route).

Consumers transitively depend on `sorryAx` through `riemannianFiberNormSq_clm_apply_le` and
`op_perOrder_factorisation_continuous` alone (the latter being the single genuinely-irreducible
operator-field telescoping; `op_zero_value_homogeneous` is proved). Each posited piece is a precise,
independently-fillable analytic sub-lemma with a full trap screen (value-reads only / per-`(p, r)`
families / zero-witness rejection / no free binders).
-/

noncomputable section

set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

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
variable [CompleteSpace E]

/-- **The order-`0` fibrewise-curvature-operator factorisation hypothesis.** For a recursive operator
family `op`, this records the two structural facts that fix the order-`0` base `op 0 r` to a *fibrewise*
operator — one reading only the *value* of its section (no derivative), the structural fingerprint of a
bundled curvature operator:

* `linear` — the order-`0` base is `ℝ`-linear in the section: `op 0 r (c₁ • W₁ + c₂ • W₂) =
  c₁ • op 0 r W₁ + c₂ • op 0 r W₂`;
* `local'` — the order-`0` base is *value-local*: its fibre value at `x` depends only on the section
  value `W (x)` (if two sections agree at `x`, the operator's values at `x` agree).

Together these force `op 0 r` to factor, fibrewise, through a continuous-`ℝ`-linear operator on the
fibre applied to `W (x)` — the carrier of the genuine curvature setting. Both facts are *proved* on disk
for the two concrete towers (at order `0` each reads only its section's value, linearly). This is the
honest, instance-plumbing-free fingerprint of the fibrewise curvature operator; it is what fixes the
family away from a pathological free `covGrad_op`-family (whose high-order layer can be unbounded). -/
structure IsOrderZeroCurvFactor (g : SmoothRiemannianMetric I M)
    (op : ∀ (p r : ℕ), SmoothCcTensor g 0 r → SmoothCcTensor g 0 (r + p)) : Prop where
  /-- The order-`0` base is `ℝ`-linear in the section (stated at the fibre-value level). -/
  linear : ∀ (r : ℕ) (c₁ c₂ : ℝ) (W₁ W₂ : SmoothCcTensor g 0 r) (x : M),
    (op 0 r (c₁ • W₁ + c₂ • W₂)).toSection x =
      c₁ • (op 0 r W₁).toSection x + c₂ • (op 0 r W₂).toSection x
  /-- The order-`0` base is value-local: its fibre value at `x` depends only on `W (x)`. -/
  local' : ∀ (r : ℕ) (W₁ W₂ : SmoothCcTensor g 0 r) (x : M),
    W₁.toSection x = W₂.toSection x → (op 0 r W₁).toSection x = (op 0 r W₂).toSection x

set_option linter.unusedSectionVars false in
/-- **P1 — the value-level homogeneity of the order-`0` base** (proved). From the
`IsOrderZeroCurvFactor` fingerprint (pointwise `ℝ`-linearity + value-locality), the order-`0` base
commutes, *at each point* `x`, with multiplication of the section value by any scalar: if
`W₂.toSection x = c • W₁.toSection x` then `(op 0 r W₂).toSection x = c • (op 0 r W₁).toSection x`.

This is the value-level fingerprint that upgrades the pointwise `ℝ`-linearity of the order-`0` base to
`C^∞(M, ℝ)`-linearity (a smooth scalar `f` contributes, at `x`, only its value `f x`, by
value-locality: `op 0 r (f • W) (x) = op 0 r (any section with value f(x) • W(x)) (x) =
f(x) • op 0 r W (x)`), the bridge that makes the order-`0` operator-field extraction
(`ofLinearMapSection`) applicable. It is *false* for a non-`ℝ`-linear or non-value-local family, so it
genuinely uses both fingerprint fields. -/
theorem op_zero_value_homogeneous
    (g : SmoothRiemannianMetric I M) (r : ℕ)
    (op : ∀ (p r : ℕ), SmoothCcTensor g 0 r → SmoothCcTensor g 0 (r + p))
    (hbase : IsOrderZeroCurvFactor (I := I) (M := M) g op)
    (c : ℝ) (W₁ W₂ : SmoothCcTensor g 0 r) (x : M)
    (hval : W₂.toSection x = c • W₁.toSection x) :
    (op 0 r W₂).toSection x = c • (op 0 r W₁).toSection x := by
  have hcW : (c • W₁).toSection x = c • W₁.toSection x := by
    rw [SmoothCcTensor.toSection_smul]; rfl
  rw [hbase.local' r W₂ (c • W₁) x (by rw [hval, hcW])]
  have hlin := hbase.linear r c 0 W₁ W₁ x
  rw [show (c • W₁) = c • W₁ + (0 : ℝ) • W₁ from by rw [zero_smul, add_zero]]
  rw [hlin]
  simp only [zero_smul, add_zero]

set_option linter.unusedSectionVars false in
/-- **P4 — the fibrewise Cauchy–Schwarz for an operator-field evaluation** (posited). For a fibrewise
continuous-linear operator `φ : TensorRSSpace 0 r I x →L[ℝ] TensorRSSpace 0 s I x` between tensor
fibres at a point `x`, the intrinsic squared Riemannian fibre norm of the evaluation `φ v` is
controlled by a nonnegative fibre-operator constant `Cφ` (the squared `g`-fibre operator norm of `φ`)
times the intrinsic squared fibre norm of `v`:
```
rfns(φ v) ≤ Cφ · rfns(v).
```

**Why this is TRUE.** Both `TensorRSSpace 0 r I x` and `TensorRSSpace 0 s I x` are finite-dimensional
and carry the intrinsic `g`-fibre inner product whose squared norm is `riemannianFiberNormSq`. A
continuous-linear map between finite-dimensional inner-product spaces is bounded; taking `Cφ` to be the
square of its `g`-fibre operator norm and squaring the operator bound `‖φ v‖_g ≤ ‖φ‖_g · ‖v‖_g` gives
the displayed inequality. Equivalently, expanding `v` in a `g`-orthonormal frame of the source tensor
fibre and applying Cauchy–Schwarz over the frame index (the route of
`riemannianFiberNormSq_riemannOp_tensorCov_vw_factor_le`) yields `Cφ = ∑_α rfns(φ fα)` over the frame
`(fα)`. The ambient-to-intrinsic step is the fibre-norm bridge `riemannianFiberNormSq = ‖·‖²` (itself a
sanctioned posited child elsewhere because of the model-vs-`g`-fibre norm diamond).

**Trap screen.** Reads only the *value* `v` (no jet); a single fibrewise operator `φ` at one point `x`
(no free `(p, r)` family); the witness `Cφ` genuinely uses `φ` and rejects `Cφ ≡ 0` whenever `φ ≠ 0`
(then `rfns(φ v) > 0 = 0 · rfns(v)` for a suitable `v`); no free binders escape `x`. -/
theorem riemannianFiberNormSq_clm_apply_le
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M)
    (φ : TensorRSSpace 0 r I x →L[ℝ] TensorRSSpace 0 s I x) :
    ∃ Cφ : ℝ, 0 ≤ Cφ ∧ ∀ v : TensorRSSpace 0 r I x,
      riemannianFiberNormSq (I := I) (M := M) g 0 s x (φ v) ≤
        Cφ * riemannianFiberNormSq (I := I) (M := M) g 0 r x v := by
  sorry

/-- **P2/P3/P5 — the operator-field telescoping factorisation with a continuous fibre constant**
(posited; the single genuinely-irreducible operator-field content). For a recursive
covariant-Leibniz-remainder family `op` whose

* single-step covariant Leibniz is the exact remainder identity (`hcovGrad_op`), and whose
* order-`0` base is a fibrewise curvature operator (`hbase : IsOrderZeroCurvFactor g op`),

at every differentiation order `p` and covariant rank `r` there is a fibrewise continuous-linear
operator field `L : ∀ x, TensorRSSpace 0 r I x →L[ℝ] TensorRSSpace 0 (r + p) I x` together with a
*continuous* nonnegative per-point fibre constant `Cf : M → ℝ` such that

* **factorisation**: `(op p r W).toSection x = L x (W.toSection x)` for every section `W` and point `x`
  (the operator reads only the *value* `W (x)`; the input section's derivatives have cancelled exactly
  through the recursion's rank-cast term), and
* **continuous fibre bound**: `rfns(L x v) ≤ Cf x · rfns(v)` for every point `x` and fibre value `v`,
  with `Cf` continuous (the squared `g`-fibre operator norm of the *smooth* iterated-curvature field
  `Lᵖ = ∇ᵖ L₀`, continuous in `x` by smoothness of `L₀` and of `R`).

**Why this is TRUE — the telescoping (the deep content).** The `hbase` linearity + value-locality
identify the order-`0` base with a smooth fibrewise curvature operator field `L₀`
(`op 0 r W (x) = L₀ x (W x)`, via `op_zero_value_homogeneous` + `ofLinearMapSection`). By the exact
single-step covariant Leibniz `hcovGrad_op` and the Hom-evaluation Leibniz
`∇(τ · W) = (∇τ) · W + τ · (∇W)` on the operator-field bundle `Hom(T⁰_r, T⁰_{r+p})`, the recursion
telescopes: the input section's derivative `∇W` produced by `∇(op p r W)` is cancelled exactly by the
rank-cast lower-order term `op p (r + 1)(∇W)`, so `op p r W (x) = (∇ᵖ L₀) x (W x)` is the `p`-fold
covariant derivative of the smooth fibrewise curvature operator `L₀`, applied *fibrewise* to `W (x)` —
no derivative of `W` survives. Because `L₀` is built from `g` and the smooth Riemann curvature `R`, the
iterated coefficient `∇ᵖ L₀` is a smooth fibrewise operator field, so its squared `g`-fibre operator
norm `Cf` is continuous in `x` (the per-point Cauchy–Schwarz constant of
`riemannianFiberNormSq_clm_apply_le`, made continuous by smoothness of the field). The Hom-evaluation
Leibniz and the iterated Hom-derivative on the operator-field bundle `Hom(T⁰_r, T⁰_{r+p})` (whose source
and target are themselves Hom-bundles, requiring a Hom-connection presently absent from the library) are
the genuine, *large independent differential-geometry* content posited here.

**Trap screen / non-vacuity.** The factorisation forces the operator to read *only the value* `W (x)`
(no jet), the structural fingerprint of the iterated curvature operator; `L`, `Cf` are a single field
per fixed `(p, r)` (no free family); a degenerate `Cf ≡ 0` is rejected on any non-flat manifold at
`p = 1` (`op 1 r W (x) = (∇L₀) x (W x)` is the differentiated curvature operator, genuinely nonzero when
`∇R ≠ 0` and `L₀` carries a non-zero contraction, so `rfns(op 1 r W)(x) > 0` while `0 · rfns(W)(x) = 0`);
no free binders escape `(p, r)`. The factorisation genuinely *uses* `W` (the operator is applied to
`W (x)`), and the `hbase` hypothesis fixes the family to a genuine fibrewise curvature operator (the
statement is *false* for an arbitrary `covGrad_op`-family, whose high-order layer can be unbounded). -/
theorem op_perOrder_factorisation_continuous
    (g : SmoothRiemannianMetric I M)
    (op : ∀ (p r : ℕ), SmoothCcTensor g 0 r → SmoothCcTensor g 0 (r + p))
    (hcovGrad_op : ∀ (p r : ℕ) (W : SmoothCcTensor g 0 r),
      covGrad g 0 (r + p) (op p r W) =
        op (p + 1) r W +
          castRankCc_db g 0 (by omega : (r + 1) + p = r + (p + 1)) (op p (r + 1) (covGrad g 0 r W)))
    (hbase : IsOrderZeroCurvFactor (I := I) (M := M) g op)
    (p r : ℕ) :
    ∃ (L : ∀ x : M, TensorRSSpace 0 r I x →L[ℝ] TensorRSSpace 0 (r + p) I x) (Cf : M → ℝ),
      Continuous Cf ∧ (∀ x, 0 ≤ Cf x) ∧
        (∀ (W : SmoothCcTensor g 0 r) (x : M), (op p r W).toSection x = L x (W.toSection x)) ∧
        (∀ (x : M) (v : TensorRSSpace 0 r I x),
          riemannianFiberNormSq (I := I) (M := M) g 0 (r + p) x (L x v) ≤
            Cf x * riemannianFiberNormSq (I := I) (M := M) g 0 r x v) := by
  sorry

/-- **P6 — the per-order section-proportional fibre envelope, assembled** (non-`sorry`, over the
posited operator-field telescoping `op_perOrder_factorisation_continuous` and the posited fibrewise
Cauchy–Schwarz `riemannianFiberNormSq_clm_apply_le`). For a recursive covariant-Leibniz-remainder family
`op` whose order-`0` base is a fibrewise curvature operator (`hbase`) with the exact single-step
covariant Leibniz (`hcovGrad_op`), there is a nonnegative order × rank envelope `kappa` with
```
rfns(op p r W)(x) ≤ kappa p r · rfns(W)(x)
```
at every order `p`, rank `r`, section `W`, point `x`.

**Proof.** From `op_perOrder_factorisation_continuous` at `(p, r)` obtain the fibrewise field `L`, the
*continuous* nonnegative per-point fibre constant `Cf`, the factorisation `op p r W (x) = L x (W x)`,
and the continuous fibre bound `rfns(L x v) ≤ Cf x · rfns(v)`. Since `M` is compact and `Cf` is
continuous, `Cf` attains a finite supremum `K := ⨆` (the standard `(isCompact_univ).image · |>.bddAbove`
route); take `kappa p r := max K 0`. Then
`rfns(op p r W)(x) = rfns(L x (W x)) ≤ Cf x · rfns(W x) ≤ kappa p r · rfns(W x)`, the last step using
`Cf x ≤ kappa p r` and `rfns(W x) ≥ 0`. -/
theorem exists_proportional_recCurvDiffOp_perOrderEnvelope_via_factorisation
    (g : SmoothRiemannianMetric I M)
    (op : ∀ (p r : ℕ), SmoothCcTensor g 0 r → SmoothCcTensor g 0 (r + p))
    (hcovGrad_op : ∀ (p r : ℕ) (W : SmoothCcTensor g 0 r),
      covGrad g 0 (r + p) (op p r W) =
        op (p + 1) r W +
          castRankCc_db g 0 (by omega : (r + 1) + p = r + (p + 1)) (op p (r + 1) (covGrad g 0 r W)))
    (hbase : IsOrderZeroCurvFactor (I := I) (M := M) g op) :
    ∃ kappa : ℕ → ℕ → ℝ, (∀ p r, 0 ≤ kappa p r) ∧
      ∀ (p r : ℕ) (W : SmoothCcTensor g 0 r) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g 0 (r + p) x ((op p r W).toSection x) ≤
          kappa p r * riemannianFiberNormSq (I := I) (M := M) g 0 r x (W.toSection x) := by
  classical
  -- Per `(p, r)`: the factorisation gives a *continuous* fibre constant on the compact `M`, whose
  -- finite supremum is a single base-point-uniform proportional constant.
  have hper : ∀ p r : ℕ, ∃ K : ℝ, 0 ≤ K ∧ ∀ (W : SmoothCcTensor g 0 r) (x : M),
      riemannianFiberNormSq (I := I) (M := M) g 0 (r + p) x ((op p r W).toSection x) ≤
        K * riemannianFiberNormSq (I := I) (M := M) g 0 r x (W.toSection x) := by
    intro p r
    obtain ⟨L, Cf, hCf_cont, hCf_nn, hfact, hbound⟩ :=
      op_perOrder_factorisation_continuous (I := I) (M := M) g op hcovGrad_op hbase p r
    obtain ⟨C₀, hC₀⟩ := ((isCompact_univ (X := M)).image hCf_cont).bddAbove
    refine ⟨max C₀ 0, le_max_right _ _, fun W x => ?_⟩
    have hCf_le : Cf x ≤ max C₀ 0 := le_trans (hC₀ ⟨x, Set.mem_univ _, rfl⟩) (le_max_left _ _)
    have hrfnsW_nn : 0 ≤ riemannianFiberNormSq (I := I) (M := M) g 0 r x (W.toSection x) :=
      riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 r x _
    rw [hfact W x]
    calc
      riemannianFiberNormSq (I := I) (M := M) g 0 (r + p) x (L x (W.toSection x))
          ≤ Cf x * riemannianFiberNormSq (I := I) (M := M) g 0 r x (W.toSection x) :=
            hbound x (W.toSection x)
      _ ≤ max C₀ 0 * riemannianFiberNormSq (I := I) (M := M) g 0 r x (W.toSection x) :=
            mul_le_mul_of_nonneg_right hCf_le hrfnsW_nn
  refine ⟨fun p r => (hper p r).choose, fun p r => (hper p r).choose_spec.1,
    fun p r W x => (hper p r).choose_spec.2 W x⟩

end Connection
end Integral
end DifferentialGeometry

end
