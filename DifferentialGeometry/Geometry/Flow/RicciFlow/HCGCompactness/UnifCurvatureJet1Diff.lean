import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.UnifCurvatureSup
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.UnifCovSumCross
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.MetricCovDerivPullback

/-!
# The order-`1` curvature-jet difference for the `Λ`-class (brick 2a-hi, stage 2)

The order-`0` curvature layer of brick E3 is `UnifCurvatureSup.lean`
(`unifRicSup`, `unifRicBilin`, `unifConnDiffSup`, `unifCovConnDiffSup`) together
with `unifCurvSup` (`UnifCurvatureSup.lean`).  This file
opens the order-`1` layer: the object

`∇^{g₀} Rm(g₀) − ∇^{gBase} Rm(gBase)`,

written in the generic covariant-derivative currency of
`MetricCovDerivLinear.lean` — where the lowered Riemann tensor `metricRm04 g` is
just a rank-`4` `Tensor0SField` and `iterCov g 4 (metricRm04 g) a` *is* `∇^a Rm`.
The packaging bridge to the canonical static tower `curvCovDeriv` is
`curvCovDeriv_normSq_eq` (`CurvTowerBridge.lean`).

The content here is the **split** and its **first term**:

* `curvJet1_diff_eq` — the exact operator identity

  `∇^{g₀}Rm(g₀) − ∇^{gBase}Rm(gBase)
     = (∇^{g₀} − ∇^{gBase})Rm(g₀) + ∇^{gBase}(Rm(g₀) − Rm(gBase))`,

  i.e. `diffStep g₀ gBase 4 (metricRm04 g₀) + covStep gBase 4 (Rm(g₀) − Rm(gBase))`;

* `unifRm04Sup` — the class-uniform order-`0` sup of the *lowered* curvature
  tensor in `normSq0S` currency, `|Rm(g₀)|_{g₀} ≤ n²·F`, obtained from the
  operator sup `unifCurvSup` by evaluating the components in a
  `g₀`-orthonormal frame.  This is the first `Λ`-class curvature bound in the
  tree stated on the `(0,4)` field rather than on `riemannOp`, and it is what the
  generic `diffStep` norm layer consumes;

* `unifCurvJet1Conn` — the class-uniform bound on the **connection-insertion
  term** `(∇^{g₀} − ∇^{gBase})Rm(g₀) = A ⋆ Rm(g₀)`, with a constant closed in
  `(Λ, gBase)` before any class member is named.  It composes `unifRm04Sup` with
  the generic single-step connection-difference estimate `diffStep_jet_one_le`.

The **second** term of `curvJet1_diff_eq`, `∇^{gBase}(Rm(g₀) − Rm(gBase))`, is the
differentiated Palatini identity and is *not* proved here; see
`UnifCurvatureJet1Diff.md` for the exact remaining statement and the missing API.
-/

set_option autoImplicit false

noncomputable section

set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000

open Bundle Manifold Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff BigOperators
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Laplacian
open DifferentialGeometry.HCGCompactness

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] in
/-- **Fixed-metric curvature-jet sup, every order.**

For a single smooth metric on a closed manifold, `∇^a Rm(g)` — written in the
generic currency as `iterCov g 4 (metricRm04 g) a` — has a finite `g`-fibre-norm
sup.  Pure continuity plus compactness (`sqrtNormSq0S_bddOn`); no class currency
and no curvature-difference input.

This is the `gBase` half of the fixed-metric order-`a` curvature bound: any
class-uniform estimate on `∇^{g₀}Rm(g₀) − ∇^{gBase}Rm(gBase)` upgrades to an
absolute sup on `∇^{g₀}Rm(g₀)` by adding this constant. -/
theorem exists_curvJet_sup (g : SmoothRiemannianMetric I M) (a : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ x : M,
        Real.sqrt (normSq0S (I := I) g x (4 + a)
          (iterCov (I := I) g 4 (metricRm04 (I := I) (M := M) g) a x)) ≤ K := by
  obtain ⟨C, hC0, hC⟩ :=
    sqrtNormSq0S_bddOn (I := I) (M := M) (K := (Set.univ : Set M)) isCompact_univ (4 + a) g
      (iterCov (I := I) g 4 (metricRm04 (I := I) (M := M) g) a)
  exact ⟨C, hC0, fun x => hC x (Set.mem_univ x)⟩

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
/-- **The order-`1` curvature-jet difference split.**

`∇^{g₀}Rm(g₀) − ∇^{gBase}Rm(gBase)` decomposes as the single-step
connection-difference applied to `Rm(g₀)` (the algebraic insertion `A ⋆ Rm(g₀)`,
`A = Γ(g₀) − Γ(gBase)`) plus the *base* covariant derivative of the order-`0`
curvature difference.  Pure operator algebra: `covStep` is additive and
`diffStep g₀ gBase = covStep g₀ − covStep gBase` by definition.

This is the shape in which the order-`1` envelope is assembled: the first summand
is bounded by `unifCurvJet1Conn`, the second is the differentiated Palatini
identity. -/
theorem curvJet1_diff_eq (g₀ gBase : SmoothRiemannianMetric I M) :
    iterCov (I := I) g₀ 4 (metricRm04 (I := I) (M := M) g₀) 1 -
        iterCov (I := I) gBase 4 (metricRm04 (I := I) (M := M) gBase) 1 =
      diffStep (I := I) g₀ gBase 4 (metricRm04 (I := I) (M := M) g₀) +
        covStep (I := I) gBase 4
          (metricRm04 (I := I) (M := M) g₀ - metricRm04 (I := I) (M := M) gBase) := by
  change covStep (I := I) g₀ 4 (metricRm04 (I := I) (M := M) g₀) -
      covStep (I := I) gBase 4 (metricRm04 (I := I) (M := M) gBase) = _
  rw [covStep_sub (I := I) gBase 4 (metricRm04 (I := I) (M := M) g₀)
    (metricRm04 (I := I) (M := M) gBase)]
  simp only [diffStep]
  abel

set_option linter.unusedVariables false in
set_option linter.unusedSectionVars false in
/-- **Class-uniform lowered-curvature sup (`1 ≤ Λ < 2`), `normSq0S` currency.**

Under `Λ`-comparability of `g₀` with `gBase` and the class metric-jet bounds at
orders `1` and `2`, the `g₀`-fibre norm of the lowered Riemann tensor `Rm(g₀)` is
bounded by `n² · F`, where `n = dim E` and `F` is the operator constant of
`unifCurvSup` (closed in `(Λ, gBase)` alone).

The proof evaluates the components of `metricRm04 g₀ x` in a `g₀`-orthonormal
frame through `metricRm04StdAt_eq_inner_riemannOp`: each component is a `g₀`-inner
product of a unit frame vector with `riemannOp (LeviCivita g₀)` on unit frame
vectors, hence bounded by `F` by Cauchy--Schwarz; summing the `n⁴` squared
components gives the claim.

This is the `(0,4)`-field face of the order-`0` curvature bound — the face the
generic `covStep`/`diffStep` norm layer consumes. -/
theorem unifRm04Sup
    (gBase g₀ : SmoothRiemannianMetric I M) {Λ : ℝ} (hΛ : 1 ≤ Λ) (hΛ2 : Λ < 2)
    (hcomp : ∀ (x : M) (v : TangentSpace I x),
      Λ⁻¹ * gBase.inner x v v ≤ g₀.inner x v v ∧
        g₀.inner x v v ≤ Λ * gBase.inner x v v)
    (hjet1 : MetricCovDerivOrderBoundOn (I := I) Set.univ 1 g₀ gBase Λ)
    (hjet2 : MetricCovDerivOrderBoundOn (I := I) Set.univ 2 g₀ gBase Λ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ x : M,
        Real.sqrt (normSq0S (I := I) g₀ x 4
          (metricRm04 (I := I) (M := M) g₀ x)) ≤ C := by
  classical
  obtain ⟨F, hF0, hF⟩ :=
    unifCurvSup (I := I) (M := M) gBase g₀ hΛ hcomp hjet1 hjet2
  refine ⟨(Module.finrank ℝ E : ℝ) ^ 2 * F, by positivity, fun x => ?_⟩
  obtain ⟨basis, hON⟩ := exists_gOrthonormalBasis (I := I) g₀ x
  have hinv : MetricInverseInBasis_gen (I := I) g₀ x basis
      (identityInvMetric (Idx := Fin (Module.finrank Real (TangentSpace I x)))) := by
    have h := metricInverseInBasis_of_orthonormal (I := I) g₀ basis hON
    intro i j
    simpa [identityInvMetric, diagonalInvMetric] using h i j
  -- each `g₀`-orthonormal frame component of `Rm(g₀)` is bounded by `F`
  have hcompB : ∀ slots : Fin 4 → Fin (Module.finrank Real (TangentSpace I x)),
      |component0S (I := I) basis (metricRm04 (I := I) (M := M) g₀ x) slots| ≤ F := by
    intro slots
    have hvec : (fun a : Fin 4 => basis (slots a)) =
        vec4 (I := I) (basis (slots 0)) (basis (slots 1)) (basis (slots 2))
          (basis (slots 3)) := by
      funext a
      fin_cases a <;> simp [vec4]
    have hval : component0S (I := I) basis (metricRm04 (I := I) (M := M) g₀ x) slots =
        g₀.inner x (basis (slots 3))
          (riemannOp (cov := LeviCivita (I := I) g₀) x
            (basis (slots 0)) (basis (slots 1)) (basis (slots 2))) := by
      rw [component0S, hvec]
      rw [show metricRm04 (I := I) (M := M) g₀ x = metricRm04At (I := I) (M := M) g₀ x from rfl]
      rw [← metricRm04StdAt_apply (I := I) (M := M) g₀ x]
      exact metricRm04StdAt_eq_inner_riemannOp (I := I) (M := M) g₀ x _ _ _ _
    rw [hval]
    -- unit frame vectors
    have hunit : ∀ i, g₀.inner x (basis i) (basis i) = 1 := by
      intro i; rw [hON i i]; simp
    set R : TangentSpace I x :=
      riemannOp (cov := LeviCivita (I := I) g₀) x
        (basis (slots 0)) (basis (slots 1)) (basis (slots 2)) with hR
    have hRR : g₀.inner x R R ≤ F ^ 2 := by
      have := hF x (basis (slots 0)) (basis (slots 1)) (basis (slots 2))
      rw [hunit (slots 0), hunit (slots 1), hunit (slots 2)] at this
      simpa [hR] using this
    calc |g₀.inner x (basis (slots 3)) R|
        ≤ Real.sqrt (g₀.inner x (basis (slots 3)) (basis (slots 3))) *
            Real.sqrt (g₀.inner x R R) :=
          abs_metric_inner_le_sqrt_metric_quadratic (I := I) (M := M) g₀ x _ _
      _ = Real.sqrt (g₀.inner x R R) := by rw [hunit (slots 3)]; simp
      _ ≤ Real.sqrt (F ^ 2) := Real.sqrt_le_sqrt hRR
      _ = F := Real.sqrt_sq hF0
  have hcard := normSq0S_le_card_of_component_bound (I := I) g₀ x 4 basis hinv
    (metricRm04 (I := I) (M := M) g₀ x) F hF0 hcompB
  have hfr : Module.finrank Real (TangentSpace I x) = Module.finrank ℝ E := rfl
  have hcardval :
      (Fintype.card (Fin 4 → Fin (Module.finrank Real (TangentSpace I x))) : ℝ) =
        (Module.finrank ℝ E : ℝ) ^ 4 := by
    rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin, hfr]
    push_cast
    ring
  rw [hcardval] at hcard
  have hsq : (Module.finrank ℝ E : ℝ) ^ 4 * F ^ 2 =
      ((Module.finrank ℝ E : ℝ) ^ 2 * F) ^ 2 := by ring
  rw [hsq] at hcard
  calc Real.sqrt (normSq0S (I := I) g₀ x 4 (metricRm04 (I := I) (M := M) g₀ x))
      ≤ Real.sqrt (((Module.finrank ℝ E : ℝ) ^ 2 * F) ^ 2) := Real.sqrt_le_sqrt hcard
    _ = (Module.finrank ℝ E : ℝ) ^ 2 * F := Real.sqrt_sq (by positivity)

set_option linter.unusedSectionVars false in
/-- **The connection-insertion term of the order-`1` curvature-jet difference.**

The first summand of `curvJet1_diff_eq`, `(∇^{g₀} − ∇^{gBase})Rm(g₀)`, is the
algebraic insertion of `A = Γ(g₀) − Γ(gBase)` into the four slots of `Rm(g₀)`.
Under the `Λ`-class hypotheses its `g₀`-fibre norm is bounded uniformly on `M` by
the closed constant

`4 · √(n⁵) · (3/2)·√(Λ³)·Λ · (n² · F)`,

`F` the operator constant of `unifCurvSup`; the constant depends
only on `(Λ, gBase)` and is fixed before any class member `g₀` is named.

Composes the generic single-step connection-difference estimate
`diffStep_jet_one_le` (applied at rank `s = 4` with the roles `g₁ = gBase`,
`g₂ = g₀`, so that the norm is taken in `g₀` and the metric jet is the class
jet `∇^{gBase}g₀`) with the order-`0` curvature sup `unifRm04Sup`. -/
theorem unifCurvJet1Conn
    (gBase g₀ : SmoothRiemannianMetric I M) {Λ : ℝ} (hΛ : 1 ≤ Λ) (hΛ2 : Λ < 2)
    (hcomp : ∀ (x : M) (v : TangentSpace I x),
      Λ⁻¹ * gBase.inner x v v ≤ g₀.inner x v v ∧
        g₀.inner x v v ≤ Λ * gBase.inner x v v)
    (hjet1 : MetricCovDerivOrderBoundOn (I := I) Set.univ 1 g₀ gBase Λ)
    (hjet2 : MetricCovDerivOrderBoundOn (I := I) Set.univ 2 g₀ gBase Λ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ x : M,
        Real.sqrt (normSq0S (I := I) g₀ x 5
          (diffStep (I := I) g₀ gBase 4
            (metricRm04 (I := I) (M := M) g₀) x)) ≤ C := by
  classical
  have hΛ0 : (0 : ℝ) < Λ := lt_of_lt_of_le one_pos hΛ
  obtain ⟨C0, hC00, hC0⟩ :=
    unifRm04Sup (I := I) (M := M) gBase g₀ hΛ hΛ2 hcomp hjet1 hjet2
  have hEq : MetricUniformEquivalentOn (I := I) Set.univ gBase g₀ Λ :=
    ⟨hΛ, fun x _ v => hcomp x v⟩
  refine ⟨(4 : ℝ) * Real.sqrt ((Module.finrank ℝ E : ℝ) ^ 5) *
    ((3 / 2 : ℝ) * (Real.sqrt (Λ ^ 3) * Λ)) * C0, by positivity, fun x => ?_⟩
  -- swap the roles of the two metrics inside `diffStep` (the norm is `g₀`-side)
  have hneg : diffStep (I := I) g₀ gBase 4 (metricRm04 (I := I) (M := M) g₀) x =
      -(diffStep (I := I) gBase g₀ 4 (metricRm04 (I := I) (M := M) g₀) x) := by
    simp only [diffStep, ContMDiffSection.coe_sub, Pi.sub_apply]
    abel
  rw [hneg, normSq0S_neg]
  refine le_trans
    (diffStep_jet_one_le (I := I) (M := M) gBase g₀ 4
      (metricRm04 (I := I) (M := M) g₀) hEq hjet1 (Set.mem_univ x)) ?_
  have hpre : (0 : ℝ) ≤ (4 : ℝ) * Real.sqrt ((Module.finrank ℝ E : ℝ) ^ 5) *
      ((3 / 2 : ℝ) * (Real.sqrt (Λ ^ 3) * Λ)) := by positivity
  have hstep := mul_le_mul_of_nonneg_left (hC0 x) hpre
  refine le_trans (le_of_eq ?_) hstep
  norm_num

end RicciFlow
end PDE
end DifferentialGeometry
