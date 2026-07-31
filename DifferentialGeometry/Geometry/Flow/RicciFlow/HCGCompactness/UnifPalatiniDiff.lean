import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.UnifCurvatureJet1Diff
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.ConnDiffDeriv2Bound
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.PointwiseCurvatureDerivative

/-!
# The order-`1` curvature-jet envelope: the Palatini term (brick 2a-hi, stage 3)

`UnifCurvatureJet1Diff.lean` split the order-`1` curvature-jet difference as

`∇^{g₀}Rm(g₀) − ∇^{gBase}Rm(gBase)
   = diffStep g₀ gBase 4 (Rm(g₀)) + covStep gBase 4 (Rm(g₀) − Rm(gBase))`

and closed the first summand (`unifCurvJet1Conn`).  This file attacks the second
one.  The routing observation that makes it tractable is that the *lowered*
`(0,4)` picture is the wrong one: the `(0,4)` difference carries a
lowering defect (`Rm(0,4)` is `Rm(1,3)` lowered by two *different* metrics), and
`covStep` of it needs a metric-compatibility Leibniz on top of the Palatini
identity.  Both disappear at the `(1,3)` level, where the whole envelope reduces
to a single pointwise object:

`nablaRiemannOp g x D X Y Z = (∇_D R)(X,Y)Z`
(`Geometry/Curvature/CurvatureOperator/PointwiseCurvatureDerivative.lean`).

The reduction is `curvJet1_eval` + `curvJet1_normSq_le_of_op` below: the rank-`5`
field `iterCov g 4 (metricRm04 g) 1` is the `g`-lowering of `nablaRiemannOp g` in
its last slot, so a pointwise `g`-quintilinear bound on `nablaRiemannOp g`
*is* the `normSq0S` envelope.
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

set_option linter.unusedSectionVars false in
/-- **The order-`1` curvature jet is the lowered pointwise curvature derivative.**

`iterCov g 4 (metricRm04 g) 1` — the generic-currency `∇Rm(g)` of the
`covStep`/`diffStep` machinery — evaluated on five tangent vectors is the
`g`-lowering, in the last slot, of the pointwise operator
`nablaRiemannOp g x D X Y Z = (∇_D R)(X,Y)Z`.

Repackaging of `nablaRm04_apply` in the `iterCov` currency; it is the bridge that
lets an order-`1` curvature estimate be proved on the `(1,3)` operator (where
there is no lowering defect) and then read off on the `(0,5)` field. -/
theorem curvJet1_eval (g : SmoothRiemannianMetric I M) (x : M)
    (D X Y Z W : TangentSpace I x) :
    iterCov (I := I) g 4 (metricRm04 (I := I) (M := M) g) 1 x
        (vec5 (I := I) D X Y Z W) =
      g.inner x W (nablaRiemannOp (I := I) g x D X Y Z) :=
  nablaRm04_apply (I := I) (M := M) g x D X Y Z W

set_option linter.unusedSectionVars false in
/-- **Operator-to-field conversion for the order-`1` curvature jet.**

A pointwise `g`-quadrilinear bound on `nablaRiemannOp g` upgrades to a
`normSq0S` bound on the rank-`5` field `∇Rm(g) = iterCov g 4 (metricRm04 g) 1`,
with the dimensional factor `√(n⁵)` coming from summing the `n⁵` components in a
`g`-orthonormal frame.

Same shape as `unifRm04Sup` one order down; it is the face the generic
`covStep`/`diffStep` norm layer consumes. -/
theorem curvJet1_normSq_le_of_op
    (g : SmoothRiemannianMetric I M) {K : ℝ} (hK : 0 ≤ K)
    (hop : ∀ (x : M) (D X Y Z : TangentSpace I x),
      Real.sqrt (g.inner x (nablaRiemannOp (I := I) g x D X Y Z)
          (nablaRiemannOp (I := I) g x D X Y Z)) ≤
        K * Real.sqrt (g.inner x D D) * Real.sqrt (g.inner x X X) *
          Real.sqrt (g.inner x Y Y) * Real.sqrt (g.inner x Z Z))
    (x : M) :
    Real.sqrt (normSq0S (I := I) g x 5
        (iterCov (I := I) g 4 (metricRm04 (I := I) (M := M) g) 1 x)) ≤
      Real.sqrt ((Module.finrank ℝ E : ℝ) ^ 5) * K := by
  classical
  obtain ⟨basis, hON⟩ := exists_gOrthonormalBasis (I := I) g x
  have hinv : MetricInverseInBasis_gen (I := I) g x basis
      (identityInvMetric (Idx := Fin (Module.finrank Real (TangentSpace I x)))) := by
    have h := metricInverseInBasis_of_orthonormal (I := I) g basis hON
    intro i j
    simpa [identityInvMetric, diagonalInvMetric] using h i j
  have hunit : ∀ i, g.inner x (basis i) (basis i) = 1 := by
    intro i; rw [hON i i]; simp
  have hcompB : ∀ slots : Fin 5 → Fin (Module.finrank Real (TangentSpace I x)),
      |component0S (I := I) basis
        (iterCov (I := I) g 4 (metricRm04 (I := I) (M := M) g) 1 x) slots| ≤ K := by
    intro slots
    have hvec : (fun a : Fin 5 => basis (slots a)) =
        vec5 (I := I) (basis (slots 0)) (basis (slots 1)) (basis (slots 2))
          (basis (slots 3)) (basis (slots 4)) := by
      funext a
      fin_cases a <;> simp [vec5]
    have hval : component0S (I := I) basis
        (iterCov (I := I) g 4 (metricRm04 (I := I) (M := M) g) 1 x) slots =
        g.inner x (basis (slots 4))
          (nablaRiemannOp (I := I) g x (basis (slots 0)) (basis (slots 1))
            (basis (slots 2)) (basis (slots 3))) := by
      rw [component0S, hvec]
      exact curvJet1_eval (I := I) (M := M) g x _ _ _ _ _
    rw [hval]
    set N : TangentSpace I x :=
      nablaRiemannOp (I := I) g x (basis (slots 0)) (basis (slots 1))
        (basis (slots 2)) (basis (slots 3)) with hN
    have hNN : Real.sqrt (g.inner x N N) ≤ K := by
      have h := hop x (basis (slots 0)) (basis (slots 1)) (basis (slots 2))
        (basis (slots 3))
      rw [hunit (slots 0), hunit (slots 1), hunit (slots 2), hunit (slots 3)] at h
      simpa [hN] using h
    calc |g.inner x (basis (slots 4)) N|
        ≤ Real.sqrt (g.inner x (basis (slots 4)) (basis (slots 4))) *
            Real.sqrt (g.inner x N N) :=
          abs_metric_inner_le_sqrt_metric_quadratic (I := I) (M := M) g x _ _
      _ = Real.sqrt (g.inner x N N) := by rw [hunit (slots 4)]; simp
      _ ≤ K := hNN
  have hcard := normSq0S_le_card_of_component_bound (I := I) g x 5 basis hinv
    (iterCov (I := I) g 4 (metricRm04 (I := I) (M := M) g) 1 x) K hK hcompB
  have hfr : Module.finrank Real (TangentSpace I x) = Module.finrank ℝ E := rfl
  have hcardval :
      (Fintype.card (Fin 5 → Fin (Module.finrank Real (TangentSpace I x))) : ℝ) =
        (Module.finrank ℝ E : ℝ) ^ 5 := by
    rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin, hfr]
    push_cast
    ring
  rw [hcardval] at hcard
  calc Real.sqrt (normSq0S (I := I) g x 5
        (iterCov (I := I) g 4 (metricRm04 (I := I) (M := M) g) 1 x))
      ≤ Real.sqrt ((Module.finrank ℝ E : ℝ) ^ 5 * K ^ 2) := Real.sqrt_le_sqrt hcard
    _ = Real.sqrt ((Module.finrank ℝ E : ℝ) ^ 5) * K := by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hK]

/-! ## Tensoriality of the connection-difference derivative

`covDerivConnDiff g₂ g₁ W X Y x` is *defined* through Leibniz corrections on smooth
sections, so nothing in its definition says its value depends only on
`(W x, X x, Y x)`.  It does, and the cheapest proof is the differentiated Koszul
identity `connDiff_koszul_deriv`, whose right-hand side is manifestly a function
of the four slot *values* once `nabla0SFun` is folded back into
`totalNabla0SFun` (`totalNabla0SFun_apply_section`).  Nondegeneracy of `g₁` then
pins the vector.

This is what lets the ext-form analytic atoms (`covDerivConnDiff_gJet_le`,
`unifCovConnDiffSup`, `covDConnDiff2_gJet_le`) be applied to the non-`ext` slots
produced by the differentiated Palatini expansion. -/

set_option linter.unusedSectionVars false in
/-- **Tensoriality of `∇A`.**  The value of `covDerivConnDiff g₂ g₁ W X Y` at `x`
depends on the three sections only through their values at `x`. -/
theorem covDerivConnDiff_congr
    (g₂ g₁ : SmoothRiemannianMetric I M)
    (W X Y W' X' Y' : ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _))
    {x : M} (hW : W x = W' x) (hX : X x = X' x) (hY : Y x = Y' x) :
    covDerivConnDiff (I := I) g₂ g₁ W X Y x =
      covDerivConnDiff (I := I) g₂ g₁ W' X' Y' x := by
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
  haveI : ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I :=
    TangentBundle.contMDiffVectorBundle (I := I) (M := M) (n := 1)
  have hpair : ∀ Z : ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _),
      g₁.inner x (covDerivConnDiff (I := I) g₂ g₁ W X Y x) (Z x) =
        g₁.inner x (covDerivConnDiff (I := I) g₂ g₁ W' X' Y' x) (Z x) := by
    intro Z
    have h1 := connDiff_koszul_deriv (I := I) g₁ g₂ W X Y Z x
    have h2 := connDiff_koszul_deriv (I := I) g₁ g₂ W' X' Y' Z x
    simp only [← Tensor0SBundle.totalNabla0SFun_apply_section] at h1 h2
    rw [hW, hX, hY] at h1
    have h3 := h1.trans h2.symm
    linarith [h3]
  set a : TangentSpace I x := covDerivConnDiff (I := I) g₂ g₁ W X Y x with ha
  set b : TangentSpace I x := covDerivConnDiff (I := I) g₂ g₁ W' X' Y' x with hb
  have hZ := hpair (ContMDiffSection.mk (smoothExtensionTangent (I := I) x (a - b))
    (smoothExtensionTangent_contMDiff (I := I) x (a - b)))
  rw [ContMDiffSection.coeFn_mk, smoothExtensionTangent_eq] at hZ
  have hsym1 : g₁.inner x a (a - b) = g₁.inner x (a - b) a := g₁.symm x a (a - b)
  have hsym2 : g₁.inner x b (a - b) = g₁.inner x (a - b) b := g₁.symm x b (a - b)
  have hzero : g₁.inner x (a - b) (a - b) = 0 := by
    rw [map_sub, ← hsym1, ← hsym2, hZ, sub_self]
  have hsub : a - b = 0 := by
    by_contra hne
    exact (ne_of_gt (g₁.pos x (a - b) hne)) hzero
  exact sub_eq_zero.mp hsub

set_option linter.unusedSectionVars false in
/-- **`∇A` in canonical-extension form.**  Every `covDerivConnDiff` value is the
one taken on the canonical smooth extensions of its slot values — the shape all
the analytic atoms of the lane are stated in. -/
theorem covDerivConnDiff_eq_ext
    (g₂ g₁ : SmoothRiemannianMetric I M)
    (W X Y : ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _)) (x : M) :
    covDerivConnDiff (I := I) g₂ g₁ W X Y x =
      covDerivConnDiff (I := I) g₂ g₁
        (smoothExtensionTangent (I := I) x (W x))
        (smoothExtensionTangent (I := I) x (X x))
        (smoothExtensionTangent (I := I) x (Y x)) x := by
  refine covDerivConnDiff_congr (I := I) g₂ g₁ W X Y
    (ContMDiffSection.mk (smoothExtensionTangent (I := I) x (W x))
      (smoothExtensionTangent_contMDiff (I := I) x (W x)))
    (ContMDiffSection.mk (smoothExtensionTangent (I := I) x (X x))
      (smoothExtensionTangent_contMDiff (I := I) x (X x)))
    (ContMDiffSection.mk (smoothExtensionTangent (I := I) x (Y x))
      (smoothExtensionTangent_contMDiff (I := I) x (Y x)))
    ?_ ?_ ?_ <;>
  · exact (smoothExtensionTangent_eq (I := I) _ _).symm

/-! ## The `(1,3)` differentiated Palatini split -/

set_option linter.unusedSectionVars false in
private theorem cov_apply_sub
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    {S T : Π b : M, TangentSpace I b} {x : M}
    (hS : MDiffAt (T% S) x) (hT : MDiffAt (T% T) x) (v : TangentSpace I x) :
    cov.toFun (fun p => S p - T p) x v = cov.toFun S x v - cov.toFun T x v := by
  have hST : (fun p => S p - T p) = S + (-T) := by
    funext p; simp [sub_eq_add_neg]
  have hneg : cov.toFun (-T) x = (-1 : ℝ) • cov.toFun T x := by
    simpa using cov.isCovariantDerivativeOnUniv.smul_const (-1 : ℝ) hT
  rw [hST, cov.isCovariantDerivativeOnUniv.add hS (mdifferentiableAt_neg_section hT),
    hneg]
  simp

/-- **The mixed curvature derivative `(∇^{covD} R^{covR})(X,Y)Z`.**

`curvCovDerivOpAt` with the differentiating connection and the curvature-producing
connection decoupled.  At `covD = covR` it is `curvCovDerivOpAt` on the nose; the
brick needs the genuinely mixed value `covD = ∇^{gBase}`, `covR = ∇^{g₀}`, which
is `∇^{gBase}Rm(g₀)` — the object the order-`1` envelope must bound. -/
noncomputable def curvCovDerivOpAtOf
    (covD covR : CovariantDerivative I E (TangentSpace I : M → Type _))
    (D X Y Z : ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _)) (x : M) : TangentSpace I x :=
  (covD (fun p : M =>
      connectionRiemannCurvatureField (I := I) covR
        (fun q : M => X q) (fun q : M => Y q) (fun q : M => Z q) p) x) (D x) -
    connectionRiemannCurvatureField (I := I) covR
      (fun p : M => (covD (fun q : M => X q) p) (D p))
      (fun p : M => Y p) (fun p : M => Z p) x -
    connectionRiemannCurvatureField (I := I) covR
      (fun p : M => X p)
      (fun p : M => (covD (fun q : M => Y q) p) (D p))
      (fun p : M => Z p) x -
    connectionRiemannCurvatureField (I := I) covR
      (fun p : M => X p) (fun p : M => Y p)
      (fun p : M => (covD (fun q : M => Z q) p) (D p)) x

set_option linter.unusedSectionVars false in
/-- `curvCovDerivOpAtOf cov cov` is `curvCovDerivOpAt cov`. -/
theorem curvCovDerivOpAtOf_self
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (D X Y Z : ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _)) (x : M) :
    curvCovDerivOpAtOf (I := I) cov cov D X Y Z x =
      curvCovDerivOpAt (I := I) cov D X Y Z x := rfl

/-- **The Palatini `(1,3)` difference field** `Pal(X,Y,Z) = R^{g₀}(X,Y)Z − R^{gB}(X,Y)Z`. -/
noncomputable def palSec (gB g₀ : SmoothRiemannianMetric I M)
    (X Y Z : Π b : M, TangentSpace I b) : Π b : M, TangentSpace I b :=
  fun p =>
    connectionRiemannCurvatureField (I := I) (LeviCivita (I := I) g₀) X Y Z p -
      connectionRiemannCurvatureField (I := I) (LeviCivita (I := I) gB) X Y Z p

/-- **The tensorial base derivative of the Palatini field**, `(∇^{gB}_D Pal)(X,Y,Z)`.

This is the only genuinely new analytic object of the order-`1` envelope: it is a
combination of `∇^{gB,2}A` and `(∇^{gB}A)⋆A`, with no curvature on the
right-hand side — which is why the route is not circular. -/
noncomputable def covDerivPal (gB g₀ : SmoothRiemannianMetric I M)
    (D X Y Z : ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _)) (x : M) : TangentSpace I x :=
  (LeviCivita (I := I) gB).toFun (palSec (I := I) gB g₀
      (fun q : M => X q) (fun q : M => Y q) (fun q : M => Z q)) x (D x) -
    palSec (I := I) gB g₀
      (fun p : M => ((LeviCivita (I := I) gB) (fun q : M => X q) p) (D p))
      (fun p : M => Y p) (fun p : M => Z p) x -
    palSec (I := I) gB g₀ (fun p : M => X p)
      (fun p : M => ((LeviCivita (I := I) gB) (fun q : M => Y q) p) (D p))
      (fun p : M => Z p) x -
    palSec (I := I) gB g₀ (fun p : M => X p) (fun p : M => Y p)
      (fun p : M => ((LeviCivita (I := I) gB) (fun q : M => Z q) p) (D p)) x

set_option linter.unusedSectionVars false in
/-- **Mixed-minus-base: the derivative of the Palatini field.**

`∇^{gB}Rm(g₀) − ∇^{gB}Rm(gB) = ∇^{gB}(Rm(g₀) − Rm(gB))`, the three Leibniz slot
corrections distributing over the difference.  Pure bookkeeping (`cov_apply_sub`
plus the definition of `palSec`). -/
theorem curvCovDerivOf_sub_base (gB g₀ : SmoothRiemannianMetric I M)
    (D X Y Z : ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _)) (x : M) :
    curvCovDerivOpAtOf (I := I) (LeviCivita (I := I) gB) (LeviCivita (I := I) g₀)
        D X Y Z x -
      curvCovDerivOpAt (I := I) (LeviCivita (I := I) gB) D X Y Z x =
      covDerivPal (I := I) gB g₀ D X Y Z x := by
  classical
  have hcov₀ : CovariantDerivative.ContMDiffCovariantDerivativeLocally
      (I := I) (E := E) (M := M) (LeviCivita (I := I) gB) (∞ : WithTop ℕ∞) :=
    leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally (I := I) (M := M) gB
  have hcov₁ : CovariantDerivative.ContMDiffCovariantDerivativeLocally
      (I := I) (E := E) (M := M) (LeviCivita (I := I) g₀) (∞ : WithTop ℕ∞) :=
    leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally (I := I) (M := M) g₀
  have hR₁ : MDiffAt (T% (fun p : M =>
      connectionRiemannCurvatureField (I := I) (LeviCivita (I := I) g₀)
        (fun q : M => X q) (fun q : M => Y q) (fun q : M => Z q) p)) x :=
    (CovariantDerivative.curvField_contMDiffAt (I := I)
      (LeviCivita (I := I) g₀) hcov₁ X Y Z x).mdifferentiableAt (by simp)
  have hR₀ : MDiffAt (T% (fun p : M =>
      connectionRiemannCurvatureField (I := I) (LeviCivita (I := I) gB)
        (fun q : M => X q) (fun q : M => Y q) (fun q : M => Z q) p)) x :=
    (CovariantDerivative.curvField_contMDiffAt (I := I)
      (LeviCivita (I := I) gB) hcov₀ X Y Z x).mdifferentiableAt (by simp)
  unfold curvCovDerivOpAtOf curvCovDerivOpAt covDerivPal
  rw [show (palSec (I := I) gB g₀ (fun q : M => X q) (fun q : M => Y q)
        (fun q : M => Z q)) =
      (fun p : M =>
        connectionRiemannCurvatureField (I := I) (LeviCivita (I := I) g₀)
          (fun q : M => X q) (fun q : M => Y q) (fun q : M => Z q) p -
        connectionRiemannCurvatureField (I := I) (LeviCivita (I := I) gB)
          (fun q : M => X q) (fun q : M => Y q) (fun q : M => Z q) p) from rfl,
    cov_apply_sub (I := I) (LeviCivita (I := I) gB) hR₁ hR₀ (D x)]
  simp only [palSec]
  abel

end RicciFlow
end PDE
end DifferentialGeometry
