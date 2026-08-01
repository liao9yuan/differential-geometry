import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.UnifPalatiniJet1
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.UnifCurvaturePack
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.PointwiseCurvatureDerivative
import DifferentialGeometry.Geometry.Flow.ConnectionDifference

/-!
# The class-uniform first curvature jet

This module assembles the intrinsic `(1,3)` curvature-derivative split.  The
base derivative of the curvature difference is the differentiated Palatini
term, while changing the differentiating connection contributes four
algebraic connection-insertion terms.  The resulting estimates hold for every
metric-comparability factor `Λ ≥ 1`; no perturbative `Λ < 2` gate remains.
-/

set_option autoImplicit false

noncomputable section

set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000

open Bundle Manifold Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff BigOperators
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.HCGCompactness
open DifferentialGeometry.Analysis.Laplacian

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
private local instance : IsManifold I 1 M :=
  IsManifold.of_le (I := I) (M := M) (n := ∞)
    (by decide : (1 : WithTop ℕ∞) ≤ ∞)
private local instance : IsManifold I (1 + 1) M :=
  IsManifold.of_le (I := I) (M := M) (n := ∞)
    (by decide : ((1 : WithTop ℕ∞) + 1) ≤ ∞)
private local instance :
    ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I :=
  TangentBundle.contMDiffVectorBundle (I := I) (M := M) (n := 1)

private noncomputable def extSec1 (x : M) (v : TangentSpace I x) :
    ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _) :=
  ContMDiffSection.mk (smoothExtensionTangent (I := I) x v)
    (smoothExtensionTangent_contMDiff (I := I) x v)

set_option linter.unusedSectionVars false in
@[simp] private theorem extSec1_apply (x : M) (v : TangentSpace I x) :
    extSec1 (I := I) x v x = v :=
  smoothExtensionTangent_eq (I := I) x v

/-- The four algebraic terms produced by changing the differentiating
connection from `gBase` to `g₀` while keeping the curvature operator of `g₀`. -/
noncomputable def curvConnAt
    (gBase g₀ : SmoothRiemannianMetric I M) (x : M)
    (D X Y Z : TangentSpace I x) : TangentSpace I x :=
  let A := DeTurck.connDiff (I := I) g₀ gBase x
  let R := riemannOp (cov := LeviCivita (I := I) g₀) x
  A (R X Y Z) D -
      R (A X D) Y Z -
    R X (A Y D) Z -
  R X Y (A Z D)

set_option linter.unusedSectionVars false in
/-- The pointwise first curvature derivative is the sum of the connection
insertion, differentiated Palatini, and fixed-background terms. -/
theorem nablaRm_split
    (gBase g₀ : SmoothRiemannianMetric I M) (x : M)
    (D X Y Z : TangentSpace I x) :
    nablaRiemannOp (I := I) g₀ x D X Y Z =
      curvConnAt (I := I) gBase g₀ x D X Y Z +
        covDerivPalatini (I := I) gBase g₀
          (extSec1 (I := I) x D) (extSec1 (I := I) x X)
          (extSec1 (I := I) x Y) (extSec1 (I := I) x Z) x +
        nablaRiemannOp (I := I) gBase x D X Y Z := by
  classical
  let Ds := extSec1 (I := I) x D
  let Xs := extSec1 (I := I) x X
  let Ys := extSec1 (I := I) x Y
  let Zs := extSec1 (I := I) x Z
  let covB := LeviCivita (I := I) gBase
  let cov₀ := LeviCivita (I := I) g₀
  let Rsec : Π p : M, TangentSpace I p := fun p =>
    connectionRiemannCurvatureField (I := I) cov₀
      (fun q : M => Xs q) (fun q : M => Ys q) (fun q : M => Zs q) p
  have hcov₀ : CovariantDerivative.ContMDiffCovariantDerivativeLocally
      (I := I) (E := E) (M := M) cov₀ (∞ : WithTop ℕ∞) := by
    simpa [cov₀] using
      leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally
        (I := I) (M := M) g₀
  have hR : ContMDiff I (I.prod 𝓘(ℝ, E)) (∞ : WithTop ℕ∞) (T% Rsec) :=
    fun p => by
      simpa [Rsec] using
        CovariantDerivative.curvField_contMDiffAt
          (I := I) cov₀ hcov₀ Xs Ys Zs p
  have houter0 := DeTurck.connDiff_apply (I := I) g₀ gBase
    ((hR x).mdifferentiableAt (by simp)) (Ds x)
  have hX0 := DeTurck.connDiff_apply (I := I) g₀ gBase
    (Xs.contMDiff.contMDiffAt.mdifferentiableAt (by simp)) (Ds x)
  have hY0 := DeTurck.connDiff_apply (I := I) g₀ gBase
    (Ys.contMDiff.contMDiffAt.mdifferentiableAt (by simp)) (Ds x)
  have hZ0 := DeTurck.connDiff_apply (I := I) g₀ gBase
    (Zs.contMDiff.contMDiffAt.mdifferentiableAt (by simp)) (Ds x)
  have houter :
      cov₀.toFun Rsec x (Ds x) =
        covB.toFun Rsec x (Ds x) +
          DeTurck.connDiff (I := I) g₀ gBase x (Rsec x) (Ds x) := by
    have h := (sub_eq_iff_eq_add).mp houter0.symm
    simpa [covB, cov₀, add_comm] using h
  have hX :
      covApply cov₀ (fun p => Ds p) (fun p => Xs p) x =
        covApply covB (fun p => Ds p) (fun p => Xs p) x +
          DeTurck.connDiff (I := I) g₀ gBase x (Xs x) (Ds x) := by
    have h := (sub_eq_iff_eq_add).mp hX0.symm
    simpa [covApply, covB, cov₀, add_comm] using h
  have hY :
      covApply cov₀ (fun p => Ds p) (fun p => Ys p) x =
        covApply covB (fun p => Ds p) (fun p => Ys p) x +
          DeTurck.connDiff (I := I) g₀ gBase x (Ys x) (Ds x) := by
    have h := (sub_eq_iff_eq_add).mp hY0.symm
    simpa [covApply, covB, cov₀, add_comm] using h
  have hZ :
      covApply cov₀ (fun p => Ds p) (fun p => Zs p) x =
        covApply covB (fun p => Ds p) (fun p => Zs p) x +
          DeTurck.connDiff (I := I) g₀ gBase x (Zs x) (Ds x) := by
    have h := (sub_eq_iff_eq_add).mp hZ0.symm
    simpa [covApply, covB, cov₀, add_comm] using h
  have houterRaw :
      (LeviCivita (I := I) g₀).toFun
          (fun p : M =>
            connectionRiemannCurvatureField (I := I) (LeviCivita (I := I) g₀)
              (fun q : M => Xs q) (fun q : M => Ys q) (fun q : M => Zs q) p)
          x (Ds x) =
        (LeviCivita (I := I) gBase).toFun
            (fun p : M =>
              connectionRiemannCurvatureField (I := I) (LeviCivita (I := I) g₀)
                (fun q : M => Xs q) (fun q : M => Ys q) (fun q : M => Zs q) p)
            x (Ds x) +
          DeTurck.connDiff (I := I) g₀ gBase x
            (connectionRiemannCurvatureField (I := I) (LeviCivita (I := I) g₀)
              (fun q : M => Xs q) (fun q : M => Ys q) (fun q : M => Zs q) x)
            (Ds x) := by
    simpa [covB, cov₀, Rsec] using houter
  have hconn :
      curvCovDerivOpAt (I := I) cov₀ Ds Xs Ys Zs x -
          mixedCurvDeriv (I := I) gBase g₀ Ds Xs Ys Zs x =
        curvConnAt (I := I) gBase g₀ x D X Y Z := by
    have hDX₀ : ContMDiff I (I.prod 𝓘(ℝ, E)) (∞ : WithTop ℕ∞)
        (T% (covApply cov₀ (fun p => Ds p) (fun p => Xs p))) :=
      covApply_contMDiff (cov := cov₀) Ds.contMDiff Xs.contMDiff
    have hDY₀ : ContMDiff I (I.prod 𝓘(ℝ, E)) (∞ : WithTop ℕ∞)
        (T% (covApply cov₀ (fun p => Ds p) (fun p => Ys p))) :=
      covApply_contMDiff (cov := cov₀) Ds.contMDiff Ys.contMDiff
    have hDZ₀ : ContMDiff I (I.prod 𝓘(ℝ, E)) (∞ : WithTop ℕ∞)
        (T% (covApply cov₀ (fun p => Ds p) (fun p => Zs p))) :=
      covApply_contMDiff (cov := cov₀) Ds.contMDiff Zs.contMDiff
    have hDXB : ContMDiff I (I.prod 𝓘(ℝ, E)) (∞ : WithTop ℕ∞)
        (T% (covApply covB (fun p => Ds p) (fun p => Xs p))) :=
      covApply_contMDiff (cov := covB) Ds.contMDiff Xs.contMDiff
    have hDYB : ContMDiff I (I.prod 𝓘(ℝ, E)) (∞ : WithTop ℕ∞)
        (T% (covApply covB (fun p => Ds p) (fun p => Ys p))) :=
      covApply_contMDiff (cov := covB) Ds.contMDiff Ys.contMDiff
    have hDZB : ContMDiff I (I.prod 𝓘(ℝ, E)) (∞ : WithTop ℕ∞)
        (T% (covApply covB (fun p => Ds p) (fun p => Zs p))) :=
      covApply_contMDiff (cov := covB) Ds.contMDiff Zs.contMDiff
    have hRop_of
        (A B C : (p : M) → TangentSpace I p)
        (hA : ContMDiff I (I.prod 𝓘(ℝ, E)) (∞ : WithTop ℕ∞) (T% A))
        (hB : ContMDiff I (I.prod 𝓘(ℝ, E)) (∞ : WithTop ℕ∞) (T% B))
        (hC : ContMDiff I (I.prod 𝓘(ℝ, E)) (∞ : WithTop ℕ∞) (T% C)) :
        connectionRiemannCurvatureField (I := I) cov₀ A B C x =
          riemannOp (cov := cov₀) x (A x) (B x) (C x) := by
      change riemannSec cov₀ A B C x =
        riemannOp (cov := cov₀) x (A x) (B x) (C x)
      exact (riemannOp_apply_smooth (cov := cov₀) hA hB hC).symm
    have hRXYZ := hRop_of (fun p => Xs p) (fun p => Ys p) (fun p => Zs p)
      Xs.contMDiff Ys.contMDiff Zs.contMDiff
    have hRDX₀ := hRop_of
      (fun p => cov₀.toFun (fun q => Xs q) p (Ds p))
      (fun p => Ys p) (fun p => Zs p)
      (by simpa only [covApply] using hDX₀) Ys.contMDiff Zs.contMDiff
    have hRDXB := hRop_of
      (fun p => covB.toFun (fun q => Xs q) p (Ds p))
      (fun p => Ys p) (fun p => Zs p)
      (by simpa only [covApply] using hDXB) Ys.contMDiff Zs.contMDiff
    have hRDY₀ := hRop_of
      (fun p => Xs p) (fun p => cov₀.toFun (fun q => Ys q) p (Ds p))
      (fun p => Zs p) Xs.contMDiff
      (by simpa only [covApply] using hDY₀) Zs.contMDiff
    have hRDYB := hRop_of
      (fun p => Xs p) (fun p => covB.toFun (fun q => Ys q) p (Ds p))
      (fun p => Zs p) Xs.contMDiff
      (by simpa only [covApply] using hDYB) Zs.contMDiff
    have hRDZ₀ := hRop_of
      (fun p => Xs p) (fun p => Ys p)
      (fun p => cov₀.toFun (fun q => Zs q) p (Ds p))
      Xs.contMDiff Ys.contMDiff (by simpa only [covApply] using hDZ₀)
    have hRDZB := hRop_of
      (fun p => Xs p) (fun p => Ys p)
      (fun p => covB.toFun (fun q => Zs q) p (Ds p))
      Xs.contMDiff Ys.contMDiff (by simpa only [covApply] using hDZB)
    have hXRaw :
        cov₀.toFun (fun p => Xs p) x (Ds x) =
          covB.toFun (fun p => Xs p) x (Ds x) +
            DeTurck.connDiff (I := I) g₀ gBase x (Xs x) (Ds x) := by
      simpa only [covApply] using hX
    have hYRaw :
        cov₀.toFun (fun p => Ys p) x (Ds x) =
          covB.toFun (fun p => Ys p) x (Ds x) +
            DeTurck.connDiff (I := I) g₀ gBase x (Ys x) (Ds x) := by
      simpa only [covApply] using hY
    have hZRaw :
        cov₀.toFun (fun p => Zs p) x (Ds x) =
          covB.toFun (fun p => Zs p) x (Ds x) +
            DeTurck.connDiff (I := I) g₀ gBase x (Zs x) (Ds x) := by
      simpa only [covApply] using hZ
    unfold curvCovDerivOpAt mixedCurvDeriv curvConnAt
    simp only [cov₀]
    rw [houterRaw, hRXYZ, hRDX₀, hRDXB, hRDY₀, hRDYB, hRDZ₀, hRDZB]
    simp only
    rw [hXRaw, hYRaw, hZRaw]
    simp only [map_add, ContinuousLinearMap.add_apply]
    simp only [Ds, Xs, Ys, Zs, cov₀, extSec1_apply]
    abel
  have hpal := mixed_sub_eq_pal (I := I) gBase g₀ Ds Xs Ys Zs x
  have h₀ := nablaRiemannOp_eq (I := I) g₀ Ds Xs Ys Zs x
  have hB := nablaRiemannOp_eq (I := I) gBase Ds Xs Ys Zs x
  have hB' :
      curvCovDerivOpAt (I := I) covB Ds Xs Ys Zs x =
        nablaRiemannOp (I := I) gBase x (Ds x) (Xs x) (Ys x) (Zs x) := by
    simpa [covB] using hB.symm
  simpa [Ds, Xs, Ys, Zs, covB, cov₀] using
    calc
      nablaRiemannOp (I := I) g₀ x (Ds x) (Xs x) (Ys x) (Zs x) =
          curvCovDerivOpAt (I := I) cov₀ Ds Xs Ys Zs x := by
            simpa [cov₀] using h₀
      _ = (curvCovDerivOpAt (I := I) cov₀ Ds Xs Ys Zs x -
            mixedCurvDeriv (I := I) gBase g₀ Ds Xs Ys Zs x) +
          (mixedCurvDeriv (I := I) gBase g₀ Ds Xs Ys Zs x -
            curvCovDerivOpAt (I := I) covB Ds Xs Ys Zs x) +
          curvCovDerivOpAt (I := I) covB Ds Xs Ys Zs x := by abel
      _ = curvConnAt (I := I) gBase g₀ x D X Y Z +
          covDerivPalatini (I := I) gBase g₀ Ds Xs Ys Zs x +
          nablaRiemannOp (I := I) gBase x (Ds x) (Xs x) (Ys x) (Zs x) := by
            rw [hconn, hpal, hB']

set_option linter.unusedSectionVars false in
private theorem jet1_eval (g : SmoothRiemannianMetric I M) (x : M)
    (D X Y Z W : TangentSpace I x) :
    iterCov (I := I) g 4 (metricRm04 (I := I) (M := M) g) 1 x
        (vec5 (I := I) D X Y Z W) =
      g.inner x W (nablaRiemannOp (I := I) g x D X Y Z) :=
  nablaRm04_apply (I := I) (M := M) g x D X Y Z W

private theorem sqrt_cancel {q A : ℝ}
    (hq : 0 ≤ q) (hA : 0 ≤ A) (h : q ^ 2 ≤ A * q) :
    q ≤ A := by
  rcases hq.eq_or_lt with hq0 | hqpos
  · rw [← hq0]
    exact hA
  · exact le_of_mul_le_mul_right (by simpa [pow_two] using h) hqpos

set_option linter.unusedSectionVars false in
private theorem base_le_scaled
    (gBase g₀ : SmoothRiemannianMetric I M) {Λ : ℝ} (hΛ : 1 ≤ Λ)
    (hcomp : ∀ (x : M) (v : TangentSpace I x),
      Λ⁻¹ * gBase.inner x v v ≤ g₀.inner x v v ∧
        g₀.inner x v v ≤ Λ * gBase.inner x v v)
    (x : M) (v : TangentSpace I x) :
    gBase.inner x v v ≤ Λ * g₀.inner x v v := by
  have hΛ0 : (0 : ℝ) < Λ := lt_of_lt_of_le one_pos hΛ
  have hz := mul_le_mul_of_nonneg_left (hcomp x v).1 hΛ0.le
  rwa [← mul_assoc, mul_inv_cancel₀ hΛ0.ne', one_mul] at hz

private theorem sqrt_scaled {a b Λ : ℝ}
    (hΛ : 0 ≤ Λ) (h : a ≤ Λ * b) :
    Real.sqrt a ≤ Real.sqrt Λ * Real.sqrt b := by
  calc
    Real.sqrt a ≤ Real.sqrt (Λ * b) := Real.sqrt_le_sqrt h
    _ = Real.sqrt Λ * Real.sqrt b := Real.sqrt_mul hΛ b

private theorem sqrt_sq_mul3 {F a b c : ℝ}
    (hF : 0 ≤ F) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt (F ^ 2 * a * b * c) =
      F * Real.sqrt a * Real.sqrt b * Real.sqrt c := by
  rw [show F ^ 2 * a * b * c = F ^ 2 * (a * (b * c)) by ring,
    Real.sqrt_mul (sq_nonneg F), Real.sqrt_sq hF,
    Real.sqrt_mul ha, Real.sqrt_mul hb]
  ring

/-- Explicit coefficient for the connection-insertion part of `∇Rm`. -/
noncomputable def curvConnC (Λ Kb : ℝ) : ℝ :=
  4 * (Real.sqrt Λ) ^ 3 * (3 / 2 * Λ ^ 3 * Λ) *
    (Λ ^ 2 * (riemannDiffC Λ Λ Λ + Real.sqrt Kb))

/-- Explicit operator coefficient for the full first curvature jet. -/
noncomputable def rmOneOpC (Λ Kb₀ Kb₁ : ℝ) : ℝ :=
  curvConnC Λ Kb₀ + (Real.sqrt Λ) ^ 5 * palatiniOneC Λ +
    (Real.sqrt Λ) ^ 5 * Kb₁

/-- Explicit section-norm coefficient for the full first curvature jet. -/
noncomputable def rmOneC (Λ Kb₀ Kb₁ : ℝ) : ℝ :=
  Real.sqrt ((Module.finrank ℝ E : ℝ) ^ 5) * rmOneOpC Λ Kb₀ Kb₁

set_option linter.unusedSectionVars false in
private theorem curvConn_le_of
    (gBase g₀ : SmoothRiemannianMetric I M) {Λ : ℝ}
    (hΛ : 1 ≤ Λ)
    {Kb : ℝ} (hKb0 : 0 ≤ Kb)
    (hKb : ∀ (x : M) (v w u : TangentSpace I x),
      gBase.inner x (riemannOp (cov := LeviCivita (I := I) gBase) x v w u)
          (riemannOp (cov := LeviCivita (I := I) gBase) x v w u) ≤
        Kb * gBase.inner x v v * gBase.inner x w w * gBase.inner x u u)
    (hcomp : ∀ (x : M) (v : TangentSpace I x),
      Λ⁻¹ * gBase.inner x v v ≤ g₀.inner x v v ∧
        g₀.inner x v v ≤ Λ * gBase.inner x v v)
    (hjet1 : MetricCovDerivOrderBoundOn (I := I) Set.univ 1 g₀ gBase Λ)
    (hjet2 : MetricCovDerivOrderBoundOn (I := I) Set.univ 2 g₀ gBase Λ) :
    ∀ (x : M) (D X Y Z : TangentSpace I x),
      Real.sqrt (g₀.inner x
          (curvConnAt (I := I) gBase g₀ x D X Y Z)
          (curvConnAt (I := I) gBase g₀ x D X Y Z)) ≤
        curvConnC Λ Kb * Real.sqrt (g₀.inner x D D) *
          Real.sqrt (g₀.inner x X X) *
          Real.sqrt (g₀.inner x Y Y) *
          Real.sqrt (g₀.inner x Z Z) := by
  classical
  have hEq : MetricUniformEquivalentOn (I := I) Set.univ gBase g₀ Λ :=
    ⟨hΛ, fun x _ => hcomp x⟩
  let C₀ : ℝ := 3 / 2 * Λ ^ 3 * Λ
  have hC₀0 : 0 ≤ C₀ := by
    dsimp [C₀]
    positivity
  have hC₀ : ∀ (x : M) (v w : TangentSpace I x),
      Real.sqrt (gBase.inner x
          (DifferentialGeometry.PDE.DeTurck.connDiff (I := I) g₀ gBase x v w)
          (DifferentialGeometry.PDE.DeTurck.connDiff (I := I) g₀ gBase x v w)) ≤
        C₀ * Real.sqrt (gBase.inner x v v) * Real.sqrt (gBase.inner x w w) := by
    intro x v w
    have h := connDiff_gJet_le (I := I) hEq hjet1 (Set.mem_univ x) w v
    simpa [C₀, DifferentialGeometry.PDE.DeTurck.connDiff,
      mul_assoc, mul_left_comm, mul_comm] using h
  let F : ℝ := Λ ^ 2 * (riemannDiffC Λ Λ Λ + Real.sqrt Kb)
  have hF0 : 0 ≤ F := by
    dsimp [F, riemannDiffC]
    positivity
  have hF := unifCurvSup_of (I := I) (M := M) gBase g₀ hΛ
    hKb0 hKb hcomp hjet1 hjet2
  let S : ℝ := Real.sqrt Λ
  intro x D X Y Z
  let L₀ : TangentSpace I x → ℝ := fun v => Real.sqrt (g₀.inner x v v)
  let LB : TangentSpace I x → ℝ := fun v => Real.sqrt (gBase.inner x v v)
  let A := DeTurck.connDiff (I := I) g₀ gBase x
  let R := riemannOp (cov := LeviCivita (I := I) g₀) x
  let B : ℝ := S ^ 3 * C₀ * F * L₀ D * L₀ X * L₀ Y * L₀ Z
  have hΛ0 : 0 ≤ Λ := le_trans zero_le_one hΛ
  have h0B : ∀ v : TangentSpace I x, L₀ v ≤ S * LB v := by
    intro v
    exact sqrt_scaled hΛ0 (hcomp x v).2
  have hB0 : ∀ v : TangentSpace I x, LB v ≤ S * L₀ v := by
    intro v
    exact sqrt_scaled hΛ0 (base_le_scaled (I := I) (M := M)
      gBase g₀ hΛ hcomp x v)
  have hA : ∀ v w : TangentSpace I x,
      LB (A v w) ≤ C₀ * LB v * LB w := by
    intro v w
    simpa [LB, A] using hC₀ x v w
  have hR : ∀ v w u : TangentSpace I x,
      L₀ (R v w u) ≤ F * L₀ v * L₀ w * L₀ u := by
    intro v w u
    have h := hF x v w u
    calc
      L₀ (R v w u) ≤
          Real.sqrt (F ^ 2 * g₀.inner x v v *
            g₀.inner x w w * g₀.inner x u u) := by
        dsimp [L₀, R]
        exact Real.sqrt_le_sqrt h
      _ = F * L₀ v * L₀ w * L₀ u := by
        simpa [L₀] using sqrt_sq_mul3 hF0
          (metric_inner_self_nonneg (I := I) (M := M) g₀ x v)
          (metric_inner_self_nonneg (I := I) (M := M) g₀ x w)
  have houter : L₀ (A (R X Y Z) D) ≤ B := by
    calc
      L₀ (A (R X Y Z) D) ≤ S * LB (A (R X Y Z) D) := h0B _
      _ ≤ S * (C₀ * LB (R X Y Z) * LB D) := by
        gcongr
        exact hA _ _
      _ ≤ S * (C₀ * (S * L₀ (R X Y Z)) * (S * L₀ D)) := by
        gcongr
        · exact hB0 _
        · exact hB0 _
      _ ≤ S * (C₀ * (S * (F * L₀ X * L₀ Y * L₀ Z)) * (S * L₀ D)) := by
        gcongr
        exact hR _ _ _
      _ = B := by
        dsimp [B]
        ring
  have hX : L₀ (R (A X D) Y Z) ≤ B := by
    calc
      L₀ (R (A X D) Y Z) ≤ F * L₀ (A X D) * L₀ Y * L₀ Z := hR _ _ _
      _ ≤ F * (S * LB (A X D)) * L₀ Y * L₀ Z := by
        gcongr
        exact h0B _
      _ ≤ F * (S * (C₀ * LB X * LB D)) * L₀ Y * L₀ Z := by
        gcongr
        exact hA _ _
      _ ≤ F * (S * (C₀ * (S * L₀ X) * (S * L₀ D))) * L₀ Y * L₀ Z := by
        gcongr
        · exact hB0 _
        · exact hB0 _
      _ = B := by
        dsimp [B]
        ring
  have hY : L₀ (R X (A Y D) Z) ≤ B := by
    calc
      L₀ (R X (A Y D) Z) ≤ F * L₀ X * L₀ (A Y D) * L₀ Z := hR _ _ _
      _ ≤ F * L₀ X * (S * LB (A Y D)) * L₀ Z := by
        gcongr
        exact h0B _
      _ ≤ F * L₀ X * (S * (C₀ * LB Y * LB D)) * L₀ Z := by
        gcongr
        exact hA _ _
      _ ≤ F * L₀ X * (S * (C₀ * (S * L₀ Y) * (S * L₀ D))) * L₀ Z := by
        gcongr
        · exact hB0 _
        · exact hB0 _
      _ = B := by
        dsimp [B]
        ring
  have hZ : L₀ (R X Y (A Z D)) ≤ B := by
    calc
      L₀ (R X Y (A Z D)) ≤ F * L₀ X * L₀ Y * L₀ (A Z D) := hR _ _ _
      _ ≤ F * L₀ X * L₀ Y * (S * LB (A Z D)) := by
        gcongr
        exact h0B _
      _ ≤ F * L₀ X * L₀ Y * (S * (C₀ * LB Z * LB D)) := by
        gcongr
        exact hA _ _
      _ ≤ F * L₀ X * L₀ Y * (S * (C₀ * (S * L₀ Z) * (S * L₀ D))) := by
        gcongr
        · exact hB0 _
        · exact hB0 _
      _ = B := by
        dsimp [B]
        ring
  have hneg : ∀ v : TangentSpace I x, L₀ (-v) = L₀ v := by
    intro v
    simpa only [L₀, neg_one_smul, abs_neg, abs_one, one_mul] using
      Geometry.Riemannian.sqrt_inner_smul (I := I) g₀ x (-1 : ℝ) v
  have hsub : ∀ u v : TangentSpace I x, L₀ (u - v) ≤ L₀ u + L₀ v := by
    intro u v
    calc
      L₀ (u - v) = L₀ (u + -v) := by rw [sub_eq_add_neg]
      _ ≤ L₀ u + L₀ (-v) :=
        Geometry.Riemannian.sqrt_inner_add_le (I := I) g₀ x u (-v)
      _ = L₀ u + L₀ v := by rw [hneg]
  have hsum :
      L₀ (A (R X Y Z) D - R (A X D) Y Z -
          R X (A Y D) Z - R X Y (A Z D)) ≤ 4 * B := by
    calc
      L₀ (A (R X Y Z) D - R (A X D) Y Z -
          R X (A Y D) Z - R X Y (A Z D)) ≤
          L₀ (A (R X Y Z) D - R (A X D) Y Z -
            R X (A Y D) Z) + L₀ (R X Y (A Z D)) := hsub _ _
      _ ≤ (L₀ (A (R X Y Z) D - R (A X D) Y Z) +
            L₀ (R X (A Y D) Z)) + L₀ (R X Y (A Z D)) := by
        gcongr
        exact hsub _ _
      _ ≤ ((L₀ (A (R X Y Z) D) + L₀ (R (A X D) Y Z)) +
            L₀ (R X (A Y D) Z)) + L₀ (R X Y (A Z D)) := by
        gcongr
        exact hsub _ _
      _ ≤ ((B + B) + B) + B := by gcongr
      _ = 4 * B := by ring
  calc
    Real.sqrt (g₀.inner x
        (curvConnAt (I := I) gBase g₀ x D X Y Z)
        (curvConnAt (I := I) gBase g₀ x D X Y Z)) ≤ 4 * B := by
      simpa [curvConnAt, A, R, L₀] using hsum
    _ = (4 * S ^ 3 * C₀ * F) * Real.sqrt (g₀.inner x D D) *
        Real.sqrt (g₀.inner x X X) *
        Real.sqrt (g₀.inner x Y Y) *
        Real.sqrt (g₀.inner x Z Z) := by
      dsimp [B, L₀]
      ring
    _ = curvConnC Λ Kb * Real.sqrt (g₀.inner x D D) *
        Real.sqrt (g₀.inner x X X) *
        Real.sqrt (g₀.inner x Y Y) *
        Real.sqrt (g₀.inner x Z Z) := by
      dsimp [curvConnC, S, C₀, F]

set_option linter.unusedSectionVars false in
private theorem curvConn_le
    (gBase g₀ : SmoothRiemannianMetric I M) {Λ : ℝ}
    (hΛ : 1 ≤ Λ)
    (hcomp : ∀ (x : M) (v : TangentSpace I x),
      Λ⁻¹ * gBase.inner x v v ≤ g₀.inner x v v ∧
        g₀.inner x v v ≤ Λ * gBase.inner x v v)
    (hjet1 : MetricCovDerivOrderBoundOn (I := I) Set.univ 1 g₀ gBase Λ)
    (hjet2 : MetricCovDerivOrderBoundOn (I := I) Set.univ 2 g₀ gBase Λ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (x : M) (D X Y Z : TangentSpace I x),
        Real.sqrt (g₀.inner x
            (curvConnAt (I := I) gBase g₀ x D X Y Z)
            (curvConnAt (I := I) gBase g₀ x D X Y Z)) ≤
          C * Real.sqrt (g₀.inner x D D) *
            Real.sqrt (g₀.inner x X X) *
            Real.sqrt (g₀.inner x Y Y) *
            Real.sqrt (g₀.inner x Z Z) := by
  obtain ⟨Kb, hKb0, hKb⟩ :=
    exists_uniform_riemannOp_LeviCivita_gNorm_bound (I := I) (M := M) gBase
  refine ⟨curvConnC Λ Kb, ?_, ?_⟩
  · have hΛ0 : 0 ≤ Λ := le_trans zero_le_one hΛ
    dsimp [curvConnC, riemannDiffC]
    positivity
  · exact curvConn_le_of (I := I) (M := M) gBase g₀ hΛ
      hKb0 hKb hcomp hjet1 hjet2

set_option linter.unusedSectionVars false in
private theorem fixedRmOpOne_of (g : SmoothRiemannianMetric I M)
    {K : ℝ} (hK0 : 0 ≤ K)
    (hK : ∀ x : M,
      Real.sqrt (normSq0S (I := I) g x 5
        (iterCov (I := I) g 4 (metricRm04 (I := I) (M := M) g) 1 x)) ≤ K) :
    ∀ (x : M) (D X Y Z : TangentSpace I x),
      Real.sqrt (g.inner x
          (nablaRiemannOp (I := I) g x D X Y Z)
          (nablaRiemannOp (I := I) g x D X Y Z)) ≤
        K * Real.sqrt (g.inner x D D) *
          Real.sqrt (g.inner x X X) *
          Real.sqrt (g.inner x Y Y) *
          Real.sqrt (g.inner x Z Z) := by
  classical
  intro x D X Y Z
  let R : TangentSpace I x := nablaRiemannOp (I := I) g x D X Y Z
  let q : ℝ := Real.sqrt (g.inner x R R)
  let A : ℝ :=
    K * Real.sqrt (g.inner x D D) *
      Real.sqrt (g.inner x X X) *
      Real.sqrt (g.inner x Y Y) *
      Real.sqrt (g.inner x Z Z)
  have hRR : 0 ≤ g.inner x R R :=
    metric_inner_self_nonneg (I := I) (M := M) g x R
  have hA0 : 0 ≤ A := by
    dsimp [A]
    positivity
  have hraw := Tensor0SBundle.abs_apply_le_norm0S (I := I) g x 5
    (iterCov (I := I) g 4 (metricRm04 (I := I) (M := M) g) 1 x)
    (vec5 (I := I) D X Y Z R)
  rw [jet1_eval] at hraw
  have hprod :
      (∏ a : Fin 5,
          Real.sqrt (g.inner x
            (vec5 (I := I) D X Y Z R a)
            (vec5 (I := I) D X Y Z R a))) =
        Real.sqrt (g.inner x D D) *
          Real.sqrt (g.inner x X X) *
          Real.sqrt (g.inner x Y Y) *
          Real.sqrt (g.inner x Z Z) * q := by
    simp [vec5, Fin.prod_univ_succ, q, mul_assoc]
  have hprod0 : 0 ≤
      (∏ a : Fin 5,
        Real.sqrt (g.inner x
          (vec5 (I := I) D X Y Z R a)
          (vec5 (I := I) D X Y Z R a))) :=
    Finset.prod_nonneg fun _ _ => Real.sqrt_nonneg _
  have hbound := hraw.trans (mul_le_mul_of_nonneg_right (hK x) hprod0)
  rw [hprod, abs_of_nonneg hRR] at hbound
  have hquad : q ^ 2 ≤ A * q := by
    rw [show q ^ 2 = g.inner x R R from Real.sq_sqrt hRR]
    simpa [A, mul_assoc] using hbound
  have hq := sqrt_cancel (Real.sqrt_nonneg _) hA0 hquad
  simpa [q, A, R] using hq

set_option linter.unusedSectionVars false in
private theorem fixedRmOpOne (g : SmoothRiemannianMetric I M) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (x : M) (D X Y Z : TangentSpace I x),
        Real.sqrt (g.inner x
            (nablaRiemannOp (I := I) g x D X Y Z)
            (nablaRiemannOp (I := I) g x D X Y Z)) ≤
          K * Real.sqrt (g.inner x D D) *
            Real.sqrt (g.inner x X X) *
            Real.sqrt (g.inner x Y Y) *
            Real.sqrt (g.inner x Z Z) := by
  obtain ⟨K, hK0, hK⟩ := exists_curvJet_sup (I := I) (M := M) g 1
  exact ⟨K, hK0, fixedRmOpOne_of (I := I) (M := M) g hK0 hK⟩

set_option linter.unusedSectionVars false in
private theorem jet1_norm_le
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
    intro i
    rw [hON i i]
    simp
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
      exact jet1_eval (I := I) (M := M) g x _ _ _ _ _
    rw [hval]
    set N : TangentSpace I x :=
      nablaRiemannOp (I := I) g x (basis (slots 0)) (basis (slots 1))
        (basis (slots 2)) (basis (slots 3)) with hN
    have hNN : Real.sqrt (g.inner x N N) ≤ K := by
      have h := hop x (basis (slots 0)) (basis (slots 1)) (basis (slots 2))
        (basis (slots 3))
      rw [hunit (slots 0), hunit (slots 1), hunit (slots 2), hunit (slots 3)] at h
      simpa [hN] using h
    calc
      |g.inner x (basis (slots 4)) N| ≤
          Real.sqrt (g.inner x (basis (slots 4)) (basis (slots 4))) *
            Real.sqrt (g.inner x N N) :=
        abs_metric_inner_le_sqrt_metric_quadratic (I := I) (M := M) g x _ _
      _ = Real.sqrt (g.inner x N N) := by
        rw [hunit (slots 4)]
        simp
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
  calc
    Real.sqrt (normSq0S (I := I) g x 5
        (iterCov (I := I) g 4 (metricRm04 (I := I) (M := M) g) 1 x)) ≤
      Real.sqrt ((Module.finrank ℝ E : ℝ) ^ 5 * K ^ 2) :=
        Real.sqrt_le_sqrt hcard
    _ = Real.sqrt ((Module.finrank ℝ E : ℝ) ^ 5) * K := by
      rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hK]

set_option linter.unusedSectionVars false in
private theorem unifRmOpOne_of
    (gBase g₀ : SmoothRiemannianMetric I M) {Λ : ℝ}
    (hΛ : 1 ≤ Λ)
    {Kb₀ Kb₁ : ℝ} (hKb₀0 : 0 ≤ Kb₀)
    (hKb₀ : ∀ (x : M) (v w u : TangentSpace I x),
      gBase.inner x (riemannOp (cov := LeviCivita (I := I) gBase) x v w u)
          (riemannOp (cov := LeviCivita (I := I) gBase) x v w u) ≤
        Kb₀ * gBase.inner x v v * gBase.inner x w w * gBase.inner x u u)
    (hKb₁0 : 0 ≤ Kb₁)
    (hKb₁ : ∀ x : M,
      Real.sqrt (normSq0S (I := I) gBase x 5
        (iterCov (I := I) gBase 4
          (metricRm04 (I := I) (M := M) gBase) 1 x)) ≤ Kb₁)
    (hcomp : ∀ (x : M) (v : TangentSpace I x),
      Λ⁻¹ * gBase.inner x v v ≤ g₀.inner x v v ∧
        g₀.inner x v v ≤ Λ * gBase.inner x v v)
    (hjet1 : MetricCovDerivOrderBoundOn (I := I) Set.univ 1 g₀ gBase Λ)
    (hjet2 : MetricCovDerivOrderBoundOn (I := I) Set.univ 2 g₀ gBase Λ)
    (hjet3 : MetricCovDerivOrderBoundOn (I := I) Set.univ 3 g₀ gBase Λ) :
    ∀ (x : M) (D X Y Z : TangentSpace I x),
      Real.sqrt (g₀.inner x
          (nablaRiemannOp (I := I) g₀ x D X Y Z)
          (nablaRiemannOp (I := I) g₀ x D X Y Z)) ≤
        rmOneOpC Λ Kb₀ Kb₁ * Real.sqrt (g₀.inner x D D) *
          Real.sqrt (g₀.inner x X X) *
          Real.sqrt (g₀.inner x Y Y) *
          Real.sqrt (g₀.inner x Z Z) := by
  classical
  let Cc : ℝ := curvConnC Λ Kb₀
  let Cp : ℝ := palatiniOneC Λ
  let Cb : ℝ := Kb₁
  have hCc0 : 0 ≤ Cc := by
    have hΛ0 : 0 ≤ Λ := le_trans zero_le_one hΛ
    dsimp [Cc, curvConnC, riemannDiffC]
    positivity
  have hCp0 : 0 ≤ Cp := by
    dsimp [Cp, palatiniOneC]
    positivity
  have hCb0 : 0 ≤ Cb := by simpa [Cb] using hKb₁0
  have hCc := curvConn_le_of (I := I) (M := M) gBase g₀ hΛ
    hKb₀0 hKb₀ hcomp hjet1 hjet2
  have hCp := unifPalatini1_le (I := I) (M := M) gBase g₀
    hΛ hcomp hjet1 hjet2 hjet3
  have hCb := fixedRmOpOne_of (I := I) (M := M) gBase hKb₁0 hKb₁
  let S : ℝ := Real.sqrt Λ
  intro x D X Y Z
  let L₀ : TangentSpace I x → ℝ := fun v => Real.sqrt (g₀.inner x v v)
  let LB : TangentSpace I x → ℝ := fun v => Real.sqrt (gBase.inner x v v)
  let Vc : TangentSpace I x := curvConnAt (I := I) gBase g₀ x D X Y Z
  let Vp : TangentSpace I x :=
    covDerivPalatini (I := I) gBase g₀
      (extSec1 (I := I) x D) (extSec1 (I := I) x X)
      (extSec1 (I := I) x Y) (extSec1 (I := I) x Z) x
  let Vb : TangentSpace I x := nablaRiemannOp (I := I) gBase x D X Y Z
  have hΛ0 : 0 ≤ Λ := le_trans zero_le_one hΛ
  have h0B : ∀ v : TangentSpace I x, L₀ v ≤ S * LB v := by
    intro v
    exact sqrt_scaled hΛ0 (hcomp x v).2
  have hB0 : ∀ v : TangentSpace I x, LB v ≤ S * L₀ v := by
    intro v
    exact sqrt_scaled hΛ0 (base_le_scaled (I := I) (M := M)
      gBase g₀ hΛ hcomp x v)
  have hc : L₀ Vc ≤ Cc * L₀ D * L₀ X * L₀ Y * L₀ Z := by
    simpa [L₀, Vc] using hCc x D X Y Z
  have hpB : LB Vp ≤ Cp * LB D * LB X * LB Y * LB Z := by
    simpa [LB, Vp, palatiniJet1At, extSec1] using hCp x D X Y Z
  have hbB : LB Vb ≤ Cb * LB D * LB X * LB Y * LB Z := by
    simpa [LB, Vb] using hCb x D X Y Z
  have hp : L₀ Vp ≤ S ^ 5 * Cp * L₀ D * L₀ X * L₀ Y * L₀ Z := by
    calc
      L₀ Vp ≤ S * LB Vp := h0B _
      _ ≤ S * (Cp * LB D * LB X * LB Y * LB Z) := by
        gcongr
      _ ≤ S * (Cp * (S * L₀ D) * (S * L₀ X) *
          (S * L₀ Y) * (S * L₀ Z)) := by
        gcongr
        · exact hB0 _
        · exact hB0 _
        · exact hB0 _
        · exact hB0 _
      _ = S ^ 5 * Cp * L₀ D * L₀ X * L₀ Y * L₀ Z := by ring
  have hb : L₀ Vb ≤ S ^ 5 * Cb * L₀ D * L₀ X * L₀ Y * L₀ Z := by
    calc
      L₀ Vb ≤ S * LB Vb := h0B _
      _ ≤ S * (Cb * LB D * LB X * LB Y * LB Z) := by
        gcongr
      _ ≤ S * (Cb * (S * L₀ D) * (S * L₀ X) *
          (S * L₀ Y) * (S * L₀ Z)) := by
        gcongr
        · exact hB0 _
        · exact hB0 _
        · exact hB0 _
        · exact hB0 _
      _ = S ^ 5 * Cb * L₀ D * L₀ X * L₀ Y * L₀ Z := by ring
  have hsplit :
      nablaRiemannOp (I := I) g₀ x D X Y Z = Vc + Vp + Vb := by
    simpa [Vc, Vp, Vb] using
      nablaRm_split (I := I) (M := M) gBase g₀ x D X Y Z
  have hadd :
      L₀ (Vc + Vp + Vb) ≤ (L₀ Vc + L₀ Vp) + L₀ Vb := by
    calc
      L₀ (Vc + Vp + Vb) ≤ L₀ (Vc + Vp) + L₀ Vb := by
        simpa [L₀] using
          Geometry.Riemannian.sqrt_inner_add_le (I := I) g₀ x (Vc + Vp) Vb
      _ ≤ (L₀ Vc + L₀ Vp) + L₀ Vb := by
        gcongr
        simpa [L₀] using
          Geometry.Riemannian.sqrt_inner_add_le (I := I) g₀ x Vc Vp
  calc
    Real.sqrt (g₀.inner x
        (nablaRiemannOp (I := I) g₀ x D X Y Z)
        (nablaRiemannOp (I := I) g₀ x D X Y Z)) =
        L₀ (Vc + Vp + Vb) := by rw [hsplit]
    _ ≤ (L₀ Vc + L₀ Vp) + L₀ Vb := hadd
    _ ≤ (Cc * L₀ D * L₀ X * L₀ Y * L₀ Z +
          S ^ 5 * Cp * L₀ D * L₀ X * L₀ Y * L₀ Z) +
        S ^ 5 * Cb * L₀ D * L₀ X * L₀ Y * L₀ Z := by
      gcongr
    _ = (Cc + S ^ 5 * Cp + S ^ 5 * Cb) *
          Real.sqrt (g₀.inner x D D) *
          Real.sqrt (g₀.inner x X X) *
          Real.sqrt (g₀.inner x Y Y) *
          Real.sqrt (g₀.inner x Z Z) := by
      dsimp [L₀]
      ring
    _ = rmOneOpC Λ Kb₀ Kb₁ * Real.sqrt (g₀.inner x D D) *
          Real.sqrt (g₀.inner x X X) *
          Real.sqrt (g₀.inner x Y Y) *
          Real.sqrt (g₀.inner x Z Z) := by
      dsimp [rmOneOpC, Cc, Cp, Cb, S]

set_option linter.unusedSectionVars false in
private theorem unifRmOpOne
    (gBase g₀ : SmoothRiemannianMetric I M) {Λ : ℝ}
    (hΛ : 1 ≤ Λ)
    (hcomp : ∀ (x : M) (v : TangentSpace I x),
      Λ⁻¹ * gBase.inner x v v ≤ g₀.inner x v v ∧
        g₀.inner x v v ≤ Λ * gBase.inner x v v)
    (hjet1 : MetricCovDerivOrderBoundOn (I := I) Set.univ 1 g₀ gBase Λ)
    (hjet2 : MetricCovDerivOrderBoundOn (I := I) Set.univ 2 g₀ gBase Λ)
    (hjet3 : MetricCovDerivOrderBoundOn (I := I) Set.univ 3 g₀ gBase Λ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (x : M) (D X Y Z : TangentSpace I x),
        Real.sqrt (g₀.inner x
            (nablaRiemannOp (I := I) g₀ x D X Y Z)
            (nablaRiemannOp (I := I) g₀ x D X Y Z)) ≤
          C * Real.sqrt (g₀.inner x D D) *
            Real.sqrt (g₀.inner x X X) *
            Real.sqrt (g₀.inner x Y Y) *
            Real.sqrt (g₀.inner x Z Z) := by
  obtain ⟨Kb₀, hKb₀0, hKb₀⟩ :=
    exists_uniform_riemannOp_LeviCivita_gNorm_bound (I := I) (M := M) gBase
  obtain ⟨Kb₁, hKb₁0, hKb₁⟩ :=
    exists_curvJet_sup (I := I) (M := M) gBase 1
  refine ⟨rmOneOpC Λ Kb₀ Kb₁, ?_, ?_⟩
  · have hΛ0 : 0 ≤ Λ := le_trans zero_le_one hΛ
    dsimp [rmOneOpC, curvConnC, palatiniOneC, riemannDiffC]
    positivity
  · exact unifRmOpOne_of (I := I) (M := M) gBase g₀ hΛ
      hKb₀0 hKb₀ hKb₁0 hKb₁ hcomp hjet1 hjet2 hjet3

set_option linter.unusedSectionVars false in
/-- The first curvature jet with both fixed-background caps supplied. -/
theorem unifRmJetOne_of
    (gBase g₀ : SmoothRiemannianMetric I M) {Λ Kb₀ Kb₁ : ℝ}
    (hΛ : 1 ≤ Λ)
    (hKb₀0 : 0 ≤ Kb₀)
    (hKb₀ : ∀ (x : M) (v w u : TangentSpace I x),
      gBase.inner x (riemannOp (cov := LeviCivita (I := I) gBase) x v w u)
          (riemannOp (cov := LeviCivita (I := I) gBase) x v w u) ≤
        Kb₀ * gBase.inner x v v * gBase.inner x w w * gBase.inner x u u)
    (hKb₁0 : 0 ≤ Kb₁)
    (hKb₁ : ∀ x : M,
      Real.sqrt (normSq0S (I := I) gBase x 5
        (iterCov (I := I) gBase 4
          (metricRm04 (I := I) (M := M) gBase) 1 x)) ≤ Kb₁)
    (hcomp : ∀ (x : M) (v : TangentSpace I x),
      Λ⁻¹ * gBase.inner x v v ≤ g₀.inner x v v ∧
        g₀.inner x v v ≤ Λ * gBase.inner x v v)
    (hjet1 : MetricCovDerivOrderBoundOn (I := I) Set.univ 1 g₀ gBase Λ)
    (hjet2 : MetricCovDerivOrderBoundOn (I := I) Set.univ 2 g₀ gBase Λ)
    (hjet3 : MetricCovDerivOrderBoundOn (I := I) Set.univ 3 g₀ gBase Λ) :
    ∀ x : M,
      Real.sqrt (normSq0S (I := I) g₀ x 5
        (iterCov (I := I) g₀ 4
          (metricRm04 (I := I) (M := M) g₀) 1 x)) ≤
        rmOneC (E := E) Λ Kb₀ Kb₁ := by
  have hOp0 : 0 ≤ rmOneOpC Λ Kb₀ Kb₁ := by
    have hΛ0 : 0 ≤ Λ := le_trans zero_le_one hΛ
    dsimp [rmOneOpC, curvConnC, palatiniOneC, riemannDiffC]
    positivity
  have hOp := unifRmOpOne_of (I := I) (M := M) gBase g₀ hΛ
    hKb₀0 hKb₀ hKb₁0 hKb₁ hcomp hjet1 hjet2 hjet3
  intro x
  simpa [rmOneC] using
    jet1_norm_le (I := I) (M := M) g₀ hOp0 hOp x

set_option linter.unusedSectionVars false in
/-- For every `Λ ≥ 1`, the first lowered-curvature jet has a class-uniform
`g₀` fibre bound using metric jets only through order three. -/
theorem unifRmJetOne
    (gBase g₀ : SmoothRiemannianMetric I M) {Λ : ℝ}
    (hΛ : 1 ≤ Λ)
    (hcomp : ∀ (x : M) (v : TangentSpace I x),
      Λ⁻¹ * gBase.inner x v v ≤ g₀.inner x v v ∧
        g₀.inner x v v ≤ Λ * gBase.inner x v v)
    (hjet1 : MetricCovDerivOrderBoundOn (I := I) Set.univ 1 g₀ gBase Λ)
    (hjet2 : MetricCovDerivOrderBoundOn (I := I) Set.univ 2 g₀ gBase Λ)
    (hjet3 : MetricCovDerivOrderBoundOn (I := I) Set.univ 3 g₀ gBase Λ) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ x : M,
        Real.sqrt (normSq0S (I := I) g₀ x 5
          (iterCov (I := I) g₀ 4
            (metricRm04 (I := I) (M := M) g₀) 1 x)) ≤ K := by
  obtain ⟨C, hC0, hC⟩ :=
    unifRmOpOne (I := I) (M := M) gBase g₀
      hΛ hcomp hjet1 hjet2 hjet3
  refine ⟨Real.sqrt ((Module.finrank ℝ E : ℝ) ^ 5) * C, by positivity, ?_⟩
  intro x
  exact jet1_norm_le (I := I) (M := M) g₀ hC0 hC x

private theorem sq_le_of_sqrt_le {a K : ℝ}
    (ha : 0 ≤ a) (h : Real.sqrt a ≤ K) :
    a ≤ K ^ 2 := by
  nlinarith [Real.sq_sqrt ha, Real.sqrt_nonneg a]

set_option linter.unusedSectionVars false in
/-- The section-currency first curvature jet with both background caps supplied. -/
theorem unifRmSecOne_of
    (gBase g₀ : SmoothRiemannianMetric I M) {Λ Kb₀ Kb₁ : ℝ}
    (hΛ : 1 ≤ Λ)
    (hKb₀0 : 0 ≤ Kb₀)
    (hKb₀ : ∀ (x : M) (v w u : TangentSpace I x),
      gBase.inner x (riemannOp (cov := LeviCivita (I := I) gBase) x v w u)
          (riemannOp (cov := LeviCivita (I := I) gBase) x v w u) ≤
        Kb₀ * gBase.inner x v v * gBase.inner x w w * gBase.inner x u u)
    (hKb₁0 : 0 ≤ Kb₁)
    (hKb₁ : ∀ x : M,
      Real.sqrt (normSq0S (I := I) gBase x 5
        (iterCov (I := I) gBase 4
          (metricRm04 (I := I) (M := M) gBase) 1 x)) ≤ Kb₁)
    (hcomp : ∀ (x : M) (v : TangentSpace I x),
      Λ⁻¹ * gBase.inner x v v ≤ g₀.inner x v v ∧
        g₀.inner x v v ≤ Λ * gBase.inner x v v)
    (hjet1 : MetricCovDerivOrderBoundOn (I := I) Set.univ 1 g₀ gBase Λ)
    (hjet2 : MetricCovDerivOrderBoundOn (I := I) Set.univ 2 g₀ gBase Λ)
    (hjet3 : MetricCovDerivOrderBoundOn (I := I) Set.univ 3 g₀ gBase Λ) :
    ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + 1) x
          ((iteratedCovGrad (I := I) g₀ 0 4 1
            (rmSection (I := I) (M := M) g₀)).toSection x) ≤
        rmOneC (E := E) Λ Kb₀ Kb₁ ^ 2 := by
  intro x
  apply sq_le_of_sqrt_le
    (riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (4 + 1) x _)
  rw [rfns_rmSection_eq (I := I) g₀ 1 x]
  exact unifRmJetOne_of (I := I) (M := M) gBase g₀ hΛ
    hKb₀0 hKb₀ hKb₁0 hKb₁ hcomp hjet1 hjet2 hjet3 x

set_option linter.unusedSectionVars false in
/-- For every `Λ ≥ 1`, the class-uniform first curvature jet in the smooth
section currency used by the short-time existence estimates. -/
theorem unifRmSecOne
    (gBase g₀ : SmoothRiemannianMetric I M) {Λ : ℝ}
    (hΛ : 1 ≤ Λ)
    (hcomp : ∀ (x : M) (v : TangentSpace I x),
      Λ⁻¹ * gBase.inner x v v ≤ g₀.inner x v v ∧
        g₀.inner x v v ≤ Λ * gBase.inner x v v)
    (hjet1 : MetricCovDerivOrderBoundOn (I := I) Set.univ 1 g₀ gBase Λ)
    (hjet2 : MetricCovDerivOrderBoundOn (I := I) Set.univ 2 g₀ gBase Λ)
    (hjet3 : MetricCovDerivOrderBoundOn (I := I) Set.univ 3 g₀ gBase Λ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + 1) x
          ((iteratedCovGrad (I := I) g₀ 0 4 1
            (rmSection (I := I) (M := M) g₀)).toSection x) ≤ K ^ 2 := by
  obtain ⟨K, hK0, hK⟩ :=
    unifRmJetOne (I := I) (M := M) gBase g₀
      hΛ hcomp hjet1 hjet2 hjet3
  refine ⟨K, hK0, fun x => ?_⟩
  apply sq_le_of_sqrt_le
    (riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (4 + 1) x _)
  rw [rfns_rmSection_eq (I := I) g₀ 1 x]
  exact hK x

end RicciFlow
end PDE
end DifferentialGeometry
