import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.DifferentiatedPalatini
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.UnifCurvatureJet1Diff
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.ConnDiffDeriv2Bound

/-!
# The class-uniform differentiated Palatini bound

This module estimates the exact curvature-layer identity `covDerivPal_eq` at
the fixed order needed by the uniform short-time existence lane.  Its only
inputs are the already banked class-uniform bounds for the connection
difference and its first two base covariant derivatives.
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

private noncomputable def extSec (x : M) (v : TangentSpace I x) :
    ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _) :=
  ContMDiffSection.mk (smoothExtensionTangent (I := I) x v)
    (smoothExtensionTangent_contMDiff (I := I) x v)

set_option linter.unusedSectionVars false in
@[simp] private theorem extSec_apply (x : M) (v : TangentSpace I x) :
    extSec (I := I) x v x = v :=
  smoothExtensionTangent_eq (I := I) x v

set_option linter.unusedSectionVars false in
private theorem covD_congr
    (g₂ g₁ : SmoothRiemannianMetric I M)
    (W X Y W' X' Y' : ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _))
    {x : M} (hW : W x = W' x) (hX : X x = X' x) (hY : Y x = Y' x) :
    covDerivConnDiff (I := I) g₂ g₁ W X Y x =
      covDerivConnDiff (I := I) g₂ g₁ W' X' Y' x := by
  classical
  haveI : IsManifold I 2 M :=
    IsManifold.of_le (I := I) (M := M) (n := ∞)
      (by decide : (2 : WithTop ℕ∞) ≤ ∞)
  haveI : IsManifold I ((∞ : WithTop ℕ∞) + 1) M := by
    change IsManifold I ∞ M
    infer_instance
  haveI : IsManifold I (1 + 1) M :=
    IsManifold.of_le (I := I) (M := M) (n := ∞)
      (by decide : ((1 : WithTop ℕ∞) + 1) ≤ ∞)
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
  have hZ := hpair (extSec (I := I) x (a - b))
  rw [extSec_apply] at hZ
  have hsym1 : g₁.inner x a (a - b) = g₁.inner x (a - b) a :=
    g₁.symm x a (a - b)
  have hsym2 : g₁.inner x b (a - b) = g₁.inner x (a - b) b :=
    g₁.symm x b (a - b)
  have hzero : g₁.inner x (a - b) (a - b) = 0 := by
    rw [map_sub, ← hsym1, ← hsym2, hZ, sub_self]
  have hsub : a - b = 0 := by
    by_contra hne
    exact (ne_of_gt (g₁.pos x (a - b) hne)) hzero
  exact sub_eq_zero.mp hsub

set_option linter.unusedSectionVars false in
private theorem covD_eq_ext
    (g₂ g₁ : SmoothRiemannianMetric I M)
    (W X Y : ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _)) (x : M) :
    covDerivConnDiff (I := I) g₂ g₁ W X Y x =
      covDerivConnDiff (I := I) g₂ g₁
        (extSec (I := I) x (W x))
        (extSec (I := I) x (X x))
        (extSec (I := I) x (Y x)) x := by
  apply covD_congr (I := I) g₂ g₁ W X Y
    (extSec (I := I) x (W x))
    (extSec (I := I) x (X x))
    (extSec (I := I) x (Y x))
  all_goals simp

set_option linter.unusedSectionVars false in
private theorem covD2_eq_hcg
    (gB g₀ : SmoothRiemannianMetric I M)
    (D X Y Z : Π b : M, TangentSpace I b) (x : M) :
    Integral.Connection.covDerivConnDiff2 (I := I) gB g₀ D X Y Z x =
      HCGCompactness.covDerivConnDiff2 (I := I) gB g₀ D X Y Z x :=
  rfl

/-- The differentiated Palatini self-difference evaluated on canonical smooth
extensions of four tangent vectors. -/
noncomputable def palatiniJet1At
    (gBase g₀ : SmoothRiemannianMetric I M) (x : M)
    (D X Y Z : TangentSpace I x) : TangentSpace I x :=
  covDerivPalatini (I := I) gBase g₀
    (extSec (I := I) x D) (extSec (I := I) x X)
    (extSec (I := I) x Y) (extSec (I := I) x Z) x

/-- The explicit first differentiated-Palatini coefficient at class size `Λ`. -/
def palatiniOneC (Λ : ℝ) : ℝ :=
  2 * (3 / 2 * Λ ^ 5 * Λ + 9 / 2 * Λ ^ 6 * Λ * Λ + 3 * Λ ^ 7 * Λ ^ 3) +
    4 * (3 / 2 * Λ ^ 3 * Λ) * (3 / 2 * Λ ^ 4 * (Λ + Λ * Λ ^ 2))

set_option linter.unusedSectionVars false in
/-- The differentiated Palatini term obeys the explicit `palatiniOneC` bound. -/
theorem unifPalatini1_le
    (gBase g₀ : SmoothRiemannianMetric I M) {Λ : ℝ}
    (hΛ : 1 ≤ Λ)
    (hcomp : ∀ (x : M) (v : TangentSpace I x),
      Λ⁻¹ * gBase.inner x v v ≤ g₀.inner x v v ∧
        g₀.inner x v v ≤ Λ * gBase.inner x v v)
    (hjet1 : MetricCovDerivOrderBoundOn (I := I) Set.univ 1 g₀ gBase Λ)
    (hjet2 : MetricCovDerivOrderBoundOn (I := I) Set.univ 2 g₀ gBase Λ)
    (hjet3 : MetricCovDerivOrderBoundOn (I := I) Set.univ 3 g₀ gBase Λ) :
    ∀ (x : M) (D X Y Z : TangentSpace I x),
      Real.sqrt (gBase.inner x
          (palatiniJet1At (I := I) gBase g₀ x D X Y Z)
          (palatiniJet1At (I := I) gBase g₀ x D X Y Z)) ≤
        palatiniOneC Λ * Real.sqrt (gBase.inner x D D) *
          Real.sqrt (gBase.inner x X X) *
          Real.sqrt (gBase.inner x Y Y) *
          Real.sqrt (gBase.inner x Z Z) := by
  classical
  have hEq : MetricUniformEquivalentOn (I := I) Set.univ gBase g₀ Λ :=
    ⟨hΛ, fun x _hx v => hcomp x v⟩
  let C₀ : ℝ := 3 / 2 * Λ ^ 3 * Λ
  have hC₀0 : 0 ≤ C₀ := by
    dsimp [C₀]
    positivity
  have hC₀ : ∀ (x : M) (v w : TangentSpace I x),
      Real.sqrt (gBase.inner x
          (DifferentialGeometry.PDE.DeTurck.connDiff (I := I) g₀ gBase x v w)
          (DifferentialGeometry.PDE.DeTurck.connDiff (I := I) g₀ gBase x v w)) ≤
        C₀ * Real.sqrt (gBase.inner x v v) *
          Real.sqrt (gBase.inner x w w) := by
    intro x v w
    have h := connDiff_gJet_le (I := I) hEq hjet1 (Set.mem_univ x) w v
    simpa [C₀, DifferentialGeometry.PDE.DeTurck.connDiff,
      mul_assoc, mul_left_comm, mul_comm] using h
  let C₁ : ℝ := 3 / 2 * Λ ^ 4 * (Λ + Λ * Λ ^ 2)
  have hC₁0 : 0 ≤ C₁ := by
    dsimp [C₁]
    positivity
  have hC₁ : ∀ (x : M) (v w u : TangentSpace I x),
      Real.sqrt (gBase.inner x
          (covDerivConnDiff (I := I) gBase g₀
            (smoothExtensionTangent (I := I) x v)
            (smoothExtensionTangent (I := I) x w)
            (smoothExtensionTangent (I := I) x u) x)
          (covDerivConnDiff (I := I) gBase g₀
            (smoothExtensionTangent (I := I) x v)
            (smoothExtensionTangent (I := I) x w)
            (smoothExtensionTangent (I := I) x u) x)) ≤
        C₁ * Real.sqrt (gBase.inner x v v) *
          Real.sqrt (gBase.inner x w w) *
          Real.sqrt (gBase.inner x u u) := by
    intro x v w u
    simpa [C₁] using
      covDerivConnDiff_gJet_le (I := I) hEq hjet1 hjet2
        (Set.mem_univ x) v w u
  let C₂ : ℝ :=
    3 / 2 * Λ ^ 5 * Λ + 9 / 2 * Λ ^ 6 * Λ * Λ + 3 * Λ ^ 7 * Λ ^ 3
  have hC₂0 : 0 ≤ C₂ := by
    dsimp [C₂]
    positivity
  intro x D X Y Z
  let Ds := extSec (I := I) x D
  let Xs := extSec (I := I) x X
  let Ys := extSec (I := I) x Y
  let Zs := extSec (I := I) x Z
  let A₂xy : TangentSpace I x :=
    Integral.Connection.covDerivConnDiff2 (I := I) gBase g₀ Ds Xs Ys Zs x
  let A₂yx : TangentSpace I x :=
    Integral.Connection.covDerivConnDiff2 (I := I) gBase g₀ Ds Ys Xs Zs x
  let AYZs : ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _) :=
    ContMDiffSection.mk
      (diffSec (LeviCivita (I := I) gBase) (LeviCivita (I := I) g₀) Ys Zs)
      (by
        apply diffSec_contMDiff
        · exact Ys.contMDiff
        · simpa using Zs.contMDiff)
  let AXZs : ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _) :=
    ContMDiffSection.mk
      (diffSec (LeviCivita (I := I) gBase) (LeviCivita (I := I) g₀) Xs Zs)
      (by
        apply diffSec_contMDiff
        · exact Xs.contMDiff
        · simpa using Zs.contMDiff)
  let Cdyzs : ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _) :=
    ContMDiffSection.mk
      (fun p => covDerivConnDiff (I := I) gBase g₀ Ds Ys Zs p)
      (by
        simpa [Ds, Ys, Zs] using
          covDerivConnDiff_contMDiff (I := I) gBase g₀ Ds Ys Zs)
  let Cdxzs : ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _) :=
    ContMDiffSection.mk
      (fun p => covDerivConnDiff (I := I) gBase g₀ Ds Xs Zs p)
      (by
        simpa [Ds, Xs, Zs] using
          covDerivConnDiff_contMDiff (I := I) gBase g₀ Ds Xs Zs)
  let P : TangentSpace I x :=
    covDerivConnDiff (I := I) gBase g₀ Ds Xs AYZs x
  let Q : TangentSpace I x :=
    diffSec (LeviCivita (I := I) gBase) (LeviCivita (I := I) g₀) Xs Cdyzs x
  let R : TangentSpace I x :=
    covDerivConnDiff (I := I) gBase g₀ Ds Ys AXZs x
  let S : TangentSpace I x :=
    diffSec (LeviCivita (I := I) gBase) (LeviCivita (I := I) g₀) Ys Cdxzs x
  let L : TangentSpace I x → ℝ := fun v => Real.sqrt (gBase.inner x v v)
  let prod4 : ℝ := L D * L X * L Y * L Z
  have hsplit :
      palatiniJet1At (I := I) gBase g₀ x D X Y Z =
        A₂xy - A₂yx + (P + Q) - (R + S) := by
    simpa [palatiniJet1At, Ds, Xs, Ys, Zs, A₂xy, A₂yx,
      AYZs, AXZs, Cdyzs, Cdxzs, P, Q, R, S] using
      covDerivPal_eq (I := I) gBase g₀ Ds Xs Ys Zs x
  have hprod40 : 0 ≤ prod4 := by
    dsimp [prod4, L]
    positivity
  have hA₂xy : L A₂xy ≤ C₂ * prod4 := by
    simpa [A₂xy, Ds, Xs, Ys, Zs, extSec, L, prod4, C₂, covD2_eq_hcg,
      mul_assoc] using
      HCGCompactness.covDConnDiff2_gJet_le (I := I) hEq hjet1 hjet2 hjet3
        (Set.mem_univ x) D X Y Z
  have hA₂yx : L A₂yx ≤ C₂ * prod4 := by
    have h := HCGCompactness.covDConnDiff2_gJet_le (I := I)
      hEq hjet1 hjet2 hjet3 (Set.mem_univ x) D Y X Z
    simpa [A₂yx, Ds, Xs, Ys, Zs, extSec, L, prod4, C₂, covD2_eq_hcg, mul_assoc,
      mul_left_comm, mul_comm] using h
  have hAYZ : L (AYZs x) ≤ C₀ * L Y * L Z := by
    have h := hC₀ x Z Y
    simpa [AYZs, Ys, Zs, L, DifferentialGeometry.PDE.DeTurck.connDiff,
      diffSec, mul_assoc, mul_left_comm, mul_comm] using h
  have hAXZ : L (AXZs x) ≤ C₀ * L X * L Z := by
    have h := hC₀ x Z X
    simpa [AXZs, Xs, Zs, L, DifferentialGeometry.PDE.DeTurck.connDiff,
      diffSec, mul_assoc, mul_left_comm, mul_comm] using h
  have hCdyz : L (Cdyzs x) ≤ C₁ * L D * L Y * L Z := by
    have h := hC₁ x D Y Z
    simpa [Cdyzs, Ds, Ys, Zs, L] using h
  have hCdxz : L (Cdxzs x) ≤ C₁ * L D * L X * L Z := by
    have h := hC₁ x D X Z
    simpa [Cdxzs, Ds, Xs, Zs, L] using h
  have hP : L P ≤ C₀ * C₁ * prod4 := by
    have heq :
        covDerivConnDiff (I := I) gBase g₀ Ds Xs AYZs x =
          covDerivConnDiff (I := I) gBase g₀
            (smoothExtensionTangent (I := I) x (Ds x))
            (smoothExtensionTangent (I := I) x (Xs x))
            (smoothExtensionTangent (I := I) x (AYZs x)) x := by
      simpa [extSec] using covD_eq_ext (I := I) gBase g₀ Ds Xs AYZs x
    have h := hC₁ x (Ds x) (Xs x) (AYZs x)
    rw [← heq] at h
    have hcoef : 0 ≤ C₁ * L D * L X := by
      exact mul_nonneg (mul_nonneg hC₁0 (Real.sqrt_nonneg _))
        (Real.sqrt_nonneg _)
    have hmul := mul_le_mul_of_nonneg_left hAYZ hcoef
    calc
      L P ≤ C₁ * L D * L X * L (AYZs x) := by
        simpa [P, Ds, Xs, L] using h
      _ ≤ (C₁ * L D * L X) * (C₀ * L Y * L Z) := by
        simpa [mul_assoc] using hmul
      _ = C₀ * C₁ * prod4 := by ring
  have hR : L R ≤ C₀ * C₁ * prod4 := by
    have heq :
        covDerivConnDiff (I := I) gBase g₀ Ds Ys AXZs x =
          covDerivConnDiff (I := I) gBase g₀
            (smoothExtensionTangent (I := I) x (Ds x))
            (smoothExtensionTangent (I := I) x (Ys x))
            (smoothExtensionTangent (I := I) x (AXZs x)) x := by
      simpa [extSec] using covD_eq_ext (I := I) gBase g₀ Ds Ys AXZs x
    have h := hC₁ x (Ds x) (Ys x) (AXZs x)
    rw [← heq] at h
    have hcoef : 0 ≤ C₁ * L D * L Y := by
      exact mul_nonneg (mul_nonneg hC₁0 (Real.sqrt_nonneg _))
        (Real.sqrt_nonneg _)
    have hmul := mul_le_mul_of_nonneg_left hAXZ hcoef
    calc
      L R ≤ C₁ * L D * L Y * L (AXZs x) := by
        simpa [R, Ds, Ys, L] using h
      _ ≤ (C₁ * L D * L Y) * (C₀ * L X * L Z) := by
        simpa [mul_assoc] using hmul
      _ = C₀ * C₁ * prod4 := by ring
  have hQ : L Q ≤ C₀ * C₁ * prod4 := by
    have h := hC₀ x (Cdyzs x) (Xs x)
    have hcoef : 0 ≤ C₀ * L X := by
      exact mul_nonneg hC₀0 (Real.sqrt_nonneg _)
    have hmul := mul_le_mul_of_nonneg_left hCdyz hcoef
    calc
      L Q ≤ C₀ * L (Cdyzs x) * L X := by
        simpa [Q, Cdyzs, Xs, L, DifferentialGeometry.PDE.DeTurck.connDiff,
          diffSec] using h
      _ ≤ (C₀ * L X) * (C₁ * L D * L Y * L Z) := by
        simpa [mul_assoc, mul_left_comm, mul_comm] using hmul
      _ = C₀ * C₁ * prod4 := by ring
  have hS : L S ≤ C₀ * C₁ * prod4 := by
    have h := hC₀ x (Cdxzs x) (Ys x)
    have hcoef : 0 ≤ C₀ * L Y := by
      exact mul_nonneg hC₀0 (Real.sqrt_nonneg _)
    have hmul := mul_le_mul_of_nonneg_left hCdxz hcoef
    calc
      L S ≤ C₀ * L (Cdxzs x) * L Y := by
        simpa [S, Cdxzs, Ys, L, DifferentialGeometry.PDE.DeTurck.connDiff,
          diffSec] using h
      _ ≤ (C₀ * L Y) * (C₁ * L D * L X * L Z) := by
        simpa [mul_assoc, mul_left_comm, mul_comm] using hmul
      _ = C₀ * C₁ * prod4 := by ring
  have hneg : ∀ v : TangentSpace I x, L (-v) = L v := by
    intro v
    simpa only [L, neg_one_smul, abs_neg, abs_one, one_mul] using
      Geometry.Riemannian.sqrt_inner_smul (I := I) gBase x (-1 : ℝ) v
  have hsub : ∀ u v : TangentSpace I x, L (u - v) ≤ L u + L v := by
    intro u v
    calc
      L (u - v) = L (u + -v) := by rw [sub_eq_add_neg]
      _ ≤ L u + L (-v) :=
        Geometry.Riemannian.sqrt_inner_add_le (I := I) gBase x u (-v)
      _ = L u + L v := by rw [hneg]
  have hleft : L (A₂xy - A₂yx) ≤ L A₂xy + L A₂yx := hsub _ _
  have hpq : L (P + Q) ≤ L P + L Q :=
    Geometry.Riemannian.sqrt_inner_add_le (I := I) gBase x P Q
  have hrs : L (R + S) ≤ L R + L S :=
    Geometry.Riemannian.sqrt_inner_add_le (I := I) gBase x R S
  have hright : L ((P + Q) - (R + S)) ≤ (L P + L Q) + (L R + L S) :=
    le_trans (hsub _ _) (add_le_add hpq hrs)
  calc
    Real.sqrt (gBase.inner x
        (palatiniJet1At (I := I) gBase g₀ x D X Y Z)
        (palatiniJet1At (I := I) gBase g₀ x D X Y Z)) =
        L ((A₂xy - A₂yx) + ((P + Q) - (R + S))) := by
          rw [hsplit]
          congr 1
          abel
    _ ≤ L (A₂xy - A₂yx) + L ((P + Q) - (R + S)) :=
      Geometry.Riemannian.sqrt_inner_add_le (I := I) gBase x _ _
    _ ≤ (L A₂xy + L A₂yx) + ((L P + L Q) + (L R + L S)) :=
      add_le_add hleft hright
    _ ≤ (C₂ * prod4 + C₂ * prod4) +
        ((C₀ * C₁ * prod4 + C₀ * C₁ * prod4) +
          (C₀ * C₁ * prod4 + C₀ * C₁ * prod4)) :=
      add_le_add (add_le_add hA₂xy hA₂yx)
        (add_le_add (add_le_add hP hQ) (add_le_add hR hS))
    _ = (2 * C₂ + 4 * C₀ * C₁) * prod4 := by ring
    _ = (2 * C₂ + 4 * C₀ * C₁) *
        Real.sqrt (gBase.inner x D D) *
        Real.sqrt (gBase.inner x X X) *
        Real.sqrt (gBase.inner x Y Y) *
        Real.sqrt (gBase.inner x Z Z) := by
      dsimp [prod4, L]
      ring
    _ = palatiniOneC Λ * Real.sqrt (gBase.inner x D D) *
        Real.sqrt (gBase.inner x X X) *
        Real.sqrt (gBase.inner x Y Y) *
        Real.sqrt (gBase.inner x Z Z) := by
      dsimp [palatiniOneC, C₀, C₁, C₂]

set_option linter.unusedSectionVars false in
/-- The differentiated Palatini term has a class-uniform quadrilinear bound
using metric jets only through order three. -/
theorem unifPalatini1
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
        Real.sqrt (gBase.inner x
            (palatiniJet1At (I := I) gBase g₀ x D X Y Z)
            (palatiniJet1At (I := I) gBase g₀ x D X Y Z)) ≤
          C * Real.sqrt (gBase.inner x D D) *
            Real.sqrt (gBase.inner x X X) *
            Real.sqrt (gBase.inner x Y Y) *
            Real.sqrt (gBase.inner x Z Z) := by
  refine ⟨palatiniOneC Λ, ?_, ?_⟩
  · unfold palatiniOneC
    positivity
  · exact unifPalatini1_le (I := I) (M := M) gBase g₀
      hΛ hcomp hjet1 hjet2 hjet3

end RicciFlow
end PDE
end DifferentialGeometry
