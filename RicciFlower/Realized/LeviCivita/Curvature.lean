import RicciFlower.Realized.CurvatureComponents
import RicciFlower.Realized.LeviCivita.Torsion
import RicciFlower.Tensor.RSTensor.NablaOnTensors.Connection
import RicciFlower.VectorBundle.PartialMfderiv

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# Levi-Civita curvature endpoints

This file localizes the geometric Levi-Civita curvature facts needed by scalar
Bochner.  Generic curvature realization predicates remain in
`RicciFlower.Realized.CurvatureComponents`; this file only specializes them to
`leviCivitaConnectionOfMetric`.
-/

noncomputable section

namespace RicciFlower
namespace Realized
namespace LeviCivita

open Bundle Tensor0SBundle
open scoped Topology Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [IsManifold I 1 M] [IsManifold I 2 M] [IsManifold I 3 M]
variable [IsManifold I ((⊤ : WithTop ℕ∞) + 1) M]
variable [SigmaCompactSpace M] [T2Space M]

private theorem directionalDeriv_congr_nhds
    {X : (p : M) -> TangentSpace I p} {f h : M -> Real} {x : M}
    (hfh : f =ᶠ[𝓝 x] h) :
    directionalDeriv (I := I) X f x = directionalDeriv (I := I) X h x := by
  have hx : f x = h x := hfh.self_of_nhds
  unfold directionalDeriv extDerivFun
  rw [hfh.mfderiv_eq]
  rw [hx]

private theorem directionalDeriv_add_fun
    (X : (p : M) -> TangentSpace I p) {f h : M -> Real} (x : M)
    (hf : MDifferentiableAt I 𝓘(Real, Real) f x)
    (hh : MDifferentiableAt I 𝓘(Real, Real) h x) :
    directionalDeriv (I := I) X (fun y : M => f y + h y) x =
        directionalDeriv (I := I) X f x +
        directionalDeriv (I := I) X h x := by
  unfold directionalDeriv
  change (extDerivFun (I := I) (f + h) x) (X x) =
    (extDerivFun (I := I) f x) (X x) + (extDerivFun (I := I) h x) (X x)
  rw [extDerivFun_add hf hh]
  rw [ContinuousLinearMap.add_apply]

private theorem mdifferentiableAt_metric_inner
    (g : SmoothRiemannianMetric I M)
    {X Y : (p : M) -> TangentSpace I p} {x : M}
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) :
    MDiffAt (fun y : M => g.inner y (X y) (Y y)) x := by
  have hg :
      MDifferentiableAt I
        (I.prod 𝓘(Real, E →L[Real] E →L[Real] Real))
        (fun y : M =>
          TotalSpace.mk' (E →L[Real] E →L[Real] Real)
            (E := fun y : M =>
              TangentSpace I y →L[Real] TangentSpace I y →L[Real] Real)
            y (g.inner y)) x :=
    g.contMDiff.mdifferentiableAt (by simp)
  have htotal :
      MDifferentiableAt I (I.prod 𝓘(Real, Real))
        (fun y : M =>
          TotalSpace.mk' Real (E := Bundle.Trivial M Real) y
            (g.inner y (X y) (Y y))) x := by
    exact MDifferentiableAt.clm_bundle_apply₂
      (F₁ := E) (F₂ := E) hg hX hY
  rw [mdifferentiableAt_totalSpace] at htotal
  exact htotal.2

private theorem contMDiffAt_metric_inner
    (g : SmoothRiemannianMetric I M)
    {X Y : (p : M) -> TangentSpace I p} {x : M} {n : WithTop ℕ∞}
    (hX : ContMDiffAt I (I.prod 𝓘(Real, E)) n (T% X) x)
    (hY : ContMDiffAt I (I.prod 𝓘(Real, E)) n (T% Y) x) :
    ContMDiffAt I 𝓘(Real, Real) n
      (fun y : M => g.inner y (X y) (Y y)) x := by
  have hg :
      ContMDiffAt I
        (I.prod 𝓘(Real, E →L[Real] E →L[Real] Real)) n
        (fun y : M =>
          TotalSpace.mk' (E →L[Real] E →L[Real] Real)
            (E := fun y : M =>
              TangentSpace I y →L[Real] TangentSpace I y →L[Real] Real)
            y (g.inner y)) x :=
    (g.contMDiff.contMDiffAt).of_le le_top
  have htotal :
      ContMDiffAt I (I.prod 𝓘(Real, Real)) n
        (fun y : M =>
          TotalSpace.mk' Real (E := Bundle.Trivial M Real) y
            (g.inner y (X y) (Y y))) x := by
    exact ContMDiffAt.clm_bundle_apply₂
      (F₁ := E) (F₂ := E) hg hX hY
  rw [contMDiffAt_totalSpace] at htotal
  exact htotal.2

private theorem mdifferentiableAt_tangentConstAt_of_mem
    (x₀ : M) (v : TangentSpace I x₀) {p : M}
    (hp : p ∈ (trivializationAt E (TangentSpace I) x₀).baseSet) :
    MDiffAt
      (T% (tangentConstAt (I := I) x₀ v :
        (p : M) -> TangentSpace I p)) p := by
  unfold tangentConstAt
  exact TensorLieDeriv.mdifferentiableAt_tangentConstInChart_of_mem
    (𝕜 := Real) (I := I) (x₀ := x₀) (p := p) v hp

private theorem contMDiffAt_tangentConstAt_self_minTwo
    (x₀ : M) (v : TangentSpace I x₀) :
    ContMDiffAt I (I.prod 𝓘(Real, E)) (minSmoothness Real 2)
      (T% (tangentConstAt (I := I) x₀ v :
        (p : M) -> TangentSpace I p)) x₀ := by
  haveI : IsManifold I (minSmoothness Real 2) M := by
    rw [minSmoothness_of_isRCLikeNormedField]
    exact (inferInstance : IsManifold I 2 M)
  haveI : IsManifold I ((minSmoothness Real 2 : WithTop ℕ∞) + 1) M := by
    rw [minSmoothness_of_isRCLikeNormedField]
    have h : ((2 : WithTop ℕ∞) + 1) = (3 : WithTop ℕ∞) := by
      norm_num
    exact h.symm ▸ (inferInstance : IsManifold I 3 M)
  have h_on :
      ContMDiffOn I (I.prod 𝓘(Real, E)) (minSmoothness Real 2)
        (T% (tangentConstAt (I := I) x₀ v :
          (p : M) -> TangentSpace I p))
        (trivializationAt E (TangentSpace I) x₀).baseSet := by
    simpa [tangentConstAt] using
      (TensorLieDeriv.tangentConstInChart_contMDiffOn_baseSet
        (𝕜 := Real) (I := I) (M := M)
        (n := minSmoothness Real 2) x₀ v)
  exact (h_on x₀ (mem_baseSet_trivializationAt E (TangentSpace I) x₀)).contMDiffAt
    ((trivializationAt E (TangentSpace I) x₀).open_baseSet.mem_nhds
      (mem_baseSet_trivializationAt E (TangentSpace I) x₀))

private theorem cov_tangentConstAt_apply_contMDiffOn_baseSet
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov
      (1 : WithTop ℕ∞))
    (x₀ : M) (v w : TangentSpace I x₀) :
    ContMDiffOn I (I.prod 𝓘(Real, E)) (1 : WithTop ℕ∞)
      (T% (fun p : M =>
        (cov (tangentConstAt (I := I) x₀ w) p)
          ((tangentConstAt (I := I) x₀ v) p)))
      (trivializationAt E (TangentSpace I) x₀).baseSet := by
  let e := trivializationAt E (TangentSpace I) x₀
  haveI : IsManifold I ((1 : WithTop ℕ∞) + 1) M := by
    have h : ((1 : WithTop ℕ∞) + 1) = (2 : WithTop ℕ∞) := by
      norm_num
    exact h.symm ▸ (inferInstance : IsManifold I 2 M)
  haveI : IsManifold I (((1 : WithTop ℕ∞) + 1) + 1) M := by
    have h : (((1 : WithTop ℕ∞) + 1) + 1) = (3 : WithTop ℕ∞) := by
      norm_num
    exact h.symm ▸ (inferInstance : IsManifold I 3 M)
  have hw :
      ContMDiffOn I (I.prod 𝓘(Real, E)) ((1 : WithTop ℕ∞) + 1)
        (T% (tangentConstAt (I := I) x₀ w :
          (p : M) -> TangentSpace I p)) e.baseSet := by
    simpa [e, tangentConstAt] using
      (TensorLieDeriv.tangentConstInChart_contMDiffOn_baseSet
        (𝕜 := Real) (I := I) (M := M)
        (n := (1 : WithTop ℕ∞) + 1) x₀ w)
  have hcovw :
      ContMDiffOn I (I.prod 𝓘(Real, E →L[Real] E)) (1 : WithTop ℕ∞)
        (fun p : M =>
          (⟨p, cov (tangentConstAt (I := I) x₀ w) p⟩ :
            TotalSpace (E →L[Real] E)
              (fun p : M =>
                TangentSpace I p →L[Real] TangentSpace I p)))
        e.baseSet := by
    exact (hcov e.open_baseSet).contMDiff hw
  have hv :
      ContMDiffOn I (I.prod 𝓘(Real, E)) (1 : WithTop ℕ∞)
        (T% (tangentConstAt (I := I) x₀ v :
          (p : M) -> TangentSpace I p)) e.baseSet := by
    simpa [e, tangentConstAt] using
      (TensorLieDeriv.tangentConstInChart_contMDiffOn_baseSet
        (𝕜 := Real) (I := I) (M := M)
        (n := (1 : WithTop ℕ∞)) x₀ v)
  simpa [e] using hcovw.clm_bundle_apply hv

private theorem cov_tangentConstAt_apply_mdiffAt_of_mem
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov
      (1 : WithTop ℕ∞))
    (x₀ : M) (v w : TangentSpace I x₀) {p : M}
    (hp : p ∈ (trivializationAt E (TangentSpace I) x₀).baseSet) :
    MDiffAt
      (T% (fun q : M =>
        (cov (tangentConstAt (I := I) x₀ w) q)
          ((tangentConstAt (I := I) x₀ v) q))) p := by
  let e := trivializationAt E (TangentSpace I) x₀
  have h_on :=
    cov_tangentConstAt_apply_contMDiffOn_baseSet (I := I) cov hcov x₀ v w
  exact ((h_on p (by simpa [e] using hp)).contMDiffAt
    (e.open_baseSet.mem_nhds hp)).mdifferentiableAt
      (by norm_num : (1 : WithTop ℕ∞) ≠ 0)

/-- The scalar Lie bracket acts as the commutator of directional derivatives.

This is the local scalar-calculus identity used by the metric-compatibility
curvature skew calculation. -/
theorem directionalDeriv_directionalDeriv_sub_commutator
    (X Y : (p : M) -> TangentSpace I p) (f : M -> Real) (x : M)
    (hX : ContMDiffAt I (I.prod 𝓘(Real, E)) (minSmoothness Real 2) (T% X) x)
    (hY : ContMDiffAt I (I.prod 𝓘(Real, E)) (minSmoothness Real 2) (T% Y) x)
    (hf : ContMDiffAt I 𝓘(Real, Real) (minSmoothness Real 2) f x) :
    directionalDeriv (I := I) X (fun y : M => directionalDeriv (I := I) Y f y) x -
        directionalDeriv (I := I) Y (fun y : M => directionalDeriv (I := I) X f y) x -
          directionalDeriv (I := I) (VectorField.mlieBracket I X Y) f x = 0 := by
  have h := vderiv_mlieBracket (I := I) X Y f x hX hY hf
  unfold directionalDeriv
  unfold vderiv at h
  rw [h]
  ring

/-- Metric-compatible curvature endomorphisms are skew-adjoint in the metric.

The proof uses only metric compatibility.  The tangent-constant covariant
derivative smoothness facts are supplied by
`CovariantDerivative.tangentConst_cov_mdiffAt`; the remaining local scalar
commutator expansion is isolated in
`directionalDeriv_directionalDeriv_sub_commutator`. -/
private theorem connectionRiemannCurvatureField_metric_skew_at_of_metricCompatible
    (g : SmoothRiemannianMetric I M)
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov
      (1 : WithTop ℕ∞))
    (hmc : IsMetricCompatible (I := I) cov g)
    {x : M} (W X Y Z : TangentSpace I x) :
    g.inner x W
        ((connectionRiemannCurvatureField (I := I) cov
          (tangentConstAt (I := I) x X)
          (tangentConstAt (I := I) x Y)
          (tangentConstAt (I := I) x Z)) x) =
      -g.inner x Z
        ((connectionRiemannCurvatureField (I := I) cov
          (tangentConstAt (I := I) x X)
          (tangentConstAt (I := I) x Y)
          (tangentConstAt (I := I) x W)) x) := by
  let Xc : (p : M) -> TangentSpace I p := tangentConstAt (I := I) x X
  let Yc : (p : M) -> TangentSpace I p := tangentConstAt (I := I) x Y
  let Zc : (p : M) -> TangentSpace I p := tangentConstAt (I := I) x Z
  let Wc : (p : M) -> TangentSpace I p := tangentConstAt (I := I) x W
  let YZc : (p : M) -> TangentSpace I p := fun p => (cov Zc p) (Yc p)
  let YWc : (p : M) -> TangentSpace I p := fun p => (cov Wc p) (Yc p)
  let XZc : (p : M) -> TangentSpace I p := fun p => (cov Zc p) (Xc p)
  let XWc : (p : M) -> TangentSpace I p := fun p => (cov Wc p) (Xc p)
  let Bc : (p : M) -> TangentSpace I p := VectorField.mlieBracket I Xc Yc
  let f : M -> Real := fun p => g.inner p (Zc p) (Wc p)
  have hX : MDiffAt (T% Xc) x := by
    simpa [Xc] using mdifferentiableAt_tangentConstAt_self (I := I) x X
  have hY : MDiffAt (T% Yc) x := by
    simpa [Yc] using mdifferentiableAt_tangentConstAt_self (I := I) x Y
  have hZ : MDiffAt (T% Zc) x := by
    simpa [Zc] using mdifferentiableAt_tangentConstAt_self (I := I) x Z
  have hW : MDiffAt (T% Wc) x := by
    simpa [Wc] using mdifferentiableAt_tangentConstAt_self (I := I) x W
  have hX2 : ContMDiffAt I (I.prod 𝓘(Real, E)) (minSmoothness Real 2) (T% Xc) x := by
    simpa [Xc] using contMDiffAt_tangentConstAt_self_minTwo (I := I) x X
  have hY2 : ContMDiffAt I (I.prod 𝓘(Real, E)) (minSmoothness Real 2) (T% Yc) x := by
    simpa [Yc] using contMDiffAt_tangentConstAt_self_minTwo (I := I) x Y
  have hZ2 : ContMDiffAt I (I.prod 𝓘(Real, E)) (minSmoothness Real 2) (T% Zc) x := by
    simpa [Zc] using contMDiffAt_tangentConstAt_self_minTwo (I := I) x Z
  have hW2 : ContMDiffAt I (I.prod 𝓘(Real, E)) (minSmoothness Real 2) (T% Wc) x := by
    simpa [Wc] using contMDiffAt_tangentConstAt_self_minTwo (I := I) x W
  have hf2 : ContMDiffAt I 𝓘(Real, Real) (minSmoothness Real 2) f x := by
    simpa [f] using contMDiffAt_metric_inner (I := I) g hZ2 hW2
  haveI : IsManifold I (minSmoothness Real 2) M := by
    rw [minSmoothness_of_isRCLikeNormedField]
    exact (inferInstance : IsManifold I 2 M)
  have hYZ : MDiffAt (T% YZc) x := by
    simpa [YZc, Yc, Zc, tangentConstAt] using
      CovariantDerivative.tangentConst_cov_mdiffAt
        (𝕜 := Real) (I := I) cov hcov (x := x) (v := Y) (w := Z)
  have hYW : MDiffAt (T% YWc) x := by
    simpa [YWc, Yc, Wc, tangentConstAt] using
      CovariantDerivative.tangentConst_cov_mdiffAt
        (𝕜 := Real) (I := I) cov hcov (x := x) (v := Y) (w := W)
  have hXZ : MDiffAt (T% XZc) x := by
    simpa [XZc, Xc, Zc, tangentConstAt] using
      CovariantDerivative.tangentConst_cov_mdiffAt
        (𝕜 := Real) (I := I) cov hcov (x := x) (v := X) (w := Z)
  have hXW : MDiffAt (T% XWc) x := by
    simpa [XWc, Xc, Wc, tangentConstAt] using
      CovariantDerivative.tangentConst_cov_mdiffAt
        (𝕜 := Real) (I := I) cov hcov (x := x) (v := X) (w := W)
  have hX2nat : ContMDiffAt I (I.prod 𝓘(Real, E)) (2 : ℕ∞) (T% Xc) x := by
    simpa [minSmoothness_of_isRCLikeNormedField] using hX2
  have hY2nat : ContMDiffAt I (I.prod 𝓘(Real, E)) (2 : ℕ∞) (T% Yc) x := by
    simpa [minSmoothness_of_isRCLikeNormedField] using hY2
  haveI : IsManifold I (((2 : ℕ∞) : WithTop ℕ∞) + 1) M := by
    change IsManifold I (3 : WithTop ℕ∞) M
    exact (inferInstance : IsManifold I 3 M)
  have hB1 : ContMDiffAt I (I.prod 𝓘(Real, E)) (1 : ℕ∞) (T% Bc) x := by
    simpa [Bc] using
      (ContMDiffAt.mlieBracket_vectorField (I := I) (m := (1 : ℕ∞)) (n := (2 : ℕ∞))
        hX2nat hY2nat (by
          rw [minSmoothness_of_isRCLikeNormedField]
          norm_num))
  have hB : MDiffAt (T% Bc) x :=
    hB1.mdifferentiableAt (by norm_num : ((1 : ℕ∞) : WithTop ℕ∞) ≠ 0)
  have hYf_eq :
      (fun p : M => directionalDeriv (I := I) Yc f p) =ᶠ[𝓝 x]
        fun p => g.inner p (YZc p) (Wc p) + g.inner p (Zc p) (YWc p) := by
    let e := trivializationAt E (TangentSpace I) x
    filter_upwards [e.open_baseSet.mem_nhds
      (mem_baseSet_trivializationAt E (TangentSpace I) x)] with p hp
    have hYp : MDiffAt (T% Yc) p := by
      simpa [Yc] using mdifferentiableAt_tangentConstAt_of_mem (I := I) x Y hp
    have hZp : MDiffAt (T% Zc) p := by
      simpa [Zc] using mdifferentiableAt_tangentConstAt_of_mem (I := I) x Z hp
    have hWp : MDiffAt (T% Wc) p := by
      simpa [Wc] using mdifferentiableAt_tangentConstAt_of_mem (I := I) x W hp
    have hmetric := RicciFlower.Realized.metric_compatible_apply (I := I) hmc
      (x := p) Yc Zc Wc hYp hZp hWp
    simpa [directionalDeriv, extDerivFun, NormedSpace.fromTangentSpace, f, YZc, YWc]
      using hmetric
  have hXf_eq :
      (fun p : M => directionalDeriv (I := I) Xc f p) =ᶠ[𝓝 x]
        fun p => g.inner p (XZc p) (Wc p) + g.inner p (Zc p) (XWc p) := by
    let e := trivializationAt E (TangentSpace I) x
    filter_upwards [e.open_baseSet.mem_nhds
      (mem_baseSet_trivializationAt E (TangentSpace I) x)] with p hp
    have hXp : MDiffAt (T% Xc) p := by
      simpa [Xc] using mdifferentiableAt_tangentConstAt_of_mem (I := I) x X hp
    have hZp : MDiffAt (T% Zc) p := by
      simpa [Zc] using mdifferentiableAt_tangentConstAt_of_mem (I := I) x Z hp
    have hWp : MDiffAt (T% Wc) p := by
      simpa [Wc] using mdifferentiableAt_tangentConstAt_of_mem (I := I) x W hp
    have hmetric := RicciFlower.Realized.metric_compatible_apply (I := I) hmc
      (x := p) Xc Zc Wc hXp hZp hWp
    simpa [directionalDeriv, extDerivFun, NormedSpace.fromTangentSpace, f, XZc, XWc]
      using hmetric
  have hYZ_W : MDiffAt (fun p : M => g.inner p (YZc p) (Wc p)) x :=
    mdifferentiableAt_metric_inner (I := I) g hYZ hW
  have hZ_YW : MDiffAt (fun p : M => g.inner p (Zc p) (YWc p)) x :=
    mdifferentiableAt_metric_inner (I := I) g hZ hYW
  have hXZ_W : MDiffAt (fun p : M => g.inner p (XZc p) (Wc p)) x :=
    mdifferentiableAt_metric_inner (I := I) g hXZ hW
  have hZ_XW : MDiffAt (fun p : M => g.inner p (Zc p) (XWc p)) x :=
    mdifferentiableAt_metric_inner (I := I) g hZ hXW
  have hXYf :
      directionalDeriv (I := I) Xc
          (fun y : M => directionalDeriv (I := I) Yc f y) x =
        (g.inner x ((cov YZc x) (Xc x)) (Wc x) +
          g.inner x (YZc x) ((cov Wc x) (Xc x))) +
        (g.inner x ((cov Zc x) (Xc x)) (YWc x) +
          g.inner x (Zc x) ((cov YWc x) (Xc x))) := by
    have h1 := RicciFlower.Realized.metric_compatible_apply (I := I) hmc
      (x := x) Xc YZc Wc hX hYZ hW
    have h1' :
        directionalDeriv (I := I) Xc (fun p : M => g.inner p (YZc p) (Wc p)) x =
          g.inner x ((cov YZc x) (Xc x)) (Wc x) +
            g.inner x (YZc x) ((cov Wc x) (Xc x)) := by
      simpa [directionalDeriv, extDerivFun, NormedSpace.fromTangentSpace] using h1
    have h2 := RicciFlower.Realized.metric_compatible_apply (I := I) hmc
      (x := x) Xc Zc YWc hX hZ hYW
    have h2' :
        directionalDeriv (I := I) Xc (fun p : M => g.inner p (Zc p) (YWc p)) x =
          g.inner x ((cov Zc x) (Xc x)) (YWc x) +
            g.inner x (Zc x) ((cov YWc x) (Xc x)) := by
      simpa [directionalDeriv, extDerivFun, NormedSpace.fromTangentSpace] using h2
    calc
      directionalDeriv (I := I) Xc
          (fun y : M => directionalDeriv (I := I) Yc f y) x
          = directionalDeriv (I := I) Xc
              (fun p : M => g.inner p (YZc p) (Wc p) +
                g.inner p (Zc p) (YWc p)) x :=
            directionalDeriv_congr_nhds (I := I) (X := Xc) hYf_eq
      _ = directionalDeriv (I := I) Xc
              (fun p : M => g.inner p (YZc p) (Wc p)) x +
            directionalDeriv (I := I) Xc
              (fun p : M => g.inner p (Zc p) (YWc p)) x :=
            directionalDeriv_add_fun (I := I) Xc x hYZ_W hZ_YW
      _ = _ := by rw [h1', h2']
  have hYXf :
      directionalDeriv (I := I) Yc
          (fun y : M => directionalDeriv (I := I) Xc f y) x =
        (g.inner x ((cov XZc x) (Yc x)) (Wc x) +
          g.inner x (XZc x) ((cov Wc x) (Yc x))) +
        (g.inner x ((cov Zc x) (Yc x)) (XWc x) +
          g.inner x (Zc x) ((cov XWc x) (Yc x))) := by
    have h1 := RicciFlower.Realized.metric_compatible_apply (I := I) hmc
      (x := x) Yc XZc Wc hY hXZ hW
    have h1' :
        directionalDeriv (I := I) Yc (fun p : M => g.inner p (XZc p) (Wc p)) x =
          g.inner x ((cov XZc x) (Yc x)) (Wc x) +
            g.inner x (XZc x) ((cov Wc x) (Yc x)) := by
      simpa [directionalDeriv, extDerivFun, NormedSpace.fromTangentSpace] using h1
    have h2 := RicciFlower.Realized.metric_compatible_apply (I := I) hmc
      (x := x) Yc Zc XWc hY hZ hXW
    have h2' :
        directionalDeriv (I := I) Yc (fun p : M => g.inner p (Zc p) (XWc p)) x =
          g.inner x ((cov Zc x) (Yc x)) (XWc x) +
            g.inner x (Zc x) ((cov XWc x) (Yc x)) := by
      simpa [directionalDeriv, extDerivFun, NormedSpace.fromTangentSpace] using h2
    calc
      directionalDeriv (I := I) Yc
          (fun y : M => directionalDeriv (I := I) Xc f y) x
          = directionalDeriv (I := I) Yc
              (fun p : M => g.inner p (XZc p) (Wc p) +
                g.inner p (Zc p) (XWc p)) x :=
            directionalDeriv_congr_nhds (I := I) (X := Yc) hXf_eq
      _ = directionalDeriv (I := I) Yc
              (fun p : M => g.inner p (XZc p) (Wc p)) x +
            directionalDeriv (I := I) Yc
              (fun p : M => g.inner p (Zc p) (XWc p)) x :=
            directionalDeriv_add_fun (I := I) Yc x hXZ_W hZ_XW
      _ = _ := by rw [h1', h2']
  have hBf :
      directionalDeriv (I := I) Bc f x =
        g.inner x ((cov Zc x) (Bc x)) (Wc x) +
          g.inner x (Zc x) ((cov Wc x) (Bc x)) := by
    have hmetric := RicciFlower.Realized.metric_compatible_apply (I := I) hmc
      (x := x) Bc Zc Wc hB hZ hW
    simpa [directionalDeriv, extDerivFun, NormedSpace.fromTangentSpace, f] using hmetric
  have hcomm :=
    directionalDeriv_directionalDeriv_sub_commutator
      (I := I) Xc Yc f x hX2 hY2 hf2
  rw [hXYf, hYXf, hBf] at hcomm
  have hXc_self : Xc x = X := by
    simpa [Xc] using tangentConstAt_self (I := I) x X
  have hYc_self : Yc x = Y := by
    simpa [Yc] using tangentConstAt_self (I := I) x Y
  have hZc_self : Zc x = Z := by
    simpa [Zc] using tangentConstAt_self (I := I) x Z
  have hWc_self : Wc x = W := by
    simpa [Wc] using tangentConstAt_self (I := I) x W
  have hcurv_zero :
      g.inner x ((cov YZc x) X) W +
        g.inner x Z ((cov YWc x) X) -
        g.inner x ((cov XZc x) Y) W -
        g.inner x Z ((cov XWc x) Y) -
        g.inner x ((cov Zc x) (Bc x)) W -
        g.inner x Z ((cov Wc x) (Bc x)) = 0 := by
    have h := hcomm
    dsimp [YZc, YWc, XZc, XWc] at h
    rw [hXc_self, hYc_self, hZc_self, hWc_self] at h
    ring_nf at h
    change
      g.inner x ((cov YZc x) X) W +
        g.inner x Z ((cov YWc x) X) -
        g.inner x ((cov XZc x) Y) W -
        g.inner x Z ((cov XWc x) Y) -
        g.inner x ((cov Zc x) (Bc x)) W -
        g.inner x Z ((cov Wc x) (Bc x)) = 0 at h
    exact h
  have hsum :
      g.inner x W
          ((cov YZc x) X - (cov XZc x) Y - (cov Zc x) (Bc x)) +
        g.inner x Z
          ((cov YWc x) X - (cov XWc x) Y - (cov Wc x) (Bc x)) = 0 := by
    rw [g.symm x W
      ((cov YZc x) X - (cov XZc x) Y - (cov Zc x) (Bc x))]
    simp only [map_add, map_neg, sub_eq_add_neg, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.neg_apply]
    ring_nf at hcurv_zero ⊢
    exact hcurv_zero
  have hgoal :
      g.inner x W
          ((cov YZc x) X - (cov XZc x) Y - (cov Zc x) (Bc x)) =
        -g.inner x Z
          ((cov YWc x) X - (cov XWc x) Y - (cov Wc x) (Bc x)) := by
    linarith
  change g.inner x W ((connectionRiemannCurvatureField (I := I) cov Xc Yc Zc) x) =
      -g.inner x Z ((connectionRiemannCurvatureField (I := I) cov Xc Yc Wc) x)
  simpa [connectionRiemannCurvatureField, YZc, YWc, XZc, XWc, Bc,
    hXc_self, hYc_self] using hgoal

/-- The lowered Levi-Civita curvature tensor is skew-adjoint in the output
slot. -/
theorem rm04OutputSkewAt_of_leviCivita_realizes
    (g : SmoothRiemannianMetric I M)
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally
      (leviCivitaConnectionOfMetric (I := I) g) (1 : WithTop ℕ∞))
    (Rm04 : Tensor04Section (I := I) (M := M))
    (hRm04 : Rm04RealizesConnection (I := I) g
      (leviCivitaConnectionOfMetric (I := I) g) Rm04)
    {x : M} :
    Rm04OutputSkewAt (I := I) (Rm04 x) := by
  intro W X Y Z
  let Wsec : (p : M) -> TangentSpace I p := tangentConstAt (I := I) x W
  let Xsec : (p : M) -> TangentSpace I p := tangentConstAt (I := I) x X
  let Ysec : (p : M) -> TangentSpace I p := tangentConstAt (I := I) x Y
  let Zsec : (p : M) -> TangentSpace I p := tangentConstAt (I := I) x Z
  have hleft := hRm04 Wsec Xsec Ysec Zsec x
  have hright := hRm04 Zsec Xsec Ysec Wsec x
  have hskew :=
    connectionRiemannCurvatureField_metric_skew_at_of_metricCompatible
      (I := I) g (leviCivitaConnectionOfMetric (I := I) g) hcov
      (leviCivitaConnectionOfMetric_isMetricCompatible (I := I) g) W X Y Z
  dsimp [Wsec, Xsec, Ysec, Zsec] at hleft hright
  rw [tangentConstAt_self] at hleft
  rw [tangentConstAt_self] at hleft
  rw [tangentConstAt_self] at hleft
  rw [tangentConstAt_self] at hleft
  rw [tangentConstAt_self] at hright
  rw [tangentConstAt_self] at hright
  rw [tangentConstAt_self] at hright
  rw [tangentConstAt_self] at hright
  exact hleft.trans (hskew.trans (congrArg (fun r : Real => -r) hright.symm))

/-- The `(1,3)` Levi-Civita curvature tensor is metric-skew in the output
slot. -/
theorem rm13MetricSkewAt_of_leviCivita_realizes
    (g : SmoothRiemannianMetric I M)
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally
      (leviCivitaConnectionOfMetric (I := I) g) (1 : WithTop ℕ∞))
    (Rm13 : Tensor13Section (I := I) (M := M))
    (Rm04 : Tensor04Section (I := I) (M := M))
    (hRm13 : Rm13RealizesConnection (I := I)
      (leviCivitaConnectionOfMetric (I := I) g) Rm13)
    (hRm04 : Rm04RealizesConnection (I := I) g
      (leviCivitaConnectionOfMetric (I := I) g) Rm04)
    {x : M} :
    Rm13MetricSkewAt (I := I) g x (Rm13 x) :=
  rm13MetricSkewAt_of_realizes_outputSkew (I := I) g
    (leviCivitaConnectionOfMetric (I := I) g) Rm13 Rm04 hRm13 hRm04
    (rm04OutputSkewAt_of_leviCivita_realizes (I := I) g hcov Rm04 hRm04)

private theorem oneFormThirdCovDerivCommAt_of_leviCivita_higherOrder_frontier
    (g : SmoothRiemannianMetric I M)
    (Rm13 : Tensor13Section (I := I) (M := M))
    (alphaSec : OneFormSection (I := I) (M := M))
    (nablaAlphaSec : TwoTensorSection (I := I) (M := M))
    {x : M}
    (alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x)
    (nabla2Alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (hRm13 : Rm13RealizesConnection (I := I)
      (leviCivitaConnectionOfMetric (I := I) g) Rm13)
    (halpha : alphaSec x = alpha)
    (hnabla2 : Nabla2OneFormRealizesAt (I := I)
      (leviCivitaConnectionOfMetric (I := I) g) alphaSec nablaAlphaSec x
      nabla2Alpha) :
    OneFormThirdCovDerivCommAt (I := I) Rm13 alpha nabla2Alpha := by
  -- Frontier: prove the one-form Ricci identity from the higher-order
  -- covariant derivative API.  The existing coordinate theorem
  -- `one_form_third_comm_of_coord_ijk` remains a possible backend once the
  -- coordinate curvature producer is rebuilt.
  sorry

/-- Levi-Civita Ricci identity for the third covariant derivative of a
one-form. -/
theorem oneFormThirdCovDerivCommAt_of_leviCivita
    (g : SmoothRiemannianMetric I M)
    (Rm13 : Tensor13Section (I := I) (M := M))
    (alphaSec : OneFormSection (I := I) (M := M))
    (nablaAlphaSec : TwoTensorSection (I := I) (M := M))
    {x : M}
    (alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x)
    (nabla2Alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (hRm13 : Rm13RealizesConnection (I := I)
      (leviCivitaConnectionOfMetric (I := I) g) Rm13)
    (halpha : alphaSec x = alpha)
    (hnabla2 : Nabla2OneFormRealizesAt (I := I)
      (leviCivitaConnectionOfMetric (I := I) g) alphaSec nablaAlphaSec x
      nabla2Alpha) :
    OneFormThirdCovDerivCommAt (I := I) Rm13 alpha nabla2Alpha :=
  oneFormThirdCovDerivCommAt_of_leviCivita_higherOrder_frontier
    (I := I) g Rm13 alphaSec nablaAlphaSec alpha nabla2Alpha hRm13
    halpha hnabla2

end LeviCivita
end Realized
end RicciFlower
