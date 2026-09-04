import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Exp
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Solutions.Pullback
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Solutions.OpenRestriction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.Regularity
import DifferentialGeometry.Geometry.Connection.ParallelTransport.PullbackNaturality

set_option autoImplicit false

/-!
# Diffeomorphism naturality of Perelman's L-geometry

This file transports the L-density, L-length, and regularized L-geodesic
equation through a fixed diffeomorphism and identifies the maximal domain and
totalized exponential map.
-/

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open Bundle Set Function Filter
open scoped Manifold ContDiff Topology

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Riemannian.AlongCurve
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong

universe uM uN uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
  [InnerProductSpace Real E] [FiniteDimensional Real E]
  [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]
variable {N : Type uN} [TopologicalSpace N] [ChartedSpace H N]
  [IsManifold I ∞ N] [T2Space N] [SigmaCompactSpace N]
variable {D : RealTimeInterval}

private lemma infty_ne_zero_nat : (∞ : WithTop ℕ∞) ≠ 0 := by decide

omit [InnerProductSpace Real E] [FiniteDimensional Real E]
  [NeZero (Module.finrank Real E)] [I.Boundaryless]
  [IsManifold I ∞ M] [IsManifold I ∞ N] [T2Space M] [T2Space N]
  [SigmaCompactSpace M] [SigmaCompactSpace N] in
private theorem mfderiv_fwd_inv
    (Phi : M ≃ₘ⟮I, I⟯ N) (x : M) (Y : TangentSpace I (Phi x)) :
    mfderiv I I (Phi : M → N) x
        (mfderiv I I (Phi.symm : N → M) (Phi x) Y) = Y := by
  rw [← mfderiv_symm_apply (I := I) Phi x Y]
  rw [← Phi.mfderivToContinuousLinearEquiv_coe infty_ne_zero_nat]
  exact (Phi.mfderivToContinuousLinearEquiv infty_ne_zero_nat x).apply_symm_apply Y

omit [InnerProductSpace Real E] [FiniteDimensional Real E]
  [NeZero (Module.finrank Real E)] [I.Boundaryless]
  [IsManifold I ∞ M] [IsManifold I ∞ N] [T2Space M] [T2Space N]
  [SigmaCompactSpace M] [SigmaCompactSpace N] in
private theorem mfderiv_inv_fwd
    (Phi : M ≃ₘ⟮I, I⟯ N) (x : M) (X : TangentSpace I x) :
    mfderiv I I (Phi.symm : N → M) (Phi x)
        (mfderiv I I (Phi : M → N) x X) = X := by
  rw [← mfderiv_symm_apply (I := I) Phi x]
  rw [← Phi.mfderivToContinuousLinearEquiv_coe infty_ne_zero_nat]
  exact (Phi.mfderivToContinuousLinearEquiv infty_ne_zero_nat x).symm_apply_apply X

omit [InnerProductSpace Real E] [FiniteDimensional Real E]
  [NeZero (Module.finrank Real E)] [I.Boundaryless]
  [IsManifold I ∞ M] [IsManifold I ∞ N]
  [T2Space M] [T2Space N] [SigmaCompactSpace M] [SigmaCompactSpace N] in
private theorem lVelocity_pull
    (Phi : M ≃ₘ⟮I, I⟯ N) (alpha : Real → M) (s : Real) :
    lVelocity (I := I) (fun r => Phi (alpha r)) s =
      mfderiv I I (Phi : M → N) (alpha s) (lVelocity (I := I) alpha s) := by
  by_cases halpha : MDifferentiableAt 𝓘(Real, Real) I alpha s
  · simpa only [lVelocity] using
      (mfderiv_comp_apply (I := 𝓘(Real, Real)) (I' := I) (I'' := I)
        (x := s) (f := alpha) (g := (Phi : M → N))
        (Phi.contMDiff.mdifferentiableAt infty_ne_zero_nat) halpha (1 : Real))
  · have hmap : ¬MDifferentiableAt 𝓘(Real, Real) I
        (fun r => Phi (alpha r)) s := by
      intro h
      have hback := (Phi.symm.contMDiff.mdifferentiableAt infty_ne_zero_nat).comp s h
      have heq : (Phi.symm : N → M) ∘ (fun r => Phi (alpha r)) = alpha := by
        funext r
        exact Phi.symm_apply_apply (alpha r)
      rw [heq] at hback
      exact halpha hback
    simp only [lVelocity, mfderiv_zero_of_not_mdifferentiableAt halpha,
      mfderiv_zero_of_not_mdifferentiableAt hmap, ContinuousLinearMap.zero_apply,
      map_zero]

omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)] in
/-- Perelman's L-density is natural under a fixed diffeomorphism. -/
theorem lDensity_pull
    (S : SolutionOn (I := I) (M := N) D) (Phi : M ≃ₘ⟮I, I⟯ N)
    (T : Real) (alpha : Real → M) (s : Real) :
    lDensity (solutionOn_pullback (I := I) S Phi) T alpha s =
      lDensity S T (fun r => Phi (alpha r)) s := by
  unfold lDensity lSpeedSq
  rw [scalar_pullback (I := I) S Phi]
  rw [show (solutionOn_pullback (I := I) S Phi).base.metric (T - s) =
      Diffeomorph.pullbackMetric (I := I) (S.base.metric (T - s)) Phi from rfl]
  rw [Diffeomorph.pullbackMetric_inner, lVelocity_pull]

omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)] in
/-- Perelman's L-length is natural under a fixed diffeomorphism. -/
theorem lLength_pull
    (S : SolutionOn (I := I) (M := N) D) (Phi : M ≃ₘ⟮I, I⟯ N)
    (T : Real) (alpha : Real → M) (a b : Real) :
    lLength (solutionOn_pullback (I := I) S Phi) T alpha a b =
      lLength S T (fun r => Phi (alpha r)) a b := by
  unfold lLength
  apply intervalIntegral.integral_congr
  intro s _
  exact lDensity_pull (I := I) S Phi T alpha s

omit [InnerProductSpace Real E] [FiniteDimensional Real E]
  [NeZero (Module.finrank Real E)]
  [I.Boundaryless] [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]
  [IsManifold I ∞ N] [T2Space N] [SigmaCompactSpace N] in
private theorem mdiff_restrict_iff
    (U : TopologicalSpace.Opens M) (gamma : Real → U) (s : Real) :
    MDifferentiableAt 𝓘(Real, Real) I (fun r ↦ (gamma r : M)) s ↔
      MDifferentiableAt 𝓘(Real, Real) I gamma s := by
  classical
  constructor
  · intro hgamma
    let cor : M → U := fun x ↦ if hx : x ∈ U then ⟨x, hx⟩ else gamma s
    have hcorval : ∀ x : U, cor (x : M) = x := by
      intro x
      simp only [cor, dif_pos x.2, Subtype.coe_eta]
    have hcor : ContMDiffAt I I ∞ cor (gamma s : M) := by
      rw [← contMDiffAt_subtype_iff (I := I) (I' := I) (U := U)
        (n := ∞) (x := gamma s)]
      have hid : (fun x : U ↦ cor (x : M)) = id := by
        funext x
        exact hcorval x
      rw [hid]
      exact contMDiffAt_id
    have hcomp := (hcor.mdifferentiableAt infty_ne_zero_nat).comp s hgamma
    have heq : cor ∘ (fun r ↦ (gamma r : M)) = gamma := by
      funext r
      exact hcorval (gamma r)
    rw [heq] at hcomp
    exact hcomp
  · intro hgamma
    exact ((contMDiff_subtype_val (I := I) (U := U)).mdifferentiableAt
      infty_ne_zero_nat).comp s hgamma

omit [InnerProductSpace Real E] [FiniteDimensional Real E]
  [NeZero (Module.finrank Real E)]
  [I.Boundaryless] [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]
  [IsManifold I ∞ N] [T2Space N] [SigmaCompactSpace N] in
private theorem lVelocity_restrict
    (U : TopologicalSpace.Opens M) (gamma : Real → U) (s : Real) :
    lVelocity (I := I) (fun r ↦ (gamma r : M)) s =
      lVelocity (I := I) gamma s := by
  by_cases hgamma : MDifferentiableAt 𝓘(Real, Real) I gamma s
  · simpa only [lVelocity, mfderiv_subtype_val_apply] using
      (mfderiv_comp_apply (I := 𝓘(Real, Real)) (I' := I) (I'' := I)
        (x := s) (f := gamma) (g := (Subtype.val : U → M))
        ((contMDiff_subtype_val (I := I) (U := U)).mdifferentiableAt
          infty_ne_zero_nat) hgamma (1 : Real))
  · have hcoe : ¬MDifferentiableAt 𝓘(Real, Real) I
        (fun r ↦ (gamma r : M)) s := by
      exact fun h ↦ hgamma ((mdiff_restrict_iff (I := I) U gamma s).mp h)
    simp only [lVelocity, mfderiv_zero_of_not_mdifferentiableAt hgamma,
      mfderiv_zero_of_not_mdifferentiableAt hcoe, ContinuousLinearMap.zero_apply]
    rfl

omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
  [IsManifold I ∞ N] [T2Space N] [SigmaCompactSpace N] in
private theorem lDensity_restrict
    (S : SolutionOn (I := I) (M := M) D)
    (U : TopologicalSpace.Opens M) [SigmaCompactSpace U] [T2Space U]
    (T : Real) (gamma : Real → U) (s : Real) :
    lDensity
        (DifferentialGeometry.HCGCompactness.solutionOn_restrictOpen
          (I := I) S U) T gamma s =
      lDensity S T (fun r ↦ (gamma r : M)) s := by
  unfold lDensity lSpeedSq
  rw [DifferentialGeometry.HCGCompactness.scalar_restrictOpen]
  change Real.sqrt s *
      (S.scalar (T - s) (gamma s : M) +
        ((S.base.metric (T - s)).restrictOpen (I := I) U).inner
          (gamma s) (lVelocity (I := I) gamma s) (lVelocity (I := I) gamma s)) = _
  rw [SmoothRiemannianMetric.restrictOpen_inner]
  rw [lVelocity_restrict (I := I) U gamma s]

omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
  [IsManifold I ∞ N] [T2Space N] [SigmaCompactSpace N] in
/-- L-length is unchanged when a solution and its raw curve are restricted to
an open submanifold. -/
theorem lLength_restrict
    (S : SolutionOn (I := I) (M := M) D)
    (U : TopologicalSpace.Opens M) [SigmaCompactSpace U] [T2Space U]
    (T : Real) (gamma : Real → U) (a b : Real) :
    lLength
        (DifferentialGeometry.HCGCompactness.solutionOn_restrictOpen
          (I := I) S U) T gamma a b =
      lLength S T (fun s ↦ (gamma s : M)) a b := by
  unfold lLength
  apply intervalIntegral.integral_congr
  intro s _
  exact lDensity_restrict (I := I) S U T gamma s

omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)] in
/-- The regularized L-acceleration is natural under a fixed diffeomorphism. -/
theorem lRegAccel_pull
    (S : SolutionOn (I := I) (M := N) D) (Phi : M ≃ₘ⟮I, I⟯ N)
    (T s : Real) (x : M) (A : TangentSpace I x) :
    mfderiv I I (Phi : M → N) x
        (lRegAccel (solutionOn_pullback (I := I) S Phi) T s x A) =
      lRegAccel S T s (Phi x) (mfderiv I I (Phi : M → N) x A) := by
  let SP := solutionOn_pullback (I := I) S Phi
  let t := T - s ^ 2
  let g := S.base.metric t
  let Yback : TangentSpace I (Phi x) → TangentSpace I x :=
    fun Y => mfderiv I I (Phi.symm : N → M) (Phi x) Y
  apply (metricFlatEquiv (I := I) g (Phi x)).injective
  ext Y
  rw [metricFlatEquiv_apply, metricFlatEquiv_apply]
  have hY : mfderiv I I (Phi : M → N) x (Yback Y) = Y :=
    mfderiv_fwd_inv (I := I) Phi x Y
  have hscalar : SP.scalar t = S.scalar t ∘ (Phi : M → N) := by
    funext y
    exact scalar_pullback (I := I) S Phi t y
  have hgrad := gradientFun_pullback (I := I) g Phi (S.scalar t) x
    ((scalarSmoothOfSol (I := I) S t).contMDiffAt.mdifferentiableAt (by simp))
  have hgradMap :
      mfderiv I I (Phi : M → N) x
          (gradientFun (I := I) (Diffeomorph.pullbackMetric (I := I) g Phi)
            (SP.scalar t) x) =
        gradientFun (I := I) g (S.scalar t) (Phi x) := by
    rw [hscalar, hgrad]
    rw [← Phi.mfderivToContinuousLinearEquiv_coe infty_ne_zero_nat]
    exact (Phi.mfderivToContinuousLinearEquiv infty_ne_zero_nat x).apply_symm_apply _
  have hric :
      SP.ricciAt t x (vec2 (Yback Y) A) =
        S.ricciAt t (Phi x)
          (vec2 Y (mfderiv I I (Phi : M → N) x A)) := by
    change metricRicci (I := I)
        (Diffeomorph.pullbackMetric (I := I) g Phi) x (vec2 (Yback Y) A) = _
    rw [metricRicci_pullback_eval (I := I) g Phi]
    congr 1
    funext q
    fin_cases q
    · exact hY
    · rfl
  calc
    g.inner (Phi x)
        (mfderiv I I (Phi : M → N) x
          (lRegAccel SP T s x A)) Y =
      g.inner (Phi x) Y
        (mfderiv I I (Phi : M → N) x
          (lRegAccel SP T s x A)) := g.symm _ _ _
    _ = (SP.base.metric t).inner x
        (Yback Y) (lRegAccel SP T s x A) := by
          rw [show SP.base.metric t = Diffeomorph.pullbackMetric (I := I) g Phi from rfl,
            Diffeomorph.pullbackMetric_inner, hY]
    _ = 2 * s ^ 2 * (SP.base.metric t).inner x
          (gradientFun (I := I) (SP.base.metric t) (SP.scalar t) x) (Yback Y) -
        4 * s * SP.ricciAt t x (vec2 (Yback Y) A) :=
      by simpa only [t] using lRegAccel_inner SP T s x A (Yback Y)
    _ = 2 * s ^ 2 * g.inner (Phi x)
          (gradientFun (I := I) g (S.scalar t) (Phi x)) Y -
        4 * s * S.ricciAt t (Phi x)
          (vec2 Y (mfderiv I I (Phi : M → N) x A)) := by
      rw [show SP.base.metric t = Diffeomorph.pullbackMetric (I := I) g Phi from rfl,
        Diffeomorph.pullbackMetric_inner, hgradMap, hY, hric]
    _ = g.inner (Phi x)
        Y (lRegAccel S T s (Phi x) (mfderiv I I (Phi : M → N) x A)) := by
      simpa only [t, g] using (lRegAccel_inner S T s (Phi x)
        (mfderiv I I (Phi : M → N) x A) Y).symm
    _ = g.inner (Phi x)
        (lRegAccel S T s (Phi x) (mfderiv I I (Phi : M → N) x A)) Y :=
      g.symm _ _ _

omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)] in
/-- A regularized L-curve for a pulled-back flow maps to a regularized
L-curve for the original flow. -/
theorem isLRegCurve_pull
    (S : SolutionOn (I := I) (M := N) D) (Phi : M ≃ₘ⟮I, I⟯ N)
    (T : Real) (alpha : Real → M) (J : Set Real) (x : M)
    (Z : TangentSpace I x) (halpha :
      IsLRegCurveOn (solutionOn_pullback (I := I) S Phi) T alpha J x Z) :
    IsLRegCurveOn S T (fun s => Phi (alpha s)) J (Phi x)
      (mfderiv I I (Phi : M → N) x Z) := by
  refine ⟨?_, ?_, ?_⟩
  · change Phi (alpha 0) = Phi x
    rw [halpha.1]
  · rw [lVelocity_pull (I := I), halpha.2.1, halpha.1]
    exact map_nsmul (mfderiv I I (Phi : M → N) x) 2 Z
  · intro s hs
    obtain ⟨ht, hmd, hvel, hacc⟩ := halpha.2.2 s hs
    refine ⟨ht, (Phi.contMDiff.mdifferentiableAt infty_ne_zero_nat).comp s hmd, ?_, ?_⟩
    · have hmap := chartRep_map_diff (I := I) Phi alpha
        (fun r => lVelocity (I := I) alpha r) s hmd hvel
      have heq :
          (fun r => lVelocity (I := I) (fun q => Phi (alpha q)) r) =
            fun r => mfderiv I I (Phi : M → N) (alpha r)
              (lVelocity (I := I) alpha r) := by
        funext r
        exact lVelocity_pull (I := I) Phi alpha r
      rw [heq]
      exact hmap
    · have hnat := covAlong_natMDiff (I := I)
        (S.base.metric (T - s ^ 2)) Phi alpha
        (fun r => lVelocity (I := I) alpha r) s hmd hvel
      have hvelEq :
          (fun r => mfderiv I I (Phi : M → N) (alpha r)
            (lVelocity (I := I) alpha r)) =
            fun r => lVelocity (I := I) (fun q => Phi (alpha q)) r := by
        funext r
        exact (lVelocity_pull (I := I) Phi alpha r).symm
      have hacc' :
          covDerivAlong (I := I)
              (Diffeomorph.pullbackMetric (I := I) (S.base.metric (T - s ^ 2)) Phi)
              alpha (fun r => lVelocity (I := I) alpha r) s =
            lRegAccel (solutionOn_pullback (I := I) S Phi) T s (alpha s)
              (lVelocity (I := I) alpha s) := hacc
      rw [← hvelEq, ← hnat, hacc', lRegAccel_pull, lVelocity_pull]

omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)] [I.Boundaryless] in
private theorem solution_pull_inv
    (S : SolutionOn (I := I) (M := N) D) (Phi : M ≃ₘ⟮I, I⟯ N) :
    solutionOn_pullback (I := I) (solutionOn_pullback (I := I) S Phi) Phi.symm = S := by
  cases S with
  | mk base =>
      cases base with
      | mk metric =>
          unfold solutionOn_pullback
          congr 2
          funext t
          change Diffeomorph.pullbackMetric
              (Diffeomorph.pullbackMetric (metric t) Phi) Phi.symm = metric t
          rw [Diffeomorph.pullbackMetric_trans, Phi.symm_trans_self,
            Diffeomorph.pullbackMetric_refl]

omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)] in
/-- Pullback by a diffeomorphism preserves the maximal regularized L-curve
domain after transporting the initial tangent vector. -/
theorem lRegDomain_pull
    (S : SolutionOn (I := I) (M := N) D) (Phi : M ≃ₘ⟮I, I⟯ N)
    (T : Real) (x : M) (Z : TangentSpace I x) :
    lRegDomain (solutionOn_pullback (I := I) S Phi) T x Z =
      lRegDomain S T (Phi x) (mfderiv I I (Phi : M → N) x Z) := by
  ext s
  constructor
  · rintro ⟨alpha, J, hJopen, hJconn, h0J, hsJ, halpha⟩
    exact ⟨fun r => Phi (alpha r), J, hJopen, hJconn, h0J, hsJ,
      isLRegCurve_pull (I := I) S Phi T alpha J x Z halpha⟩
  · rintro ⟨beta, J, hJopen, hJconn, h0J, hsJ, hbeta⟩
    have hdouble :
        solutionOn_pullback (I := I) (solutionOn_pullback (I := I) S Phi) Phi.symm = S :=
      solution_pull_inv (I := I) S Phi
    have hbeta' : IsLRegCurveOn
        (solutionOn_pullback (I := I) (solutionOn_pullback (I := I) S Phi) Phi.symm)
        T beta J (Phi x) (mfderiv I I (Phi : M → N) x Z) := by
      rw [hdouble]
      exact hbeta
    have hback := isLRegCurve_pull (I := I)
      (solutionOn_pullback (I := I) S Phi) Phi.symm T beta J (Phi x)
      (mfderiv I I (Phi : M → N) x Z) hbeta'
    have hZ := mfderiv_inv_fwd (I := I) Phi x Z
    refine ⟨fun r => Phi.symm (beta r), J, hJopen, hJconn, h0J, hsJ, ?_⟩
    convert hback using 1 <;> simp only [Phi.symm_apply_apply, hZ]

omit [InnerProductSpace Real E] in
/-- The totalized regularized L-curve commutes with pullback by a
diffeomorphism. -/
theorem lRegCurve_pull
    (S : SolutionOn (I := I) (M := N) D) (hS : IsSolutionOn (I := I) S)
    (Phi : M ≃ₘ⟮I, I⟯ N) (T : Real) (x : M) (Z : TangentSpace I x) (s : Real) :
    lRegCurve S T (Phi x) (mfderiv I I (Phi : M → N) x Z) s =
      Phi (lRegCurve (solutionOn_pullback (I := I) S Phi) T x Z s) := by
  by_cases hs : s ∈ lRegDomain (solutionOn_pullback (I := I) S Phi) T x Z
  · obtain ⟨J, hJopen, hJconn, h0J, hsJ, hchosen⟩ :=
      lRegChosen_spec (solutionOn_pullback (I := I) S Phi) T x Z hs
    have hmap := isLRegCurve_pull (I := I) S Phi T
      (lRegChosen (solutionOn_pullback (I := I) S Phi) T x Z hs) J x Z hchosen
    have heq := lRegCurve_eqOn S hS T hJopen hJconn h0J hmap hsJ
    rw [heq, lRegCurve_of_mem hs]
  · have ht : s ∉ lRegDomain S T (Phi x)
        (mfderiv I I (Phi : M → N) x Z) := by
      rw [← lRegDomain_pull (I := I) S Phi T x Z]
      exact hs
    rw [lRegCurve_of_not_mem hs, lRegCurve_of_not_mem ht]

omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)] in
/-- Pullback by a diffeomorphism preserves the maximal L-exponential domain. -/
theorem lExpDomain_pull
    (S : SolutionOn (I := I) (M := N) D) (Phi : M ≃ₘ⟮I, I⟯ N)
    (T : Real) (x : M) (Z : TangentSpace I x) :
    lExpDomain (solutionOn_pullback (I := I) S Phi) T x Z =
      lExpDomain S T (Phi x) (mfderiv I I (Phi : M → N) x Z) := by
  ext tau
  simp only [lExpDomain, mem_setOf_eq, and_congr_right_iff]
  intro _
  rw [lRegDomain_pull (I := I) S Phi T x Z]

omit [InnerProductSpace Real E] in
/-- Perelman's totalized L-exponential map commutes with pullback by a fixed
diffeomorphism. -/
theorem lExp_pull
    (S : SolutionOn (I := I) (M := N) D) (hS : IsSolutionOn (I := I) S)
    (Phi : M ≃ₘ⟮I, I⟯ N) (T : Real) (x : M) (Z : TangentSpace I x) (tau : Real) :
    lExp S T (Phi x) (mfderiv I I (Phi : M → N) x Z) tau =
      Phi (lExp (solutionOn_pullback (I := I) S Phi) T x Z tau) := by
  exact lRegCurve_pull (I := I) S hS Phi T x Z (Real.sqrt tau)

end DifferentialGeometry.PDE.RicciFlow.Perelman
