import DifferentialGeometry.Analysis.Calculus.CurveDerivative
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Scalar.JointRegularity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.MinMax
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.TraceDensity

set_option autoImplicit false

/-!
# Hamilton's H quantity along regularized L-rays

This file rewrites the spatial trace of the regularized L-index density using
the scalar-curvature evolution equation.  The square-root-time realization is
polynomial at the initial endpoint, so no division by the time parameter is
introduced there.
-/

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open Bundle Set
open scoped Manifold ContDiff Topology

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open DifferentialGeometry.Tensor0SBundle
open MeasureTheory

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
  [InnerProductSpace Real E] [FiniteDimensional Real E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]
variable {D : RealTimeInterval}

/-- Hamilton's scalar `H(X)` quantity in backward time, with the backward
scalar derivative already rewritten by the Ricci-flow evolution equation. -/
noncomputable def lHamilton
    (S : SolutionOn (I := I) (M := M) D) (T tau : Real)
    (x : M) (X : TangentSpace I x) : Real :=
  let g := S.base.metric (T - tau)
  laplacian (I := I) (LeviCivita (I := I) g) g
      (S.scalar (T - tau)) x +
    2 * normSq0S (I := I) g x 2 (S.ricci (T - tau) x) -
    S.scalar (T - tau) x / tau -
    2 * g.inner x
      (gradientFun (I := I) g (S.scalar (T - tau)) x) X +
    2 * S.ricciAt (T - tau) x (vec2 X X)

omit [InnerProductSpace Real E] in
/-- On a regular Ricci-flow time, `lHamilton` is Hamilton's original
backward-time scalar-derivative expression. -/
theorem lHamilton_eq
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T tau : Real)
    (ht : T - tau ∈ D.regular) (x : M) (X : TangentSpace I x) :
    lHamilton S T tau x X =
      -deriv (fun r : Real ↦ S.scalar (T - r) x) tau -
        S.scalar (T - tau) x / tau -
        2 * (S.base.metric (T - tau)).inner x
          (gradientFun (I := I) (S.base.metric (T - tau))
            (S.scalar (T - tau)) x) X +
        2 * S.ricciAt (T - tau) x (vec2 X X) := by
  let G := flowG (I := I) S
  have hbase :=
    (scalarEvolOfSol (I := I) S hS G
      (fun _ ↦ rfl) (fun _ ↦ rfl) ⟨T - tau, ht⟩ x).hasDerivAt
      (D.regular_mem_nhds ht)
  have hsub : HasDerivAt (fun r : Real ↦ T - r) (-1) tau := by
    simpa only [sub_eq_add_neg, Pi.add_apply, Pi.neg_apply, id_eq, zero_add] using
      (hasDerivAt_const (x := tau) (c := T)).sub (hasDerivAt_id (x := tau))
  have hrev := hbase.comp tau hsub
  have hderiv :
      deriv (fun r : Real ↦ S.scalar (T - r) x) tau =
        -(laplacian (I := I) (LeviCivita (I := I)
              (S.base.metric (T - tau))) (S.base.metric (T - tau))
            (S.scalar (T - tau)) x +
          2 * normSq0S (I := I) (S.base.metric (T - tau)) x 2
            (S.ricci (T - tau) x)) := by
    have h :
        deriv (fun r : Real ↦ S.scalar (T - r) x) tau =
          (laplacian (I := I) (LeviCivita (I := I)
                (S.base.metric (T - tau))) (S.base.metric (T - tau))
              (S.scalar (T - tau)) x +
            2 * normSq0S (I := I) (S.base.metric (T - tau)) x 2
              (S.ricci (T - tau) x)) * (-1) := by
      simpa only [Function.comp_apply, G, laplacianAt, flowG,
        SolutionOn.family, SolutionFamily.connection, LeviCivita] using hrev.deriv
    calc
      deriv (fun r : Real ↦ S.scalar (T - r) x) tau = _ := h
      _ = _ := by ring
  rw [hderiv]
  unfold lHamilton
  ring

/-- Polynomial square-root-time realization of `s^4 H`, expressed using the
regularized velocity. -/
noncomputable def lHamSq
    (S : SolutionOn (I := I) (M := M) D) (T : Real)
    (alpha : Real → M) (s : Real) : Real :=
  let t := T - s ^ 2
  let x := alpha s
  let g := S.base.metric t
  let A := lVelocity (I := I) alpha s
  s ^ 4 *
      (laplacian (I := I) (LeviCivita (I := I) g) g (S.scalar t) x +
        2 * normSq0S (I := I) g x 2 (S.ricci t x)) -
    s ^ 2 * S.scalar t x -
    s ^ 3 * g.inner x (gradientFun (I := I) g (S.scalar t) x) A +
    (s ^ 2 / 2) * S.ricciAt t x (vec2 A A)

omit [InnerProductSpace Real E] [I.Boundaryless] [SigmaCompactSpace M] in
/-- Whenever the regularized velocity is `2s` times a raw velocity,
`lHamSq` is exactly `s^4` times Hamilton's `H`. -/
theorem lHamSq_eq
    (S : SolutionOn (I := I) (M := M) D) (T : Real)
    (alpha : Real → M) (s : Real) (X : TangentSpace I (alpha s))
    (hA : lVelocity (I := I) alpha s = (2 * s) • X) :
    lHamSq S T alpha s =
      s ^ 4 * lHamilton S T (s ^ 2) (alpha s) X := by
  by_cases hs : s = 0
  · subst s
    simp [lHamSq, lHamilton]
  let t := T - s ^ 2
  let x := alpha s
  let g := S.base.metric t
  have hinner :
      g.inner x (gradientFun (I := I) g (S.scalar t) x) ((2 * s) • X) =
        (2 * s) * g.inner x
          (gradientFun (I := I) g (S.scalar t) x) X := by
    rw [(g.inner x (gradientFun (I := I) g (S.scalar t) x)).map_smul]
    rfl
  have hfun :
      vec2 (I := I) ((2 * s) • X) ((2 * s) • X) =
        fun i : Fin 2 ↦ (2 * s) • vec2 (I := I) X X i := by
    funext i
    fin_cases i <;> simp [vec2]
  have hric :
      S.ricciAt t x (vec2 (I := I) ((2 * s) • X) ((2 * s) • X)) =
        (2 * s) ^ 2 * S.ricciAt t x (vec2 (I := I) X X) := by
    rw [hfun]
    have hmap := (S.ricciAt t x).map_smul_univ
      (fun _ : Fin 2 ↦ 2 * s) (vec2 (I := I) X X)
    simpa [Fin.prod_univ_two, pow_two, smul_eq_mul] using hmap
  simp only [lHamSq, lHamilton]
  rw [hA, show T - s ^ 2 = t from rfl,
    show alpha s = x from rfl, hinner, hric]
  field_simp [hs]
  ring

omit [InnerProductSpace Real E] in
/-- The scalar curvature along a differentiable square-root-time path obeys
the Ricci-flow time evolution plus its spatial gradient derivative. -/
theorem lScalar_path_deriv
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : Real)
    (alpha : Real → M) {s : Real}
    (ht : T - s ^ 2 ∈ D.regular)
    (halpha : MDifferentiableAt (modelWithCornersSelf Real Real) I alpha s) :
    HasDerivAt (fun r : Real ↦ S.scalar (T - r ^ 2) (alpha r))
      (-2 * s *
          (laplacian (I := I) (LeviCivita (I := I)
              (S.base.metric (T - s ^ 2))) (S.base.metric (T - s ^ 2))
              (S.scalar (T - s ^ 2)) (alpha s) +
            2 * normSq0S (I := I) (S.base.metric (T - s ^ 2))
              (alpha s) 2 (S.ricci (T - s ^ 2) (alpha s))) +
        (S.base.metric (T - s ^ 2)).inner (alpha s)
          (gradientFun (I := I) (S.base.metric (T - s ^ 2))
            (S.scalar (T - s ^ 2)) (alpha s))
          (lVelocity (I := I) alpha s)) s := by
  let time : Real → Real := fun r ↦ T - r ^ 2
  let F : Real × M → Real := fun p ↦ S.scalar p.1 p.2
  let J : Real → Real × M := fun r ↦ (time r, alpha r)
  have hFmd : MDifferentiableAt
      ((modelWithCornersSelf Real Real).prod I)
      (modelWithCornersSelf Real Real) F (J s) := by
    have hnh : D.regular ×ˢ (Set.univ : Set M) ∈ nhds (J s) := by
      apply (IsOpen.prod D.regular_isOpen isOpen_univ).mem_nhds
      exact ⟨by simpa only [J, time] using ht, Set.mem_univ _⟩
    exact ((scalar_joint (I := I) S hS).contMDiffAt hnh).mdifferentiableAt
      (by simp)
  have htimeC : ContMDiff (modelWithCornersSelf Real Real)
      (modelWithCornersSelf Real Real) ∞ time := by
    exact contMDiff_const.sub (contMDiff_id.pow 2)
  have htimeM : MDifferentiableAt (modelWithCornersSelf Real Real)
      (modelWithCornersSelf Real Real) time s :=
    htimeC.mdifferentiableAt (x := s) (by simp)
  have hJmd : MDifferentiableAt (modelWithCornersSelf Real Real)
      ((modelWithCornersSelf Real Real).prod I) J s := by
    exact htimeM.prodMk halpha
  have hcurve :=
    DifferentialGeometry.Analysis.Calculus.hasDerivAt_comp_mfderiv_along
      ((modelWithCornersSelf Real Real).prod I) F J s hFmd hJmd
  have htime : HasDerivAt time (-2 * s) s := by
    change HasDerivAt (fun r : Real ↦ T - r ^ 2) (-2 * s) s
    convert (hasDerivAt_const (x := s) (c := T)).sub
      ((hasDerivAt_id (x := s)).pow 2) using 1
    all_goals simp only [id_eq]
    all_goals ring
  have hJderiv :
      (mfderiv (modelWithCornersSelf Real Real)
        ((modelWithCornersSelf Real Real).prod I) J s) 1 =
        ((-2 * s : Real), lVelocity (I := I) alpha s) := by
    have hJhas : HasMFDerivAt (modelWithCornersSelf Real Real)
        ((modelWithCornersSelf Real Real).prod I) J s
        ((mfderiv (modelWithCornersSelf Real Real)
            (modelWithCornersSelf Real Real) time s).prod
          (mfderiv (modelWithCornersSelf Real Real) I alpha s)) :=
      HasMFDerivAt.prodMk htimeM.hasMFDerivAt halpha.hasMFDerivAt
    rw [hJhas.mfderiv]
    change
      ((mfderiv (modelWithCornersSelf Real Real)
          (modelWithCornersSelf Real Real) time s) 1,
        (mfderiv (modelWithCornersSelf Real Real) I alpha s) 1) =
        ((-2 * s : Real), lVelocity (I := I) alpha s)
    congr 1
    rw [mfderiv_eq_fderiv]
    change (fderiv Real time s) 1 = -2 * s
    rw [fderiv_apply_one_eq_deriv, htime.deriv]
  have hbase :=
    (scalarEvolOfSol (I := I) S hS (flowG (I := I) S)
      (fun _ ↦ rfl) (fun _ ↦ rfl) ⟨T - s ^ 2, ht⟩ (alpha s)).hasDerivAt
      (D.regular_mem_nhds ht)
  apply hcurve.congr_deriv
  change NormedSpace.fromTangentSpace (F (J s))
      ((mfderiv ((modelWithCornersSelf Real Real).prod I)
        (modelWithCornersSelf Real Real) F (J s))
        ((mfderiv (modelWithCornersSelf Real Real)
          ((modelWithCornersSelf Real Real).prod I) J s) 1)) = _
  rw [hJderiv]
  have hsplit := mfderiv_prod_eq_add_apply
    (I := modelWithCornersSelf Real Real) (I' := I)
    (I'' := modelWithCornersSelf Real Real) (f := F)
    (p := J s)
    (v := ((-2 * s : Real), lVelocity (I := I) alpha s)) hFmd
  have hlin :
      NormedSpace.fromTangentSpace (F (J s))
          (mfderiv (modelWithCornersSelf Real Real)
              (modelWithCornersSelf Real Real) (fun r ↦ F (r, alpha s))
              (T - s ^ 2) (-2 * s) +
            mfderiv I (modelWithCornersSelf Real Real)
              (fun x : M ↦ F (T - s ^ 2, x)) (alpha s)
              (lVelocity (I := I) alpha s)) =
        NormedSpace.fromTangentSpace (F (J s))
            (mfderiv (modelWithCornersSelf Real Real)
              (modelWithCornersSelf Real Real) (fun r ↦ F (r, alpha s))
              (T - s ^ 2) (-2 * s)) +
          NormedSpace.fromTangentSpace (F (J s))
            (mfderiv I (modelWithCornersSelf Real Real)
              (fun x : M ↦ F (T - s ^ 2, x)) (alpha s)
              (lVelocity (I := I) alpha s)) := by
    simp [NormedSpace.fromTangentSpace, map_add]
  have hsplit0 :
      mfderiv ((modelWithCornersSelf Real Real).prod I)
          (modelWithCornersSelf Real Real) F (J s)
          ((-2 * s : Real), lVelocity (I := I) alpha s) =
        mfderiv (modelWithCornersSelf Real Real)
            (modelWithCornersSelf Real Real) (fun r ↦ F (r, alpha s))
            (T - s ^ 2) (-2 * s) +
          mfderiv I (modelWithCornersSelf Real Real)
            (fun x : M ↦ F (T - s ^ 2, x)) (alpha s)
            (lVelocity (I := I) alpha s) := by
    simpa only [J, time, Prod.fst, Prod.snd] using hsplit
  have hsplitF := congrArg
    (NormedSpace.fromTangentSpace (F (J s))) hsplit0
  refine hsplitF.trans (hlin.trans ?_)
  congr 1
  · have hd :
        deriv (fun r : Real ↦ F (r, alpha s)) (T - s ^ 2) =
          NormedSpace.fromTangentSpace (F (J s))
            (mfderiv (modelWithCornersSelf Real Real)
              (modelWithCornersSelf Real Real) (fun r ↦ F (r, alpha s))
              (T - s ^ 2) 1) := by
      rw [mfderiv_eq_fderiv]
      change deriv (fun r : Real ↦ F (r, alpha s)) (T - s ^ 2) =
        (fderiv Real (fun r : Real ↦ F (r, alpha s)) (T - s ^ 2)) 1
      rw [fderiv_apply_one_eq_deriv]
    calc
      NormedSpace.fromTangentSpace (F (J s))
          (mfderiv (modelWithCornersSelf Real Real)
            (modelWithCornersSelf Real Real) (fun r ↦ F (r, alpha s))
            (T - s ^ 2) (-2 * s)) =
          (-2 * s) * NormedSpace.fromTangentSpace (F (J s))
            (mfderiv (modelWithCornersSelf Real Real)
              (modelWithCornersSelf Real Real) (fun r ↦ F (r, alpha s))
              (T - s ^ 2) 1) := by
        have harg :
            mfderiv (modelWithCornersSelf Real Real)
                (modelWithCornersSelf Real Real) (fun r ↦ F (r, alpha s))
                (T - s ^ 2) (-2 * s) =
              (-2 * s) •
                mfderiv (modelWithCornersSelf Real Real)
                  (modelWithCornersSelf Real Real) (fun r ↦ F (r, alpha s))
                  (T - s ^ 2) 1 := by
          calc
            mfderiv (modelWithCornersSelf Real Real)
                (modelWithCornersSelf Real Real) (fun r ↦ F (r, alpha s))
                (T - s ^ 2) (-2 * s) =
              mfderiv (modelWithCornersSelf Real Real)
                (modelWithCornersSelf Real Real) (fun r ↦ F (r, alpha s))
                (T - s ^ 2) ((-2 * s) • (1 : Real)) := by
              exact congrArg
                (mfderiv (modelWithCornersSelf Real Real)
                  (modelWithCornersSelf Real Real) (fun r ↦ F (r, alpha s))
                  (T - s ^ 2))
                (show (-2 * s : Real) = (-2 * s) • (1 : Real) by simp)
            _ = (-2 * s) •
                mfderiv (modelWithCornersSelf Real Real)
                  (modelWithCornersSelf Real Real) (fun r ↦ F (r, alpha s))
                  (T - s ^ 2) 1 :=
              (mfderiv (modelWithCornersSelf Real Real)
                (modelWithCornersSelf Real Real) (fun r ↦ F (r, alpha s))
                (T - s ^ 2)).map_smul (-2 * s) (1 : Real)
        calc
          NormedSpace.fromTangentSpace (F (J s))
              (mfderiv (modelWithCornersSelf Real Real)
                (modelWithCornersSelf Real Real) (fun r ↦ F (r, alpha s))
                (T - s ^ 2) (-2 * s)) =
              NormedSpace.fromTangentSpace (F (J s))
                ((-2 * s) •
                  mfderiv (modelWithCornersSelf Real Real)
                    (modelWithCornersSelf Real Real) (fun r ↦ F (r, alpha s))
                    (T - s ^ 2) 1) :=
            congrArg (NormedSpace.fromTangentSpace (F (J s))) harg
          _ = (-2 * s) * NormedSpace.fromTangentSpace (F (J s))
              (mfderiv (modelWithCornersSelf Real Real)
                (modelWithCornersSelf Real Real) (fun r ↦ F (r, alpha s))
                (T - s ^ 2) 1) := by
            simpa only [smul_eq_mul] using
              (NormedSpace.fromTangentSpace (F (J s))).map_smul
                (-2 * s)
                ((mfderiv (modelWithCornersSelf Real Real)
                  (modelWithCornersSelf Real Real) (fun r ↦ F (r, alpha s))
                  (T - s ^ 2)) 1)
      _ = -2 * s *
          (laplacian (I := I) (LeviCivita (I := I)
              (S.base.metric (T - s ^ 2))) (S.base.metric (T - s ^ 2))
              (S.scalar (T - s ^ 2)) (alpha s) +
            2 * normSq0S (I := I) (S.base.metric (T - s ^ 2))
              (alpha s) 2 (S.ricci (T - s ^ 2) (alpha s))) := by
        rw [← hd]
        simpa only [F, laplacianAt, flowG, SolutionOn.family,
          SolutionFamily.connection, LeviCivita] using
          congrArg (fun q : Real ↦ (-2 * s) * q) hbase.deriv
  · have hinner := inner_gradientFun (I := I)
        (S.base.metric (T - s ^ 2)) (S.scalar (T - s ^ 2)) (alpha s)
        (lVelocity (I := I) alpha s)
    symm
    simpa only [F, J, time] using hinner

omit [InnerProductSpace Real E] in
/-- The weighted traced index density differs from Hamilton's square-root
quantity by the derivative of `s^3 R` along the regularized path. -/
theorem lTrace_deriv
    [NeZero (Module.finrank Real E)]
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : Real)
    (alpha : Real → M)
    (P : Fin (Module.finrank Real E) → ∀ r, TangentSpace I (alpha r))
    (s : Real)
    (ht : T - s ^ 2 ∈ D.regular)
    (halpha : MDifferentiableAt (modelWithCornersSelf Real Real) I alpha s)
    (hDP : ∀ i,
      covDerivAlong (I := I) (S.base.metric (T - s ^ 2)) alpha (P i) s =
        (-2 * s) • ricciSharp (I := I) (S.base.metric (T - s ^ 2))
          (alpha s) (P i s))
    (hON : ∀ i j,
      (S.base.metric (T - s ^ 2)).inner (alpha s) (P i s) (P j s) =
        if i = j then 1 else 0) :
    HasDerivAt
      (fun r : Real ↦ r ^ 3 * S.scalar (T - r ^ 2) (alpha r))
      (-lHamSq S T alpha s -
        (s ^ 2 * ∑ i : Fin (Module.finrank Real E),
            lRegIndexInt S T alpha (P i) (P i) s -
          2 * s ^ 2 * S.scalar (T - s ^ 2) (alpha s))) s := by
  have hR := lScalar_path_deriv S hS T alpha ht halpha
  have hF := (hasDerivAt_pow 3 s).mul hR
  have htrace := lIndexInt_trace S T alpha P s hDP hON
  apply hF.congr_deriv
  rw [htrace]
  simp only [lHamSq, ricciNorm, SolutionOn.family_metric]
  ring

/-- Hamilton's accumulated `K` quantity in square-root time. -/
noncomputable def lK
    (S : SolutionOn (I := I) (M := M) D) (T : Real)
    (alpha : Real → M) (b : Real) : Real :=
  2 * ∫ s in (0 : Real)..b, lHamSq S T alpha s

omit [InnerProductSpace Real E] [I.Boundaryless] [SigmaCompactSpace M] in
/-- The square-root realization `lK` agrees with Hamilton's raw backward-time
weighted `H` integral. -/
theorem lK_sq
    (S : SolutionOn (I := I) (M := M) D) (T : Real)
    (gamma : Real → M) (b : Real) (hb : 0 ≤ b) :
    lK S T (sqReparam gamma) b =
      ∫ rho in (0 : Real)..b ^ 2,
        rho * Real.sqrt rho *
          lHamilton S T rho (gamma rho) (lVelocity (I := I) gamma rho) := by
  let k : Real → Real := fun rho ↦
    rho * Real.sqrt rho *
      lHamilton S T rho (gamma rho) (lVelocity (I := I) gamma rho)
  have hsub :=
    intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg
      (g := k) (f := fun s : Real ↦ s ^ 2)
      (f' := fun s : Real ↦ 2 * s) (a := (0 : Real)) (b := b)
      (continuous_id.pow 2).continuousOn
      (by
        intro s _hs
        simpa using hasDerivAt_pow 2 s)
      (by
        intro s hs
        rw [min_eq_left hb, max_eq_right hb] at hs
        exact mul_nonneg (by norm_num) hs.1.le)
  have hpoint : ∀ s ∈ Set.uIcc (0 : Real) b,
      2 * lHamSq S T (sqReparam gamma) s =
        (k ∘ fun r : Real ↦ r ^ 2) s * (2 * s) := by
    intro s hs
    by_cases hs0 : s = 0
    · subst s
      simp [lHamSq, k]
    · have hsI : s ∈ Set.Icc (0 : Real) b := by
        simpa only [Set.uIcc_of_le hb] using hs
      have hspos : 0 < s := lt_of_le_of_ne hsI.1 (Ne.symm hs0)
      rw [lHamSq_eq S T (sqReparam gamma) s
        (lVelocity (I := I) gamma (s ^ 2))
        (lVelocity_sq_pos (I := I) gamma s hspos)]
      simp only [k, Function.comp_apply, sqReparam, Real.sqrt_sq hspos.le]
      ring
  rw [lK, ← intervalIntegral.integral_const_mul]
  calc
    (∫ s in (0 : Real)..b, 2 * lHamSq S T (sqReparam gamma) s) =
        ∫ s in (0 : Real)..b, (k ∘ fun r : Real ↦ r ^ 2) s * (2 * s) := by
      exact intervalIntegral.integral_congr hpoint
    _ = ∫ rho in (0 : Real)..b ^ 2, k rho := by
      simpa [k] using hsub

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
omit [InnerProductSpace Real E] in
/-- Multiplying the regularized Lagrangian by square-root time turns
Hamilton's polynomial density into an exact derivative. -/
theorem lLagMul_deriv
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : Real)
    {alpha : Real → M} {J : Set Real} {x : M}
    {Z : TangentSpace I x}
    (halpha : IsLRegCurveOn S T alpha J x Z)
    {s : Real} (hs : s ∈ J) :
    HasDerivAt (fun r ↦ r * lRegLag S T alpha r)
      (lRegLag S T alpha s - 4 * lHamSq S T alpha s) s := by
  let R : Real → Real := fun r ↦ S.scalar (T - r ^ 2) (alpha r)
  let U : Real → Real := lRegSpeedSq S T alpha
  let F : Real → Real := fun r ↦ r ^ 3 * R r + (r / 4) * U r
  have hR := lScalar_path_deriv S hS T alpha
    (halpha.2.2 s hs).1 (halpha.2.2 s hs).2.1
  have hU := lRegSpeedSq_deriv (I := I) S hS T halpha hs
  have hF : HasDerivAt F (lRegLag S T alpha s / 2 -
      2 * lHamSq S T alpha s) s := by
    have hout := ((hasDerivAt_pow 3 s).mul hR).add
      (((hasDerivAt_id s).div_const 4).mul hU)
    apply hout.congr_deriv
    simp only [id_eq, lRegLag, lRegSpeedSq, lHamSq]
    ring
  have hscaled := hF.const_mul 2
  have hfun : (fun r ↦ 2 * F r) =
      fun r ↦ r * lRegLag S T alpha r := by
    funext r
    simp only [F, R, U, lRegLag, lRegSpeedSq]
    ring
  rw [hfun] at hscaled
  apply hscaled.congr_deriv
  ring

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
omit [InnerProductSpace Real E] in
/-- On a regularized L-ray, Hamilton's accumulated `K` is half the action
minus its terminal Lagrangian boundary term. -/
theorem lK_energy_eq
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : Real)
    {alpha : Real → M} {x : M} {Z : TangentSpace I x}
    (b : Real)
    (halpha : IsLRegCurveOn S T alpha (Set.uIcc (0 : Real) b) x Z)
    (hLag : IntervalIntegrable (lRegLag S T alpha)
      MeasureTheory.volume 0 b)
    (hHam : IntervalIntegrable (lHamSq S T alpha)
      MeasureTheory.volume 0 b) :
    lK S T alpha b =
      (lRegAction S T alpha 0 b - b * lRegLag S T alpha b) / 2 := by
  have hdiff : IntervalIntegrable
      (fun s ↦ lRegLag S T alpha s - 4 * lHamSq S T alpha s)
      MeasureTheory.volume 0 b := hLag.sub (hHam.const_mul 4)
  have hFTC :
      (∫ s in (0 : Real)..b,
          (lRegLag S T alpha s - 4 * lHamSq S T alpha s)) =
        b * lRegLag S T alpha b := by
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun s hs ↦ lLagMul_deriv S hS T halpha hs) hdiff
      |>.trans (by ring)
  rw [intervalIntegral.integral_sub hLag (hHam.const_mul 4),
    intervalIntegral.integral_const_mul] at hFTC
  rw [lRegAction, lK]
  linarith

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
omit [InnerProductSpace Real E] [SigmaCompactSpace M] in
/-- The regularized Lagrangian of a canonical ray is integrable on every
positive compact interval in its maximal domain. -/
theorem lRayLag_int
    [NeZero (Module.finrank Real E)]
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : Real)
    (x : M) (Z : TangentSpace I x) {b : Real}
    (hb : 0 < b) (hbdom : b ∈ lRegDomain S T x Z) :
    IntervalIntegrable
      (lRegLag S T (lRegCurve S T x Z)) MeasureTheory.volume 0 b := by
  let U : Set Real := lRegDomain S T x Z
  let alpha : Real → M := lRegCurve S T x Z
  let z : E := Z
  have hpair : ContDiff Real ∞ (fun s : Real ↦ (z, s)) :=
    contDiff_const.prodMk contDiff_id
  have hlag : ContDiffOn Real ∞ (lRegLag S T alpha) U := by
    simpa only [alpha, z, Function.comp_apply] using
      (lRayLag_smooth S hS T x).comp hpair.contDiffOn
        (fun s (hs : s ∈ U) ↦ by
          simpa only [lRegJointDom, z, U] using hs)
  have hseg : Set.Icc (0 : Real) b ⊆ U := by
    intro s hs
    simpa only [U] using lRegDomain_seg S T x Z hbdom hs.1 hs.2
  exact (hlag.continuousOn.mono hseg).intervalIntegrable_of_Icc hb.le

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
omit [InnerProductSpace Real E] in
/-- Hamilton's square-root density along a canonical L-ray is integrable on
every positive compact interval in its maximal domain. -/
theorem lRayHam_int
    [NeZero (Module.finrank Real E)]
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : Real)
    (x : M) (Z : TangentSpace I x) {b : Real}
    (hb : 0 < b) (hbdom : b ∈ lRegDomain S T x Z) :
    IntervalIntegrable
      (lHamSq S T (lRegCurve S T x Z)) MeasureTheory.volume 0 b := by
  let U : Set Real := lRegDomain S T x Z
  let alpha : Real → M := lRegCurve S T x Z
  let z : E := Z
  let F : Real → Real := fun s ↦ s * lRegLag S T alpha s
  have hpair : ContDiff Real ∞ (fun s : Real ↦ (z, s)) :=
    contDiff_const.prodMk contDiff_id
  have hlag : ContDiffOn Real ∞ (lRegLag S T alpha) U := by
    simpa only [alpha, z, Function.comp_apply] using
      (lRayLag_smooth S hS T x).comp hpair.contDiffOn
        (fun s (hs : s ∈ U) ↦ by
          simpa only [lRegJointDom, z, U] using hs)
  have hF : ContDiffOn Real ∞ F U := by
    simpa only [F, id_eq] using contDiff_id.contDiffOn.mul hlag
  have hUopen : IsOpen U := by
    simpa only [U] using lRegDomain_isOpen S T x Z
  have hseg : Set.Icc (0 : Real) b ⊆ U := by
    intro s hs
    simpa only [U] using lRegDomain_seg S T x Z hbdom hs.1 hs.2
  have hFdcont : ContinuousOn (deriv F) (Set.Icc (0 : Real) b) :=
    (hF.continuousOn_deriv_of_isOpen hUopen (by simp)).mono hseg
  have hFdint : IntervalIntegrable (deriv F)
      MeasureTheory.volume 0 b :=
    hFdcont.intervalIntegrable_of_Icc hb.le
  have hLagInt : IntervalIntegrable (lRegLag S T alpha)
      MeasureTheory.volume 0 b := by
    simpa only [alpha] using lRayLag_int S hS T x Z hb hbdom
  have hright : IntervalIntegrable
      (fun s ↦ (lRegLag S T alpha s - deriv F s) / 4)
      MeasureTheory.volume 0 b := (hLagInt.sub hFdint).div_const 4
  have hgeo := lRegCurve_isReg (I := I) S hS T x Z hb hbdom
  refine hright.congr ?_
  intro s hs
  have hs' : s ∈ Set.Ioc (0 : Real) b := by
    simpa only [Set.uIoc_of_le hb.le] using hs
  have hsIcc : s ∈ Set.Icc (0 : Real) b := ⟨hs'.1.le, hs'.2⟩
  have hpoint := (lLagMul_deriv S hS T hgeo
    (by simpa only [Set.uIcc_of_le hb.le] using hsIcc)).deriv
  have hpoint' : deriv F s =
      lRegLag S T alpha s - 4 * lHamSq S T alpha s := by
    simpa only [F, alpha] using hpoint
  change (lRegLag S T alpha s - deriv F s) / 4 =
    lHamSq S T alpha s
  rw [hpoint']
  ring

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
omit [InnerProductSpace Real E] in
/-- Hamilton's `K` identity along a canonical regularized L-ray requires no
adapted frame or supplied integrability hypothesis. -/
theorem lK_ray_energy
    [NeZero (Module.finrank Real E)]
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : Real)
    (x : M) (Z : TangentSpace I x) {b : Real}
    (hb : 0 < b) (hbdom : b ∈ lRegDomain S T x Z) :
    lK S T (lRegCurve S T x Z) b =
      (lRegAction S T (lRegCurve S T x Z) 0 b -
        b * lRegLag S T (lRegCurve S T x Z) b) / 2 := by
  exact lK_energy_eq S hS T b
    (lRegCurve_isReg (I := I) S hS T x Z hb hbdom)
    (lRayLag_int S hS T x Z hb hbdom)
    (lRayHam_int S hS T x Z hb hbdom)

end DifferentialGeometry.PDE.RicciFlow.Perelman
