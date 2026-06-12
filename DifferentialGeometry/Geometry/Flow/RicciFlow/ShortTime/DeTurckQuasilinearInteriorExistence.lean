import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.DeTurckInitialAnchorConstruction

/-! # `g₀`-anchored DeTurck–Ricci interior existence from the honest self-representative remainder

This file re-homes the `g₀`-anchored DeTurck–Ricci interior parabolic-existence node
`deturck_metric_pde_interior_at_initial`
(`Geometry/Flow/RicciFlow/ShortTime/DeTurckInitialDataExistence.lean`) onto the **honest,
self-representative** maximal-regularity carrier, removing every smoothing/synthesis
reconciliation between two *different* representatives' realized remainders.

The earlier construction (`deturck_metric_pde_interior_at_initial_construction`, via
`deTurck_g0_realize_data`) drives the *one-derivative-loss* Duhamel engine with the
**un-gated synthesis** nonlinearity `N_cont u = deTurckG0SpectralN g₀ a
(deTurckRealizeRemainderOf g₀ g_bg (P u))`, where `P` is a smoothing operator producing a
representative *different* from the trajectory's own smooth representative `T_s s`.  The
forcing along the trajectory is then the realized remainder of `P (ι (u₂ s))`, which must be
reconciled with the honest gate gauge `deTurckRemainderRealizeSection g₀ g_bg (ι (u₂ s))`
through a per-curve match (`PerCurveRealizeGaugeMatch`).  That match is a posited equality
between *two distinct representatives' remainders* — exactly the family of statements the
project has repeatedly refuted (the "smoothed-vs-gate remainder match"; see
`PROVE_REFUTED.md`).

Here the nonlinearity fed to the carrier engine is the **gated, self-representative**
remainder directly,

  `N_cont u := deTurckG0SpectralN g₀ a (deTurckRemainderRealizeSection g₀ g_bg u)` ,

so that along the constructed trajectory the forcing is *by the definition of*
`deTurckRemainderRealizeSection` the realized DeTurck remainder of the trajectory's *own*
gate representative.  No smoothing operator, no second representative, and no
remainder–remainder reconciliation: the spectral-coordinate tie `hN_coeff` is then
**definitional** (`deTurckG0SpectralN_coeff`, `Nsec := deTurckRemainderRealizeSection g₀ g_bg`,
`hNsec_realize := rfl`), and the geometric reconciliation to `deTurckRicciRHS g_bg (g_DT s)`
is the corrector-free decoupled principal-part match `deTurck_g0_decoupled_principal_match`
(itself `deTurckRemainderRealize_geomMatch`, a fully proven geometric identity).

## Decomposition of the carrier

Because the gated remainder is a genuine **two-derivative-loss** nonlinearity
(`[(g₀ + T)⁻¹ − g₀⁻¹] · ∇²T`) — and is *not* one-derivative-loss-Lipschitz (the on-disk
`deTurck_g0_carrier_realize_transport` engine consumes a `H^{a+1} → Hᵃ` `FirstOrderOperatorLoss`
+ `H^{a+1}`-ball Lipschitz, which the gated remainder does not satisfy) — the carrier
`deTurck_g0_selfRepresentative_carrier` cannot be produced by the one-loss driver
`deturck_g0_engine_carrier_extraction`.  It is instead **sorry-free glue** over exactly two
posited analytic primitives plus the existing generic (`N`-free) carrier machinery:

* `deTurckGatedRemainder_maxReg_trajectory_exists` — the trajectory-level **two-loss
  maximal-regularity fixed point**: a positive horizon, an `L²`-time forcing `gforce`, and the
  Duhamel solution `u = maxRegDuhamelMap … 0 gforce` whose forcing is reproduced a.e. by the
  gated self-representative nonlinearity along the trajectory's own solution field, together
  with the trajectory-native all-order forcing/solution mass coupling (the parabolic
  bootstrap of the constructed zero-datum solution).  This is the genuine quasilinear
  strictly-parabolic contraction, funded by the fibre-small δ-smallness of the principal
  coefficient (`deTurckNonlinearitySpectral_principalPart_cancels`) and small-time gains on
  the first-order part.
* `deTurckGated_carrier_RHS_continuousOn_interior` — the interior continuity of the gated
  carrier right-hand side `r ↦ Δ_∇ (u₂ r) + N_cont (ι (u₂ r))` on a fibre-small sub-horizon
  (the Nemytskii continuity of the gated remainder along the all-order-continuous
  trajectory).

Everything else — the pointwise-carrier extraction (`zeroDatum_allscale_continuity_uptoZero`),
the all-order interior membership, the canonical smooth-representative family
(`deturck_g0_carrier_realize_package`), the up-to-`t = 0` `H^{2k}` continuity
(`deturck_g0_carrier_Hk_continuousOn_upto_zero`) and decay
(`deturck_g0_carrier_Hk_smallness_upto_zero`), the fibre-small horizon shrink, the realized
metric family, and the interior FTC strong derivative (over
`deturck_g0_carrier_timeDeriv_ae`) — is assembled here without new analytic content.
Consumers transitively depend on `sorryAx` through the two posited primitives (and the
pre-existing deep nodes those generic engines transit, e.g. the Weyl counting bound).
-/

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle
open scoped Manifold ContDiff NNReal ENNReal Topology BigOperators
open DifferentialGeometry
open DifferentialGeometry.PDE
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSobolev
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [BoundarylessManifold I M]
      [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

/-- **The trajectory-level two-derivative-loss maximal-regularity fixed point for the gated
self-representative DeTurck nonlinearity (genuine analytic input).**

For an anchor metric `g₀`, a flow background `g_bg`, and a supercritical spectral order `a`
(`2a > dim M + 4`, plus the engine arithmetic `dim M < 2(a − 2)`), there are a positive
horizon `T ≤ 1`, an `L²`-time forcing `gforce ∈ L²([0,T]; Hᵃ)`, and the maximal-regularity
Duhamel solution `u` of the smooth datum `0`, such that:

* `hu` — `u = maxRegDuhamelMap a hT hT1 0 gforce` (the solution is the affine Duhamel image
  of its forcing);
* `hforce` — `gforce =ᵐ (fun t => deTurckG0SpectralN g₀ a (deTurckRemainderRealizeSection g₀
  g_bg (field_{a+1} t)))` along the `H^{a+1}`-view solution field: the forcing is reproduced
  almost everywhere by the **gated, self-representative** nonlinearity evaluated on the
  trajectory's *own* solution field — the fixed-point equation of the construction.  By the
  definition of `deTurckRemainderRealizeSection`, the forcing at time `t` is the realized
  DeTurck remainder of the field's own gate representative; no smoothing operator, no second
  representative, no remainder–remainder match;
* `hcouple` — the trajectory-native all-order mass coupling: for every `d`, summability of
  the solution-field mass at order `d + 1` implies summability of the forcing mass at order
  `d`.  This is a property of the **constructed** trajectory (the parabolic bootstrap of the
  zero-datum solution, which is smooth up to `t = 0` on a closed manifold — no spatial
  boundary, hence no compatibility obstruction), *not* a static all-order operator-loss
  hypothesis on the nonlinearity (`FirstOrderOperatorLoss`-style couplings are
  Lean-refuted for the gated gauge; see `PROVE_REFUTED.md`).

This is the standard quasilinear strictly-parabolic short-time existence in spectral
currency: a contraction in the maximal-regularity trajectory space, where the
two-order-loss principal term `[(g₀+T)⁻¹ − g₀⁻¹]·∇²T` of the gated remainder carries a
δ-small coefficient on the fibre-small ball (the principal cancellation
`deTurckNonlinearitySpectral_principalPart_cancels`), funding the contraction together with
small-time gains on the one-order part; each Picard iterate is a smooth trajectory (the
gated gauge of a gate-realizable element is a smooth section, and the zero-datum Duhamel
image of a smooth forcing trajectory is gate-realizable on a small horizon), and the mass
coupling is propagated along the iteration.  The expected next-descent split: the
δ-weighted top/lower-order split Lipschitz of the gated remainder on smooth fibre-small
balls (over `exists_realizedRHSRemainder_weightedHa_le_toHs_highOrder` and
`deTurckG0SpectralN_dist_le_pouHaNorm`), the abstract two-loss small-time contraction, and
the gate-domain persistence of the iterates.

The existential is non-degenerate: `hforce` pins `gforce` to the gated remainder of the
trajectory, so the zero trajectory is a witness exactly when `deTurckRHSSection g_bg g₀`
vanishes — i.e. when `g₀` is a DeTurck fixed point (e.g. the flat torus with `g_bg = g₀`),
in which case the constant flow *is* the honest solution.  The body is the posited
classical parabolic-existence input; it remains `sorry`, so consumers transitively depend
on `sorryAx`. -/
theorem deTurckGatedRemainder_maxReg_trajectory_exists
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha : 2 * a > Module.finrank ℝ E + 4)
    (ha2 : Module.finrank ℝ E < 2 * (a - 2)) :
    ∃ (T : ℝ) (hT : 0 < T) (hT1 : T ≤ 1)
      (gforce : Analysis.Parabolic.TimeSobolev.timeL2
        (tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T)
      (u : Analysis.Parabolic.QuasiLinear.MaxRegSolutionSpace (I := I) (M := M) (a : ℝ) T),
      u = Analysis.Parabolic.QuasiLinear.maxRegDuhamelMap (I := I) (M := M) (a : ℝ)
          hT hT1 (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce ∧
      ((gforce : ℝ → tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ))
          =ᵐ[Analysis.Parabolic.TimeSobolev.timeMeasure T]
        (fun t => deTurckG0SpectralN (I := I) g₀ a
          (deTurckRemainderRealizeSection (I := I) g₀ g_bg
            (Analysis.Parabolic.QuasiLinear.maxRegDuhamelSolFieldHa1 (I := I) (M := M)
              (a : ℝ) hT hT1
              (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce t)))) ∧
      (∀ d : ℝ,
        Summable (solFieldMass (I := I) (M := M) hT.le gforce (d + 1)) →
          Summable (forcingMass (I := I) (M := M) gforce d)) :=
  sorry

/-- **Interior continuity of the gated self-representative carrier right-hand side on a
fibre-small sub-horizon (posited analytic input).**

For the gated trajectory data — the Duhamel solution `u` of the smooth datum `0` (`hu`),
its all-order mass coupling (`hcouple`), the pointwise order-`(a+2)` carrier `u₂` matching
the solution through the everywhere bridge (`hbridge`), and the canonical smooth
representatives `T_s` tied to the carrier coordinates (`hsmoothrepr`) — and any sub-horizon
`0 < Tf ≤ T` on which the realized perturbation is uniformly `g₀`-fibre `1/4`-small
(`hsmall`), the carrier right-hand side

  `r ↦ Δ_∇ (u₂ r) + deTurckG0SpectralN g₀ a (deTurckRemainderRealizeSection g₀ g_bg (ι (u₂ r)))`

is continuous on the open interior `(0, Tf)` into `Hᵃ`.

On `[0, Tf]` the carrier inclusion is gate-realizable (its `L²` class lies in every `Hˢ` by
the coupling bootstrap, and its gate representative is `T_s r` by `hsmoothrepr` and
`L²`-injectivity, fibre-small by `hsmall`), so the gauge takes its honest branch and the
forcing equals the order-`a` spectral read-off of the realized remainder of `T_s r`.  The
continuity is then the Nemytskii continuity of the realized two-derivative-loss remainder
along the trajectory: the interior all-order time-continuity of the carrier
(`interior_allscale_time_continuity` through `hcouple`) makes `r ↦ T_s r` continuous into
every intrinsic `H^{2k}`, and the high-order remainder Sobolev–Lipschitz bound
(`exists_realizedRHSRemainder_weightedHa_le_toHs_highOrder` at the uniform `δ = 1/4 < 1/2`
fibre-smallness, with the `H^{a+2}`-size bound from interior continuity) together with the
spectral-lift Lipschitz `deTurckG0SpectralN_dist_le_pouHaNorm` transports that continuity
to the gated forcing; the Laplacian summand is the continuous order-drop
`scaleLaplacianFun` along the `H^{a+2}`-continuous interior trajectory.  The hypotheses are
honest trajectory data, structurally distinct from the continuity conclusion; no
packaging.  The body is the posited Nemytskii-continuity input; it remains `sorry`, so
consumers transitively depend on `sorryAx`. -/
theorem deTurckGated_carrier_RHS_continuousOn_interior
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha : 2 * a > Module.finrank ℝ E + 4)
    {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1)
    (gforce : Analysis.Parabolic.TimeSobolev.timeL2
      (tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T)
    (u : Analysis.Parabolic.QuasiLinear.MaxRegSolutionSpace (I := I) (M := M) (a : ℝ) T)
    (u₂ : ℝ → tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2))
    (T_s : ℝ → Integral.L2.SmoothCcTensor g₀ 0 2)
    (hu : u = Analysis.Parabolic.QuasiLinear.maxRegDuhamelMap (I := I) (M := M) (a : ℝ)
      hT hT1 (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce)
    (hcouple : ∀ d : ℝ,
      Summable (solFieldMass (I := I) (M := M) hT.le gforce (d + 1)) →
        Summable (forcingMass (I := I) (M := M) gforce d))
    (hbridge : ∀ s ∈ Set.Icc (0 : ℝ) T,
      tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
        (show (a : ℝ) ≤ (a : ℝ) + 2 by linarith) (u₂ s) =
        Analysis.Parabolic.TimeSobolev.timeH1.toFun u s)
    (hsmoothrepr : ∀ s ∈ Set.Icc (0 : ℝ) T,
        ∀ i : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
          (I := I) (M := M) g₀ 0 2,
      (u₂ s).coeff i
        = tensorL2Coeff (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
            (Integral.L2.SmoothCcTensor.toL2 (T_s s)) i)
    {Tf : ℝ} (hTf : 0 < Tf) (hTfT : Tf ≤ T)
    (hsmall : ∀ s ∈ Set.Icc (0 : ℝ) Tf,
      gFibreOpBound (I := I) (M := M) g₀
        (ccTensorBilinSymm (I := I) g₀ (T_s s)) (1 / 4 : ℝ)) :
    ContinuousOn
      (fun r : ℝ => scaleLaplacianFun (I := I) (M := M) (u₂ r) +
        deTurckG0SpectralN (I := I) g₀ a
          (deTurckRemainderRealizeSection (I := I) g₀ g_bg
            (tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
              (show ((a : ℝ) + 1) ≤ (a : ℝ) + 2 by linarith) (u₂ r))))
      (Set.Ioo (0 : ℝ) Tf) :=
  sorry

/-- All-order interior membership of the gated smooth-datum carrier: for the
maximal-regularity carrier `u` of the smooth datum `0` (`hu`), the all-order mass coupling
`hcouple`, and the pointwise representative `u₂` matching the carrier through the
everywhere bridge `hbridge`, the `L²` class of `u₂ s` lies in every intrinsic Sobolev
space on `[0, T]` (the `MemAllTensorHs` antecedent the smooth-representative gate
consumes).  This is the gated-route copy of the corresponding (file-private) lemma of
`DeTurckG0AnalyticInputs.lean`. -/
private theorem gated_carrier_memAllTensorHs
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ) {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1)
    (u₂ : ℝ → tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2))
    (gforce : Analysis.Parabolic.TimeSobolev.timeL2
      (tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T)
    (u : Analysis.Parabolic.QuasiLinear.MaxRegSolutionSpace (I := I) (M := M) (a : ℝ) T)
    (hu : u = Analysis.Parabolic.QuasiLinear.maxRegDuhamelMap (I := I) (M := M) (a : ℝ)
      hT hT1 (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce)
    (hcouple : ∀ d : ℝ,
      Summable (solFieldMass (I := I) (M := M) hT.le gforce (d + 1)) →
        Summable (forcingMass (I := I) (M := M) gforce d))
    (hbridge : ∀ s ∈ Set.Icc (0 : ℝ) T,
      tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
        (show (a : ℝ) ≤ (a : ℝ) + 2 by linarith) (u₂ s) =
        Analysis.Parabolic.TimeSobolev.timeH1.toFun u s) :
    ∀ s ∈ Set.Icc (0 : ℝ) T,
      MemAllTensorHs (I := I) (M := M) g₀ 0 2
        (tensorHsToL2 (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
          (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
          (show (0 : ℝ) ≤ (a : ℝ) + 2 by positivity) (u₂ s)) := by
  classical
  set hcompact := tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2
    with hcompact_def
  have hbase : Summable (forcingMass (I := I) (M := M) gforce ((a : ℝ) - 2)) := by
    have hsum := summable_weight_mul_norm_timeModeCoeff_sq (I := I) (M := M) gforce hcompact
    refine Summable.of_nonneg_of_le
      (fun i => forcingMass_nonneg (I := I) (M := M) gforce ((a : ℝ) - 2) i)
      (fun i => ?_) hsum
    have hbase_ge : (1 : ℝ) ≤ 1 + TensorEigenIdx.lambda (I := I) (M := M) i :=
      one_le_one_add_lambda (I := I) (M := M) i
    have hwle : tensorSobolevWeight (I := I) (M := M) i ((a : ℝ) - 2) ≤
        tensorSobolevWeight (I := I) (M := M) i (a : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hbase_ge (by linarith)
    simpa only [forcingMass] using mul_le_mul_of_nonneg_right hwle (sq_nonneg _)
  have hsolbase : Summable (solFieldMass (I := I) (M := M) hT.le gforce (a : ℝ)) := by
    have hgain := solFieldMass_summable_of_forcingMass_summable (I := I) (M := M)
      hT.le gforce ((a : ℝ) - 2) hbase
    have hrw : (a : ℝ) - 2 + 2 = (a : ℝ) := by ring
    rwa [hrw] at hgain
  have hsolall := solFieldMass_summable_all (I := I) (M := M) hT.le gforce hcouple hsolbase
  have hforce_all : ∀ σ : ℝ, Summable (forcingMass (I := I) (M := M) gforce σ) := by
    intro σ
    exact hcouple σ (hsolall (σ + 1))
  intro s hs σ hσ
  have hb := hbridge s hs
  have hb_coeff : ∀ i : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
        (I := I) (M := M) g₀ 0 2,
      (u₂ s).coeff i = (Analysis.Parabolic.TimeSobolev.timeH1.toFun u s).coeff i := by
    intro i
    rw [← tensorHsInclusion_coeff_apply
      (show (a : ℝ) ≤ (a : ℝ) + 2 by linarith) (u₂ s) i, hb]
  have hsum_σ : Summable (fun i : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
        (I := I) (M := M) g₀ 0 2 =>
      tensorSobolevWeight (I := I) (M := M) i σ * ((u₂ s).coeff i) ^ 2) := by
    refine Summable.of_nonneg_of_le
      (fun i => mul_nonneg (tensorSobolevWeight_nonneg (I := I) (M := M) i σ) (sq_nonneg _))
      (fun i => ?_) ((hforce_all σ).mul_left (4 * T))
    rw [hb_coeff i]
    exact zeroDatum_carrier_weighted_coeff_sq_le (I := I) (M := M) g₀ a gforce hT hT1
      u hu σ i hs
  refine ⟨Analysis.Parabolic.MaximalRegularity.timeModeSynthesisPointwise
      (g := g₀) (r := 0) (s := 2) (b := σ) (fun i => (u₂ s).coeff i) hsum_σ, ?_⟩
  set v := Analysis.Parabolic.MaximalRegularity.timeModeSynthesisPointwise
      (g := g₀) (r := 0) (s := 2) (b := σ) (fun i => (u₂ s).coeff i) hsum_σ with hv_def
  apply (tensorResolventHilbertEigenbasisSigma (I := I) (M := M) hcompact).repr.injective
  ext i
  have hlhs : tensorL2Coeff (I := I) (M := M) hcompact
      (tensorHsToL2 (I := I) (M := M) (g := g₀) (r := 0) (s := 2) hcompact hσ v) i
        = (u₂ s).coeff i := by
    rw [tensorHsToL2_tensorL2Coeff hσ v i, hv_def,
      Analysis.Parabolic.MaximalRegularity.timeModeSynthesisPointwise_coeff]
  have hrhs : tensorL2Coeff (I := I) (M := M) hcompact
      (tensorHsToL2 (I := I) (M := M) (g := g₀) (r := 0) (s := 2) hcompact
        (show (0 : ℝ) ≤ (a : ℝ) + 2 by positivity) (u₂ s)) i = (u₂ s).coeff i :=
    tensorHsToL2_tensorL2Coeff (show (0 : ℝ) ≤ (a : ℝ) + 2 by positivity) (u₂ s) i
  exact hlhs.trans hrhs.symm

/-- The pointwise carrier vanishes at any time where its inclusion vanishes (the smooth
initial datum `0`): from `ι (u₂ s₀) = 0` the order-`(a+2)` carrier `u₂ s₀` is `0`, since
the spectral inclusion is injective on eigenbasis coordinates.  (Gated-route copy of the
file-private lemma of `DeTurckG0AnalyticInputs.lean`.) -/
private theorem gated_carrier_zero_at_zero
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (u₂ : ℝ → tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2))
    {s₀ : ℝ}
    (hcar0 : tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
        (show (a : ℝ) ≤ (a : ℝ) + 2 by linarith) (u₂ 0) = 0)
    (hs0 : s₀ = 0) :
    u₂ s₀ = 0 := by
  subst hs0
  refine tensorHs.ext (funext (fun i => ?_))
  have hc : (tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
      (show (a : ℝ) ≤ (a : ℝ) + 2 by linarith) (u₂ 0)).coeff i = 0 := by
    rw [hcar0]; rfl
  rw [tensorHsInclusion_coeff_apply] at hc
  rw [tensorHs.zero_coeff, hc]

/-- The extracted symmetric bilinear form of the **zero** smooth section vanishes.
(Gated-route copy of the file-private lemma of `DeTurckG0AnalyticInputs.lean`.) -/
private theorem gated_ccTensorBilinSymm_zero_apply
    (g : SmoothRiemannianMetric I M) (x : M) (v w : TangentSpace I x) :
    ccTensorBilinSymm (I := I) g (0 : Integral.L2.SmoothCcTensor g 0 2) x v w = 0 := by
  have hsec0 : (0 : Integral.L2.SmoothCcTensor g 0 2).toSection x
      (ContinuousMultilinearMap.constOfIsEmpty ℝ
        (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ)) = 0 := by
    rw [Integral.L2.SmoothCcTensor.toSection_zero]
    rfl
  have hmodel : ccTensorModel (I := I) g (0 : Integral.L2.SmoothCcTensor g 0 2) x = 0 := by
    rw [ccTensorModel, ccTensorMultilinear_apply, hsec0]
    exact map_zero _
  rw [ccTensorBilinSymm_apply, ccTensorBilin_apply, ccTensorBilin_apply, hmodel,
    ContinuousMultilinearMap.zero_apply, ContinuousMultilinearMap.zero_apply]
  ring

/-- If the `L²` class of a smooth section vanishes, its extracted symmetric bilinear form
vanishes pointwise (`smoothCcTensor_toL2_injective`).  (Gated-route copy of the
file-private lemma of `DeTurckG0AnalyticInputs.lean`.) -/
private theorem gated_ccTensorBilinSymm_of_toL2_zero
    (g : SmoothRiemannianMetric I M) (T : Integral.L2.SmoothCcTensor g 0 2)
    (hT : Integral.L2.SmoothCcTensor.toL2 T = 0) (x : M) (v w : TangentSpace I x) :
    ccTensorBilinSymm (I := I) g T x v w = 0 := by
  have hTzero : T = 0 :=
    smoothCcTensor_toL2_injective (I := I) (M := M) g 0 2
      (by rw [hT, map_zero])
  rw [hTzero]
  exact gated_ccTensorBilinSymm_zero_apply (I := I) g x v w

open MeasureTheory in
/-- **The `g₀`-anchored honest self-representative DeTurck carrier.**

For an arbitrary initial metric `g₀` and a flow background `g_bg` on a closed manifold there
exist a positive time `T`, a supercritical spectral Sobolev order `a` (`2a > dim M + 4`), a
maximal-regularity Duhamel carrier `u₂ : ℝ → Hᵃ⁺²(g₀)`, and its canonical smooth representative
`T_s : ℝ → SmoothCcTensor g₀ 0 2`, with realized metric family `g_DT`, such that:

* `g_DT 0 = g₀` (the perturbation carrier starts at zero, anchoring the flow at the prescribed
  initial metric);
* `hreal` — `g_DT s` is the linear realize `g₀ + ccTensorBilinSymm (T_s s)`;
* `hcont` — the included carrier `s ↦ ι (u₂ s)` is continuous up to `t = 0`;
* `hreg` — the carrier `u₂` solves, on the open interior `(0, T)`, the genuine spectral
  parabolic equation with the **gated, self-representative** nonlinearity,
  ```
  ∂_t (ι u₂) = Δ_∇ u₂
      + deTurckG0SpectralN g₀ a (deTurckRemainderRealizeSection g₀ g_bg (ι (u₂ s))) ,
  ```
  i.e. the forcing is the order-`a` spectral read-off of the realized DeTurck remainder of the
  carrier's *own* gate representative — the realized remainder of the trajectory's own smooth
  representative `T_s s` (they coincide as smooth sections), with **no** smoothing operator and
  **no** second representative;
* `hsmall` — the realized perturbation `ccTensorBilinSymm (T_s s)` is `g₀`-fibre small on the
  interior (the principal coefficient `[(g₀+T_s)⁻¹ − g₀⁻¹]` is `δ`-small, `δ < 1`, which is what
  makes the gated remainder honest and funds the contraction);
* `hsmoothrepr` — `u₂ s`'s eigenbasis coordinates are the `L²` coordinates of `T_s s`;
* `hcanon` — `T_s s` is the canonical smooth representative of the carrier: its `L²` class equals
  the `L²` realization `tensorHsToL2` of `u₂ s`;
* `hHk` — every supercritical `H^{2k}` Sobolev norm of `T_s s` is continuous up to `t = 0` (the
  parabolic-up-to-boundary regularity the chart-`C²` joint-continuity bridge consumes).

This is **sorry-free glue** over the two posited analytic primitives
`deTurckGatedRemainder_maxReg_trajectory_exists` (the two-loss trajectory fixed point with its
trajectory-native mass coupling) and `deTurckGated_carrier_RHS_continuousOn_interior` (the
interior Nemytskii continuity of the gated forcing), assembled through the generic (`N`-free)
carrier machinery: the up-to-`t = 0` pointwise-carrier synthesis
`zeroDatum_allscale_continuity_uptoZero`, the canonical smooth-representative package
`deturck_g0_carrier_realize_package`, the up-to-`0` `H^{2k}` continuity
`deturck_g0_carrier_Hk_continuousOn_upto_zero` and decay
`deturck_g0_carrier_Hk_smallness_upto_zero` (with the `C⁰` fibre embedding
`gFibreOpBound_ccTensorBilinSymm_le_tensorHsNorm`) funding a uniform `1/4`-fibre-small horizon
shrink, the `L²`-time-derivative transport `deturck_g0_carrier_timeDeriv_ae`, and the interior
FTC.  It constrains only the internal carrier `u₂`/`T_s`/`g_DT`, never `g₀`/the headline; the
eight conjuncts are coordinate/realize identities and the genuine parabolic existence, none of
them the interface conclusion (which is the geometric `deTurckRicciRHS`-derivative of `g_DT`,
assembled downstream).  Consumers transitively depend on `sorryAx` through the two posited
primitives. -/
theorem deTurck_g0_selfRepresentative_carrier
    (g₀ g_bg : SmoothRiemannianMetric I M) :
    ∃ (T : ℝ) (a : ℕ), 0 < T ∧ 2 * a > Module.finrank ℝ E + 4 ∧
      ∃ (g_DT : ℝ → SmoothRiemannianMetric I M)
        (u₂ : ℝ → tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2))
        (T_s : ℝ → Integral.L2.SmoothCcTensor g₀ 0 2),
        g_DT 0 = g₀ ∧
        (∀ s ∈ Set.Icc (0 : ℝ) T, ∀ (x : M) (v w : TangentSpace I x),
          (g_DT s).inner x v w
            = g₀.inner x v w + ccTensorBilinSymm (I := I) g₀ (T_s s) x v w) ∧
        ContinuousOn
          (fun s : ℝ => tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
            (show (a : ℝ) ≤ (a : ℝ) + 2 by linarith) (u₂ s)) (Set.Icc 0 T) ∧
        (∀ s ∈ Set.Ioo (0 : ℝ) T,
          HasDerivAt
            (fun r => (tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
              (show (a : ℝ) ≤ (a : ℝ) + 2 by linarith) (u₂ r)))
            (scaleLaplacianFun (I := I) (M := M) (u₂ s) +
              deTurckG0SpectralN (I := I) g₀ a
                (deTurckRemainderRealizeSection (I := I) g₀ g_bg
                  (tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
                    (show ((a : ℝ) + 1) ≤ (a : ℝ) + 2 by linarith) (u₂ s)))) s) ∧
        (∀ s ∈ Set.Ioo (0 : ℝ) T, ∃ δ' : ℝ, δ' < 1 ∧
          gFibreOpBound (I := I) (M := M) g₀
            (ccTensorBilinSymm (I := I) g₀ (T_s s)) δ') ∧
        (∀ s ∈ Set.Icc (0 : ℝ) T,
            ∀ i : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
              (I := I) (M := M) g₀ 0 2,
          (u₂ s).coeff i
            = tensorL2Coeff (I := I) (M := M)
                (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
                (Integral.L2.SmoothCcTensor.toL2 (T_s s)) i) ∧
        (∀ s ∈ Set.Icc (0 : ℝ) T,
          Integral.L2.SmoothCcTensor.toL2 (T_s s) =
            tensorHsToL2 (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
              (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
              (show (0 : ℝ) ≤ (a : ℝ) + 2 by positivity) (u₂ s)) ∧
        (∀ (k : ℕ), 2 * k > Module.finrank ℝ E + 4 →
          ContinuousOn
            (fun s : ℝ => IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2)
              (2 * k) (T_s s)) (Set.Icc 0 T)) := by
  classical
  set a : ℕ := Module.finrank ℝ E + 5 with ha_def
  have ha : 2 * a > Module.finrank ℝ E + 4 := by rw [ha_def]; omega
  have ha2 : Module.finrank ℝ E < 2 * (a - 2) := by rw [ha_def]; omega
  set hcompact := tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2
    with hcompact_def
  -- The two-loss trajectory fixed point for the gated self-representative nonlinearity.
  obtain ⟨T, hT, hT1, gforce, u, hu, hforce, hcouple⟩ :=
    deTurckGatedRemainder_maxReg_trajectory_exists (I := I) (M := M) g₀ g_bg a ha ha2
  -- The pointwise order-`(a+2)` carrier, continuous up to `t = 0`, with the everywhere bridge.
  obtain ⟨u₂, hu₂cont, hbridge⟩ :=
    zeroDatum_allscale_continuity_uptoZero (I := I) (M := M) g₀ a gforce hT hT1 u hu
      hcouple ((a : ℝ) + 2) (by linarith)
  have hcont : ContinuousOn
      (fun s : ℝ => tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
        (show (a : ℝ) ≤ (a : ℝ) + 2 by linarith) (u₂ s)) (Set.Icc 0 T) :=
    (tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
      (show (a : ℝ) ≤ (a : ℝ) + 2 by linarith)).continuous.comp_continuousOn hu₂cont
  -- All-order interior membership, and the canonical smooth-representative family.
  have hmem := gated_carrier_memAllTensorHs (I := I) (M := M) g₀ a hT hT1 u₂ gforce u hu
    hcouple hbridge
  obtain ⟨T_s, hsmoothrepr, hcanon⟩ :=
    deturck_g0_carrier_realize_package (I := I) (M := M) g₀ a u₂ hmem
  -- Up-to-`t = 0` supercritical `H^{2k}` continuity of the smooth representatives.
  have hHk : ∀ (k : ℕ), 2 * k > Module.finrank ℝ E + 4 →
      ContinuousOn
        (fun s : ℝ => SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) (2 * k) (T_s s))
        (Set.Icc 0 T) :=
    deturck_g0_carrier_Hk_continuousOn_upto_zero (I := I) (M := M) g₀ a hT hT1
      u₂ T_s gforce u hu hcouple hbridge hcanon
  -- The carrier vanishes at `t = 0` (smooth datum `0`), hence so does `T_s 0`'s `L²` class.
  have hcar0 : tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
      (show (a : ℝ) ≤ (a : ℝ) + 2 by linarith) (u₂ 0) = 0 := by
    rw [hbridge 0 ⟨le_rfl, hT.le⟩, Analysis.Parabolic.TimeSobolev.timeH1.toFun_zero, hu,
      Analysis.Parabolic.QuasiLinear.maxRegDuhamelMap_init, map_zero]
  have hTs0 : Integral.L2.SmoothCcTensor.toL2 (T_s 0) = 0 := by
    have hu₂0 : u₂ 0 = 0 :=
      gated_carrier_zero_at_zero (I := I) (M := M) g₀ a u₂ hcar0 rfl
    rw [hcanon 0 ⟨le_rfl, hT.le⟩, hu₂0, map_zero]
  -- Supercritical decay of `T_s` to `0` as `t → 0⁺`, and the `C⁰` fibre embedding.
  obtain ⟨C, hC0, hCbound⟩ :=
    gFibreOpBound_ccTensorBilinSymm_le_tensorHsNorm (I := I) (M := M) g₀
  set k₀ : ℕ := (Module.finrank ℝ E + 4) / 2 + 1 with hk₀_def
  have hk₀_super : 2 * k₀ > Module.finrank ℝ E + 4 := by rw [hk₀_def]; omega
  have hdecay := deturck_g0_carrier_Hk_smallness_upto_zero (I := I) (M := M) g₀ a hT hT1
    u₂ T_s gforce u hu hcouple hbridge hcanon k₀ hk₀_super
  -- `C · ‖(T_s s).toHs (2k₀)‖ → 0`, hence `< 1/4` on a punctured right-neighbourhood of `0`.
  have htend : Filter.Tendsto
      (fun s : ℝ => C * ‖SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) (2 * k₀) (T_s s)‖)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
    have := hdecay.const_mul C
    simpa using this
  have hev : ∀ᶠ s in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      C * ‖SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) (2 * k₀) (T_s s)‖ < 1 / 4 :=
    htend.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 4))
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hev
  obtain ⟨η, hη_pos, hη⟩ := hev
  -- Final horizon: shrink so the whole closed interval lies in the `1/4`-fibre-small regime.
  set Tf : ℝ := min T (η / 2) with hTf_def
  have hTf_pos : 0 < Tf := lt_min hT (by linarith)
  have hTf_lt_η : Tf < η := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  have hTfT : Tf ≤ T := min_le_left _ _
  have hsub : Set.Icc (0 : ℝ) Tf ⊆ Set.Icc (0 : ℝ) T :=
    Set.Icc_subset_Icc le_rfl hTfT
  -- Uniform `1/4`-fibre-smallness of the realized perturbation on the shrunk interval.
  have hsmall_quarter : ∀ s ∈ Set.Icc (0 : ℝ) Tf,
      gFibreOpBound (I := I) (M := M) g₀
        (ccTensorBilinSymm (I := I) g₀ (T_s s)) (1 / 4 : ℝ) := by
    intro s hs
    rcases eq_or_lt_of_le hs.1 with hs0 | hs0
    · intro x v w
      have hTsL2 : Integral.L2.SmoothCcTensor.toL2 (T_s s) = 0 := by
        rw [← hs0]; exact hTs0
      rw [gated_ccTensorBilinSymm_of_toL2_zero (I := I) g₀ (T_s s) hTsL2 x v w, abs_zero]
      have hv := Real.sqrt_nonneg (g₀.inner x v v)
      have hw := Real.sqrt_nonneg (g₀.inner x w w)
      positivity
    · have hs_lt_η : s < η := lt_of_le_of_lt hs.2 hTf_lt_η
      have hsmall_lt : C * ‖SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2)
          (2 * k₀) (T_s s)‖ < 1 / 4 := by
        apply hη
        · rw [Real.dist_eq, sub_zero, abs_of_pos hs0]; exact hs_lt_η
        · exact hs0
      intro x v w
      have hv := Real.sqrt_nonneg (g₀.inner x v v)
      have hw := Real.sqrt_nonneg (g₀.inner x w w)
      calc |ccTensorBilinSymm (I := I) g₀ (T_s s) x v w|
          ≤ C * ‖SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) (2 * k₀) (T_s s)‖ *
              Real.sqrt (g₀.inner x v v) * Real.sqrt (g₀.inner x w w) :=
            hCbound k₀ hk₀_super (T_s s) x v w
        _ ≤ 1 / 4 * Real.sqrt (g₀.inner x v v) * Real.sqrt (g₀.inner x w w) := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right hsmall_lt.le hv) hw
  -- The interior strong derivative: FTC over the `L²`-time-derivative transport and the
  -- posited interior continuity of the gated right-hand side.
  have hderiv_ae := deturck_g0_carrier_timeDeriv_ae (I := I) (M := M) g₀ a hT hT1
    (fun v => deTurckG0SpectralN (I := I) g₀ a
      (deTurckRemainderRealizeSection (I := I) g₀ g_bg v))
    gforce u u₂ hu hbridge hforce
  have hRHS_cont := deTurckGated_carrier_RHS_continuousOn_interior (I := I) (M := M)
    g₀ g_bg a ha hT hT1 gforce u u₂ T_s hu hcouple hbridge hsmoothrepr hTf_pos hTfT
    hsmall_quarter
  have hreg : ∀ s ∈ Set.Ioo (0 : ℝ) Tf,
      HasDerivAt
        (fun r => (tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
          (show (a : ℝ) ≤ (a : ℝ) + 2 by linarith) (u₂ r)))
        (scaleLaplacianFun (I := I) (M := M) (u₂ s) +
          deTurckG0SpectralN (I := I) g₀ a
            (deTurckRemainderRealizeSection (I := I) g₀ g_bg
              (tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
                (show ((a : ℝ) + 1) ≤ (a : ℝ) + 2 by linarith) (u₂ s)))) s := by
    set RHS : ℝ → tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ) := fun r =>
      scaleLaplacianFun (I := I) (M := M) (u₂ r) +
        deTurckG0SpectralN (I := I) g₀ a
          (deTurckRemainderRealizeSection (I := I) g₀ g_bg
            (tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
              (show ((a : ℝ) + 1) ≤ (a : ℝ) + 2 by linarith) (u₂ r))) with hRHS_def
    intro s hs
    obtain ⟨hs0, hsT⟩ := hs
    have hsmem : s ∈ Set.Ioo (0 : ℝ) Tf := ⟨hs0, hsT⟩
    have hsIccT : s ∈ Set.Icc (0 : ℝ) T := ⟨hs0.le, hsT.le.trans hTfT⟩
    have h0memT : (0 : ℝ) ∈ Set.Icc (0 : ℝ) T := ⟨le_rfl, hT.le⟩
    have hderiv_int : IntervalIntegrable (fun r => u.deriv r)
        MeasureTheory.volume 0 s :=
      u.intervalIntegrable_deriv h0memT hsIccT
    have hRHS_int : IntervalIntegrable RHS MeasureTheory.volume 0 s := by
      have hsub' : Set.uIoc (0 : ℝ) s ⊆ Set.Icc (0 : ℝ) T :=
        (Set.uIoc_subset_uIcc).trans (Set.uIcc_subset_Icc h0memT hsIccT)
      have hae := ae_restrict_of_ae_restrict_of_subset (μ := MeasureTheory.volume)
        hsub' hderiv_ae
      exact hderiv_int.congr_ae hae
    have hRHS_at : ContinuousAt RHS s :=
      hRHS_cont.continuousAt (isOpen_Ioo.mem_nhds hsmem)
    have hRHS_meas : StronglyMeasurableAtFilter RHS (nhds s) MeasureTheory.volume :=
      hRHS_cont.stronglyMeasurableAtFilter isOpen_Ioo s hsmem
    have hftc_RHS : HasDerivAt (fun r => ∫ x in (0 : ℝ)..r, RHS x) (RHS s) s :=
      intervalIntegral.integral_hasDerivAt_right hRHS_int hRHS_meas hRHS_at
    have heq : (fun r => ∫ x in (0 : ℝ)..r, u.deriv x)
        =ᶠ[nhds s] fun r => ∫ x in (0 : ℝ)..r, RHS x := by
      filter_upwards [Ioo_mem_nhds hs0 hsT] with r hr
      refine intervalIntegral.integral_congr_ae ?_
      have hrIcc : r ∈ Set.Icc (0 : ℝ) T := ⟨hr.1.le, hr.2.le.trans hTfT⟩
      have hsub' : Set.uIoc (0 : ℝ) r ⊆ Set.Icc (0 : ℝ) T :=
        (Set.uIoc_subset_uIcc).trans (Set.uIcc_subset_Icc h0memT hrIcc)
      have hae := ae_restrict_of_ae_restrict_of_subset (μ := MeasureTheory.volume)
        hsub' hderiv_ae
      rw [ae_restrict_iff' measurableSet_uIoc] at hae
      filter_upwards [hae] with x hx hxmem
      exact hx hxmem
    have hftc_u : HasDerivAt (fun r => ∫ x in (0 : ℝ)..r, u.deriv x) (RHS s) s :=
      hftc_RHS.congr_of_eventuallyEq heq
    have htoFun : HasDerivAt
        (fun r => (Analysis.Parabolic.TimeSobolev.timeH1.toFun u r :
          tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ))) (RHS s) s := by
      have h := hftc_u.const_add u.init
      refine h.congr_of_eventuallyEq ?_
      filter_upwards with r
      rw [Analysis.Parabolic.TimeSobolev.timeH1.toFun_apply]
    have hfin : HasDerivAt
        (fun r => (tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
          (show (a : ℝ) ≤ (a : ℝ) + 2 by linarith) (u₂ r))) (RHS s) s := by
      refine htoFun.congr_of_eventuallyEq ?_
      filter_upwards [Ioo_mem_nhds hs0 hsT] with r hr
      exact hbridge r ⟨hr.1.le, hr.2.le.trans hTfT⟩
    simpa only [hRHS_def] using hfin
  -- The realized metric family `g_DT s := g₀ + ccTensorBilinSymm (T_s s)` (`g₀` off the
  -- fibre-small regime — never inspected outside `[0, Tf]`).
  have hsmall_ex : ∀ s ∈ Set.Icc (0 : ℝ) Tf, ∃ δ' : ℝ, δ' < 1 ∧
      gFibreOpBound (I := I) (M := M) g₀
        (ccTensorBilinSymm (I := I) g₀ (T_s s)) δ' :=
    fun s hs => ⟨1 / 4, by norm_num, hsmall_quarter s hs⟩
  set g_DT : ℝ → SmoothRiemannianMetric I M := fun s =>
    if h : ∃ δ' : ℝ, δ' < 1 ∧
        gFibreOpBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ (T_s s)) δ' then
      tensorSectionRealizeMetric (I := I) g₀ (T_s s) h.choose_spec.1 h.choose_spec.2
    else g₀ with hg_DT_def
  have hreal : ∀ s ∈ Set.Icc (0 : ℝ) Tf, ∀ (x : M) (v w : TangentSpace I x),
      (g_DT s).inner x v w
        = g₀.inner x v w + ccTensorBilinSymm (I := I) g₀ (T_s s) x v w := by
    intro s hs x v w
    rw [hg_DT_def]
    simp only [dif_pos (hsmall_ex s hs)]
    exact tensorSectionRealizeMetric_inner (I := I) g₀ (T_s s) _ _ x v w
  have h0 : g_DT 0 = g₀ := by
    have h0mem : (0 : ℝ) ∈ Set.Icc (0 : ℝ) Tf := ⟨le_rfl, hTf_pos.le⟩
    refine smoothRiemannianMetric_eq_of_inner (I := I) (g_DT 0) g₀ (fun x v w => ?_)
    rw [hreal 0 h0mem x v w,
      gated_ccTensorBilinSymm_of_toL2_zero (I := I) g₀ (T_s 0) hTs0 x v w, add_zero]
  exact ⟨Tf, a, hTf_pos, ha, g_DT, u₂, T_s, h0, hreal, hcont.mono hsub, hreg,
    fun s hs => hsmall_ex s ⟨hs.1.le, hs.2.le⟩,
    fun s hs => hsmoothrepr s (hsub hs),
    fun s hs => hcanon s (hsub hs),
    fun k hk => (hHk k hk).mono hsub⟩

/-- **The `g₀`-anchored DeTurck–Ricci interior parabolic existence, assembled from the honest
self-representative carrier.**

The full four-conjunct interior-existence statement consumed by
`deturck_metric_pde_interior_at_initial`, assembled from the honest self-representative carrier
`deTurck_g0_selfRepresentative_carrier` and the three derived-property assemblers
(`deTurck_g0_inner_continuous_icc`, `deTurck_g0_rhs_right_continuous_at_zero`,
`deTurck_g0_interior_deriv_from_data`), with the corrector-free decoupled principal-part match
`deTurck_g0_decoupled_principal_match` supplying the spectral-coordinate tie and the geometric
reconciliation, and `deTurck_g0_chartGram_continuity` the `k ≤ 2` chart-Gram continuity.

The carrier's gated nonlinearity reads the realized DeTurck remainder of the carrier's own gate
representative directly, so the spectral-coordinate tie `hN_coeff` holds **definitionally** (no
per-curve smoothed-vs-gate match), and the geometric reconciliation is the fully proven gate
identity.  This is sorry-free glue over the carrier node; consumers transitively depend on the
`sorryAx` of the carrier's two posited primitives. -/
theorem deturck_metric_pde_interior_at_initial_selfRepresentative
    (g₀ g_bg : SmoothRiemannianMetric I M) :
    ∃ T : ℝ, 0 < T ∧ ∃ g_DT : ℝ → SmoothRiemannianMetric I M,
      g_DT 0 = g₀ ∧
      (∀ (x : M) (v w : TangentSpace I x),
        ContinuousOn (fun s : ℝ => (g_DT s).inner x v w) (Set.Icc 0 T)) ∧
      (∀ (x : M) (v w : TangentSpace I x),
        ContinuousWithinAt
          (fun s : ℝ => deTurckRicciRHS (I := I) g_bg (g_DT s) x v w)
          (Set.Ioi 0) 0) ∧
      (∀ t ∈ Set.Ioo (0 : ℝ) T, ∀ (x : M) (v w : TangentSpace I x),
        HasDerivWithinAt (fun s : ℝ => (g_DT s).inner x v w)
          (deTurckRicciRHS (I := I) g_bg (g_DT t) x v w) (Set.Ici 0) t) := by
  classical
  obtain ⟨T, a, hT, ha, g_DT, u₂, T_s, h0, hreal, hcont, hreg, hsmall, hsmoothrepr,
      hcanon, hHk⟩ :=
    deTurck_g0_selfRepresentative_carrier (I := I) g₀ g_bg
  -- The honest gated, self-representative nonlinearity and its `L²` gauge section, taken
  -- **concretely** as `deTurckRemainderRealizeSection g₀ g_bg`, so the `L²`-coordinate tie is
  -- definitional and `repr = Nsec`, `hNsec_realize = rfl`.
  set Nsec : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 1) →
      Integral.L2.SmoothCcTensor g₀ 0 2 :=
    deTurckRemainderRealizeSection (I := I) g₀ g_bg with hNsec_def
  set N_cont : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 1) →
      tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ) :=
    fun u => deTurckG0SpectralN (I := I) g₀ a (deTurckRemainderRealizeSection (I := I) g₀ g_bg u)
    with hN_cont_def
  have hNsec_realize : ∀ (u : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 1))
      (x : M) (v w : TangentSpace I x),
      ccTensorBilinSymm (I := I) g₀ (Nsec u) x v w =
        ccTensorBilinSymm (I := I) g₀ (Nsec u) x v w := fun _ _ _ _ => rfl
  -- The corrector-free decoupled geometric reconciliation to `deTurckRicciRHS` (the proven gate
  -- identity), stated for the concrete gauge `Nsec = deTurckRemainderRealizeSection g₀ g_bg`.
  have hgeom := deTurckRemainderRealize_geomMatch (I := I) (M := M) g₀ g_bg a
  -- The carrier inclusion `ι (u₂ s)` is gate-realizable on `[0, T)`: `MemAllTensorHs` from the
  -- smooth representative `T_s s`, and `g₀`-fibre-smallness from `hsmall` on the interior and
  -- from `hreal`/`h0` (`ccTensorBilinSymm g₀ (T_s 0) = 0`) at the initial time.
  have hgate : ∀ s ∈ Set.Ico (0 : ℝ) T,
      realizableAtGate (I := I) g₀
        (tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
          (show ((a : ℝ) + 1) ≤ (a : ℝ) + 2 by linarith) (u₂ s)) := by
    intro s hs
    refine realizableAtGate_carrierInclusion (I := I) g₀ a u₂ T_s
      (hsmoothrepr s (Set.Ico_subset_Icc_self hs)) ?_
    rcases eq_or_lt_of_le hs.1 with hs0 | hs0
    · refine ⟨0, by norm_num, ?_⟩
      intro x v w
      have hz : ccTensorBilinSymm (I := I) g₀ (T_s s) x v w = 0 := by
        have hre := hreal s (Set.Ico_subset_Icc_self hs) x v w
        have hg0 : (g_DT s).inner x v w = g₀.inner x v w := by rw [← hs0, h0]
        rw [hg0] at hre
        linarith [hre]
      rw [hz]; simp
    · exact hsmall s ⟨hs0, hs.2⟩
  -- The spectral-coordinate tie `hN_coeff`: **definitional** for the gated, self-representative
  -- nonlinearity (`deTurckG0SpectralN_coeff`, `Nsec = deTurckRemainderRealizeSection g₀ g_bg`),
  -- with no per-curve smoothed-vs-gate match.
  have hN_coeff : ∀ s ∈ Set.Ico (0 : ℝ) T,
      ∀ i : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
        (I := I) (M := M) g₀ 0 2,
      (N_cont (tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
          (show ((a : ℝ) + 1) ≤ (a : ℝ) + 2 by linarith) (u₂ s))).coeff i =
        tensorL2Coeff (I := I) (M := M)
          (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
          (Integral.L2.SmoothCcTensor.toL2
            (Nsec (tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
              (show ((a : ℝ) + 1) ≤ (a : ℝ) + 2 by linarith) (u₂ s)))) i := by
    intro s hs i
    simp only [hN_cont_def, hNsec_def, deTurckG0SpectralN_coeff]
  -- The carrier `hreg` rephrased with the named gated nonlinearity `N_cont`.
  have hreg' : ∀ s ∈ Set.Ioo (0 : ℝ) T,
      HasDerivAt
        (fun r => (tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
          (show (a : ℝ) ≤ (a : ℝ) + 2 by linarith) (u₂ r)))
        (scaleLaplacianFun (I := I) (M := M) (u₂ s) +
          N_cont
            (tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
              (show ((a : ℝ) + 1) ≤ (a : ℝ) + 2 by linarith) (u₂ s))) s := by
    intro s hs
    simpa only [hN_cont_def] using hreg s hs
  -- The corrector-free geometric reconciliation conjunct (the `hNsec_geom` shape), with the
  -- concrete gauge `Nsec = deTurckRemainderRealizeSection g₀ g_bg` as `repr`.
  have hNsec_geom : ∀ s ∈ Set.Ico (0 : ℝ) T, ∀ (x' : M) (v' w' : TangentSpace I x'),
      ccTensorBilinSymm (I := I) g₀
          (rawTensorConnLapSmooth (I := I) g₀ 0 2 (T_s s)) x' v' w'
        + ccTensorBilinSymm (I := I) g₀
            (Nsec (tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
              (show ((a : ℝ) + 1) ≤ (a : ℝ) + 2 by linarith) (u₂ s))) x' v' w'
        = deTurckRicciRHS (I := I) g_bg (g_DT s) x' v' w' :=
    hgeom T g_DT u₂ T_s hgate
      (fun s hs => hreal s (Set.Ico_subset_Icc_self hs))
      (fun s hs => hsmoothrepr s (Set.Ico_subset_Icc_self hs))
      (fun s hs => hcanon s (Set.Ico_subset_Icc_self hs))
  -- The `k ≤ 2` chart-Gram joint continuity up to `t = 0`, from the carrier data.
  have hC2_chart := deTurck_g0_chartGram_continuity (I := I) g₀ a ha hT g_DT u₂ T_s N_cont
    hreal hcont hreg' h0 hcanon hHk
  refine ⟨T, hT, g_DT, h0, ?_, ?_, ?_⟩
  · exact deTurck_g0_inner_continuous_icc (I := I) g₀ a ha g_DT u₂ T_s hcont hreal
      hsmoothrepr hC2_chart
  · exact deTurck_g0_rhs_right_continuous_at_zero (I := I) g₀ g_bg hT a ha g_DT T_s u₂
      hreal hcont hsmoothrepr hC2_chart
  · exact deTurck_g0_interior_deriv_from_data (I := I) g₀ g_bg a ha g_DT u₂ T_s
      N_cont Nsec Nsec hreal hN_coeff hNsec_realize hreg' hsmoothrepr hNsec_geom

end DifferentialGeometry.PDE.RicciFlow
