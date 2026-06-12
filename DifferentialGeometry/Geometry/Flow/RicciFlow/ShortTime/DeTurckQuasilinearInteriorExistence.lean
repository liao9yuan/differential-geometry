import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.DeTurckInitialAnchorConstruction

/-! # `g₀`-anchored DeTurck–Ricci interior existence from the honest self-representative remainder

This file re-homes the `g₀`-anchored DeTurck–Ricci interior parabolic-existence node
`deturck_metric_pde_interior_at_initial`
(`Geometry/Flow/RicciFlow/ShortTime/DeTurckInitialDataExistence.lean`) onto a single
**honest, self-representative** maximal-regularity carrier primitive, removing every
smoothing/synthesis reconciliation between two *different* representatives' realized
remainders.

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

Because the gated remainder is a genuine **two-derivative-loss** nonlinearity
(`[(g₀ + T)⁻¹ − g₀⁻¹] · ∇²T`) — and is *not* one-derivative-loss-Lipschitz (the on-disk
`deTurck_g0_carrier_realize_transport` engine consumes a `H^{a+1} → Hᵃ` `FirstOrderOperatorLoss`
+ `H^{a+1}`-ball Lipschitz, which the gated remainder does not satisfy) — the carrier is
produced by the single posited primitive `deTurck_g0_selfRepresentative_carrier`, the standard
quasilinear strictly-parabolic short-time existence for the honest gated nonlinearity, with the
contraction funded by the fibre-small smallness of the principal coefficient.  This is the lone
genuinely-open analytic node; everything above it is sorry-free glue.
-/

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle
open scoped Manifold ContDiff NNReal ENNReal Topology BigOperators
open DifferentialGeometry
open DifferentialGeometry.PDE
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
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

/-- **The `g₀`-anchored honest self-representative DeTurck carrier (genuine analytic input).**

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

This is the genuine, faithful analytic content of the strictly-parabolic, smooth-quasilinear
DeTurck–Ricci flow from smooth initial data, anchored at `g₀`, driven by the honest gated
two-derivative-loss nonlinearity (whose contraction is funded by the fibre-small smallness of the
principal coefficient — the standard quasilinear-parabolic short-time existence; cf. the
principal-symbol cancellation `deTurckNonlinearitySpectral_principalPart_cancels`).  It is the
two-derivative-loss companion of the one-derivative-loss carrier
`deTurck_g0_carrier_realize_transport`, whose engine cannot consume the gated nonlinearity
(it is not `H^{a+1} → Hᵃ`-Lipschitz).  It constrains only the internal carrier
`u₂`/`T_s`/`g_DT`, never `g₀`/the headline; the eight conjuncts are coordinate/realize identities
and the genuine parabolic existence, none of them the interface conclusion (which is the geometric
`deTurckRicciRHS`-derivative of `g_DT`, assembled downstream).  The body is the posited classical
parabolic-existence input; it remains `sorry`, so consumers transitively depend on `sorryAx`. -/
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
              (2 * k) (T_s s)) (Set.Icc 0 T)) :=
  sorry

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
identity.  This is sorry-free glue over the single carrier node; consumers transitively depend on
`deTurck_g0_selfRepresentative_carrier`'s `sorryAx`. -/
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
