import DifferentialGeometry.Synthetic.Flow.RicciFlow.HamiltonThreeManifold
import Mathlib.Algebra.CharP.Invertible
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# Hamilton Three-Manifold Typeclass Smoke Test

This module is intentionally not imported by `DifferentialGeometry.lean`.

It validates that the final synthetic Hamilton theorem elaborates with the
three named gap typeclasses supplied by deliberately fake instances. The fake
P1/P2 instances use characteristic two, where `IsHalfCoefficient half` is
impossible, so their half-dependent conclusions are vacuous. The fake P3
instance makes its geometric-reaction data predicate `False`.

The unrelated analytic/global realization stack is represented by local smoke
axioms; those are not the target of this test.
-/

open SyntheticTensor

namespace HamiltonThreeManifoldSmoke

abbrev K := ℚ
abbrev R := ℚ
abbrev V := PUnit.{1}
abbrev Time := PUnit.{1}
abbrev A := ℚ
abbrev Point := PUnit.{1}
abbrev Index := PUnit.{1}
abbrev SpaceTime := PUnit.{1}
abbrev Manifold := PUnit.{1}
abbrev Metric := PUnit.{1}
abbrev Diffeomorphism := PUnit.{1}

noncomputable instance ratInvertibleTwo : Invertible (2 : R) :=
  invertibleOfNonzero (by norm_num : (2 : R) ≠ 0)

noncomputable def toyEmb : DerivationEmbedding K R V where
  embed := 0
  embed_injective := by
    intro X Y _
    exact Subsingleton.elim X Y
  bracket_closed := by
    intro _ _
    refine Exists.intro 0 ?_
    simp

def toyConn (_ _ : V) : V := 0

theorem toyConn_add_right (X Y Z : V) :
    toyConn X (Y + Z) = toyConn X Y + toyConn X Z := by
  simp [toyConn]

theorem toyConn_add_left (X Y Z : V) :
    toyConn (X + Y) Z = toyConn X Z + toyConn Y Z := by
  simp [toyConn]

theorem toyConn_smul_left (f : R) (X Z : V) :
    toyConn (f • X) Z = f • toyConn X Z := by
  simp [toyConn]

theorem toyConn_leibniz (X : V) (f : R) (Y : V) :
    toyConn X (f • Y) = (toyEmb.embed X) f • Y + f • toyConn X Y := by
  simp [toyConn]

noncomputable def toyMetricDuality : MetricDuality R V where
  g_tensor := 0
  symm_tensor := by
    ext vs as
    simp [SyntheticTensor.swap_covariant_eval]
  g_inv := 0
  eq_of_forall_g_eq := by
    intro X Y _
    exact Subsingleton.elim X Y
  inverse_eval := by
    intro Y alpha
    have hY : Y = 0 := Subsingleton.elim Y 0
    rw [hY]
    exact (map_zero alpha).symm
  sharp_spec := by
    intro alpha
    refine Exists.intro 0 ?_
    intro Z
    have hZ : Z = 0 := Subsingleton.elim Z 0
    rw [hZ]
    exact (map_zero alpha).symm

theorem toyMetricCompatible : IsMetricCompatible toyEmb toyConn toyMetricDuality := by
  intro X Y Z
  have hX : X = 0 := Subsingleton.elim X 0
  have hY : Y = 0 := Subsingleton.elim Y 0
  have hZ : Z = 0 := Subsingleton.elim Z 0
  rw [hX, hY, hZ]
  simp [toyConn, toyMetricDuality, MetricDuality.g]

theorem toyTorsionFree : IsTorsionFree toyEmb toyConn := by
  intro X Y
  exact Subsingleton.elim _ _

noncomputable def toyLC : LeviCivitaMetricData toyEmb where
  met := toyMetricDuality
  conn := toyConn
  conn_add_right := toyConn_add_right
  conn_add_left := toyConn_add_left
  conn_smul_left := toyConn_smul_left
  conn_leibniz := toyConn_leibniz
  metric_compat := toyMetricCompatible
  torsion_free := toyTorsionFree

noncomputable def toyTD : TimeDerivativeData R A Time where
  dt := 0
  lift f := f PUnit.unit
  eval a _ := a
  lift_algebraMap := by
    intro _
    rfl
  eval_add := by
    intro _ _ _
    rfl
  eval_mul := by
    intro _ _ _
    rfl
  eval_algebraMap := by
    intro _ _
    rfl

instance toyTimeRegularFam : TimeRegularFam toyTD where
  isSmoothFam _ := True
  eval_lift := by
    intro f _ t
    cases t
    rfl
  lift_add := by
    intro _ _ _ _
    rfl
  lift_mul := by
    intro _ _ _ _
    rfl
  isSmoothFam_const := by
    intro _
    trivial
  isSmoothFam_add := by
    intro _ _ _ _
    trivial
  isSmoothFam_mul := by
    intro _ _ _ _
    trivial
  isSmoothFam_neg := by
    intro _ _
    trivial

instance toyTimeRegularFam2 : TimeRegularFam2 toyTD where
  isSmoothFam2 _ := True
  isSmoothFam2_const := by
    intro _
    trivial
  isSmoothFam2_add := by
    intro _ _ _ _
    trivial
  isSmoothFam2_mul := by
    intro _ _ _ _
    trivial
  isSmoothFam2_neg := by
    intro _ _
    trivial
  isSmoothFam2_of_single_fst := by
    intro _ _
    trivial
  isSmoothFam2_of_single_snd := by
    intro _ _
    trivial
  diag_isSmoothFam := by
    intro _ _
    trivial
  slice_left_isSmoothFam := by
    intro _ _ _
    trivial
  slice_right_isSmoothFam := by
    intro _ _ _
    trivial
  dt_apply_diag_leibniz := by
    intro G t _
    simp [TimeDerivativeData.dt_apply, toyTD]

axiom toyAtr : AbstractTrace R V
axiom toyDimensionThree : IsDimensionThree toyAtr
axiom toyRicciPositive :
  RicciPositive toyEmb toyConn toyConn_add_right toyConn_add_left
    toyConn_smul_left toyConn_leibniz toyAtr

noncomputable def toyGFam (_ : Time) : MetricDuality R V := toyMetricDuality
def toyConnFam (_ : Time) : V -> V -> V := toyConn
noncomputable def toyLCFam (_ : Time) : LeviCivitaMetricData toyEmb := toyLC

theorem toyHMet : forall vs as, toyTD.isSmoothFam (fun t => (toyGFam t).g_tensor vs as) := by
  intro _ _
  trivial

theorem toyHaFam : forall s, forall X Y Z, toyConnFam s X (Y + Z) =
    toyConnFam s X Y + toyConnFam s X Z := by
  intro _ X Y Z
  exact toyConn_add_right X Y Z

theorem toyHalFam : forall s, forall X Y Z, toyConnFam s (X + Y) Z =
    toyConnFam s X Z + toyConnFam s Y Z := by
  intro _ X Y Z
  exact toyConn_add_left X Y Z

theorem toyHslFam : forall s, forall (f : R) X Z, toyConnFam s (f • X) Z =
    f • toyConnFam s X Z := by
  intro _ f X Z
  exact toyConn_smul_left f X Z

theorem toyHlFam : forall s, forall X (f : R) Y, toyConnFam s X (f • Y) =
    (toyEmb.embed X) f • Y + f • toyConnFam s X Y := by
  intro _ X f Y
  exact toyConn_leibniz X f Y

theorem toyHRcSmooth : forall vs as, toyTD.isSmoothFam
    (fun t => ricciForm_tensor toyEmb (toyConnFam t) (toyHaFam t) (toyHalFam t)
      (toyHslFam t) (toyHlFam t) toyAtr vs as) := by
  intro _ _
  trivial

axiom toyIsRicciFlow :
  IsRicciFlow toyEmb toyTD toyAtr toyGFam toyHMet toyConnFam toyHaFam toyHalFam
    toyHslFam toyHlFam

axiom toySpatialTemporalComm : SpatialTemporalComm toyEmb toyTD
axiom toyTimeTrComm : TimeTrComm toyAtr toyTD
axiom toyNablaTrComm :
  forall t, NablaTrComm toyEmb toyAtr (toyConnFam t) (toyHaFam t) (toyHlFam t)
axiom toyNablaContractComm :
  forall t, NablaTensorContractComm toyEmb toyAtr (toyConnFam t) (toyHaFam t) (toyHlFam t)
axiom toyNablaTimeProductRule :
  NablaTimeProductRule toyEmb toyTD toyConnFam toyHaFam toyHlFam
axiom toyMetricBilinProductRule : MetricBilinProductRule toyTD toyGFam toyHMet
axiom toyMetricFullProductRule : MetricFullProductRule toyTD toyGFam toyHMet
axiom toyScalarCurvatureProductRule :
  ScalarCurvatureProductRule toyEmb toyTD toyAtr toyGFam toyHMet toyConnFam toyHaFam
    toyHalFam toyHslFam toyHlFam toyHRcSmooth

noncomputable def toyFlow : RicciFlowData K R V Time A where
  emb := toyEmb
  td := toyTD
  atr := toyAtr
  lc_fam := toyLCFam
  h_met := by
    simpa [toyLCFam, toyLC, toyGFam] using toyHMet
  ricci_flow := by
    simpa [toyLCFam, toyLC, toyGFam, toyConnFam] using toyIsRicciFlow
  nabla_time_product_rule := by
    simpa [toyLCFam, toyLC, toyConnFam] using toyNablaTimeProductRule
  spatial_temporal_comm := toySpatialTemporalComm
  time_tr_comm := toyTimeTrComm
  nabla_tr_comm := by
    intro t
    simpa [toyLCFam, toyLC, toyConnFam] using toyNablaTrComm t
  nabla_contract_comm := by
    intro t
    simpa [toyLCFam, toyLC, toyConnFam] using toyNablaContractComm t
  h_mvp := toyMetricBilinProductRule
  h_mfp := toyMetricFullProductRule
  h_Rc_smooth := toyHRcSmooth
  h_sc_prod := toyScalarCurvatureProductRule

def toyContext : HamiltonThreeManifoldGeometricContext K R V Time A
    Manifold Metric Diffeomorphism where
  manifoldOfFlow _ := PUnit.unit
  metricOn _ _ := True
  isCompact _ := True
  isConnected _ := True
  isDiffeomorphism _ _ _ := True
  hasConstantPositiveSectionalCurvature _ _ := True
  pullback_constant_positive := by
    intro _ _ _ _ _ _ _
    refine Exists.intro PUnit.unit ?_
    exact And.intro trivial trivial

noncomputable def toyInput : HamiltonThreeManifoldTypedInput K R V Time A toyContext where
  data := toyFlow
  initialTime := PUnit.unit
  initialManifold := PUnit.unit
  initial_manifold_eq := rfl
  dimensionThree := toyDimensionThree
  compactInitialManifold := trivial
  connectedInitialManifold := trivial
  positiveRicciInitial := toyRicciPositive

axiom toyContractedSecondBianchi :
  forall (D : RicciFlowData K R V Time A) (t : Time) (half : R),
    IsHalfCoefficient half ->
      ContractedSecondBianchiIdentity D.emb (D.conn_fam t) (D.ha_fam t)
        (D.hal_fam t) (D.hsl_fam t) (D.hl_fam t) D.atr (D.g_fam t) half

/-- Fake P1 gap witness. The smoke test only checks final wrapper wiring. -/
instance toyP1 : HamiltonP1ContractedSecondBianchiTheorem K R V Time A where
  contracted_second_bianchi := toyContractedSecondBianchi

axiom toyRiemannFromRicci3DResidualZero
    (emb : DerivationEmbedding K R V) (conn : V -> V -> V)
    (ha : forall X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : forall X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : forall (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (hl : forall X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (atr : AbstractTrace R V) (met : MetricDuality R V) :
  forall (_ : IsDimensionThree atr) (half : R) (h_half : IsHalfCoefficient half) X Y Z W,
    riemannFromRicci3DResidual emb conn ha hal hsl hl atr met half h_half X Y Z W = 0

/-- Fake slice-level P2 calculus. The smoke test only checks final wrapper wiring. -/
@[reducible] def toyRiemannFromRicci3DCalculus
    (emb : DerivationEmbedding K R V) (conn : V -> V -> V)
    (ha : forall X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : forall X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : forall (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (hl : forall X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (atr : AbstractTrace R V) (met : MetricDuality R V) :
    HasRiemannFromRicci3DCalculus emb conn ha hal hsl hl atr met where
  residual_zero := toyRiemannFromRicci3DResidualZero emb conn ha hal hsl hl atr met

/-- Fake P2 gap witness, intentionally routed through the P2 architecture
bridge from slice-level calculus to the Hamilton-level gap typeclass. -/
instance toyP2 : HamiltonP2RiemannFromRicci3DTheorem K R V Time A :=
  hamiltonP2RiemannFromRicci3DTheorem_of_dim3_calculus K R V Time A
    (fun D t =>
      toyRiemannFromRicci3DCalculus D.emb (D.conn_fam t) (D.ha_fam t)
        (D.hal_fam t) (D.hsl_fam t) (D.hl_fam t) D.atr (D.g_fam t))

/-- Fake P3.3 gap witness. Its reaction-data predicate is `False`, so the
cubic-reaction equation is never required. -/
instance toyP3 : HamiltonP3CubicReactionGeometryTheorem K R V Time A where
  IsGeometricReactionData _ _ _ := False
  cubic_reaction_relation := by
    intro _ _ _ _ hdata _
    exact False.elim hdata

instance toyScalarStrongMaximumPrinciple : ScalarStrongMaximumPrinciple R SpaceTime where
  strict_of_nontrivial := by
    intro _ _ _ hex z _
    cases z
    rcases hex with ⟨z0, _, hpos⟩
    cases z0
    exact hpos

axiom toyAnalyticInputs : HamiltonSyntheticAnalyticInputs K R V Time A Point Index
noncomputable instance toyAnalyticInputsInstance :
    HamiltonSyntheticAnalyticInputs K R V Time A Point Index :=
  toyAnalyticInputs
axiom toyEventuallyPositive :
  EventuallyPositiveWitness Index R
    toyAnalyticInputs.curvature_ratio_convergence.profile.eventually
axiom toyBuilder :
  HamiltonSection12ClaimBuilderInput K R V Time A toyContext toyInput
    (Point := Point) (Index := Index) (SpaceTime := SpaceTime)

/-- Smoke check: the final synthetic Hamilton theorem elaborates end-to-end
with the fake P1/P2/P3 gap instances in scope. -/
theorem hamilton_three_manifold_typeclass_smoke :
    exists g : Metric,
      toyContext.metricOn toyInput.initialManifold g /\
        toyContext.hasConstantPositiveSectionalCurvature toyInput.initialManifold g := by
  exact hamilton_three_manifold_from_typed_input K R V Time A toyContext toyInput
    (Point := Point) (Index := Index) (SpaceTime := SpaceTime)
    toyEventuallyPositive toyBuilder

end HamiltonThreeManifoldSmoke
