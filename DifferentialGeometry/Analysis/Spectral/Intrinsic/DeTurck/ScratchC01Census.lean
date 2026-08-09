import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.LowRegC01JetTower
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.LowRegLadderRung
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.LowRegA2PerIndex
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.LowRegA1PerIndex
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.RicciOrder1RadiusFree
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.GradCapAtgw
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.Lc0VBCapWindow
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.GradCapArms
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.SelfLowCapWindows
import DifferentialGeometry.Analysis.Spectral.Intrinsic.HeatSemigroup.GalerkinParabolicEnergy
import DifferentialGeometry.Analysis.Sobolev.Tensor.CrossScaleCauchySchwarz
import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.LowRegOperatorTime
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.LowRegTraceH3Pair
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.HsTwoJet

open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

#print axioms DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.a1_ladder
#print axioms DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.n_diff_hm_rung
#print axioms DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.a2_ladder
#print axioms DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.appCc_cap_hs_le
#print axioms
  DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.exists_appCc_iteratedCovGrad_l2_coeffJetEnvelope_dataJetWindow_le
#print axioms DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.jetNeg
#print axioms DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.opJetAdd
#print axioms DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.moserWin_add
#print axioms DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.selfLow_split
#print axioms DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.c1_jet_tower
#print axioms DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.c0_jet_tower
#print axioms DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.low1Ker_jet
#print axioms DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.selfLow_jet
#print axioms DifferentialGeometry.Integral.Connection.atgwFold
#print axioms DifferentialGeometry.Integral.Connection.atgwToJet
#print axioms DifferentialGeometry.Integral.Connection.permAppEqRs
#print axioms DifferentialGeometry.Integral.Connection.ricci1Split
#print axioms DifferentialGeometry.Integral.Connection.insertAtgw
#print axioms DifferentialGeometry.Integral.Connection.ricciKerAtgw
#print axioms DifferentialGeometry.Integral.Connection.rfns_iCG_connDiffSection_atgw_rf
#print axioms
  DifferentialGeometry.Analysis.Parabolic.TensorSpectral.kernelField_eq_neg_arm_combination
#print axioms DifferentialGeometry.Integral.Connection.b4_mcd_atgw
#print axioms DifferentialGeometry.Integral.Connection.pureAtgw
#print axioms DifferentialGeometry.Integral.Connection.fourTrAtgw
#print axioms DifferentialGeometry.Integral.Connection.dltcEqPure
#print axioms DifferentialGeometry.Integral.Connection.dltcAtgw
#print axioms DifferentialGeometry.Integral.Connection.ricci1Atgw
#print axioms DifferentialGeometry.Integral.Connection.sfEndoAtgw
#print axioms DifferentialGeometry.Integral.Connection.kappaAtgw
#print axioms DifferentialGeometry.Integral.Connection.psiBAtgw
#print axioms DifferentialGeometry.Integral.Connection.bgCcEqConn
#print axioms DifferentialGeometry.Integral.Connection.pieceAtgw
#print axioms DifferentialGeometry.Integral.Connection.lieA1Atgw
#print axioms DifferentialGeometry.Integral.Connection.low1Atgw

-- A1-CUR-2 session 1: valence-generic grid engines + the `Λ₁`-capped currency
#print axioms DifferentialGeometry.Integral.Connection.grid_prod_int_le
#print axioms DifferentialGeometry.Integral.Connection.atgGridIntRs
#print axioms DifferentialGeometry.Integral.Connection.bfGridWinIntRs
#print axioms DifferentialGeometry.Integral.Connection.antidiagonalTupleGrid_integral_radiusFree
#print axioms
  DifferentialGeometry.Integral.Connection.boundedFactorGridWindow_integral_radiusFree_topSeparated
#print axioms DifferentialGeometry.Integral.Connection.atgwToJetRs
#print axioms DifferentialGeometry.Integral.Connection.icgNormComp
#print axioms DifferentialGeometry.Integral.Connection.gradBase_eq
#print axioms DifferentialGeometry.Integral.Connection.gradBase_fun
#print axioms DifferentialGeometry.Integral.Connection.gradCapOfJets
#print axioms DifferentialGeometry.Integral.Connection.gradCapOfBall
#print axioms DifferentialGeometry.Integral.Connection.shiftConst_nn
#print axioms DifferentialGeometry.Integral.Connection.atgwShift
#print axioms DifferentialGeometry.Integral.Connection.atgwCapToJet
#print axioms DifferentialGeometry.Integral.Connection.armShift
#print axioms DifferentialGeometry.Integral.Connection.atgwCapArm
#print axioms DifferentialGeometry.Integral.Connection.atgwCapFold
#print axioms DifferentialGeometry.Integral.Connection.b4_wOmega_atgw
#print axioms DifferentialGeometry.Integral.Connection.lc0VBCapAtgw
#print axioms DifferentialGeometry.Integral.Connection.lc0VBCapJet

-- A1-CUR-2 session 2: the arm calculus, the summand windows, the assembly
#print axioms DifferentialGeometry.Integral.Connection.HasCapWin
#print axioms DifferentialGeometry.Integral.Connection.capOfArm
#print axioms DifferentialGeometry.Integral.Connection.capOfBnd
#print axioms DifferentialGeometry.Integral.Connection.capApp
#print axioms DifferentialGeometry.Integral.Connection.capMono
#print axioms DifferentialGeometry.Integral.Connection.capCongr
#print axioms DifferentialGeometry.Integral.Connection.capAdd
#print axioms DifferentialGeometry.Integral.Connection.capSmul
#print axioms DifferentialGeometry.Integral.Connection.capNeg
#print axioms DifferentialGeometry.Integral.Connection.capSub
#print axioms DifferentialGeometry.Integral.Connection.capReindex
#print axioms DifferentialGeometry.Integral.Connection.capDdc
#print axioms DifferentialGeometry.Integral.Connection.capSlotExt
#print axioms DifferentialGeometry.Integral.Connection.capIter
#print axioms DifferentialGeometry.Integral.Connection.capJet
#print axioms DifferentialGeometry.Integral.Connection.lc0RiemCap
#print axioms DifferentialGeometry.Integral.Connection.lc0AMixCap
#print axioms DifferentialGeometry.Integral.Connection.aaCoreP
#print axioms DifferentialGeometry.Integral.Connection.aaCore
#print axioms DifferentialGeometry.Integral.Connection.aaKerSplit
#print axioms DifferentialGeometry.Integral.Connection.ricciAACap

-- A1-CUR-2 session 3: the last two per-arm windows
#print axioms DifferentialGeometry.Integral.Connection.capOfP
#print axioms DifferentialGeometry.Integral.Connection.capOfDP
#print axioms DifferentialGeometry.Integral.Connection.capDdc0
#print axioms DifferentialGeometry.Integral.Connection.ricciDACap
#print axioms DifferentialGeometry.Integral.Connection.lieCovCap

-- Tame C0 bottom, session 5: the `covGrad connLowOp` groundwork, the Palatini
-- `∇A ⋆ ∇P` arm, and the quadratic assembly.
#print axioms DifferentialGeometry.Combinatorics.prodLeGrid
#print axioms DifferentialGeometry.Combinatorics.prodLeMark1
#print axioms DifferentialGeometry.Combinatorics.atgLeMark1
#print axioms DifferentialGeometry.Integral.Connection.mkOfAtg
#print axioms DifferentialGeometry.Integral.Connection.ricciDAMark
#print axioms DifferentialGeometry.Integral.Connection.ricciDAJet
#print axioms DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.selfLow_jet_quad

-- Tame C0 bottom, session 6: the frontier itself, its two consumers, the six arm
-- jets, the quadratic tower sibling, and the new Lyapunov interpolation brick.
#print axioms DifferentialGeometry.Integral.Connection.gridIntHigh
#print axioms DifferentialGeometry.Integral.Connection.markMon
#print axioms DifferentialGeometry.Integral.Connection.markJet
#print axioms DifferentialGeometry.Integral.Connection.markJet0
#print axioms DifferentialGeometry.Integral.Connection.ricciAAJet
#print axioms DifferentialGeometry.Integral.Connection.lieCovJet
#print axioms DifferentialGeometry.Integral.Connection.lc0VBJet
#print axioms DifferentialGeometry.Integral.Connection.lc0AMixJet
#print axioms DifferentialGeometry.Integral.Connection.lc0RiemJet
#print axioms DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.c0_jet_tower_quad
#print axioms DifferentialGeometry.Integral.lyapunov_pow_le
#print axioms
  DifferentialGeometry.Integral.holder_integral_prod_rpow_le_prod_integral_rpow
#print axioms
  DifferentialGeometry.Integral.Connection.holder_integral_prod_riemannianFiberNormSq_le

-- Tame C0 bottom, session 7: the two-anchor GN bound and the free-weight
-- product assembly that closes `gridIntHigh`.
#print axioms DifferentialGeometry.Integral.Connection.gnTwoAnchor
#print axioms DifferentialGeometry.Integral.Connection.gnProdJet

-- M3: the ball-free (quad) towers and the radius-indexed ladder layer.
#print axioms DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.c1JetTowerQ
#print axioms DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.c2JetTowerQ
#print axioms DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.a2LadderQ
#print axioms DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.a1LadderQ
#print axioms DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.nDiffHmQ
#print axioms DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.c2_jet_tower

-- J4-PREP: the sharp windows (adapter G), the byte-identical compatibility
-- wrappers, and the per-index `a₂` assembly (`appCcPerIdxL2` is a wrapper over
-- `app_jet_sq_le`).  The widened Galerkin identification is censused in
-- `ShortTime/ScratchIdentCensus.lean`.
#print axioms DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.topKerJetSharp
#print axioms DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.topKer_jet
#print axioms DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.c2JetTowerSharp
#print axioms DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.appCcPerIdxL2
#print axioms DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.a2PerIdxJet
#print axioms DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.a2PerIdxLin

-- Brick 4a / Brick A: the head/tail Hölder engine, the promoted shared helpers,
-- and the per-index `a₁` assembly (both `appCc` summands, ball-free).  The `a₁`
-- assembly is the v3 PER-GROUP mixed split (ledger №157), on
-- `app_jet_sq_split` with `S = range q` for the `C₁` summand and
-- `S = range (q-1)` for the `C₀` summand, so that the `C₀` group never reaches
-- state order `q+2`.
#print axioms DifferentialGeometry.Integral.Connection.app_jet_sq_head
#print axioms DifferentialGeometry.Integral.Connection.app_jet_sq_split
#print axioms DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.icgWinShift
#print axioms DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.sqrtAdd2
#print axioms DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.sqrtFinSum
#print axioms DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.a1PerIdxJet
#print axioms DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.a1PerIdxLin

-- Brick C, part 1: the two interface variants the rung-3 closure needs.
-- `energy_l1_single` / `galerkin_l1_single` are the SINGLE-SCALE `L¹`-Grönwall
-- engine with an additive source `c₀` (the `∀ k` hierarchy engines are
-- underivable at the low base, where the ladder prefactor grows with the
-- scale); `two_sum_ladder_add_le` is the cross-scale closure with an additive
-- constant in the ladder hypothesis, absorbed by one further Young step at the
-- same `ε`.
#print axioms DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.energy_l1_single
#print axioms
  DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.galerkin_l1_single
#print axioms
  DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.two_sum_ladder_add_le

-- Brick C, part 4: the quadratic `L¹` rider.  `galRiderBound` runs the
-- single-scale engine with the concrete coefficient `Crid·(1 + E_σ)` — the
-- shape a ladder slot takes when its coefficient factor is a state quantity at
-- the working scale — building the rider's primitive `Crid·(t + P N t)` from
-- the a-priori `∫₀^T E_σ ≤ B` input supplied in primitive form.
#print axioms DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.galRiderBound

-- The dissipation-retaining siblings.  `energy_l1_diss` bounds the augmented
-- energy `Y + cD`; `galRiderDiss` specializes it to the quadratic Galerkin
-- rider and exports a shared bound for the next-scale primitive.
#print axioms DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.energy_l1_diss
#print axioms DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.galRiderDiss

-- The radius-flexible A2 pair and its strict-contraction specialization.
#print axioms DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.radialA2_pairR
#print axioms DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.lowA2_small_one

-- The arbitrary-background H3 inverse-slot pair and the curvature-free easy
-- spectral H2 comparison used by the new high-coefficient lanes.
#print axioms DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.app_h3_tame
#print axioms DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.inv_slot_pair_h3
#print axioms
  DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.LowBaseInternal.trace1_pair_h3
#print axioms DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.rawLap_le_grad2
#print axioms DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.hs_two_le_jet
