import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegGalerkinIdent
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegSmoothBridge
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegForceArms
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegRungThree
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegRungFour
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegRungPack
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegFatouIdent
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegFatouMass
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegAllOrderJet
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegDeTurckOpen
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegUnifGate
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegUnifBounds

-- J4-PREP: the widened Galerkin identification (constants and certificates
-- bound once outside `∀ N`; six per-`N` conjuncts exposed).
#print axioms DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.lowreg_proj_tendsto
#print axioms
  DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.lowreg_projMode_tendsto

-- Brick A: the low-regularity static seed mass `‖𝒩(0)‖`, the `a = 1` analogue
-- of `deTurckGalerkinForcing_seed_mass` (whose supercriticality gate blocks
-- reuse at the low base).  Its finite-mass step is the PRE-EXISTING finite-set
-- Bessel truncation `cc_partial_le_norm`, censused here as the reused producer.
#print axioms DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.lowRegSeedMass
#print axioms
  DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.cc_partial_le_norm

-- Brick B: the forcing-realization layer along the order-one Galerkin
-- trajectory.  Named smooth representative of the retracted Galerkin state,
-- its smooth-core membership, the two fibre certificates, the evaluation of
-- the dense nonlinearity on it, the seed-subtracted arm identity, the hoisted
-- `C2` fibre cap, and the per-mode forcing-coordinate reading.
#print axioms DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.galCoreRep
#print axioms DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.galCoreRep_eq
#print axioms DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.galRepHs_le
#print axioms
  DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.galCoreRep_ball
#print axioms DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.galState_core
#print axioms DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.galRepFib
#print axioms
  DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.lowregFibZero
#print axioms DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.galN_eval
#print axioms DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.galArmId
#print axioms DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.galArmCap
#print axioms DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.galForceArm

-- Brick C, part 1c: jet control of the trajectory representative.
-- `symmS_jet_le` is the public form of the symmetrization jet contraction;
-- `galRepJet_le` is the RETRACTION-SHRINK route (the retraction scalar lies in
-- `[0,1]`, so every jet of the representative is bounded by the spectral
-- energy of the RAW coefficient family — no ball or first-exit hypothesis);
-- `galRepJet_rad` is the same jet read off the state ball instead, the form
-- the `i = q` Leibniz slots consume.
#print axioms DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.symmS_jet_le
#print axioms DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.galRepJet_le
#print axioms
  DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.galRepJet_rad

-- Brick C, parts 3 and 2: the rung-3 closure and its endpoint.
-- `galArmVec` names the seed-subtracted forcing arm of a retracted Galerkin
-- state; `galArmMass` is the ladder input, with the `E₄` coefficient
-- decomposed EXACTLY into the whitelist `Ctop·Cδ + K_R·R + K_R^{a₁}·R`;
-- `lowregRung3` is the endpoint — the `N`-uniform `H³` energy bound, granted
-- one explicit absorption inequality on those constants plus `ε`, and the
-- registered honest input `Pr` (the primitive form of `∫₀^T E₃ ≤ B`).
#print axioms DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.galArmVec
#print axioms DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.galArmMass
#print axioms DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.lowregRung3

-- F2 FATOU-IDENT: the rung ridden on the PROJECTED sequence's mode
-- coordinates.  `lowregProjMode` is the trajectory; the next three are the
-- rung's `hUinit`/`hUcont` and the spatial identification that turns the
-- package's a.e. state ball into `galTameForce_eq`'s `hc`; `lowregForceMode`
-- is the a.e. per-mode forcing identity; `lowregForceCont`/`lowregModeDeriv`
-- are the continuity gate and the per-mode ODE (`hUderiv`); `lowregFatouE3`
-- is the endpoint -- Fatou's `hbound`, conditional on the rung's absorption
-- gate and on the registered honest input `hL2H3`.
#print axioms
  DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.lowregProjMode
#print axioms
  DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.lowregProjMode_zero
#print axioms
  DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.lowregProjMode_cont
#print axioms
  DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.lowregFieldCombo
#print axioms
  DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.lowregForceMode
#print axioms
  DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.lowregForceCont
#print axioms
  DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.lowregModeDeriv
#print axioms DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.lowregFatouE3

-- F3 FATOU-L2H3: the honest input `hL2H3` DISCHARGED.  `lowregL2H3` is the
-- time-integrated `H³` energy bound: the a.e. spatial identification turns the
-- Galerkin energy into `‖field‖²_{H³}`, whose time integral is the squared
-- time-`L²` norm of the field, which zero-seed maximal regularity bounds by
-- `((1+T)‖fseq N‖)²`.  It is fed at the package's own forcing ball `R/4`.
#print axioms DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.lowregL2H3
-- and the F1-to-F3 wiring: the endpoint fed straight from the identification
-- package, i.e. Fatou's `hconv` and `hbound` from one call, now with NO
-- `hL2H3` antecedent -- the single destructure of `lowreg_projMode_tendsto`
-- inside the pack supplies conjunct 6 and the Nemytskii conjunct at coherent
-- witnesses, so `lowregL2H3` discharges the bound in place.
#print axioms
  DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.lowregFatouPack

-- F4 FATOU-ASSEMBLE: the original `σ ≤ 3` compatibility deliverable.  The
-- all-real closure is separately censused below through the coherent higher
-- path and the generic `lowregMassOfEnergy` adapter.
#print axioms
  DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.lowregMassLow

-- GAP-ORDER: the cap modulus and the two radius coefficients are fixed before
-- the fibre/radius parameters, first at the arm estimate and then at rung 3.
-- The old declarations remain compatibility wrappers over these interfaces.
#print axioms
  DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.galArmMassOrd
#print axioms
  DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.lowregRung3Ord

-- Explicit-package redesign: exact solve witnesses, stored ordered constants,
-- calibrated absorption, and the exact projection/Fatou/mass consumers.
#print axioms
  DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.isLowSolveAt_of_sol
#print axioms
  DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.IsLowSolveAt.toIsLowSolve
#print axioms
  DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.lowreg_solve_two_at
#print axioms
  DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.lowreg_solve_open
#print axioms
  DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.lowregRung3Pack
#print axioms
  DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.lowreg_absorb
#print axioms
  DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.lowreg_solve_adapt
#print axioms
  DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.lowreg_adapt_open
#print axioms
  DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.lowreg_proj_at
#print axioms
  DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.lowreg_projMode_at
#print axioms
  DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.lowregFatouE3At
#print axioms
  DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.lowregFatouPackAt
#print axioms
  DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.lowregMassLowAt
#print axioms
  DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.lowregMassOfEnergy
#print axioms
  DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.opJetAdd
#print axioms
  DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.opJetSmul

-- Ordered higher-rung packages.  Rungs four and five consume the already-
-- established common pointwise lower-rung caps; the all-order package records
-- the independent top coefficient of `nDiffHmQ`.
#print axioms
  DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.galArmMass4Ord
#print axioms
  DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.lowregRung4Ord
#print axioms
  DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.IsRung4Ord
#print axioms
  DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.lowregRung4Pack
#print axioms
  DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.galArmMass5Ord
#print axioms
  DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.lowregRung5Ord
#print axioms
  DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.IsRung5Ord
#print axioms
  DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.lowregRung5Pack
#print axioms
  DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.IsHmRungOrd
#print axioms
  DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.lowregHmPack
#print axioms
  DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.rungGate_le
#print axioms
  DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.IsLowGateOrd
#print axioms
  DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.lowregGatePack

-- Coherent same-trajectory packages and the direct generic higher-rung closure.
#print axioms
  DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.IsRung5Path
#print axioms
  DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.lowregRung5PathAt
#print axioms
  DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.galArmMassHm
#print axioms
  DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.lowregHighRungs
#print axioms
  DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.IsAllRungPath
#print axioms
  DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.lowregAllRungsAt
#print axioms
  DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.lowregAllMassAt

-- Former frontier control: the all-real low-mass theorem must now be free of
-- `sorryAx`; only the ambient classical quotient axioms are expected.
#print axioms
  DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.lowreg_loMass
#print axioms
  DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.lowreg_spatialMass
#print axioms
  DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.lowreg_forceJetMass
#print axioms
  DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.lowreg_allOrderJet
#print axioms
  DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.lowreg_joint_two
#print axioms
  DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.lowreg_joint_open
#print axioms
  DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.LowRegGateData
#print axioms
  DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.IsLowGateUnif
#print axioms
  DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.deTurck_rem_repr
#print axioms
  DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.lowreg_dt_open

-- Background-aware common-time packages.  The final theorem is conditional on
-- the honest exists-before-metric coefficient package, not on an all-rung gate.
#print axioms
  DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.LowRegBoundData
#print axioms
  DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.LowRegHorizonData
#print axioms
  DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.LowRegBoundData.toHorizon
#print axioms
  DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.IsLowBoundCap
#print axioms
  DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.boundCap_refl
#print axioms
  DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.horizon_le_of_cap
#print axioms
  DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.IsLowBoundsAt
#print axioms
  DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.IsLowSolveBg
#print axioms
  DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.lowreg_sol_of_data
#print axioms
  DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.IsLowBoundsUnif
#print axioms
  DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.unif_solve_of_bounds
#print axioms
  DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.IsLowBoundsCap
#print axioms
  DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.IsLowBoundsUnif.toCaps
#print axioms
  DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.unif_solve_of_caps
