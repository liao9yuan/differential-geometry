# Independent audit of the `lowreg_loMass` endgame

- Date: 2026-08-04
- Checkout: `E:\testdifferential-geometry-ste-align`
- Branch: `codex/short-time-existence-align`

This audit treats the current three-brick ledger as an untrusted proposal.  The
headline result is **STOP-AND-REDESIGN for that brick sequence**, while retaining
the projected fixed-point/Fatou strategy.  The theorem `lowreg_loMass` remains
0%; its dedicated, route-correct machinery is approximately 30%.  The larger
front-2 low-regularity closure is approximately 60%, and the whole HCG
compactness project remains in the low single digits (approximately 3%).

## §1. Census verification

### 1.1 Campaign `sorry` census: PASS, with scope qualification

The front-2 source files contain exactly one live proof-body `sorry`:
`lowreg_loMass` is stated at
`ShortTime/LowRegAllOrderJet.lean:1052-1063` and its proof is the `sorry` at
`:1064`.  The black-box endpoint `(N)` is separately stated at
`Evolution/ExtendViaUniqueness.lean:80-97` and has its `sorry` at `:98`.

This is a campaign-scoped statement, not a repository-wide no-`sorry` claim.
For example, `ShortTime/WeylEigenvalueCountingBound.lean:115`,
`Evolution/CinftyLimitGlue.lean:295`, and
`Evolution/BernsteinComplete.lean:2937` still contain unrelated `sorry`s.  The
first is consumed only by `ShortTime/RealizeTransport.lean:90,118`; none of
these three lies in the audited front-2 import closure.

Fresh isolated `#print axioms` probes, after a focused refresh of their source
modules, gave:

| Declaration | Axioms printed | Audit |
|---|---|---|
| `lowreg_spatialMass` (`LowRegAllOrderJet.lean:1117-1181`) | `propext`, `sorryAx`, `Classical.choice`, `Quot.sound` | expected dependency on `lowreg_loMass` via `:1180` |
| `lowreg_forceJetMass` (`LowRegAllOrderJet.lean:1217-1321`) | same, including `sorryAx` | expected through `lowreg_spatialMass` at `:1317-1318` |
| `lowreg_allOrderJet` (`LowRegAllOrderJet.lean:1445-1570`) | same, including `sorryAx` | expected through `lowreg_forceJetMass` at `:1570` |
| `lowreg_joint_two` (`LowRegAllOrderJet.lean:1823-1871`) | same, including `sorryAx` | expected through `lowreg_joint_of_re` at `:1871` |
| `lowreg_joint_smooth` (`LowRegAllOrderJet.lean:1639-1745`) | `propext`, `Classical.choice`, `Quot.sound` | clean |
| `c1_jet_tower` (`DeTurck/LowRegC01JetTower.lean:472-492`) | `propext`, `Classical.choice`, `Quot.sound` | clean |
| `c0_jet_tower` (`DeTurck/LowRegC01JetTower.lean:547-568`) | same, no `sorryAx` | clean |
| `a1_ladder` (`DeTurck/LowRegLadderRung.lean:425-447`) | same, no `sorryAx` | clean |
| `a2_ladder` (`DeTurck/LowRegLadderRung.lean:243-268`) | same, no `sorryAx` | clean |
| `n_diff_hm_rung` (`DeTurck/LowRegLadderRung.lean:565-608`) | same, no `sorryAx` | clean |

The probe scratch file was removed and its own claim released.  No campaign
source was changed for this check.

### 1.2 F6 estimate chain: PASS, but not an `a = 1` closure

Both advertised towers are unconditional in the relevant sense: their
declarations are proved without `sorryAx`.  `c1_jet_tower` consumes
`low1Ker_jet` in its proof at
`DeTurck/LowRegC01JetTower.lean:472-519`; `c0_jet_tower` consumes
`selfLow_jet` at `:547-570`.  The ladder assembly is likewise proved:
`a2_ladder` at `DeTurck/LowRegLadderRung.lean:243-268`, `a1_ladder` at
`:425-451`, and `n_diff_hm_rung` at `:565-608`.

The qualification is load-bearing.  `a1_ladder` requires `2 ≤ a` at
`LowRegLadderRung.lean:428`, while `a2_ladder` and `n_diff_hm_rung` require
`3 ≤ a` at `:246` and `:568`.  These declarations therefore do not supply the
advertised bottom closure for the actual `a = 1` trajectory.

### 1.3 Floor deletion: PASS

A targeted search over all `.lean` files returned no occurrence of
`lowregFloorHorizon`.  The actual producer horizon is precisely the minimum of
`lowregHorizon` and `lowregLiftHorizon'` at
`ShortTime/LowRegApplyTwo.lean:721-723`; there is no third floor in that
formula.

### 1.4 Order-two `staticForce` claim: FAIL literally, PASS semantically for horizons

There are six direct order-two source occurrences, not two:

- `ShortTime/LowRegLiftNTerm.lean:170,230,260`;
- `ShortTime/LowRegForceHi.lean:144,215,284`.

The occurrence at `LowRegLiftNTerm.lean:260` is the consumerless norm-bound
vestige.  The object-level facts are still active infrastructure:
`baseForceH2_eq_static` at `:170` is consumed at `:183`, and `liftForceHi` at
`:228-230` is consumed by `ShortTime/LowRegApplyTwo.lean:157,392`.  The
`LowRegForceHi.lean:144,215,284` occurrences form the active frozen-force split.
The safe corrected claim is only that order-two `staticForce` no longer occurs
in a horizon or radius formula; it has not been reduced to two textual
vestiges.

## §2. Backward completeness map

The conclusion of `lowreg_loMass` is the right object.  It bounds

`perModeConv λᵢ (timeModeCoeff fLo i)`

at every time and every real weight (`LowRegAllOrderJet.lean:1057-1063`).  This
is the **state coordinate**, not the raw forcing coordinate.  Its only consumer
uses equality of forcing modes to transport exactly that expression:
`lowreg_spatialMass` proves `hmode` at `:1173-1179`, calls `lowreg_loMass` at
`:1180`, and closes by `simpa` at `:1181`.  Thus the target conclusion is
sufficient and should not be widened again.

Walking backward from that conclusion exposes the following joints.  “Missing”
below means no public declaration with the required producer/consumer shape was
found after checking siblings and actual call sites.

### J0. Energy-honest low-solve contract: missing

- **Producer currently available.** `lowreg_solve_two` has `hDim`,
  `0 ≤ δ`, `δ ≤ 1/3`, and `δ < 1` at
  `ShortTime/LowRegApplyTwo.lean:615-641`; it instantiates the self-background
  `g,g` at `:710-712`, produces `hcoreN` at `:720`, and packages the solve via
  `isLowSolve_of_sol` at `:788-790`.
- **Consumer requirement.** The smooth identification
  `lowRegN_on_smooth` requires
  `Continuous (coreN g₀ g_bg hδ hreal)` at
  `ShortTime/LowRegSmoothBridge.lean:84-103`.  The landed ladders require
  dimension three, self-background, `0 ≤ δ`, and `δ ≤ 1/3`
  (`DeTurck/LowRegLadderRung.lean:243-268,425-447,565-592`).  Their top
  coefficient has the form `κ * δ / (1 - δ)^2`, so an actual absorption
  certificate is also required.
- **Mismatch.** `IsLowSolve` existentially hides an arbitrary `g_bg` and stores
  only `δ < 1` plus the fixed-point data
  (`ShortTime/UnifClassBounds.lean:407-451`).  It drops all the stronger data
  above.  Moreover, the actual solve hardcodes the dimension-only
  `deTurckArmContractionThreshold''` before `κ` is known
  (`LowRegApplyTwo.lean:636-645`), whereas the paper requires choosing `δ*`
  after `κ` (`ShortTime/PSTOP_PROPOSITION.md:76-82`).
- **Required joint.** The actual solve producer must choose its realization
  threshold after a canonical `κ`, and the one canonical `IsLowSolve` package
  must retain self-background, the full delta range, the smooth-core bridge,
  and the resulting absorption certificate.  Merely adding these as new
  consumer assumptions would be another false wrapper frontier.

### J1. Same-witness projected solution packet: missing

- **Producer currently available.** `proj_partial_sol_tame` returns, for every
  `N` on the same horizon, a maximal-regularity state, projected forcing,
  state-ball fact, fixed equation, zero trace, PDE, and forcing-ball fact
  (`HeatSemigroup/EigenProjTameSol.lean:118-162`).
- **Consumer requirement.** The energy identity and Fatou bound must use the
  state and forcing belonging to the very same `fseq N`.
- **Mismatch.** `lowreg_proj_tendsto` calls that exact producer at
  `ShortTime/LowRegGalerkinIdent.lean:135-142`, then explicitly discards
  `_u`, `_hstate`, `_htr`, and `_hpde`; its public result retains only
  projector fixedness and convergence (`:69-76,141-153`).
- **Required joint.** A strengthened result must return the full projected
  packet together with `Tendsto fseq (𝓝 fLo)`.  It should reuse the existing
  witness, not construct an independent trajectory and later try to identify
  the two.

### J2. Finite-mode state and time-energy adapter: missing

- **Producer currently available.** Projector fixedness of the forcing is
  supplied by `projForce_fixed` and `projField_fixed`
  (`HeatSemigroup/EigenProjPartialSol.lean:538-578`); the time-`H¹` layer has a
  continuous state representative and an a.e. derivative, and upgrades to an
  everywhere derivative when the derivative has a continuous representative
  (`TimeSobolev/TimeH1.lean:290-303,340-395`).
- **Consumer requirement.** `galerkin_energy_l1_bound` asks for coordinate
  continuity and `HasDerivWithinAt` at every time
  (`HeatSemigroup/GalerkinParabolicEnergy.lean:504-509`).  The final mass is in
  the Duhamel coordinate used by `lowreg_projMode_tendsto`
  (`ShortTime/LowRegGalerkinIdent.lean:165-187`).
- **Mismatch.** The projected solve supplies the PDE and fixed equation only
  a.e. (`EigenProjTameSol.lean:149-156`).  No public theorem packages the
  finite-mode state, an absolutely-continuous/everywhere-classical energy
  identity, and its equality with the relevant `perModeConv` coordinates.
- **Required joint.** Either prove an a.e./absolutely-continuous energy engine,
  or prove a continuous finite-mode representative and the all-time coordinate
  ODE for the retained projected solve.  The latter can reuse the existing
  pointwise-coordinate bridge rather than create a new Galerkin solution.

### J3. Quantitative `C0` coefficient bound at `a = 1`: missing and decisive

- **Producer currently available.** `selfLow_jet` and `c0_jet_tower` are proved
  at `a = 1`, but they take a fixed pointwise `H^{a+2}` radius `R₀` and return
  an opaque constant selected after `R₀`
  (`DeTurck/LowRegC01JetTower.lean:305-325,542-568`).
- **Consumer requirement.** Projected maximal regularity gives only an
  `N`-uniform `L²_t H³` bound, not a pointwise `H³` ball
  (`LocallyLipschitzExistence.lean:361-372`, together with the uniform
  projected forcing ball at `EigenProjTameSol.lean:142-157`).  The bottom energy
  closure therefore needs a coefficient of the explicit form
  `C_k + Q_k * ‖U_N(t)‖²_{H³}`, whose time integral is uniformly bounded.
  This is exactly the paper's intended replacement at
  `ShortTime/PSTOP_PROPOSITION.md:220-240`.
- **Mismatch.** Nothing in the current statement of `selfLow_jet` exposes that
  the hidden `R₀` dependence is at most quadratic.  Substituting a pointwise
  radius into an opaque `K(R₀)` is not an `L¹_t` estimate.
- **Required joint.** A ball-free quantitative sibling of `selfLow_jet` (and
  its `C0` tower consequence) with constants fixed before `T,N` and at most
  quadratic dependence on the actual `H³` norm.  This is the fourth instance
  of a named step silently assuming a missing interface.

### J4. Tower-direct bottom-rung closure: missing

- **Producer currently available.** The `C2`, `C1`, and `C0` towers expose
  `range (i+2)` state-jet budgets; the algebraic pairing lemma
  `two_mul_sum_ladder_le` has the desired top/mid/static conclusion once
  `α,β,D` are supplied
  (`Sobolev/Tensor/CrossScaleCauchySchwarz.lean:232-247`).
- **Consumer requirement.** Rungs 3--5 must close with an absorbable,
  `N`-independent top coefficient and an `L¹_t` coefficient depending at most
  quadratically on `‖U_N(t)‖_{H³}`
  (`ShortTime/PSTOP_PROPOSITION.md:227-249`).
- **Mismatch.** No such tower-direct pairing theorem exists.  The landed
  `a1_ladder`/`a2_ladder` cannot be instantiated at `a = 1`, and the latter
  consumes an `H⁵` ball at the bottom (`LowRegLadderRung.lean:243-268,425-447`).
- **Required joint.** Prove the lowest bottom closure first, then rungs 4 and 5,
  with no `H⁵` radius, no inverse estimate, no largest-eigenvalue dependence,
  and no same-rung radius in its own Grönwall coefficient.

### J5. `N`-indexed `L¹` energy engine: missing statement variant

- **Producer currently available.** The generic engine is
  `galerkin_energy_l1_bound`
  (`HeatSemigroup/GalerkinParabolicEnergy.lean:494-521`).
- **Consumer requirement.** The natural coefficient is
  `A_N(t) ≍ C‖U_N(t)‖²_{H³}` with a separate primitive `S_N`, while the bound
  on every `S_N` is common.
- **Mismatch.** The declaration quantifies a single shared
  `{A S : ℝ → ℝ}` at `:498`; all `N` use that same `A t` in the closure at
  `:510-517`.  Uniform bounds on `∫ A_N` do not imply integrability of
  `sup_N A_N`; moving disjoint spikes give the elementary counterexample.
- **Required joint.** An indexed sibling with
  `A S : ℕ → ℝ → ℝ`, `S` hypotheses indexed by `N`, a common `Sbd`, and
  closure coefficient `A N t`.  Its proof should specialize the existing
  one-family engine separately for each `N`.

### J6. High-rung calibration and static seed: partly missing

- **Producer currently available.** `two_mul_sum_ladder_le` converts a split
  and ladder bound into coefficients `2α+ε`, `β²/ε`, and static seed
  `2D√E` (`CrossScaleCauchySchwarz.lean:232-247`).  `staticForce g g σ` is
  defined at arbitrary real order, not only order two
  (`ShortTime/LowRegLiftNTerm.lean:138-155`).
- **Consumer requirement.** After rungs 3--5 give a fixed `H⁵` radius, high
  rungs need explicit `α = κδ/(1-δ)^2`, lower coefficient `β`, per-datum
  `D_k`, projector contraction, and an absorption proof `2α+ε < 2`.
- **Mismatch.** The separate facts exist, but no theorem calibrates them for
  the actual `a = 1` projected family.  The current fixed-point delta was not
  chosen from `κ` (J0).
- **Required joint.** One canonical calibration theorem after J0 and J4,
  followed by the static-mode seed adapter.  This is ordinary assembly only
  after those producer gaps are closed.

### J7. Real weights and Fatou assembly: adapters exist; final glue missing

`lowreg_projMode_tendsto` already supplies the convergence hypothesis in the
correct state coordinates (`ShortTime/LowRegGalerkinIdent.lean:165-187`), and
`fatou_sq_mass` has the required finite-partial-sum conclusion
(`Intrinsic/GalerkinCompactness.lean:28-34`).  The established high-order
template converts an integer hierarchy to arbitrary real `σ` by choosing a
larger natural weight and applying weight monotonicity
(`HeatSemigroup/GalerkinLimitUniformMass.lean:1167-1210`).  Once J1--J6 produce
the uniform projected bound, the remaining real-weight/Fatou step is a small
adapter, not another mathematical frontier.

## §3. Necessity verdict

**Finite-dimensional projected approximants are unavoidable with the current
public APIs; a separately constructed classical Galerkin ODE is avoidable and
should be deleted.**

No Galerkin-free semigroup escape was found.  The direct interior-smoothing
route requires the very all-order coupling it is supposed to prove:
`solField_into_all_tensorHs_interior` assumes the coupling family at
`ParabolicInteriorSmoothing.lean:326-339`, and
`spectralMass_sup_le_of_timeL2_allHs` assumes the same input at
`SpectralMassUniformSup.lean:173-185`.  The Duhamel all-order theorem similarly
assumes all-order forcing mass (`DuhamelSmoothing.lean:367-383`).  Applying any
of these directly to the `a = 1` fixed point is circular.

The independent-ODE necessity claim is nevertheless false.  The designated
paper says that the projected fixed-point trajectory already is the needed
approximation and that the ODE brick must be deleted
(`ShortTime/PSTOP_PROPOSITION.md:321-325`); it identifies preservation of the
projected state and its energy identity as the actual adapter at `:327-337`.
The code now has the tame version of that producer:
`proj_partial_sol_tame` already returns the full projected packet
(`HeatSemigroup/EigenProjTameSol.lean:118-162`).

The in-flight, untracked `HeatSemigroup/GalerkinTameSol.lean` was inspected only
as a snapshot and is excluded from the landed count.  Its current endpoint
constructs a retracted-force ODE (`:571-613`) but does not connect it to
`IsLowSolve`, the time-`L²` projected forcing used by Fatou, the Duhamel
`perModeConv` state, or the projected fixed-point witness.  It would therefore
create an additional identification obligation.  The route-correct design is
to retain the state/PDE data currently discarded by `lowreg_proj_tendsto` and
add a finite-mode absolutely-continuous or classical energy adapter for that
same witness.

## §4. Statement audit

### 4.1 `lowreg_loMass`: third widening is required

The conclusion is both correctly stated and sufficient, as shown by its exact
consumer at `LowRegAllOrderJet.lean:1173-1181`.  The hypotheses are not enough
for the intended proof.  In particular, every landed low-base tower/ladder route
uses dimension three (`LowRegC01JetTower.lean:305-325,472-492,547-568`), while
the current theorem has no dimension binder (`LowRegAllOrderJet.lean:1052-1064`).

The corrected direct binder list should be exactly the current list plus one
leading dimension certificate:

```lean
theorem lowreg_loMass
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M)
    {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1)
    (fLo : timeL2 (tensorHs (I := I) (M := M) g 0 2 ((1 : ℕ) : ℝ)) T)
    (hlo : IsLowSolve (I := I) (M := M) g hT hT1 fLo)
    (σ : ℝ) :
    ∃ Cσ : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) T,
      Summable (fun i => tensorSobolevWeight (I := I) (M := M) i σ *
          (perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i)
            (fun u => (timeModeCoeff (I := I) (M := M) fLo i) u) t) ^ 2) ∧
        ∑' i, tensorSobolevWeight (I := I) (M := M) i σ *
            (perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i)
              (fun u => (timeModeCoeff (I := I) (M := M) fLo i) u) t) ^ 2 ≤ Cσ
```

`lowreg_spatialMass` must receive and pass this `hDim`; its caller
`lowreg_forceJetMass` already has the binder at
`LowRegAllOrderJet.lean:1217-1220` and calls the spatial theorem at
`:1315-1318`, so this propagation is local.

The canonical `IsLowSolve` package itself must also be strengthened rather than
creating a parallel “energy solve” predicate.  Its existential witness must
retain, in addition to its current fixed-point fields:

1. `g_bg = g₀` (or remove the existential background and use `g₀` directly);
2. `hδ0 : 0 ≤ δ` and `hδ_le : δ ≤ 1 / 3`;
3. `hcore : Continuous (coreN (I := I) (M := M) g₀ g_bg hδ hreal)`;
4. a producer-backed absorption certificate for the canonical top constant,
   chosen before the solve, not a consumer-supplied assumption.

The exact type of item 4 cannot honestly be frozen until J3/J4 expose the
canonical bottom/high-rung coefficient.  That is a design dependency, not a
license to add `habs` as an opaque new assumption.

### 4.2 `IsLowSolve` versus the actual fixed-point engine

For its narrow role, the package is accurate.  The actual engine is
`partial_sol_tame`, not `partial_sol_const`; its input/output slots are at
`TameForcingFixedPoint.lean:332-371`.  The actual campaign instantiation
`lowreg_partial_sol_of_bounds` reconstructs its three coefficients, smallness
conditions, zero bound, state ball, fixed equation, trace, PDE, and force ball
at `ShortTime/UnifClassBounds.lean:263-375`.  The package records enough of
those facts for projected existence and contraction, as demonstrated by the
exact call to `proj_partial_sol_tame` and `projFixTame_le_two` in
`ShortTime/LowRegGalerkinIdent.lean:78-150`.

The failure is semantic scope: `IsLowSolve` is an honest **fixed-point and
projection** package, but not yet an honest **smooth energy** package.  Its
docstring claim that it is enough for every order-one Galerkin estimate
(`UnifClassBounds.lean:453-457`) is therefore stronger than its fields.

## §5. Corrected brick plan and honest price

The ledger's “three bricks plus calibration, about four sessions” is rejected.
The corrected central estimate is **14 sessions**, with a plausible range of
**12--16 sessions**, already adjusted for this lane's historical approximately
twofold optimism.

| Phase | Deliverable | Sessions |
|---|---|---:|
| viability gate | quantitative `C0` `H³²` coefficient plus the first tower-direct bottom closure; no hidden pointwise radius | 4--5 |
| honest producer | choose `δ*` after canonical `κ`; retain dimension/self-background/delta/core/absorption in the canonical package | 2--3 |
| projected energy packet | preserve the projected fixed-point witness and prove its finite-mode AC/classical coordinate energy identity | 2--3 |
| generic engine correction | add the `N`-indexed `L¹` energy sibling | 1 |
| hierarchy calibration | finish rungs 4--5, high-rung ladder calibration, static seed, and primitive wiring | 2--3 |
| endpoint assembly | arbitrary real `σ`, Fatou, `lowreg_loMass`, focused verification | 1 |

The order is intentional: the quantitative `C0` dependence is the mathematical
viability gate.  Polishing `IsLowSolve` before knowing whether the coefficient
is quadratic would risk enshrining another unusable interface.

Honest nested progress estimates, with theorem completion separated from
infrastructure:

- next quantitative `C0` theorem: **0%**; its existing capped-window/tower
  infrastructure: approximately **70%**;
- `lowreg_loMass`: theorem **0%**; dedicated route-correct machinery:
  approximately **30%** (the in-flight ODE file is excluded);
- front-2 low-regularity closure: approximately **60%**;
- `(N) ricci_flow_unif_existence`: theorem **0%**, regardless of the machinery
  count (`Evolution/ExtendViaUniqueness.lean:80-98`);
- whole HCG compactness project: approximately **3%**.

These are engineering estimates, not theorem-closure claims.  In particular,
the clean F6 declarations do not raise `lowreg_loMass` above 0%.

## §6. Discrepancies in landed or advertised pieces

| Piece | Statement audit | Result |
|---|---|---|
| `tameMap_dist_le` | It is a contraction estimate on two forcing-ball fixed-point candidates, with state-ball hypotheses (`TameForcingFixedPoint.lean:828-864`).  This is exactly what the projected identification consumes, but it is not a global ODE Lipschitz theorem. | **PASS for contraction; FAIL if advertised as ODE input** |
| `projFixTame_le_two` | It assumes both ball bounds and both actual fixed equations and yields the factor-two distance estimate (`EigenProjTameSol.lean:384-417`); `lowreg_proj_tendsto` instantiates those exact slots at `LowRegGalerkinIdent.lean:149-150`. | **PASS** |
| `galerkin_energy_l1_bound` | It uses one common `A,S` for all `N` and every-time derivatives (`GalerkinParabolicEnergy.lean:494-521`), while the projected route naturally supplies `A_N,S_N` and initially only a.e. time equations. | **FAIL as the claimed ready engine** |
| hoisted ladders | They are proved, but gates `2 ≤ a` and `3 ≤ a` exclude the `a = 1` bottom closure (`LowRegLadderRung.lean:243-268,425-447,565-592`). | **FAIL as advertised at base one** |
| `c0_jet_tower` | It is proved, but its constant is chosen after a pointwise `H³` radius (`LowRegC01JetTower.lean:542-568`); no quadratic dependence is exposed. | **weaker than the `L²_t H³` pipeline needs** |
| `lowreg_proj_tendsto` | It proves the correct force convergence, but discards the state/PDE packet at `LowRegGalerkinIdent.lean:141-150`. | **landed identification, missing energy witness** |
| floor deletion | No `.lean` occurrence of `lowregFloorHorizon`; the live formula is `LowRegApplyTwo.lean:721-723`. | **PASS** |
| order-two `staticForce` count | Six direct source occurrences remain (`LowRegLiftNTerm.lean:170,230,260`; `LowRegForceHi.lean:144,215,284`). | **FAIL literally; no horizon regression** |

This reverse spot-check reproduces both historical failure modes: one claimed
ready engine is quantified too strongly for the actual family, and several
clean sibling declarations do not instantiate at the actual base order.

## §7. Verdict

**STOP-AND-REDESIGN.** Stop the current “independent Galerkin ODE + coordinate identification + ladder closure” three-brick lane: the designated paper itself deletes the ODE brick (`PSTOP_PROPOSITION.md:321-325`), the actual projected fixed-point producer already supplies the right approximants (`EigenProjTameSol.lean:118-162`), and the claimed base-one closure lacks both a quantitative `C0`/tower-direct producer and an `N`-indexed energy engine.  Preserve the landed projected convergence, towers, high-rung ladders, pairing algebra, and Fatou adapters; redesign around the same-witness projected packet, prove the quantitative bottom closure first, then freeze the honest solve contract and proceed only if that viability gate is green.

## Next concrete brick handoff

### Brick title

**Expose the quadratic `H³` dependence of the self-background `C0` jet bound.**

This is a single mathematical viability brick.  Do not continue the in-flight
independent ODE implementation.  Before starting, wait for the owner of the
current brick-(1) claims on
`HeatSemigroup/GalerkinTameSol.lean` and
`ShortTime/LowRegGalerkinSol.lean` to settle them.  A dead PID alone is not
permission to force-release another lane's claim.

### Ultimate consumer signature, verbatim

From `ShortTime/LowRegAllOrderJet.lean:1052-1063`:

```lean
theorem lowreg_loMass (g : SmoothRiemannianMetric I M)
    {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1)
    (fLo : timeL2 (tensorHs (I := I) (M := M) g 0 2 ((1 : ℕ) : ℝ)) T)
    (hlo : IsLowSolve (I := I) (M := M) g hT hT1 fLo)
    (σ : ℝ) :
    ∃ Cσ : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) T,
      Summable (fun i => tensorSobolevWeight (I := I) (M := M) i σ *
          (perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i)
            (fun u => (timeModeCoeff (I := I) (M := M) fLo i) u) t) ^ 2) ∧
        ∑' i, tensorSobolevWeight (I := I) (M := M) i σ *
            (perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i)
              (fun u => (timeModeCoeff (I := I) (M := M) fLo i) u) t) ^ 2 ≤ Cσ := by
```

The direct downstream closure slot, verbatim from
`HeatSemigroup/GalerkinParabolicEnergy.lean:510-517`, is:

```lean
(hclosure : ∀ (N : ℕ) (k : ℕ), ∀ t ∈ Set.Ico (0 : ℝ) T,
  2 * ∑ i ∈ sseq N, tensorSobolevWeight (I := I) (M := M) i (σ₀ + (k : ℝ)) *
      (U N t i * Fseq N t i) ≤
    Cδ * galerkinEnergy (I := I) (M := M) (sseq N) (U N) (σ₀ + (k : ℝ) + 1) t +
      (Cmid k + A t) *
        galerkinEnergy (I := I) (M := M) (sseq N) (U N) (σ₀ + (k : ℝ)) t +
      seed k *
        Real.sqrt (galerkinEnergy (I := I) (M := M) (sseq N) (U N) (σ₀ + (k : ℝ)) t))
```

The later corrected engine will replace `A t` by `A N t`; this brick must
produce the explicit quadratic factor from which that `A N t` is defined.

### Exact deliverable

Add one canonical theorem in
`Analysis/Spectral/Intrinsic/DeTurck/LowRegC01JetTower.lean`, tentatively named
`selfLow_jet_quad` (within the 20-letter rule), and document it in the existing
same-name `LowRegC01JetTower.md` note.

The theorem should keep the existing symmetry, realization, dimension-three,
and `0 ≤ δ ≤ 1/3` inputs of `selfLow_jet`, but remove the fixed radius `R₀` from
the constants.  It must expose a bound of the following mathematical shape,
with nonnegative `K₀ i`, `K₂ i` chosen before `T`:

```text
lowJetSq i (rhsSelfLow g g T ...) ≤
  (K₀ i + K₂ i * ‖T‖²_H³) *
    (1 + Σ_{j < i+2} ‖∇^j T‖²).
```

An algebraically equivalent split into a state-free term and a term linear in
`‖T‖²_H³` is acceptable.  A theorem returning an opaque `K(R₀)`, a pointwise
`H³` ball, a higher power of `‖T‖_H³`, or any `N`/largest-eigenvalue constant is
not an acceptable deliverable.

### Producer inventory

- current capped theorem and its exact budget:
  `DeTurck/LowRegC01JetTower.lean:305-325`;
- six capped arm windows used by its proof:
  `DeTurck/LowRegC01JetTower.lean:301-304,338-342`;
- current `C1` and `C0` tower statements:
  `DeTurck/LowRegC01JetTower.lean:472-492,547-568`;
- high-rung consumers and their gates:
  `DeTurck/LowRegLadderRung.lean:243-268,425-447,565-592`;
- target bottom coefficient shape:
  `ShortTime/PSTOP_PROPOSITION.md:220-240`;
- algebraic pairing consumer:
  `Sobolev/Tensor/CrossScaleCauchySchwarz.lean:232-247`;
- projected maximal-regularity family to which the later theorem will apply:
  `HeatSemigroup/EigenProjTameSol.lean:118-162`.

Search `DifferentialGeometry/` first for a thinner quantitative arm lemma.  Use
`RFreference/` only to inspect proof shape; do not import or edit it.  Prefer
refining the constants in the existing capped-arm proof over adding a parallel
coefficient hierarchy.

### Acceptance criteria

1. Constants are independent of `T`, time, truncation `N`, and any spectral
   cutoff.
2. State dependence is explicit and at most quadratic in the `H³` norm.
3. The jet budget stays `range (i+2)` and the theorem is self-background.
4. No new `sorry`, axiom, assumption-only wrapper, `maxHeartbeats`, foundational
   class, or public name longer than 20 letters.
5. A fresh `#print axioms selfLow_jet_quad` has no `sorryAx`.
6. The focused source check is green and local linter warnings introduced by
   the edit are removed.
7. The same-name note records pass/fail, the exact obstruction if failed, and
   revised nested percentages; it does not contain full commands or logs.

### Verification recipe

1. Re-run lock status and wait for the current brick-(1) owner.  Claim
   `LowRegC01JetTower.lean` before editing; never force-release someone else's
   token merely because its PID is dead.
2. Run one focused check through `scripts/lake-locked.ps1` with the claim token,
   `-NoLakeLock`, `-LeanThreads 1`.  Do not run a root build and do not raise
   heartbeat limits.
3. Run one isolated, claimed scratch probe importing the checked module and
   printing the new theorem's axioms; remove the scratch and release only its
   own claim afterward.
4. Review the scoped diff, run whitespace checking on the two touched files,
   and release the edit claim only after the file is stable.

### Stop condition

Stop and report a **mathematical obstruction** if the actual `C0` arm algebra
forces dependence higher than quadratic in `‖T‖_H³`, a same-rung radius inside
its own Grönwall coefficient, or a cutoff-dependent inverse inequality.  Give
the exact offending arm theorem and goal; do not hide it behind a new
assumption.  If the quadratic theorem is proved, the next brick is the lowest
tower-direct energy pairing, followed only then by the canonical
`IsLowSolve`/`δ*` producer redesign.
