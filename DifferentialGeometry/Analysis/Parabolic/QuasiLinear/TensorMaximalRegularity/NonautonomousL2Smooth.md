# NonautonomousL2Smooth

## Stop result

No `NonautonomousL2Smooth.lean` theorem was added.  A provisional adapter that
merely repeated the existing producer's `hForce` hypothesis was removed:
although such a wrapper would typecheck, it would not connect the
`nonautL2_realize` packet to the nonlinear Ricci--DeTurck equation.

The fixed-horizon producer
`maxreg_solution_jointly_smooth_representative_of_tame_nemytskii` would indeed
return the strongest desired package once its inputs are available:

- a canonical smooth compactly supported tensor representative on the same
  closed slab;
- its zero initial value and every-time `L²` pin to the maximal-regularity
  carrier;
- the pointwise intrinsic nonlinear evolution equation on `[0,T)`; and
- `JointChartGramSmooth` for the same realized metric family.

Its last two conclusions assemble directly into
`IsQuasilinearMetricParabolicSolution`, so neither that predicate nor
`JointChartGramSmooth` needs to be assumed.  The obstruction occurs before
that assembly.

## Concrete frontier

The generic `nonautL2_realize` packet alone does not imply the producer's
`hForce` input.  Its `A2`, `A1`, and `f0` are arbitrary, so its fixed-point and
clean heat equations cannot identify `fHi` with the Ricci--DeTurck
Nemytskii forcing.  The exact missing concrete equality is

`fHi =ᵐ[timeMeasure T] (fun t =>
  deTurckSobolevNHa2Symm g₀ g_bg a (u.hiL2 t))`.

Once this identity is available, the producer ultimately needs the equivalent
coordinate statement for every smooth representative `F` pinned to `u.lo`,
every `t ∈ [0,T)`, and every eigenmode `i`:

`f i t = tensorL2Coeff (toL2 (Nsec (F t) ...)) i`.

No existing public theorem derives the first equality from the clean Sobolev
equation `timeDeriv u.lo = timeScaleLaplacian u.hiL2 + fHi`.
`lowReg_force_smooth` transports an already-assumed low-order forcing identity,
while `deTurckForcing_smoothTimeCoordinateFamilySymm` and
`deTurckRicci_forcingBootstrap_symm` both assume the displayed high-order
identity and return subhorizon data.  The proof upgrading it to the
coordinate-level producer input,
`realizedForcingCoord_eq_smoothNSymm`, is currently private in
`MaxRegSolutionJointlySmooth.lean`.

The section representation input `hRepr` is a smaller API-extraction issue:
its proof exists locally in `DeTurckInitialDataExistence.lean`, but uses the
private helper `rawTensorConnLapSmooth_symmS`.

The next genuine producer must connect the concrete non-autonomous
`A2`/`A1`/`f0` fixed-point assembly to the displayed Nemytskii equality on
`timeMeasure T`.  This is a concrete nonlinear identity/API frontier, not a
joint-smoothness or metric-solution assumption.

## Verification

There is no Lean source change to verify because the honest stop condition was
reached before a theorem could be stated from the available inputs.  No build
was run.

## Project position

- `nonautL2_smooth`: not stated or proved, 0%; the direct final metric-package
  adapter is routine once the concrete nonlinear input is produced.
- Concrete same-horizon smooth Ricci--DeTurck realization from the low-base
  packet: not yet stated or proved, 0%; its reusable spectral realization
  machinery is substantial, but the concrete nonlinear forcing identity above
  remains independent.
- `ricci_flow_unif_existence`: unstated/unproved, 0%.
- HCG compactness is a separate project lane and is not advanced here.
