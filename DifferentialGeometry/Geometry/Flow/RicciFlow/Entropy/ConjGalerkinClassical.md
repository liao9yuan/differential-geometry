# `ConjGalerkinClassical` status

## 2026-07-16 compact-interior coefficient jet mass

`galLimExt_coeff` and `galLim_jet_mass` are proved and focused verification is
green.  On one positive interior interval, every limiting rank-zero spectral
coefficient is smooth on compact subintervals and every time jet at every
natural Sobolev order has a single summable majorant uniform over that compact
subinterval.

The proof first uses `galLimExt_smooth` at a sufficiently high spatial order,
commutes the scalar coefficient continuous linear map with the iterated time
derivative, and then applies the rank-generic `mass_le_of_compact`.  The
negative tail is produced from the closed-manifold eigenvalue counting API;
no consumer regularity assumption and no whole-Hom equality is introduced.

Honest dependency accounting: the local theorem body contains no `sorry`, but
`weyl_eigenvalue_counting_bound_of_closed` currently depends on the existing
project `sorry` in `ShortTime/WeylEigenvalueCountingBound.lean`.  Therefore the
full dependency chain is not yet globally sorry-free.

`galLim_jet_mass`: theorem **100%**, dedicated machinery **100%**.  Rank-zero
joint scalar reconstruction and `heatpot_of_gallim` remain separate theorem
frontiers at **0%**.  Classical conjugate-heat dedicated machinery is about
**90%**; whole HCG machinery remains conservatively about **59%**, and every
HCG endpoint theorem remains **0%**.

## 2026-07-16 classical heat-potential closure

The classical reconstruction route is now closed.  `galLim_slice_cc` builds,
for each time slice, one genuine smooth rank-zero representative realizing all
natural spectral Sobolev orders.  `galLim_initial`, `galLim_joint_cont`,
`galLim_joint_top`, and `galLim_slice_pos` provide the initial value, endpoint
continuity, positive-time joint smoothness, and smooth spatial slices.

`galLim_pde` proves the fully pointwise original-time equation.  Its proof
differentiates the scalar series with `scalarSpec_d1`, identifies the derivative
coefficientwise with the lifted Galerkin velocity, and realizes the three
velocity arms by `scalarLapHs_core`, `lapDiffHs_core`, and `scalarPotHs_core`.
The final scalar normalization uses `rawLap_cc_scalar`, `scalarLapDiff_eq`, and
`scalar0_smul_cc`; no whole-tensor equality, whole-Hom equality, global frame,
or new consumer assumption is used.

`heatpot_of_gallim` packages these producers into a genuine `IsHeatPotOn` for
`reverseFamily (flowG S) T` on a nontrivial closed interval.  The final interval
is strictly inside the smooth/PDE windows, so the upper endpoint has a smooth
spatial slice as required by the structure.  Focused verification passes
without warnings.  The route still inherits the existing
`WeylEigenvalueCountingBound.lean` `sorry`; the new theorem bodies contain no
local `sorry`.

Honest accounting: `galLim_pde` and `heatpot_of_gallim` are each theorem-level
**100%**, and their dedicated classical conjugate-heat machinery is **100%**.
Perelman's no-local-collapsing theorem and `ham3_noncollapse` remain endpoint-
level **0%**; their broader dedicated entropy/noncollapse machinery is about
**52%**.  Whole HCG machinery is conservatively about **60%**.

## 2026-07-16 unconditional classical existence

`heatpot_exists` now composes `scalar_gal_subseq` with
`heatpot_of_gallim`.  Thus every smooth rank-zero initial tensor produces an
actual classical heat potential on a nontrivial reversed-time interval, with
the exact scalar initial trace.  `conj_heat_exists` then applies the existing
time-reversal bridge and produces an `IsConjHeatOn` solution with the exact
terminal trace.  Neither theorem assumes Galerkin limit data from its caller.

Focused verification passes without warnings.  The target theorem bodies have
no local `sorry`; as above, the full construction still inherits the existing
Weyl-counting `sorry`.  `heatpot_exists` and `conj_heat_exists` are each
theorem-level **100%**, and classical conjugate-heat existence machinery is
**100%**.  Positivity and unit-mass packaging remain separate producers, and
the current mass-conservation API still asks for global regularity stronger
than the interval-local solution package.  Perelman no-local-collapsing and
`ham3_noncollapse` remain theorem-level **0%**; entropy/noncollapse machinery
is about **54%**, and whole HCG machinery is conservatively about **60%**.

`gallim_nonneg` now intersects the classical existence interval with the new
`conjCoeff_bound` interval, restricts `IsHeatPotOn` through its canonical
`mono` theorem, and applies the existing weak maximum principle.  Hence every
nonnegative smooth scalar initial tensor produces a nonnegative classical heat
potential, without assuming a coefficient bound at the consumer.  Focused
verification passes.  `gallim_nonneg` is theorem-level **100%**; strict
positivity and unit mass remain separate, and no noncollapsing endpoint is yet
proved.

## 2026-07-16 positive unit-mass heat potential

The interval-local mass route is now closed without adding the old global
`MetricFamilyRegularAt` or `FunctionRegularAt` assumptions to consumers.
`heatpot_mass_deriv` directly applies `first_var_joint`: reverse-time chart
Gram smoothness comes from `IsSolutionOn.smoothMetric.frameCompSmooth`, the
reverse volume trace is `+2 R` by `metricDerivAt` and the canonical volume
trace API, and the heat equation cancels the scalar term before Green's
identity kills the remaining Laplacian integral.

`heatpot_mass_eq` shrinks the interval using only regularity of the terminal
time, restricts the genuine `IsHeatPotOn`, and proves closed-interval mass
constancy. The moving integral is continuous by `integral_family_cont`; its
zero derivative makes it constant on the open interior, and
`Set.EqOn.of_subset_closure` extends that equality to both endpoints.
`gallim_unit_pos` then combines `unit_init_or_empty`, `gallim_pos`, and this
mass theorem. Thus either the manifold is empty or there is a strictly
positive genuine reversed heat potential whose moving Riemannian mass is one
at every time of a nontrivial closed interval.

Focused verification is green without warnings, and targeted module
verification is green. These three theorem endpoints and their dedicated mass/positivity
packaging are each **100%**. This completes the positive unit-mass
conjugate-heat input, but it does not prove any noncollapsing conclusion:
Perelman's no-local-collapsing theorem and `ham3_noncollapse` remain
theorem-level **0%**. Their broader dedicated entropy/noncollapse machinery is
now about **58%**, while whole HCG machinery remains conservatively about
**60%**. The construction still inherits the previously recorded
Weyl-counting `sorry`; the new theorem bodies contain no local `sorry`.
