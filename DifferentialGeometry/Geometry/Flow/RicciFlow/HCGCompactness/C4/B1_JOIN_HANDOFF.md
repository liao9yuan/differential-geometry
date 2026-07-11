# B1 join — live handoff (2026-07-10)

Work in `E:\testdifferential-geometry`, branch `short-time-existence`.  Read
`AGENTS.md`, `important_lesson.md`, `lessons.md`, `PROJECT_MAP.md`, and the
same-name notes before editing.  Use `scripts/lake-locked.ps1`; claim Lean files,
prefer focused checks, and do not force-release stale locks.

## Honest status

- Textbook B1 theorem: 0%.
- Concrete `StepB1RawInput` producer: 0%.
- Checked conditional assemblies: `stepB1_of_raw`, `stepB1_of_bounds`.
- Dedicated Step-B1 machinery: about 73%.
- Chapter 4 machinery: about 72%.
- Whole HCG compactness machinery: about 49%.
- Conditional/final compactness endpoints: 0%.

Do not report a checked wrapper or local green module as completion of B1.

## What is now checked

- `GoodCoveringSeq.inner_cover`: eventual `3 * lamInf` cover inside the existing
  `4 * lamInf` hats.
- `StepCAtoms`: intrinsic quadratic atoms, inner-one and hat-support facts,
  eventual `WeightDataOn`, canonical zero slot, and basepoint delta weights.
- `StepCAtomConv`: quadratic readout calculus, live/dead sequence atom limits,
  normalized-weight `C^infty` convergence, finite live-slot origin-metric
  extraction, and dead-slot zero overwrite.
- `StepCAtomJoin.existsLiveJoint`: one strict subsequence carries the live-slot
  origin metrics and the one-sided transition family, with eventual geometry
  and a common finite tail.
- `StepCAtomPackage.existsAtomWeightLim`: genuine dead-slot zero limits, smooth
  atom and normalized base-killed weight families, and Pi-valued `C^infty`
  convergence; exact-one is derived from the intrinsic cover.
- `MapCInfConvOnCompacts.congr_eventually`: tail locality for stabilized slots.
- `StepCCmDomain`: the actual center on an admissible set, the analytic
  `cmExt_contDiffOn` interface, the compact pinned-root gluing theorem, subtype
  center continuity, injectivity-based agreement, and the generic conditional
  `centerReadout_zero` producer.  The latter has not yet been instantiated on
  the finite-hat configuration family.
- `exists_diagInvDom` / `exists_readoutDom`: real finite-order open branch
  domains with off-diagonal smoothness and pointwise inverse/projection facts.
- `exists_diagInvDom_inf` / `exists_readoutDom_inf`: one common all-order open
  branch/readout domain for the existing `diagExpInv`.
- `exists_readoutEBall`: a finite positive branch radius for each fixed
  `(M, g, p)`.  `centerPairs_lt_of`, `centerPairs_lt_le`, and `centerPairs_lt`
  close the local center/point containment ledger, including the cage-facing
  sufficient bound `R + 2 * r < δ` with `R = 4 * lambda` available later.
- `exists_halfSqDist_md`: fixed-target local differentiability of
  `halfSqDist`; `expDiffeoRadius`, `expDiffeo_mem_of_lt`, and
  `diagInv_eq_normal_lt`: pointwise intrinsic/realized branch identification
  below a named radius.  Their finite-hat source/smallness hypotheses are not
  yet instantiated.
- `NormalPhaseEndpoint.exists_normal_diag` now combines the bilateral normal
  flow, quantitative inverse, explicit target-ball radius, and exact
  commutative square with intrinsic `diagExp`.  `normal_inv_eq` proves equality
  with the existing `diagExpInv` under concrete branch-domain identities and
  two `expDiffeoRadius` smallness inequalities.
- `DiagExpDerivative.diagExpInv_diagExp` supplies the source-side IFT germ, so
  compatibility of the two branches on a verified overlap is no longer open.

## Next tasks, in order

1. Consume the already bundled relative branch scale.  The endpoint's
   `MetricCompactnessInputs.normalRadius : NormalRadiusProfile ...` supplies the
   positive `ratio * mu(distance)` floor, with checked `floor_le_radius`,
   `floor_le_exp`, and `mul_lambda_lt_*` consumers.  Feed those bounds to
   `exists_normal_diag`; do not add another profile or a naked `branchRadius`
   field.
2. Resolve the branch-domain design gate.  Either prove an explicit
   sequence-uniform containment theorem for the exact qualitative `diagExpIFT`
   source/target, together with the two `expDiffeoRadius` inequalities, or
   refactor the canonical/readout branch package to consume the transported
   quantitative partial homeomorphism.  Pointwise openness and a fixed-index
   finite minimum are insufficient for `StepB1RawInput`.  Consult
   `NORMAL_BRANCH_RECONCILIATION_CONSULT.md` before choosing between these routes.
3. Use `centerPairs_lt_le` to thread
   finite-hat configuration containment through the branch domain and
   `centerOfMass.eqnRadius`.  Instantiate the checked fixed-target
   `exists_halfSqDist_md` producer by proving reverse-chart source/smallness,
   then use `centerReadout_zero` to discharge `hzero`.
4. Supply the book-scale Hessian/Neumann input, instantiate
   `existsCmExtension`, upgrade the ambient root with `cmExt_contDiffOn`, and
   compose it with the verified atom/weight/target limits.
5. Use the resulting C-track estimates, local diffeomorphism/injectivity, and
   basepoint delta identity to construct `StepB1RawInput`.

## Current mathematical frontier

Pinned-map extraction, compact gluing, subtype continuity, and agreement are
now implemented and verified.  `centerReadout_zero` is a checked conditional
producer for the selected center's root equation, but its finite-hat
instantiation still depends on the named geometric hypotheses above.

The qualitative all-order inverse/readout issue and local containment ledger
are closed by `exists_diagInvDom_inf`, `exists_readoutDom_inf`,
`exists_readoutEBall`, and `centerPairs_lt_le`.  The earlier claim that the
relative profile was missing was stale: it is the checked
`MetricCompactnessInputs.normalRadius` field.  The ODE-side uniform family,
phase-box confinement, quantitative approximation, arbitrary-velocity
cross-model naturality, endpoint uniqueness, explicit quantitative branch,
and its exact `diagExp` commutative square are checked.  Branch uniqueness on
overlap is also checked.  The current failure is architectural: the explicit
uniform target ball is not known to lie in the pointwise qualitative
`diagExpIFT` germ underlying totalized `diagExpInv`; the current API provides no
uniform radius from openness alone.
`halfSqDist` differentiability and
intrinsic/realized-exp agreement now have checked pointwise producers
(`exists_halfSqDist_md` and `diagInv_eq_normal_lt`); their concrete finite-hat
source/smallness hypotheses are still configuration-containment obligations,
not consequences of bare branch membership.  The book-scale
Hessian/Neumann producer remains independent and honest;
`CmHessianBoundInput.toInv` is only a projection from it.

## Forbidden routes

- Do not resurrect the false P-only `stepB1_approxIso` statement.
- Do not require `CenterInput` on the whole configuration vector space.
- Do not require `CenterInput` on an ambient open neighborhood of a sparse or
  delta weight; the nonnegative simplex has boundary there.
- Do not run metric/transition extraction over dead fallback centers.
- Do not require live-slot geometry at every index; stabilization only supplies
  the genuine centres eventually.
- Do not request reverse transitions or cocycles from the fixed-source Step-C
  atom join; those belong to the atlas-transition lane.
- Do not add consumer-side assumptions that merely rename `hsm`, `hinv`, or
  `hzero` as a polished endpoint.
- Do not glue roots with a partition of unity; it does not preserve the root
  equation.  Use the pinned-map injectivity neighborhood.
- Do not replace the intrinsic atoms by the old fixed-psi `bumpNumConv` route.
- Do not infer a uniform branch radius from uniform `metricC`; the radius field
  itself is only pointwise positive.
- Do not add a consumer-side `branchRadius` assumption that simply renames the
  missing quantitative geometry/ODE producer.

## Acceptance criteria for the next brick

- Reuse the checked fixed open inverse-exp/readout branch and local containment
  APIs; do not return to order-dependent neighborhoods.
- Either prove explicit sequence-uniform containment in the exact existing IFT
  source/target, or complete a canonical-branch/readout refactor using the
  transported quantitative partial homeomorphism.  A pointwise positive radius
  or a finite minimum at one index does not meet this criterion.
- Then prove the concrete finite-hat configurations land in that domain and below
  `centerOfMass.eqnRadius`; prove the reverse fixed-target normal-chart facts
  needed by `exists_halfSqDist_md` and the `expDiffeoRadius` smallness needed by
  `diagInv_eq_normal_lt`, so `centerReadout_zero` discharges the root equation
  without a renamed consumer assumption.
- Keep the independent Hessian/Neumann producer visible if it is not discharged
  in the same brick, and update the same-name note plus `PROJECT_MAP.md` with
  theorem completion separated from machinery progress.
