
## 2026-07-07 (goal session, cont.): B2-0 + B2-2 landed; B2 tower cancelled

**Landed (targeted build 3804 jobs green, axioms = [propext, Classical.choice, Quot.sound]):**
- `tangentCoordChange_opens` (B2-0): subtype tangent coordChange = ambient, at interior points.
  Proof: `tangentBundleCore_coordChange_achart` readout (rfl) + `Filter.EventuallyEq.fderivWithin_eq`
  on the subtype chart's `extend_target_mem_nhdsWithin` filter; pointwise via
  `subtypeRestr_symm_apply`; at-point via `EventuallyEq.eq_of_nhdsWithin` (point ∈ range I).
- `tensor0SModelAt_opens` (B2-2): subtype chart-local tensor readout = ambient.  Proof: the
  CML-bundle triv apply is rfl (`Trivialization.continuousMultilinearMap_apply`), symmL →
  coordChange via `TangentBundle.symmL_trivializationAt_eq_core`, close with B2-0 at q := x.
  The cross-manifold `A`-argument type (V-fiber vs M-fiber CML) elaborated WITHOUT any cast
  bridge — same defeq-abuse as the Mathlib core lemma.

**Lean lessons:**
- `𝓝[s] x` notation needs `open Topology` (silent `sorry`-filter + bogus `?m.261 sorry` otherwise).
- Names: `Tensor0SBundle.Tensor0SSpace`, `TensorLieDeriv.tensor0SModelAt`,
  `TangentBundle.symmL_trivializationAt_eq_core`, `TopologicalSpace.Opens.chartAt_eq` (rfl!),
  `OpenPartialHomeomorph.subtypeRestr_source/_symm_apply`, `Filter.EventuallyEq.eq_of_nhdsWithin`.
- C4 is NOT in the root import closure: bare `lake build` does NOT verify C4 files — always use
  targeted `build +DifferentialGeometry...C4.<Module>` (bare-build exit 0 here is vacuous).

**B2-3/4/5 CANCELLED** — the whole naturality tower already exists (see STEPD_PLAN codas 11–13):
OpenSubtypeNaturality.lean + MovingShiRestrictOpen.lean (`covDerivOfField_restrictOpen`) +
MetricCovDerivPullback.lean (`covDerivOfField_pullback`, field-level) + rfl/arity bridges
(`metricCovDeriv_eq_covDerivOfField`, `covDerivOfField_eq_iterCov`).  B2-0/B2-2 remain as
spare parts.  Next: the single (ii) assembly lemma per coda 13.

## 2026-07-07 (goal session, final): covNormWith_pd_zone PROVED sorry-free

D1a-(ii) endpoint complete: zone-local partial-pullback covariant-tower-norm naturality,
`tensor02CovDerivNormWith a δM G G x = tensor02CovDerivNormWith a δN g' g' (Φ x)` on x ∈ V ⊆
Φ.source, with hδ/hG the ambient-mfderiv realization hypotheses (PreApproxIsoDataOn shapes).
Verification: targeted build 3885 jobs green; axioms [propext, Classical.choice, Quot.sound].
Also green here: `tensor02_eq_covDOF` (tower bridge), private `srm_ext`.
Migrated OUT to `Tensor/RSTensor/Coordinates/OpensRestrict.lean` (canonical home): B2-0
`tangentCoordChange_opens`, B2-2 `tensor0SModelAt_opens`, `restrictOpen0S` (all green,
axiom-clean, 2731 jobs).

Key Lean lessons (this file's fight): see STEPD_PLAN codas 19–21 — def-context
section-variable inclusion does not retro-include synth-needed instances (FiniteDimensional
pending-leaf behind a NormedSpace(Tensor0SModel) error; diagnose with #synth probe);
structure-literal against Tensor0SField needs respectTransparency-false + letI-topology
(fromScalarField pattern); `mfderiv_subtype_val` CLM-form in simp (the _apply form fails the
inner-slot motive); cross-fiber CML equalities elaborate bare (defeq abuse);
ContMDiffSection FunLike-coe is not rfl.

Next brick: (iii) `partialData_comp` (coda 21).

## 2026-07-07 (goal session, rounds 5-7): partialData_comp PROVED — D1a complete

`partialData_comp` (D1a-(iii), the lbl406 composition brick) fully proved: two-sided partial
approx-iso data composes along `PartialDiffeomorph.trans` on any compact K inside the zone,
∀ε''-monotone/Nonempty form with C := max-of-four constants, hypotheses ε,ε' ≤ 1/2, lower
bound 2(ε+ε')+(ε+ε')C.  Proof ≈ 700 lines: forward + mirrored reverse pipelines, each =
collar realize (strengthened exists_pullbackField) + error triangle + four F5 inputs
(equiv/hgK/hδ₀/hδ₁ — hgK consumed from the OTHER side's reverse data, which is why the
book's data is two-sided) + comp_cov_le + germ-vanishing (restriction-naturality as
germ-congr) + tower/norm bridges.  Five covNormWith_pd_zone live calls total.
Axiom status: sorryAx inherited ONLY from F5→lemma45_corII→Lemma45F4.lean:86 (B-track's one
narrow mechanical sorry; disclosed in docstring).  All other new session declarations
axiom-clean.  Durable Lean lessons in STEPD_PLAN codas 22-36 (∃-elim-into-Prop hoisting,
acEquiv .symm direction, set_option ladder 1M→2M, left/right_inv coe traps).

## 2026-07-08: half-composition API frontier exposed

Added two data-producing interfaces for the D1b two-bracketing recursion:

- `compDataFwd`: forward half of `partialData_comp`, with only the forward
  asymmetric tolerance bound `ε/(1-ε) + ε' * max C 2`.
- `compDataRev`: reverse half of `partialData_comp`, with only the reverse
  asymmetric tolerance bound `ε'/(1-ε') + ε * max C 2`.

These are intentionally exposed at the `PullbackField` layer because the proof
organs already exist inside `partialData_comp` (`hc0P''`/`hcovP''` and
`hc0Pr`/`hcovPr`).  D1b should consume these halves separately: forward on the
peel-last `chainComp` ledger, reverse on the peel-first `chainComp'` ledger,
then assemble with `BookApproxIsoPartialData.ofParts`.

Verification: focused `PullbackField.lean` check passed.  The two new
interfaces are precise `sorry` frontiers; no Lean error remains in their
signatures.

## 2026-07-09: separated-parameter composition API

Added the first separated-parameter composition layer:

- `compSepFwd`: forward half, with explicit F5 feed `q` and new-step feed `e1`,
  outputting separated `c0''` and `cov''` ledgers;
- `compSepRev`: mirrored reverse half;
- `sepData_comp`: ordinary two-sided composition wrapper around the two halves.

Verification passed, and the targeted module build passed.  The forward/reverse
halves are precise `sorry` frontiers intended to reuse the existing
`partialData_comp` proof organs.  Important boundary: `sepData_comp` is a valid
ordinary two-sided composition wrapper, but it is not the D1b hacc replacement.
D1b still needs the half-composition split: forward on the peel-last ledger and
reverse on the peel-first shifted-tail ledger, then assemble with the existing
fold/germ transports.
