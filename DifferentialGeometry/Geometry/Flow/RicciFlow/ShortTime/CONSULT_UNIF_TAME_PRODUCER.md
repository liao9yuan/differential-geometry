# Consult prompt: design the class-first tame producer for (N)

Purpose: obtain an external Lean-aware mathematical design for the one genuine
producer still missing from the low-regularity common-time envelope: uniform
top/A2 and lower-affine constants chosen before the class metric varies.

## Submission

- Repository: `https://github.com/liao9yuan/differential-geometry`
- Branch: `codex/short-time-existence-align`
- Remote-visible base commit: `1606b0817f34483e45c1798b2a4a161694137de0`
- Start a fresh consult chat.
- Inspect these repo-relative files at that branch/commit (attach convenience
  copies only if the consult cannot access the repository):
  - `DifferentialGeometry/Geometry/Flow/RicciFlow/ShortTime/UnifClassBounds.lean`
  - `DifferentialGeometry/Geometry/Flow/RicciFlow/ShortTime/LowRegUnifBounds.lean`
  - `DifferentialGeometry/Geometry/Flow/RicciFlow/ShortTime/UnifRealizeRadius.lean`
  - `DifferentialGeometry/Geometry/Flow/RicciFlow/ShortTime/UnifNZeroClass.lean`
  - `DifferentialGeometry/Geometry/Flow/RicciFlow/ShortTime/UNIF_EXISTENCE_PLAN6.md`

---- PROMPT BEGINS (copy everything below this line) ----

I need a Lean-aware MATHEMATICAL/API DESIGN REVIEW, not an implementation and
not a restatement of the missing theorem.  Inspect the named repository files
and design the smallest honest class-first producer for the low-regularity
Ricci--DeTurck common lifetime.

## Fixed target and class

Work on a closed boundaryless three-manifold (`Module.finrank ℝ E = 3`) with a
fixed smooth metric `gBase`.  Fix `Λ ≥ 1`.  A class metric `g` satisfies:

1. `MetricUniformEquivalentOn Set.univ gBase g Λ`;
2. `MetricCovDerivOrderBoundOn Set.univ a g gBase Λ` for every `a ≤ 3`.

These hypotheses are fixed.  You may specialize the producer to dimension
three, but you may NOT strengthen the metric-jet budget beyond order three.

The eventual theorem is

```lean
lowreg_bounds_unif : ∃ U, IsLowBoundsCap gBase Λ U
```

and is currently theorem-level 0%.  `IsLowBoundsCap` requires, for every class
metric, an exact `LowRegBoundData` packet capped by one common horizon packet.
The exact packet has the scalar fields

```lean
threshold top base slope zeroBd outer realize : ℝ
```

and the analytic proof fields `hreal`, `hcont`, the joint three-arm `htame`, and
`hzero`.  Upper caps are needed for `top/base/slope/zeroBd`; positive lower
floors are needed for `outer/realize`.

Two faces have now been separated honestly:

- finite rank-two realization: one `threshold` and positive `realize` radius is
  selected before `g` (`IsLowRealizeUnif` / `exists_lowRealize`);
- zero-state forcing: one nonnegative `zeroBd` is selected before `g`
  (`IsLowZeroUnif` / `exists_lowZero`, using `unifKsupLeOne` and
  `nZero_unif`).

Do not redesign those faces.  The missing face is the joint tame producer for
`top`, `base`, `slope`, `outer`, `hcont`, and the smooth-core continuity used by
the zero-state adapter.

One small interface seam must be included in the review: `lowRegN_outer`
requires both `0 ≤ δ₀` and `δ₀ < 1`, while the current abstract
`IsLowRealizeUnif` stores only `threshold_lt`, `radius_pos`, and `realize`.
The concrete threshold is positive by
`deTurckArmContractionThreshold''_pos`, but that fact is lost after abstracting
the realization witness.  Choose one honest fix: add threshold nonnegativity to
`IsLowRealizeUnif`, store it in a separate package, or retain the concrete
realization witness through assembly.

## Existing per-metric endpoint

The closest endpoint is

`DifferentialGeometry/Geometry/Flow/RicciFlow/ShortTime/LowRegDenseSolve.lean`
`lowRegN_outer` (around lines 163--203):

```lean
theorem lowRegN_outer
    (hDim : Module.finrank ℝ E = 3)
    (g₀ g_bg : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀_nonneg : 0 ≤ δ₀) (hδ₀_lt : δ₀ < 1) :
    ∃ ρ Ctop : ℝ, ∃ B0 B1 : ℝ → ℝ,
      0 < ρ ∧ 0 ≤ Ctop ∧
      (∀ Q, 0 ≤ Q → 0 ≤ B0 Q) ∧
      (∀ Q, 0 ≤ Q → 0 ≤ B1 Q) ∧
      ∀ {Q R}, 0 ≤ Q → Q ≤ ρ → 0 < R → R ≤ Q →
        realization_on_Q →
        Continuous lowRegN ∧ Continuous coreN ∧ three_arm_bound
```

Its fatal quantifier order for uniform existence is

```text
∀ g, ∃ ρ Ctop B0 B1, ...
```

We need explicit class data giving

```text
∃ ρ Ctop B0 B1, ∀ g in the order-three class, ...
```

or a weaker final fixed-radius scalar form that is genuinely sufficient for
`IsLowBoundsCap`.  Merely defining a structure whose constructor takes this
unproved statement is not progress.

## Existing producer chain to audit

Trace the actual constants through these declarations:

1. Top second-order remainder arm (this is NOT the continuation/Galerkin A2
   packet):
   - `Analysis/Spectral/Intrinsic/DeTurck/LowRegPathSplit.lean`
     `top_path_ball_h1` (about lines 1052--1085), currently
     `g₀ g_bg` before `∃ ρ Ctop Clow`.
2. Lower multiplication constant:
   - `ShortTime/LowRegPathLower.lean`
     `lower_jet_h1` (about lines 100--123), currently `g` before `∃ C`.
3. Underlying remainder assembly:
   - `ShortTime/LowRegRemainderH1.lean`
     `rem_h1_of_jets`, which combines `top_path_ball_h1` and `lower_jet_h1`.
4. Order-zero affine path:
   - `ShortTime/LowRegRhs0Tame.lean`
     `rhs0_h1_tame`, where the actual `B0/B1` functions are constructed;
   - `ShortTime/LowRegCoreTame.lean`
     `rhs0_path_tame` (about lines 62--98), its path wrapper.
5. Order-one affine path:
   - `ShortTime/LowRegRhsOne.lean`
     `rhs1_h2_tame` and its wrapper `rhs1_path_tame` (about lines 156--192).
6. Final assembly:
   - `ShortTime/LowRegCoreTame.lean`
     `rem_h1_tame` (about lines 104--152);
   - trace `coreN_tame` to `coreN_outer`, including `Continuous coreN`;
   - `ShortTime/LowRegDenseSolve.lean`
     `lowRegN_outer`, including dense-extension continuity.

Also search `DifferentialGeometry/` for existing class-uniform Sobolev,
covariant-sum, metric-comparison, product, application, inverse-metric, and
DeTurck coefficient bounds before proposing any new lemma.  Use
`RFreference/` only as reference; do not import it and do not create a parallel
API.

In particular inspect
`Analysis/Spectral/Tensor/SobolevScale/UnifBochnerGap.lean` for existing
finite-rank uniform comparison APIs.

## Two candidate interface shapes

Referee both and choose the weakest sound one.

### Candidate A: functional outer producer

Choose `ρ`, `Ctop`, and functions `B0 B1 : ℝ → ℝ` before `g`, then reproduce
the complete `lowRegN_outer` conclusion for every class metric with
`g_bg := gBase`.  The final assembly evaluates `B0` and `B1` at
`Q = lowregOuterRad Ctop ρ P`, where the realization package already supplies
one class-uniform `P`.

### Candidate B: fixed-P exact scalar producer

Take the already-fixed realization threshold/radius and choose only the final
scalars `top`, `base`, `slope`, and positive `outer` before `g`, proving exactly
the `hcont`/`htame` facts and `Continuous coreN` needed at the final fixed
`Q,R` for every class metric.

Determine whether Candidate B is genuinely weaker and non-circular, or whether
the functional form in Candidate A is the necessary reusable producer.

### Candidate C: cap-oriented producer

Choose only common tame caps/floors before `g`, then allow each class metric to
retain its exact tame scalars and certificates:

```text
∃ U_tame, ∀ g in class, ∃ exact tame packet,
  exact.top ≤ U.top ∧ exact.base ≤ U.base ∧
  exact.slope ≤ U.slope ∧ U.outer ≤ exact.outer.
```

This matches the intended weakness of `IsLowBoundsCap`.  Candidate B may be
strictly stronger.  Decide whether monotone coefficient enlargement and radius
shrinkage prove the two forms equivalent; otherwise prefer Candidate C.

## Required review questions

1. Is a class-first cap/floor producer mathematically valid from comparability plus metric
   jets through order three?  If not, identify the first exact constant that
   needs stronger data and STOP the route there.
2. For every chosen constant in `top_path_ball_h1`, `lower_jet_h1`,
   `rhs0_path_tame`, and `rhs1_path_tame`, give a dependency table:

   ```text
   constant | current source theorem | dependence on g | available uniform API
            | smallest missing uniform lemma | metric-jet order consumed
   ```

3. Decide whether the correct implementation is:
   - one class-first sibling of `lowRegN_outer` proved by transporting all
     per-metric analytic constants to `gBase`, or
   - several lower-layer uniform siblings followed by the existing assembly.
   Prefer the lowest canonical layer and the shortest reusable route.
4. State the exact recommended Lean theorem signatures.  Names must be
   Mathlib-like and at most 20 characters.  Separate data from proof predicates;
   do not introduce a wrapper that merely assumes the desired estimates.
5. Audit the radius dependency graph

   ```text
   P -> Q = lowregOuterRad Ctop ρ P
     -> base = B0 Q, slope = B1 Q
     -> R = lowregStateRad Ctop slope ρ P
   ```

   and prove that your quantifier order has no circular choice.
6. Explain exactly how `hcont`, `Continuous coreN`, and the joint three-arm tame
   estimate travel through the proposed interface so that `lowZero_nfun` can
   use the same `Continuous coreN` witness.
7. Give the shortest implementation sequence, one declaration at a time, with
   a verification/stop condition after each declaration.
8. Account explicitly for `0 ≤ threshold` in the chosen realization/tame
   interface; do not silently use positivity that the abstract package forgot.

## Hard constraints

- Do not revive the all-rung `lowreg_gate_unif`; it is not on the common-time
  path and its rung-five comparison exceeds the order-three jet budget.
- Do not use qualitative compactness of the infinite metric class to turn
  `∀ g, ∃ C` into `∃ C, ∀ g`.
- Do not add assumptions named `hbound`, `htame`, `hsection`, etc. that simply
  restate the missing producer.
- Do not change public definitions, add foundational classes, or move the
  frontier into a polished wrapper.
- Track the Sobolev orders carefully: the live estimate is H3-to-H1 in the top
  arm and H2-to-H1 in the lower arms, in dimension three.
- Do not import the continuation/Galerkin `LowRegBgA2Time` packet into this
  producer; it is not a field of `IsLowBoundsAt`.
- Do not discharge a low-order estimate by assuming an unrestricted/all-rank
  curvature-action family (`Fc`/`hcurv`).  For every comparison theorem, report
  the exact tensor rank and derivative order.  Varying-metric inputs must remain
  within order three; arbitrary fixed finite-order caps of `gBase` are allowed
  only when identified explicitly as fixed-background data.
- If a uniform comparison theorem already exists in `DifferentialGeometry/`,
  reuse it or propose a thin adapter at its canonical layer.

## Required output

Return:

1. `CONTINUE`, `CONTINUE-WITH-CORRECTIONS`, or `STOP-AND-REDESIGN`;
2. the chosen interface shape among A/B/C and exact theorem signatures;
3. the constant-dependency/jet-budget table;
4. the first three implementation bricks, in order;
5. the smallest genuine missing lemma and an assessment: routine local proof,
   missing API, substantial design choice, or mathematical obstruction;
6. any counterexample or hidden circularity you found.

Do not claim the uniform-existence theorem is advanced merely because an
interface is designed.  The actual producer remains 0% until a theorem with
class-first quantifier order is proved in Lean.

---- PROMPT ENDS ----
