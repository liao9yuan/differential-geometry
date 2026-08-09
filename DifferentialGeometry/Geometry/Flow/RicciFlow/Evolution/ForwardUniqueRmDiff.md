# ForwardUniqueRmDiff.lean — Route-K brick K2.0 + K2.3 (go/no-go probe)

Companion note for
`DifferentialGeometry/Geometry/Flow/RicciFlow/Evolution/ForwardUniqueRmDiff.lean`.
Governing ruling: `ShortTime/FORWARD_UNIQUE_PRO_RULING.md` §4 (the Kotschwar system) and
§7 (Route-(K) stop gates).  Dispatch: `ShortTime/FORWARD_UNIQUE_PLAN.md` №2, planner
ruling R2 (K2.3 first, timeboxed).

## Probe outcome: (A) — identity proven pointwise/field-level, 0 sorry

Focused check: PASS.  Targeted module build: PASS (`✔ Built … (16s)`, zero errors and zero
warnings attributable to this file).  Axiom audit: all 21 public declarations depend on
exactly `[propext, Classical.choice, Quot.sound]`.

**Neither Route-(K) stop gate fired.**  Gate 1 (a new cross-variance connection-difference
module spanning `Geometry/Curvature` + `Analysis/Elliptic`) was dissolved by the flux
choice below, not worked around: the whole brick stays inside the `Tensor0S` stack, uses
no `(1,s)` mixed-variance object, and touches no existing file.  The repository's canonical
`rm13`/`rm04` representation was not changed, the all-`k` Shi architecture was not touched,
and no curvature-commutator framework was introduced.

## The mathematical decision that made this cheap

The ruling's flux is `Uᵃ = (g₁ᵃᵇ − g₂ᵃᵇ)∇²_bRm₂ + g₁ᵃᵇ(∇¹_b − ∇²_b)Rm₂`.  That telescopes
to `g₁ᵃᵇ∇¹_bRm₂ − g₂ᵃᵇ∇²_bRm₂`, whose `g₁`-lowering is `∇¹T − (g₁♭∘g₂♯)∇²T`.  Formalizing
*that* representative is what would have forced the composite endomorphism `g₁♭∘g₂♯` on the
divergence slot, hence a raised `(1,4)` intermediate and a connection-difference theory for
mixed variance — i.e. exactly Gate 1.

This file uses the equivalent flux

```
U₀₅ = ∇¹T − ∇²T
```

which differs from the lowered Kotschwar flux by `(id − g₁♭g₂♯)∇²T = O(|h₀₂|)·|∇²T|`.  The
divergence-form identity is then a **regrouping**, which is all it ever was in Kotschwar —
the mathematical content of K2 lives entirely in *which* `U` and `R` one picks, and both
choices satisfy the ruling's four pointwise inequalities:

* `|U| ≤ C|A₀₃|` (sharper than the required `C(|h₀₂| + |A₀₃|)`), because `∇¹T − ∇²T` is the
  algebraic action of the connection-difference tensor on `T`
  (`Tensor0SBundle.nabla0SFun_sub_cov`, already proved in the repo);
* `R = tr_{g₁}(∇¹∇²T − ∇²∇²T) + (tr_{g₁} − tr_{g₂})(∇²∇²T)`, whose first summand is
  `O(|A₀₃|)` and second summand `O(|h₀₂|)` — no `∇S₀₄`, no second derivative of `h₀₂`.

**Honest cost of the substitution (record this for K2.4/K2.5).**  Kotschwar's literal `R`
needs a background bound on `|∇²T|` only; the second summand here also needs `|∇²∇²T|`,
one more background covariant derivative of the `g₁`-lowered curvature of `g₂`.  That is
free under the smooth-class `(B)` statement (both flows are `C^∞` on `Ico a b`, so every
covariant derivative is bounded on a compact subslab `Icc a c`), but it is a real extra
input to state in the estimate bricks and should not be discovered there by surprise.

## What each declaration provides

Generic `(0,s)` operator layer (all field-level, `Tensor0SField … ∞`):

* `metricNabla0S g T` — one Levi-Civita covariant-derivative step, derivative slot first.
  Regularity is *not* a hypothesis: it is discharged by `totalNabla0S_reg` from
  `metricCov_smooth`.  `metricNabla0S_apply` (`@[simp]`, `rfl`), `_add`, `_smul`, `_sub`.
* `traceFirstTwo_sub`, `traceFirstTwo_zero` — the missing `_sub`/`_zero` companions of the
  existing `metricTraceFirstTwoField_add`/`_smul`.
* `covDiv0SField g V` — `div_g` at `(0,s+1) → (0,s)`, contracting the derivative index
  against slot `0`.  `covDiv0SField_sub`.
* `roughLap0SField g T` — `Δ_g = div_g ∘ ∇^g`, with `roughLap0SField_apply` (`rfl`)
  identifying the fiber value with the canonical `roughLap0STensor`.

Divergence-form layer:

* `lapDiffFlux g₁ g₂ T` — `U = ∇¹T − ∇²T` as a `(0,s+1)` field; `lapDiffFlux_apply`,
  `lapDiffFlux_self` (`@[simp]`).
* `lapDiffRem g₁ g₂ T` — `R`, written so that both summands are manifestly differences;
  `lapDiffRem_self` (`@[simp]`).
* `lapDiff_eq_div_flux` — **the K2.3 endpoint**:
  `Δ_{g₁}T − Δ_{g₂}T = div_{g₁}(U) + R`, generic in `s`.

Curvature layer:

* `rmDiffFlux g₁ g₂ Rm2 x : Tensor0SSpace 5 I x` — **U₀₅**, the pointwise `(0,5)` fiber
  value at `s = 4`, divergence index in slot `0`.  `rmDiffFlux_apply`.
* `rm2Low_eq_sub` — the bridge to the FIELDS carriers: the `g₁`-lowered Riemann tensor of
  `g₂` (the field `U₀₅` differentiates) is `metricRm04At g₁ − rmDiffLowAt g₁ g₂`.
* `rmLapDiff_div_flux` — the `s = 4` pointwise instance of the identity.

The two `_self` lemmas are the sanity check that neither carrier is vacuous: both `U` and
`R` vanish identically when the two metrics coincide, which is the property the Kotschwar
energy estimate consumes at `t = a`.

## Slot-0 divergence convention — verified, not assumed

`covDivergence` / `covDivergenceRaw`
(`Analysis/Elliptic/ConnectionLaplacian/GreenIdentityAndIBP/TensorCovDivergence.lean:186,
366`) is `Σᵢ contract_covariant 0 s b (eᵢ) (∇_{eᵢ}V)`, i.e. it inserts the frame vector into
slot `0`.  On this side, `totalNabla0SFun` documents "the output has one leading derivative
slot" and `metricTraceFirstTwo0STensor` is "the metric trace of the first two covariant
slots".  So `covDiv0SField g V = tr_g^{0,1}(∇^g V)` contracts the derivative index against
`V`'s own slot `0` — the same convention.  `U₀₅` therefore carries its divergence index in
slot `0` as required.

## Reuse vs new

Reused as-is (no adapters, no reproofs):

* `Tensor0SBundle.totalNabla0SFun` / `totalNabla0S` / `totalNabla0S_apply`
  (`NablaOnTensors/HigherOrder.lean`) for the derivative;
* `Tensor0SBundle.totalNabla0SFun_add` / `_smul` (`NablaOnTensors/TotalNabla0SLinear.lean`)
  for linearity — this pair is the entire engine of the identity;
* `Tensor0SBundle.totalNabla0S_reg` (`NablaOnTensors/Regularity/TotalNabla0S.lean`) —
  the reason no regularity hypothesis appears anywhere in this file;
* `metricTraceFirstTwoField` (+ `_add`, `_smul`) (`MetricTrace/NablaTraceGen.lean`) and the
  pointwise `roughLap0STensor` / `metricTraceFirstTwo0STensor`
  (`Geometry/Operator/RoughLaplacian.lean`);
* `metricCov`, `metricCov_smooth`, `metricRm04At`, `riemannCurvature04At`;
* `rmDiffLowAt` from `Evolution/ForwardUniqueFields.lean` (consumed, not redefined).

New, and why:

* `sub_of_add_smul` (private) — turns an `_add`/`_smul` pair into `_sub`; used twice.
* `metricNabla0S`, `covDiv0SField`, `roughLap0SField` — the identity cannot be *stated*
  without a field-level `∇^g`, `div_g`, `Δ_g` on `(0,s)`, and the repository has none:
  the only divergence is the compactly-supported bundled `covDivergence`, and the only
  rough Laplacian is the pointwise `roughLap0STensor` taking a *supplied* second derivative.

## Items for the planner (deliberately not acted on — brick scope was one file)

1. **Canonical home.**  `metricNabla0S` / `covDiv0SField` / `roughLap0SField` are generic
   `(0,s)` tensor calculus with no Ricci-flow content.  Their canonical home is
   `Tensor/RSTensor/NablaOnTensors/` (the first) and `Geometry/Operator/RoughLaplacian.lean`
   or a sibling (the other two), not this Ricci-flow file.  Likewise `traceFirstTwo_sub` /
   `traceFirstTwo_zero` belong next to `metricTraceFirstTwoField_add`/`_smul` in
   `MetricTrace/NablaTraceGen.lean`, and `metricNabla0S_add`/`_smul`/`_sub` next to
   `totalNabla0SFun_add`/`_smul` in `NablaOnTensors/TotalNabla0SLinear.lean`.  They are
   public here only because the protocol forbade editing existing files.
2. **The `covDivergence` identification is still owed (K2.7).**  `covDiv0SField` is the
   everywhere-defined field-level divergence; the integration-by-parts theorem
   `tensorL2Inner_covGrad_eq_neg_tensorL2Inner_covDivergence` consumes the bundled
   `SmoothCcTensor` `covDivergence`.  Identifying the two (via
   `HasCompactSupport.of_compactSpace` on the closed manifold) is the remaining typing
   reconciliation and was correctly scoped out of this probe.  Nothing here prejudges it:
   the slot conventions were checked to agree before writing.

## Lean lessons from this pass

* The K2 "three-way reconciliation" risk was **mostly a mirage created by the flux
  representative**.  Once `U` is written as `∇¹T − ∇²T`, `div` and `Δ` become the *same*
  operator applied to different arguments (`Δ_g = div_g ∘ ∇^g`), and the identity collapses
  to linearity of `∇` and of the metric trace.  Before paying for a representation bridge,
  check whether an equivalent representative of the *quantity being estimated* removes it.
* `totalNabla0S_reg` + `metricCov_smooth` make covariant-derivative regularity free for
  Levi-Civita connections of `SmoothRiemannianMetric`.  Do not carry `TotalNabla0SRegular`
  as a hypothesis in metric-indexed APIs; it is a producer, not an input.
* Contrary to the `ForwardUniqueFields.md` lesson about `Tensor0SSpace` fiber algebra, the
  **field-level** algebra is well behaved: `(A + B) x = A x + B x`, `(c • A) x = c • A x`,
  and `roughLap0SField_apply` / `metricNabla0S_apply` / `lapDiffFlux_apply` / `rmDiffFlux_apply`
  are all `rfl`.  `DFunLike.ext` works directly on `Tensor0SField`.  The earlier trouble was
  specific to rewriting *under* the fiber `FunLike` coercion, which never arises here.
* Arity unification `s + 1 + 1 =?= ?s + 2` for `metricTraceFirstTwoField` needed no help;
  `set_option backward.isDefEq.respectTransparency false` was never needed even though both
  producer files set it locally.
* The whole file elaborates in ~16 s.  No instance-synthesis trouble; the variable block is
  the `ForwardUniqueFields` one plus `[IsManifold I 2 M]` (required by
  `TotalNabla0SLinear`).

## What this brick does NOT do

No time dependence, no norm estimate, no integration by parts.  `|U₀₅| ≤ C(|h₀₂| + |A₀₃|)`
and `|R| ≤ C(|h₀₂| + |A₀₃| + |S₀₄|)` (K2.4/K2.5) are untouched, and so is the single-flow
`Rm₀₄` evolution that K2.1 takes as the Uhlenbeck-interface hypothesis per planner ruling R1.
This file is not yet wired into any aggregate import — the planner does that.
