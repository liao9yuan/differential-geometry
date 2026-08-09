# Distance-barrier elaboration consultation, round 2

I need a repository-specific Lean 4 elaboration/performance diagnosis, not a
new mathematical route.

Repository: `https://github.com/liao9yuan/differential-geometry`

Branch: `codex/short-time-existence-align`

Remote-visible commit: `80a504a87997b4984cbecb9d7a7ef8522b02f7fa`

Current local HEAD: `828e01877e66d69fc6b94957b8ab46a1dd0fd7d6`

Lean: `v4.29.0`

The files and declarations discussed below are uncommitted local changes and
are not yet visible at the remote commit. The excerpts and verification results
below are authoritative.

The cleanup branch
`https://github.com/qinz1yang/differential-geometry/tree/reunion` was also
audited read-only. It confirms the canonical
`EMetricSpace.ofRiemannianMetric` completeness-instance pattern, but it does not
contain the newer `DistanceBarrier`, `MetricTimeCompare`, or an analogous
heartbeat fix.

## Goal and invariant constraints

Keep the public theorem
`scaledDist_calabiUpperSupport_of_sol` unchanged. It produces the seven-field
smooth Calabi upper-support conclusion for

```text
exp (Lambda * t) * d_{g(t)}(O, ·)
```

from a Ricci-flow solution, completeness at time zero, a closed-slab
order-zero curvature bound, positive time, and finite nonzero distance.

Do not add:

- completeness at the selected time as an input;
- connectedness, injectivity radius, a cut-time hypothesis, or a new HCG field;
- a second metric/completeness hierarchy;
- an unlimited or file-wide heartbeat setting.

All mathematics below is already assembled without `sorry`, `admit`, or a new
axiom. The only blocker is deterministic `whnf` normalization.

## Current two-module boundary

The source was split at the smallest stable boundary:

```text
Evolution/DistanceBarrierCore.lean
Evolution/DistanceBarrier.lean
```

`DistanceBarrierCore.lean` is focused-green and exact-green
(`3994/3994`) at the default heartbeat budget. It exports:

```lean
namespace DistanceBarrierCore

structure ScaledDistSupport
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (O : M) (T t : Real) (x : M) (d Λ r : Real) : Prop where
  rho : Real → M → Real
  eq_at : ...
  upper_nhds : ...
  time_diff : ...
  space_diff_nhds : ...
  grad_diff : ...
  grad_sq : ...
  par_lower : ...

theorem ScaledDistSupport.toResult
    (h : ScaledDistSupport (I := I) S O T t x d Λ r) :
    ∃ rho : Real → M → Real, ... := ...

theorem ricci_quad_of_curv ... :
    0 ≤ (Module.finrank Real E : Real) ^ 2 * Real.sqrt K ∧
    (∀ s ∈ Set.Icc 0 T, ∀ y v,
      |ricciTensor ... v v| ≤
        ((Module.finrank Real E : Real) ^ 2 * Real.sqrt K) *
          (S.base.metric s).inner y v v)

theorem scaled_of_quad
    ...
    (hLambda : 0 ≤ Lambda)
    (hricQuad : ∀ s ∈ Set.Icc 0 T, ∀ y v, ...)
    (hcomplete_t :
      RiemannianMetricComplete (I := I) (S.base.metric t))
    ... :
    Nonempty
      (ScaledDistSupport (I := I) S O T t x
        (Module.finrank Real E : Real) Lambda
        (riemannianEDistOf
          (I := I) (S.base.metric t) O x).toReal)
```

The lower module
`Evolution/MetricTimeCompare.lean` is also focused- and exact-green and exports:

```lean
theorem complete_of_rmBound
    ...
    (hcurv : ∀ t ∈ Set.Icc a b, ∀ x : M,
      Tensor0SBundle.normSq0S (I := I) (S.base.metric t) x 4
        (S.base.rm04 t x) ≤ C)
    (ha : RiemannianMetricComplete (I := I) (S.base.metric a))
    {s : Real} (hs : s ∈ Set.Icc a b) :
    RiemannianMetricComplete (I := I) (S.base.metric s)
```

`RiemannianMetricComplete g` is the existing `Prop` structure whose only field
is a `CompleteSpace M` value under the canonical local instances for
`IsManifold I 1 M`, metrizability, `T3Space`, `RiemannianBundle`,
`IsContinuousRiemannianBundle`, and
`EMetricSpace.ofRiemannianMetric I M`.

## Current smallest failing declaration

The endpoint wrapper defines:

```lean
private structure CurvPrep
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (T K t : Real) : Prop where
  lambda_nonneg :
    0 ≤ (Module.finrank Real E : Real) ^ 2 * Real.sqrt K
  ricci_quad :
    ∀ s ∈ Set.Icc 0 T, ∀ y : M, ∀ v : TangentSpace I y,
      |ricciTensor (I := I) (S.base.metric s) y v v| ≤
        ((Module.finrank Real E : Real) ^ 2 * Real.sqrt K) *
          (S.base.metric s).inner y v v
  complete_t :
    RiemannianMetricComplete (I := I) (S.base.metric t)
```

and then:

```lean
attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
private theorem curv_prep
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    {T K t : Real}
    (hslab : Set.Icc 0 T ⊆ D.carrier)
    (hreg : Set.Ioc 0 T ⊆ D.regular)
    (hcomplete :
      RiemannianMetricComplete (I := I) (S.base.metric 0))
    (hK : 0 ≤ K)
    (hcurv : ∀ s ∈ Set.Icc 0 T, ∀ y : M,
      nablaKRm04NormSqIntrinsic (I := I) S 0 s y ≤ K)
    (ht : t ∈ Set.Icc 0 T) :
    CurvPrep (I := I) S T K t := by
  have hquad :=
    DistanceBarrierCore.ricci_quad_of_curv (I := I) S hK hcurv
  have hcurv0 : ∀ s ∈ Set.Icc 0 T, ∀ y : M,
      Tensor0SBundle.normSq0S (I := I) (S.base.metric s) y 4
        (S.base.rm04 s y) ≤ K := by
    intro s hs y
    simpa only [nablaKRm04NormSqIntrinsic, nablaKRm04Field_zero,
      Nat.add_zero] using hcurv s hs y
  exact {
    lambda_nonneg := hquad.1
    ricci_quad := hquad.2
    complete_t :=
      complete_of_rmBound
        (I := I) (D := D) (a := 0) (b := T) (C := K) (s := t)
        S hS hslab hreg hcurv0 hcomplete ht
  }
```

This declaration deterministically times out at `whnf`:

```text
DistanceBarrier.lean:52:0:
error: timeout at whnf, maximum heartbeats 200000
```

A temporary option scoped only to `curv_prep` also failed at `500000`
heartbeats. The live source has been restored to the default setting.

The later private `scaled_of_curv` now only does:

```lean
have hp := curv_prep ...
exact DistanceBarrierCore.scaled_of_quad
  ... hp.lambda_nonneg hp.ricci_quad hp.complete_t ...
```

It cannot be checked because `curv_prep` is not created.

## Routes already ruled out

1. One monolithic proof returning the public nested existential proposition.
2. Separate fixed-time `CalabiFlowCore`, scaling, and completeness helpers in
   the same module.
3. An opaque lower `completeInst` for installing the canonical
   `CompleteSpace M`.
4. A compiled top-level `complete_of_rmBound` theorem in
   `MetricTimeCompare.lean`.
5. A compiled `DistanceBarrierCore.olean` boundary while
   `scaled_of_quad` returned the full public existential proposition.
6. The same compiled boundary with `scaled_of_quad` returning
   `Nonempty ScaledDistSupport`.
7. The current `CurvPrep : Prop` packaging of `lambda_nonneg`,
   `ricci_quad`, and `complete_t`.
8. Fully explicit implicit arguments and direct `exact`/`obtain` layouts.
9. Scoped 400000 and 500000 heartbeat experiments.

The compiled core, its named support result, `ricci_quad_of_curv`,
`complete_of_rmBound`, and `scaled_of_quad` all verify individually. No stale
artifact or theorem-body type error is reported.

## Questions

1. Why does constructing this three-field `CurvPrep` force enough reduction to
   exceed 500000 heartbeats even though both producer constants are imported
   from fresh `.olean` files?
2. Is the expensive reduction caused by the `RiemannianMetricComplete` field
   and its dependent canonical-instance tower, by the record constructor, by
   elaboration of the `ricci_quad` dependent function field, or by interaction
   with the scoped removal of tangent-space instances?
3. What is the smallest Lean-native declaration or tactic shape that prevents
   this reduction while preserving all current statements and assumptions?
   Please give concrete code.
4. In particular, would any of these genuinely change elaboration here:
   - a narrowly scoped
     `set_option backward.isDefEq.respectTransparency false` at one exact
     declaration;
   - replacing the record literal with three separately typed opaque producer
     theorems and `refine ⟨?_, ?_, ?_⟩`;
   - making `CurvPrep` a data structure rather than a `Prop` structure;
   - making `complete_t` a thunk or a separately named field theorem;
   - moving `curv_prep` into `MetricTimeCompare.lean`;
   - passing `complete_of_rmBound ...` directly to `scaled_of_quad`;
   - installing the canonical metric instances once in the wrapper and passing
     a raw `CompleteSpace M` value instead of
     `RiemannianMetricComplete`;
   - using `apply`/`refine`/`show`/`change` so Lean does not synthesize the
     record's expected type by `whnf`;
   - a narrowly scoped `synthInstance.maxHeartbeats` rather than
     `maxHeartbeats`.
5. If the existing `RiemannianMetricComplete` representation itself is the
   performance problem, propose the smallest compatibility-preserving adapter.
   Do not redesign the public completeness API or add a new assumption.
6. If the source cannot be decided statically, give the smallest trace or
   diagnostic setting that distinguishes expected-type normalization,
   typeclass synthesis, the curvature-bound coercion, and normalization of
   `RiemannianMetricComplete`.

The desired answer is a surgical Lean elaboration fix. If no such boundary can
work before declaration compilation, please explain precisely which term is
being normalized and recommend the smallest justified next experiment.

## Resolution — 2026-07-27

The performance wall was caused by a normed-space instance diamond, not by
reduction of `RiemannianMetricComplete`, the `CurvPrep` record, or the imported
proof bodies.  `DistanceBarrier.lean` declared both an explicit
`NormedSpace Real E` and `InnerProductSpace Real E`; the imported
`MetricTimeCompare` theorem types use the normed-space instance induced by the
inner product.  Crossing that boundary forced a large failed definitional
equality check.

Micro-probes established:

- the inner-product-only binder is green;
- adding the independent explicit normed-space binder reproduces the timeout;
- the redundant `Module.Finite` binder is not the hotspot.

The final source removes the explicit normed-space binder and uses the proposed
named `hΛ`/`hricQuad` assembly.  No heartbeat or transparency option was added.
`DistanceBarrier` is focused- and exact-green (`3995/3995`), and its public
endpoint is closed.
