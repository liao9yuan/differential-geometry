# B1 minimizing-branch ruling and executor handoff

Status: 2026-07-12, branch `short-time-existence`, paused after Gate 3a.

This file records the GPT Pro response to
`B1_INTRINSIC_REALIZED_CONSULT.md`, reconciled with the current live tree.  It
is an executor handoff, not a replacement for `B1_JOIN_HANDOFF.md`,
`CHAPTER4_PLAN.md`, or `PROJECT_MAP.md`.

## Ruling

Use the fourth route: capture the existing Hopf-Rinow minimizing intrinsic
tangent inside the explicit source of the selected quantitative branch.

For a controlled pair `(y, pt)`, obtain `v : TangentSpace I y` with

```lean
expMapIntrinsic (I := I) g hEnorm y v = pt
Real.sqrt (g.inner y v v) = (riemannianEDist I y pt).toReal
```

from `hopf_rinow_expMapIntrinsic_surjective_minimizing`.  Prove that
`<y, v>` belongs to the selected branch source by H6 metric equivalence and
the exact source transport.  Then use the branch left inverse to conclude

```lean
B.inv (y, pt) = (⟨y, v⟩ : TangentBundle I M).
```

The finite-hat critical path should use this minimizing tangent equality, not

```lean
B.inv (y, pt) = ⟨y, normalChartAt g y pt⟩.
```

This removes `expDiffeoRadius` and the qualitative
`expMapIntrinsic = expMap` radius from the selected-branch root equation.

Do not:

- prove quantitative `expMapIntrinsic = expMap` on the whole H6 tube;
- replace the global realized normal-coordinate API;
- infer minimization from a branch endpoint identity alone;
- add a uniform `expDiffeoRadius` lower bound as an endpoint or consumer input.

## Live implementation state

The other B/C task already started this ruling.  Resume it; do not restart.

1. `DiagInvBranch.inv_eq_of_exp` is present in
   `Geometry/Exponential/DiagInvBranch.lean` and focused-check passed.  Its
   stable proof is:

   ```lean
   simpa only [diagExp_apply, hexp] using B.left_inv hvsrc
   ```

   A broad `simp` is intentionally avoided because it unfolds the intrinsic
   exponential too far.

2. `C4/NormalBranchMin.lean` now has focused-green proofs of:

   - `normalTan_metric`;
   - `normalTanHome_target`;
   - Gate 1, `IsNormalDiag.tan_mem_of_small`;
   - Gate 2, `IsNormalDiag.inv_is_min`;
   - Gate 3a, `IsNormalDiag.halfSq_eq_inv`.

3. Gate 3b, `IsNormalDiag.halfSq_inf`, is saved with a complete proof candidate
   but is not yet verified.  The last focused check stopped before local
   elaboration because an upstream `Tensor0SRiemannian/Comparison.olean` was
   missing.  The dependency refresh was intentionally stopped on pause to free
   resources.  Resume by checking the saved file; do not rewrite the candidate
   first.

4. Gate 4 `grad_half_inv`, Gate 5 center readout, and Gate 6 uniform scale have
   no Lean implementation yet.  The concrete `StepB1RawInput`, textbook B1,
   and compactness endpoints remain theorem-level 0%.

## Important correction to the Pro response

The Pro response says that `NormalRadiusProfile` supplies a uniform lower floor
for `expRadiusGp`.  The current structure does not state that.  Its
`le_exp_radius` field and `floor_le_exp` theorem target `expMapC2Radius`.

Therefore:

- the pointwise `tan_mem_of_small` statement is honest with the explicit input

  ```lean
  rho / 2 <= expRadiusGp (I := I) (X.obj k).metric x;
  ```

- the proposed sequence-uniform `normalMinScale` does not follow verbatim from
  the current `NormalRadiusProfile` API;
- before exporting `normalMinScale`, prove a real relative lower-floor producer
  for `expRadiusGp` from existing H6 metric equivalence and
  `gpCoerciveConst`, or stop with that producer as the exact missing lemma;
- do not silently replace the missing floor by a new endpoint assumption.

This correction does not invalidate the fourth route.  It separates the
pointwise source-capture theorem, which is locally feasible, from the later
sequence-uniform scale theorem.

## Implementation order

### Gate 1: verify pointwise source capture -- COMPLETE

Focused-check `NormalBranchMin.lean` as saved.  The intended proof is:

1. convert `riemannianEDist I x y < ENNReal.ofReal (rho / 2)` to a finite
   real-distance bound;
2. use `hb.chart_mem_norm_le` to obtain normal-chart source membership and
   `norm (normalChartAt g x y) < rho`;
3. use `NormalDiagFence` to put that base coordinate in `normalExpPD.source`;
4. invert `normalTanHome` at `<y, v>`;
5. use `normalTan_metric` plus `hb.metric_equiv` to prove the model fibre norm
   is below `2 * rho`;
6. use `2 * rho < q` and `IsNormalDiag.full_transport` to enter
   `B.hom.source`.

The saved theorem currently uses non-strict `rho <= hb.radius k x` and
`rho / 2 <= expRadiusGp ...`; that is sufficient because the point and tangent
bounds are strict.

### Gate 2: capture the minimizing tangent -- COMPLETE

Add `IsNormalDiag.inv_is_min` in `NormalBranchMin.lean` only after Gate 1 is
green.  For pairs controlled by

```lean
max (riemannianEDist I x y) (riemannianEDist I x pt) <
  ENNReal.ofReal (rho / 2),
```

use the triangle inequality and Hopf-Rinow to obtain `v`, then apply
`tan_mem_of_small` and `B.inv_eq_of_exp`.

Prefer the witness conclusion:

```lean
exists v : TangentSpace I y,
  B.inv (y, pt) = (⟨y, v⟩ : TangentBundle I (X.obj k).M) /\
  expMapIntrinsic (I := I) (X.obj k).metric
    (normal_enorm (I := I) (X.obj k)) y v = pt /\
  Real.sqrt ((X.obj k).metric.inner y v v) =
    (riemannianEDist I y pt).toReal
```

Also export branch-domain membership or the selected-inverse norm equality if
that materially shortens the next theorem.  Do not create a wrapper that merely
renames all of these hypotheses.

### Gate 3: identify half squared distance on the branch -- IN PROGRESS

Still in `NormalBranchMin.lean`, prove:

```lean
IsNormalDiag.halfSq_eq_inv
```

using `inv_is_min`, the Hopf-Rinow metric realization, and nonnegativity when
squaring.  Then prove:

```lean
IsNormalDiag.halfSq_inf
```

on the explicit half-cage by agreement with

```lean
fun y =>
  (1 / 2 : Real) *
    g.inner (B.inv (y, pt)).proj
      (B.inv (y, pt)).snd (B.inv (y, pt)).snd.
```

Use the selected branch's existing all-order inverse smoothness.  This replaces
the HCG use of the qualitative `exists_halfSqDist_md` radius.

Pause status: `halfSq_eq_inv` is focused-green.  `halfSq_inf` is saved but not
yet verified because the focused check encountered a missing upstream object
before reaching the declaration.

### Gate 4: branch-native first variation -- NOT STARTED

Prove:

```lean
IsNormalDiag.grad_half_inv
```

The minimizing identity is essential.  For `pt != y`, rescale the minimizing
tangent to unit speed and reuse the intrinsic fixed-endpoint variation and
`halfSqDist_dir_deriv`.  For `pt = y`, use the existing local-minimum argument
and the selected inverse of the diagonal zero tangent.

Do not infer the gradient formula from smoothness plus an intrinsic endpoint
identity; that would omit minimization.

### Gate 5: center equation and readout root -- NOT STARTED

At the generic center layer, add the shortest branch-parametric analogue of the
existing center first-order equation, preferably named

```lean
centerOfMass.invB_eqn
```

It should reuse the current minimizer and finite-sum derivative proof and accept
the branch-native summand gradient identities.

Then add in `StepCCmDomain.lean`:

```lean
centerReadoutB_min
```

with proof route:

```text
grad_half_inv for every summand
-> centerOfMass.invB_eqn
-> fixed-trivialization fibre equivalence
-> chartCmEqnB = 0.
```

The finite-hat path should migrate to this theorem.  Keep
`centerReadoutB_zero` only as a compatibility entrypoint while it still has
users; do not route the new producer back through `normalChartAt` or
`centerOfMass.eqnRadius`.

### Gate 6: sequence-uniform scale -- BLOCKED ON REAL FLOOR PRODUCER

Only after Gates 1-5 are green, design `normalMinScale` from
`normalBrAccept`, which retains `IsNormalDiag`, `NormalDiagFence`, and full
source/target transport.

Before claiming this gate, resolve both quantifier issues:

1. prove the relative `expRadiusGp` floor missing from the current
   `NormalRadiusProfile` API, or report its smallest missing producer;
2. choose large `D` before freezing the fixed-`D` packing package.

Do not add a branch-specific inequality field to `MetricCompactnessInputs`.
If the conditional endpoint is responsible for choosing book-large `D`, the
honest architecture is either:

```text
base inputs with packing available for every positive D
-> produce scale coefficients
-> choose D
-> construct the fixed-D downstream package
```

or a constructor that builds the existing fixed-`D` bundle only after the
coefficients and `D` are chosen.  Defer this public API decision until the
pointwise minimizing branch route is checked.

## Independent frontier

The Hessian/Neumann producer remains independent.  Capturing the minimizing
branch proves the root equation and first derivative formula; it does not prove
coercivity or invertibility of the center-equation derivative.

`StepB1RawInput`, textbook B1, and the conditional compactness endpoint remain
theorem-level 0% until the minimizing branch chain, Hessian producer, convergence
estimates, and final assembly are all completed.

## Ownership and coordination

The B/C task owns:

- `Geometry/Exponential/DiagInvBranch.lean` for the generic adapter already
  added;
- `C4/NormalBranchMin.lean` for Gates 1-4;
- the subsequent branch-native center/readout edits when it reaches Gate 5.

The thread that produced this handoff must not edit those Lean files in
parallel.  It may review the B/C result after each green gate.  Update the
running B1 plan status after each gate; do not restart the branch, transport,
scale-selection, or `B.readDom` work.
