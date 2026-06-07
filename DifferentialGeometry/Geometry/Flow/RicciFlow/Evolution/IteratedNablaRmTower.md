# IteratedNablaRmTower higher-order heat equation plan

## Live status

`IteratedNablaRmTower.lean` currently has the algebraic tower bridge:

- `IteratedRmTowerOn` stores `wDef`, exact `heatEq`, and `starBound`.
- `abs_towerReactionMulti_le` proves the schematic star-reaction estimate.
- `iteratedRmTower_heatBound` converts `IteratedRmTowerOn` into
  `TowerHeatBoundOn`.

The unresolved producer is not the reaction estimate.  The hard missing content
is producing `IteratedRmTowerOn.heatEq` from an actual Ricci-flow solution for
all `k`.

Lower-order files show the same pattern:

- `RiemannNorm.lean` defines `Rm04NormHeatEquationOn`.
- `RiemannNormHeatProducer.lean` closes the `k = 0` norm heat equation from raw
  component derivative data and reaction algebra.
- `NablaRiemannHeat.lean` defines `NablaRm04NormHeatEquationOn` for `k = 1`,
  but still takes the assembled `|nabla Rm|^2` heat equation as an input.

So the honest remaining frontier is a higher-order analytic producer, not local
maximum-principle algebra.

## Goal

Close the exact heat-equation producer for the tower:

```lean
HasDerivWithinAt (fun s => w k s x)
  (wLap k t x +
    (-2 * w (k + 1) t x +
      towerReactionMulti (level Â· t x) (star Â· t x) k))
  D.carrier t
```

for `w k = |nabla^k Rm|^2` in the Uhlenbeck orthonormal frame.

## Do not do this route

Do not try to prove the all-`k` result by unfolding `iteratedRmComp` and
expanding frame Christoffel formulas recursively.  That route creates a
dependent multi-index explosion and hides the geometry behind component
bookkeeping.

Do not close the theorem by adding a new assumption that is just `heatEq` under
a different name.  `IteratedRmTowerOn.heatEq` is already the exact assumption;
renaming it does not produce anything.

## Correct mathematical split

The producer should be split into two tensor-level statements plus one
component adapter.

### 1. Commuted curvature evolution

Prove a tensor/component theorem with schematic star output:

```lean
(partial_t - roughLap) (nabla^k Rm)
  = Sum_{j = 0}^k nabla^j Rm * nabla^{k-j} Rm
```

In the current component style this should probably be a predicate first:

```lean
def IteratedRmCommutedHeatOn
    (level : (k : Nat) -> Real -> M -> (Fin (4 + k) -> Idx) -> Real)
    (roughLapLevel : (k : Nat) -> Real -> M -> (Fin (4 + k) -> Idx) -> Real)
    (star : (k : Nat) -> Real -> M -> Nat -> (Fin (4 + k) -> Idx) -> Real) : Prop := ...
```

It should assert, for every regular time, point, and multi-index:

```lean
HasDerivWithinAt (fun s => level k s x m)
  (roughLapLevel k t x m + starSum k t x m)
  D.carrier t
```

where `starSum` is the finite sum over `j <= k`.  The exact contraction should
remain schematic; only the star-bound is needed later.

Prove this by induction on `k`, not by norm-square algebra:

- base `k = 0`: use the Uhlenbeck curvature evolution already present in
  `Uhlenbeck.lean`;
- induction step: commute one covariant derivative past `(partial_t - roughLap)`;
- the commutator terms must be absorbed into the schematic `star` family.

The two required local commutator APIs are:

```lean
partial_t_nabla_eq_nabla_partial_t_plus_connection_variation
laplacian_nabla_commutator
```

In book notation:

```text
partial_t (nabla A) = nabla (partial_t A) + (partial_t Gamma) * A
[Delta, nabla] A = Rm * nabla A + nabla Rm * A
```

Under Ricci flow, `partial_t Gamma = nabla Ric`, which is another
`nabla Rm`-controlled star term after Bianchi/trace realization.

### 2. Norm-square Bochner identity

Prove a rank-uniform norm-square identity for a tensor level `A_k`:

```lean
partial_t |A_k|^2
  = Delta |A_k|^2 - 2 |nabla A_k|^2
    + 2 <(partial_t - Delta) A_k, A_k>
```

In the Uhlenbeck orthonormal frame this should be component-level finite-sum
algebra, generalizing `Rm04NormHeatEquationOn` and
`NablaRm04NormHeatEquationOn`.

Good target interface:

```lean
def MultiNormHeatEquationOn
    (level : Real -> M -> (Fin r -> Idx) -> Real)
    (roughLapLevel : Real -> M -> (Fin r -> Idx) -> Real)
    (nextNormSq normLap reaction : Real -> M -> Real) : Prop := ...
```

Then prove:

```lean
multiNormHeatEquationOn_of_componentHeat
```

from:

- component time derivative for `level`;
- Laplacian split
  `Delta |level|^2 = 2 <roughLap level, level> + 2 |nabla level|^2`;
- reaction defined as the contraction of the component heat residual against
  `level`.

This is the right place to reuse and generalize the finite-sum product-rule
style from `RiemannNorm.lean`.

### 3. Adapter into `IteratedRmTowerOn`

After the two producer layers exist, add the thin assembly theorem:

```lean
theorem iteratedRmTowerOn_of_solution
    (...) :
    IteratedRmTowerOn (D := D) level star w wLap
```

This theorem should be mostly field-by-field:

- `wDef`: orthonormal-frame norm reduction, using
  `multiNormInFrame_eq_compNormSqMulti`;
- `heatEq`: from `IteratedRmCommutedHeatOn` plus
  `MultiNormHeatEquationOn`;
- `starBound`: from the already proved schematic component star estimate, or a
  new solution-facing star-bound wrapper.

## Suggested implementation order

1. Add a finite-rank generic component norm heat equation, independent of
   Ricci flow.  Test it at `r = 4` by recovering the existing `Rm04NormHeat`
   shape.
2. Add a `k = 1` closed producer first.  This should turn the current
   `NablaRm04NormHeatEquationOn` hypothesis into a theorem from connection
   variation plus laplacian commutator.  If this cannot be closed, do not start
   all-`k`.
3. Add the commutator theorem as a schematic star theorem.  Avoid specifying
   exact contractions beyond what is needed for the norm bound.
4. Prove the induction from `k` to `k + 1`.
5. Only then assemble `iteratedRmTowerOn_of_solution`.
6. Replace downstream direct assumptions on `IteratedRmTowerOn` only after the
   producer checks.

## Expected blocker

The hard blocker is the commutator/connection-variation API:

```text
partial_t (nabla T)
[Delta, nabla] T
partial_t Gamma = nabla Ric
```

This is a genuine missing analytic/geometric producer, likely substantial but
well-scoped.  The finite-sum norm-square layer should be routine compared with
that commutator layer.

## Verification status

No Lean code was changed in this planning pass.  Verification was not run.

## 2026-06-06 follow-up audit after k = 1 progress

The k = 1 equation route has moved forward.  The following modules now exist and
focused-check:

- `MultiNormHeat.lean`
- `RmRealizationBridge.lean`
- `NablaRiemannCommutator.lean`
- `NablaRiemannTimeDeriv.lean`
- `NablaRiemannCommutatorBound.lean`
- `IteratedNablaRmTower.lean`
- `BernsteinShiSolution.lean`

The key proved pieces are:

- `rm04_ricciIdentityAt`
- `nablaRm04_ricciIdentityAt`
- `iteratedRmComp_one_eq_nablaRm04Field`
- `covDerivStepComp_frameComp_eq`
- `nablaLapComm_orthonormalTrace`
- `iteratedRmComp_one_hasDerivWithinAt`
- `nablaLapCommReactionTerm_eq_covDeriv_curvatureAction_add_curvatureAction`

`#print axioms` for those declarations showed only the usual
`[propext, Classical.choice, Quot.sound]`.

What is still not closed:

- The k = 1 quantitative bound is not proved.
- `BernsteinShiSolution.lean` remains parametric in `IteratedRmTowerOn`.
- `NablaRiemannTimeDeriv.lean` still takes the level-0 time derivative,
  Christoffel time derivative, and time/spatial derivative swap as input shapes;
  concrete solution instantiation is deferred.

The precise current wall is recorded in `NablaRiemannCommutatorBound.lean`: the
slot-swap/commutator decomposition is proved, but bounding it in the required
`C(dim) |Rm| |nabla Rm|` shape runs into four missing framework pieces:

1. The inverse metric is currently a component function, not a bundled `(2,0)`
   tensor in the realization framework, so `nabla gInv = 0` is not directly
   statable there.
2. The field-level identity `rm13 = raise(rm04)` is not available as a usable
   theorem in the `SolutionOn`/`totalNabla0S` layer.
3. There is no `nablaRm13Field` or `TotalNablaRSRealizes` for `S.base.rm13`.
4. The current concrete commutator term is hardwired to `coordinateFrameAt x0`,
   while the norm estimates are stated in an orthonormal-frame convention.

## Next Claude plan: close the k = 1 quantitative producer honestly

### Target

Do not start all-`k` induction yet.  First close the k = 1 producer:

```lean
NablaRm04NormHeatEquationOn
  (D := D) (nablaRm04NormSqInFrame ...)
  nablaRmNormLap nabla2RmNormSq reaction
```

and then feed it to:

```lean
nablaRm04NormHeatBoundOn_of_components
```

with a reaction bound of the form

```text
|reaction| <= C(dim) * sqrt(|Rm|^2) * |nabla Rm|^2
```

This is the prototype needed before any general `k` producer.

### Preferred route

Work below the current coordinate-frame commutator term.  Build the missing
metric-raising and orthonormal-frame API first, then return to the k = 1 bound.

1. Add a pointwise lowering/raising bridge for curvature at the
   `DifferentialGeometry` layer.

   Desired theorem shape:

   ```lean
   rm13_comp_eq_raise_rm04_comp
   nablaRm13_comp_eq_raise_nablaRm04_comp
   ```

   These should be stated at a point, in a basis/frame carrying the metric and
   inverse-metric compatibility needed to raise/lower.  Do not use
   `coordinateFrameAt` orthonormality; it is not available.

2. Add the missing covariant-derivative raising bridge.

   Mathematically this is:

   ```text
   nabla(rm13) = raise(nabla rm04)
   ```

   because the Levi-Civita connection is metric compatible.  If the existing
   `loweredCovDerivAt_eq_lower_tensorCovDerivAt` only covers `(0,2)`, generalize
   it at the tensor layer or add the smallest `(1,3)` specialization.  Do not
   fake this with a new `nablaRm13` assumption in the Ricci-flow file.

3. Move the quantitative reaction estimate to an orthonormal-frame component
   theorem.

   Prove a pure finite-dimensional algebra lemma for an orthonormal basis:

   ```text
   |curvatureAction0SAt rm13 A ...| <= C(card) * |Rm04| * |A|
   ```

   and its covariant-derivative version:

   ```text
   |nabla(curvatureAction rm13 rm04)| <= C(card) * |Rm04| * |nablaRm04|
   ```

   The second one should use the raising bridge for `nabla rm13`; this is where
   the old route got stuck.

4. Only after the orthonormal-frame reaction bound exists, adapt the k = 1
   commutator output.

   The existing theorem

   ```lean
   nablaLapCommReactionTerm_eq_covDeriv_curvatureAction_add_curvatureAction
   ```

   is useful as a decomposition certificate, but it is in the coordinate-frame
   concrete route.  If adapting it to the orthonormal frame is larger than
   expected, stop and state the exact missing frame-change lemma instead of
   forcing a coordinate-frame bound into an orthonormal norm statement.

5. Assemble the k = 1 equation and bound.

   Use:

   - `iteratedRmComp_one_hasDerivWithinAt` for the time derivative side, after
     instantiating its `hrm`, `hchr`, and `hswap` from the concrete solution
     producers;
   - `nablaLapComm_orthonormalTrace` for the spatial commutator;
   - `MultiNormHeat.lean` for the norm-square Bochner algebra;
   - `nablaRm04NormHeatBoundOn_of_components` for the final scalar
     heat-inequality package.

### Stop conditions

Stop and report, without adding assumptions, if any of these is the first
unavailable lemma:

- `(1,3)` lowering/raising parallelism for `rm13`/`rm04`;
- a usable `nabla rm13 = raise(nabla rm04)` bridge;
- an orthonormal-frame component norm comparison for `rm13` vs `rm04`;
- a frame-change theorem from the coordinate-frame commutator term to an
  orthonormal-frame reaction term;
- concrete instantiation of `hrm`, `hchr`, or `hswap` in
  `iteratedRmComp_one_hasDerivWithinAt`.

Classify the failure as a missing tensor API or missing realization bridge, not
as a local k = 1 proof failure.

### Acceptance

- No new `sorry`.
- Focused checks for the touched files pass.
- `#print axioms` on any new public theorem shows only
  `[propext, Classical.choice, Quot.sound]`.
- `BernsteinShiSolution.lean` remains parametric in `IteratedRmTowerOn` until the
  full producer is honestly assembled.

## 2026-06-06 second follow-up: the raising bridge is available; the two walls are isolated

A new file `Evolution/RmRaisingBridge.lean` was added.  It closes step 1 of the
plan (the pointwise `rm13 = raise(rm04)` bridge) and the algebraic core of step 3
(removing `rm13` from the curvature action), and it isolates the two genuine
remaining walls precisely.  All new theorems are sorry-free and `#print axioms`
shows only `[propext, Classical.choice, Quot.sound]`.

### What was proved (`Evolution/RmRaisingBridge.lean`)

* `solution_rm04LowersRm13At` â€” the pointwise lowering relation
  `rm04(X,Y,Z,W) = rm13 (gâ™­ W)(X,Y,Z)` for the **solution** curvatures
  `S.base.rm13`/`S.base.rm04`, at every time and point.  This is
  `rm04LowersRm13At_of_realizes` (`Geometry/Curvature/Components/Lowering.lean`)
  transported through the definitional `S.base.rm13 t = metricRm13 (g t)`,
  `S.base.rm04 t = metricRm04 (g t)`; the two shared connection realizations come
  from `metricCurvData`.
* `rm13_apply_eq_rm04_raise` â€” the **raising bridge**: inverting the lowering with
  the metric sharp map `cotangentSharp_gen` gives, for an *arbitrary* covector `Î²`
  (not only `Î² = gâ™­ W`), `rm13 Î² (X,Y,Z) = rm04 (X,Y,Z, gâ™¯ Î²)`.  Proof: write `Î²`
  as `gâ™­(gâ™¯Î²)` via `cotangentSharp_inner_eval`, then apply the lowering relation.
* `curvatureAction0SAt_eq_rm04_raise` â€” the slotwise curvature action expressed
  purely through the all-lowered `rm04`:
  `curvatureAction0SAt (rm13) Î± X Y slots
     = -Î£_q rm04 (X, Y, slots_q, gâ™¯(freezeSlot Î± slots q))`.
  Every `(1,3)` `rm13` is gone; only `rm04` and the metric raising remain.
* `nablaLapComm_secondTerm_eq_rm04_raise` â€” the **second reaction summand `Tâ‚‚`**
  of `nablaLapCommReactionTerm` (the `(0,5)` curvature action on `âˆ‡Rm`,
  `[âˆ‡_a,âˆ‡_c](âˆ‡_b Rm)`) written as the all-lowered contraction of `S.base.rm04`
  against `nablaRm04Field` (`= âˆ‡rm04`) and the metric raising â€” again with **no**
  `rm13` and, crucially, **no** `âˆ‡rm13`.

### This refutes one of the four footer obstructions of `NablaRiemannCommutatorBound.lean`

Footer obstruction #2 ("`rm13 = raise(rm04)` is not available as a usable
field-level lemma") is **incorrect for the lowering/raising relation itself**: the
pointwise lowering `Rm04LowersRm13At` is proved from the *shared realization of the
connection's curvature* (both `rm13` and `rm04` realize the same
`connectionRiemannCurvatureField`), and inverting it with the metric sharp map is
elementary.  The `lowerAllUpperIndicesEquiv`/`(1,3)`-parallelism formalism named in
the footer is a *different* covariant-derivative formalism and is **not** needed
for the pointwise raise.

### The two genuine remaining walls (precisely localised)

The `k = 1` quantitative reaction bound `|reaction| â‰¤ C(dim)Â·|Rm|Â·|âˆ‡Rm|` is still
not closed.  `nablaLapCommReactionTerm = Tâ‚ + Tâ‚‚` (`NablaRiemannCommutator.lean`),
and the two summands fail for **different**, now-isolated reasons:

1. **Summand `Tâ‚ = âˆ‡_a([âˆ‡_b,âˆ‡_c]Rm)` needs `âˆ‡rm13` â€” the `(1,3)` raising
   parallelism.**  `Tâ‚` is the covariant derivative of the curvature action
   `K = curvatureAction(rm13, rm04)`.  Differentiating the `rm04`-form above
   covariantly gives `âˆ‡(gâ™¯) âˆ— rm04 + gâ™¯ âˆ— âˆ‡rm04`; the `âˆ‡(gâ™¯)` factor is the
   covariant derivative of the metric raising.  The honest statement `âˆ‡(gâ™¯) = 0`
   is the `(1,3)` index-**raising** parallelism, which is **absent**:
   - the proved parallelism `loweredCovDerivAt_eq_lower_tensorCovDerivAt` /
     `..._gen` (`MetricCompatibility/TensorLoweringParallel.lean`,
     `â€¦/TensorConnLapGreenIntertwiner.lean`) is the rank-`(0,s)` **lowering**, and
     its proof carries **no** `âˆ‡g = 0` content (at `r = 0` the lowering map is
     evaluation at the unit `(0,0)`-tensor, whose covariant derivative is `0`);
   - there is **no** `(1,3)` `totalNablaRS` realization for `rm13` (the only
     `totalNabla*` realizations for solution curvature are the lowered
     `nablaRm04Field`/`nabla2Rm04Field`/`nabla3Rm04Field` of
     `RmRealizationBridge.lean`).

   *Exact theorem needed next*, stated at the tensor layer (not the Ricci-flow
   file): a `(1,3)` raising-parallelism

   ```text
   âˆ‡_v (lowerAllUpperIndicesEquiv g 1 3 x).symm (Rm04 x)
     = (lowerAllUpperIndicesEquiv g 1 3 x).symm (âˆ‡_v Rm04 x)
   ```

   i.e. the rank-`(1,3)` analogue of `loweredCovDerivAt_eq_lower_tensorCovDerivAt`,
   which at `r â‰¥ 1` genuinely requires `âˆ‡g = 0` (`nabla_metric_zero`).  It belongs
   in `Geometry/Connection/MetricCompatibility/TensorLoweringParallel.lean`.  The
   `coordinateFrameAt` centre-orthonormality shortcut is invalid: `coordinateFrameAt`
   is the *chart coordinate frame* (`Geometry/Coordinates/CoordinateFrame.lean`
   states it does not make Christoffel symbols vanish), and its
   `InverseMetricOrthonormalAt` is never discharged â€” so the raising cannot be
   trivialised at the centre.

2. **Summand `Tâ‚‚` is `âˆ‡rm13`-free but needs the coordinateâ†’orthonormal frame
   change to match the producer's component norm.**  `nablaLapComm_secondTerm_eq_rm04_raise`
   already writes `Tâ‚‚` through `rm04`/`âˆ‡rm04` with no `rm13`/`âˆ‡rm13`, so its bound
   by `|Rm|Â·|âˆ‡Rm|` does *not* hit wall 1.  But the producer
   (`NablaRm04NormHeatEquationOn` / `nablaRm04NormHeatBoundOn_of_components`,
   `NablaRiemannHeat.lean`) consumes the reaction as `nablaRmReactionInFrame` in an
   **orthonormal** frame (`InverseMetricOrthonormalAt`, `gáµƒáµ‡ = Î´`), while
   `nablaLapCommReactionTerm` is hardwired to `coordinateFrameAt xâ‚€`, which is not
   orthonormal.  `nablaLapComm_orthonormalTrace`'s `horth : gInv = Î´` hypothesis is
   *unsatisfiable* for the coordinate frame's actual inverse metric, so it cannot
   feed the producer.

   *Exact theorem needed next*: a frame-change bridge carrying the intrinsic
   spatial commutator `[Î”, âˆ‡_c] Rm` (or the reaction array contracted against
   `âˆ‡Rm`) from `coordinateFrameAt xâ‚€` to a genuine orthonormal frame at `xâ‚€`, so
   that the producer's `InverseMetricOrthonormalAt` is satisfiable.  This belongs
   in a new orthonormal-frame adapter beside `NablaRiemannCommutator.lean`, not in
   the producer.

### Net

Step 1 (pointwise raise) and the `rm13`-elimination core of step 3 are done and
reusable.  Step 2 (`âˆ‡rm13 = raise(âˆ‡rm04)`) is the **first** stop condition hit and
is a missing **tensor-layer `(1,3)` raising-parallelism** lemma (a realization/
metric-compatibility bridge, not a `k = 1` proof failure).  Independently, even the
`âˆ‡rm13`-free `Tâ‚‚` half is gated by the missing **coordinateâ†’orthonormal frame
change**.  `BernsteinShiSolution.lean` remains parametric in `IteratedRmTowerOn`.

## 2026-06-06 third follow-up: Step A (the `(1,3)` raising-parallelism) is itself the wall

This pass took the dedicated task of proving the rank-`(1,3)` raising-parallelism
lemma (Step A above) **as a self-contained tensor-layer lemma** in
`Geometry/Connection/MetricCompatibility/TensorLoweringParallel.lean`, then closing
the `Tâ‚` summand from it.  After a full read of the lowering template, the
`lowerAllUpperIndices` definition, both `nabla_metric_zero` sites, and the two
covariant-derivative formalisms in play, the conclusion is that **Step A hits the
task's first stop condition** ("`nabla_metric_zero` at `r â‰¥ 1` is insufficient â€¦
needs a missing chain/product rule").  No Lean code was changed; fabricating a
renamed/axiomatized parallelism is forbidden by the task's honesty constraints.

### Why Step A is blocked (the precise missing ingredient)

The target is the rank-`(1,3)` lowering intertwiner
`âˆ‡(lower_{1,3} S) = lower_{1,3}(âˆ‡^{RS} S)` (equivalently the `.symm`/raising form
stated in the task), the `r â‰¥ 1` analogue of
`loweredCovDerivAt_eq_lower_tensorCovDerivAt[_gen]`
(`MetricCompatibility/TensorLoweringParallel.lean`,
`â€¦/TensorConnLapGreenIntertwiner.lean`).

* The template proof carries **no** `âˆ‡g = 0` content: at `r = 0` the lowering map is
  *evaluation at the unit `(0,0)`-tensor*, whose `tensor0SCovariantDerivative` is
  `0` (`tensor0SCovariantDerivative_unitZero_eq_zero`).  That is the entire reason
  it generalises in `s` (only a `Nat.zero_add` transport), and it is exactly why it
  does **not** generalise in `r`.
* For `r â‰¥ 1`, `lowerAllUpperIndices g r s x T` contracts `T`'s `r` upper slots
  against `r` metric factors: `lowerAllUpperIndices_apply` gives
  `T (separableFormAt g x r (vâˆ˜castAdd)) (vâˆ˜natAdd)`, and `separableFormAt_apply`
  shows `separableFormAt = âˆáµ¢ g.inner x (váµ¢) (Â·)` â€” a genuine product of `r` Gram
  factors.  Proving `âˆ‡(lower S) = lower(âˆ‡S)` therefore requires differentiating this
  metric contraction and killing the `r` `âˆ‡g`-factor terms via metric compatibility.
* That step needs a **general covariant product/contraction Leibniz rule** for
  `tensor0SCovariantDerivative s` (or `nabla0SFun s`) over the `separableFormAt`
  metric contraction at arbitrary rank.  **No such rule exists in the tree.**  The
  only covariant product rules present are `nabla_smul_metric`
  (`Tensor/RSTensor/MetricCompatibility.lean`, the scalar-multiple `âˆ‡(fÂ·g)=dfâŠ—g`,
  `r = 0`) and `nabla0SFun_one_eval_of_coordFrame_product*`
  (`Geometry/Connection/Chart/NablaComponents/OneForm.lean`, rank-1 one-forms in
  coordinate-frame moving-slot form).  There is no `âˆ‡(tensor product)`, no
  `âˆ‡(separableFormAt) = 0`, no `(0,2r)` "metric-power" section with `âˆ‡ = 0`, and no
  `(r,s)` lowering intertwiner for `r â‰¥ 1` anywhere.
* `nabla_metric_zero` **is** available â€” `Tensor/RSTensor/MetricCompatibility.lean`
  (and `Geometry/.../MetricCompatibility.lean` supplies the underlying
  `IsMetricCompatible_gen`), dischargeable for `LeviCivita g` via
  `LeviCivita_isMetricCompatible` â€” but it lives in the `nabla0SFun` formalism and is
  *insufficient on its own*: there is no rule to thread `âˆ‡g = 0` through the rank-`r`
  metric contraction.  The cross-formalism bridge
  `tensor0SCovariantDerivative_eq_tensorRSCovariantDerivative`
  (`ChartTensorNabla/Agreement/Tensor0SRSCovariantDerivativeAgreement.lean`) is
  `(0,s) â†” (r=0,s)` **only**, so it does not transport a lowering Leibniz to
  `r â‰¥ 1`.

### The inner-product route is circular (checked, not assumed)

`TensorRSMetricCompatible.lean` proves the `(r,s)` inner-product compatibility
`âˆ‡âŸ¨W,SâŸ© = âŸ¨âˆ‡W,SâŸ© + âŸ¨W,âˆ‡SâŸ©`, but with `loweredCovDerivAt` (= `âˆ‡` of the *lowered*
section) on **both** sides â€” i.e. it is the lowered-picture statement, not the
genuine `(1,3)` `tensorRSCovariantDerivative`.  Pairing `âˆ‡(lower S)` and
`lower(âˆ‡^{RS} S)` against all `(0,4)` test tensors `lower Y` via the nondegenerate
`(0,4)` inner product reduces Step A to the **genuine `(1,3)` inner-product
compatibility** `âˆ‡âŸ¨S,YâŸ© = âŸ¨âˆ‡^{RS}S,YâŸ© + âŸ¨S,âˆ‡^{RS}YâŸ©` (with
`tensorRSCovariantDerivative`), which is inter-derivable with Step A and is **equally
absent** from the tree (searched: no `tensorRSCovariantDerivative`-based inner-product
compatibility exists).  So every route converges on the same missing ingredient:
the general covariant contraction-Leibniz / `âˆ‡(separableForm)=0`.

### `Tâ‚` (Step B) is independently blocked, and Step A would not unblock it

The `Tâ‚` work the task describes is **already proved**, sorry-free, in
`Evolution/NablaRiemannCommutatorBound.lean`:
`nablaLapComm_T1_eq_covDeriv_curvatureAction` shows
`Tâ‚ = âˆ‡Â³Rm(a,b,c) âˆ’ âˆ‡Â³Rm(a,c,b) = âˆ‡_a K`, the covariant derivative of the
curvature-action field `K = [âˆ‡_b,âˆ‡_c]Rm = curvatureAction0SAt (rm13 Â·)(Rm04 Â·)`, in
explicit `eval_C1_slots` form; and
`nablaLapCommReactionTerm_eq_covDeriv_curvatureAction_add_curvatureAction` packages
the whole reaction as `âˆ‡(Rmâˆ—Rm) + Rmâˆ—âˆ‡Rm`.  The remaining `|Tâ‚| â‰¤ CÂ·|Rm|Â·|âˆ‡Rm|`
bound is blocked because differentiating `curvatureAction0SAt (rm13 Â·)(Rm04 Â·)`
covariantly needs `âˆ‡rm13 âˆ— Rm04 + rm13 âˆ— âˆ‡Rm04`, and in the **`totalNabla0S`
solution formalism** of `Tâ‚`:
  (a) there is no contraction-Leibniz for `totalNabla0S`;
  (b) `âˆ‡rm13` has **no** `totalNablaRS` realization for `S.base.rm13` (the only
      solution-curvature realizations are the lowered
      `nablaRm04Field`/`nabla2Rm04Field`/`nabla3Rm04Field`); and
  (c) Step A's parallelism â€” even if proved â€” lives in the *different*
      `tensorRSCovariantDerivative`/`lowerAllUpperIndicesEquiv` formalism, with **no**
      bridge to `totalNabla0S` at `r â‰¥ 1`.
Hence even a completed Step A would not close `Tâ‚`: this is precisely the task's
**second** stop condition ("the covariant Leibniz on the curvature-action
contraction needs an unavailable lemma even with Step A"), and it matches the
four-gap frontier independently reached by three prior agents (see
`DimensionThree/HamiltonPositiveRicci.md`, gaps 2â€“3).

### Exact theorems needed next (unchanged frontier, now localised to a Leibniz)

1. A **general covariant product/contraction Leibniz** for `nabla0SFun s` /
   `tensor0SCovariantDerivative s` (minimally, `âˆ‡(separableFormAt g r) = 0` and a
   contraction rule), from which the `(r,s)` lowering intertwiner
   `âˆ‡(lower_{r,s} S) = lower_{r,s}(âˆ‡^{RS} S)` follows by the same
   `nabla0SFun_eval_smooth_slots` + `nabla_metric_eval` cancellation that proves
   `nabla_metric_zero`/`nabla_smul_metric`.  Belongs at the tensor layer
   (`Tensor/RSTensor/â€¦` or `Connection/MetricCompatibility/â€¦`).
2. A `totalNabla*RS` realization `nablaRm13Field` for `S.base.rm13` (gap 3), plus the
   `nabla0SFun â†” totalNabla0S`/`tensorRSCovariantDerivative` bridge at `r â‰¥ 1`, to
   even *state* the contraction-Leibniz for `curvatureAction0SAt (rm13 Â·)(Rm04 Â·)` on
   the solution side.

Neither is a single lemma; both are framework-scale (the "RmRealizationBridge-style
frontier" already flagged).  Per the task, this precise wall is the deliverable.
`BernsteinShiSolution.lean` remains parametric in `IteratedRmTowerOn`; no `sorry`,
no axiomatized parallelism, no Lean changes were made this pass.

## 2026-06-06 fourth follow-up: the coordinateâ†’orthonormal frame-change adapter is BUILT (obstruction #4 removed)

This pass took the dedicated task of the **coordinateâ†’orthonormal frame-change
adapter** â€” the *second* of the two isolated walls (the `Tâ‚‚`-half / footer
obstruction #4 / fourth stop condition "no frame-change bridge from
`coordinateFrameAt` to an orthonormal frame").  It is now **closed, sorry-free**, in
a new file `Evolution/NablaRiemannOrthoFrame.lean`.  `#print axioms` on every public
theorem is `[propext, Classical.choice, Quot.sound]`.

### Route decision (the three routes scoped before building)

* **(a) orthonormalise at the centre â€” CHOSEN, viable.**  The spatial commutator
  lemmas of `NablaRiemannCommutator.lean` are derived **purely** from the *frame-free*
  `(0, s)` Ricci identities `rm04_ricciIdentityAt` / `nablaRm04_ricciIdentityAt`
  (arbitrary tangent vectors at a point); `coordinateFrameAt xâ‚€` enters only as the
  *choice* of tangent vectors fed to the bundled `âˆ‡Â³Rm = nabla3Rm04Field`, evaluated
  **only at `xâ‚€`**.  So the whole commutator is frame-generic with **zero** new
  mathematical content and needs only a *basis at `xâ‚€`* (no smooth/global frame).
* **(b) general-`gInv` producer bound â€” NOT cheaper, rejected.**  Removing the
  producer's `horth` and re-deriving `|reaction| â‰¤ C|Rm||âˆ‡Rm|` for a general `gInv`
  needs the fibre-norm â†” component-norm bridge in an orthonormal frame
  (`Curvature/FiberNormParseval/*`, `normSq0S_identity_eq_sum_sq` needs
  `identityInvMetric`); the Cauchyâ€“Schwarz core of `NablaRiemannHeat.lean`
  (`abs_nablaRmReactionDown_le`) is hardwired to `compNormSq*` (plain component sums),
  so general `gInv` requires re-deriving substantial norm machinery â€” exactly footer
  obstruction #4 restated, not a shortcut.
* **(c) normal coordinates â€” not needed.**  Route (a) supersedes it; a normal-coord
  realization with `g(centre)=Î´` is also absent in the solution layer.

### What was proved (`Evolution/NablaRiemannOrthoFrame.lean`, all sorry-free)

* `nablaLapCommF_pointwise` / `nablaLapCommF_trace` / `nablaLapCommF_orthonormalTrace`
  â€” the spatial commutator `[Î”, âˆ‡_c] Rm = reaction` over an **arbitrary** index type
  `Idx` and frame `frame : Idx â†’ (x : M) â†’ TangentSpace I x` (the genuine reusable
  abstraction of the `coordinateFrameAt` lemmas; identical one-line Ricci-identity
  proofs).  Generic defs `nabla3InnerSlotsF`, `nabla3FrameTupleF`,
  `nablaLapCommReactionTermF`, `roughLapNablaRmCompF`, `nablaRoughLapRmCompF`.
* `exists_orthoFrameAt` â€” a pointwise **`g`-orthonormal frame of `T_{xâ‚€}M`** from the
  *fibre* metric `g xâ‚€ = S.family.metric t`, with **no** model `[InnerProductSpace â„ E]`.
  Built by the chart-locality-free `letI â€¦ ofCore` Gramâ€“Schmidt
  (`g.toRiemannianMetric.toCore xâ‚€`, `RiemannianMetric.toCore`/`.continuousAt`/
  `.isVonNBounded` from `Mathlib/Topology/VectorBundle/Riemannian.lean`, which need
  only a normed model fibre) + `stdOrthonormalBasis`.  This is the technique of
  `exists_orthonormal_frame_riemannianFiberNormSq`
  (`Analysis/Elliptic/â€¦/RiemannianFiberNormSqRiemannOpVWFactorBound.lean`), replicated
  directly to avoid that file's *spurious* `[InnerProductSpace â„ E]` section variable.
* `deltaInvMetric_orthonormal` â€” the **honest** `InverseMetricOrthonormalAt` witness:
  the constant Kronecker delta `deltaInvMetric` is the *genuine* inverse metric of the
  `g`-orthonormal frame (for a `g`-orthonormal basis `gáµƒáµ‡ = Î´`), **not** an assumption
  about `coordinateFrameAt`.
* `nablaLapComm_orthoFrame` â€” the **assembled adapter**: at `xâ‚€`, for a solution at a
  regular time, there exist a `g xâ‚€`-orthonormal frame and the delta inverse metric
  such that `InverseMetricOrthonormalAt deltaInvMetric t xâ‚€` holds **honestly** and the
  spatial commutator collapses to the diagonal trace
  `Î”(âˆ‡Rm)(c) âˆ’ âˆ‡(Î”Rm)(c) = Î£_a reaction a a c m` â€” exactly the orthonormal shape the
  producer (`nablaRm04NormHeatBoundOn_of_components`, via `(âˆ‚â‚œ âˆ’ Î”)âˆ‡Rm`) consumes.

### Why this is the honest replacement for `nablaLapComm_orthonormalTrace`

`nablaLapComm_orthonormalTrace` (`NablaRiemannCommutator.lean`) carries `horth :
gInv = Î´` but is hardwired to `coordinateFrameAt xâ‚€`, whose true inverse metric is
**not** `Î´`; so its `roughLapNablaRmComp (coordinateFrameAt) Î´` is *not* the rough
Laplacian and the `horth` is unsatisfiable for the real inverse metric.  The adapter
replaces the chart frame by a **genuinely `g`-orthonormal** frame, where `gáµƒáµ‡ = Î´` is
the *true* inverse metric, so the diagonal trace really is `Î” = gáµƒáµ‡ âˆ‡â‚âˆ‡áµ¦`.  The
producer is **not** weakened: `coordinateFrameAt` is never asserted orthonormal.

### Net (the two walls after this pass)

* **Obstruction #4 (frame change) â€” RESOLVED.**  The `âˆ‡rm13`-free `Tâ‚‚` half, and
  indeed the *whole* spatial commutator, is now available in the producer's
  orthonormal convention with a genuine `gáµƒáµ‡ = Î´`.  This was the precise
  "frame-change bridge â€¦ so that the producer's `InverseMetricOrthonormalAt` is
  satisfiable" the prior follow-up named as the next theorem for `Tâ‚‚`.
* **Obstruction #1 (the `(1,3)` raising-parallelism for `Tâ‚`) â€” UNCHANGED, separate.**
  The quantitative bound `|reaction| â‰¤ C(dim)Â·|Rm|Â·|âˆ‡Rm|` is still gated by the
  `Tâ‚` summand's `âˆ‡(raise rm04) = raise(âˆ‡ rm04)` (Step A above, the general covariant
  contraction-Leibniz / `âˆ‡(separableForm)=0` in
  `Geometry/Connection/MetricCompatibility/TensorLoweringParallel.lean`), which is
  *orthogonal* to the frame change and remains the genuinely missing tensor API.

`BernsteinShiSolution.lean` remains parametric in `IteratedRmTowerOn`.  Files added:
`Evolution/NablaRiemannOrthoFrame.lean` (no existing file edited).  Focused
`lake-locked build` of the new module: EXIT 0.

## 2026-06-06 fifth follow-up: Step A's contraction-Leibniz is BUILT (the prior "Step A is the wall" verdict is refuted); Tâ‚'s bound is the second stop condition

This pass took the dedicated task of **Step A** â€” the general covariant
contraction-Leibniz at the tensor layer â€” and **closed its core**, sorry-free and
axiom-clean, in a new file `Tensor/RSTensor/ContractionLeibniz.lean`.  This directly
**refutes the third follow-up's conclusion** that "Step A is itself the wall": the
`nabla0SFun` tensor-product/contraction Leibniz **is** assemblable from
`nabla0SFun_eval_smooth_slots` + `nabla_metric_zero`, by the same concrete-evaluation
technique that proves `nabla_smul_metric`.

### What was proved (`Tensor/RSTensor/ContractionLeibniz.lean`, all sorry-free)

* `nabla0SFun_product_eval` â€” the **evaluated tensor-product Leibniz**
  `âˆ‡(A âŠ— B)(V) = âˆ‡A(X :: Vâˆ˜castAdd)Â·B(Vâˆ˜natAdd) + A(Vâˆ˜castAdd)Â·âˆ‡B(X :: Vâˆ˜natAdd)`,
  for smooth `(0,s)`/`(0,q)` fields `A`/`B` with realized derivatives, from
  `nabla0SFun_eval_smooth_slots`, `product_fun_apply`, and the scalar product rule.
* `nabla_product_zero_of_zero` â€” the tensor product of two `âˆ‡`-parallel tensors is
  parallel (`âˆ‡(A âŠ— B) = 0` when `âˆ‡A = âˆ‡B = 0`).
* `metricPow g r` â€” the `(0,2r)` metric power `g^{âŠ—r}` (the (0,2r) "metric-power
  section" each upper slot of an `(r,s)`-tensor is lowered against).
* `nabla_metricPow_zero` â€” `âˆ‡(g^{âŠ—r}) = 0` for a metric-compatible connection, by
  induction from `nabla_metric_zero` and `nabla_product_zero_of_zero`.  This is
  **Step A.1**.
* `nabla0SFun_metricPow_contraction_eval` â€” **Step A.2** in the reachable formalism:
  the contraction-against-the-metric-power Leibniz `âˆ‡(A âŠ— g^{âŠ—r}) = âˆ‡A âŠ— g^{âŠ—r}`
  (the metric factor passes through `âˆ‡` untouched).

`#print axioms` on all five (plus the helper `tensor0SField_product_apply`) is
`[propext, Classical.choice, Quot.sound]`.  Focused `lake-locked build`: EXIT 0.

### Why this is the genuine Step A primitive, and where it stops

The prior agent conflated **Step A.1/A.2 in the `nabla0SFun` formalism** (now proved)
with **Step A.3 stated in the `tensorRSCovariantDerivative`/`lowerAllUpperIndicesEquiv`
formalism** (still blocked).  The two are *different covariant-derivative
formalisms*:

* `nabla0SFun` (= `mcovariantDeriv_tensor0SFromConnection`, the concrete eval) â€” where
  `nabla_metric_zero`, `nabla_smul_metric`, the new product-Leibniz, and **all the
  solution curvature fields** `nablaRm04Field`/`nabla2Rm04Field`/`nabla3Rm04Field` (via
  `totalNabla0S`) live;
* `tensor0SCovariantDerivative` (the recursive Hom-bundle, base = `extDerivFun`, succ =
  curry/uncurry) â€” where `loweredCovDerivAt` and hence the **A.3 statement**
  `âˆ‡(lower S) = lower(âˆ‡^{RS} S)` live.

There is **no `nabla0SFun â†” tensor0SCovariantDerivative` agreement at rank `r â‰¥ 1`**
(the only bridge, `tensor0SCovariantDerivative_eq_tensorRSCovariantDerivative`, is
`(0,s) â†” (r=0,s)`).  So Step A.1/A.2 in `nabla0SFun` do **not** transport to the A.3
statement in the lowering formalism.  A.3 as literally stated is gated by that
missing rank-`â‰¥1` agreement â€” **not** by the contraction-Leibniz, which is done.

### Tâ‚'s bound is the second stop condition (now sharply localised)

`Tâ‚ = âˆ‡_a([âˆ‡_b,âˆ‡_c]Rm) = âˆ‡_a K`, `K = curvatureAction0SAt (rm13 Â·)(Rm04 Â·)`.  The
reduction `Tâ‚ = âˆ‡_a K` is re-exported as `nablaLapComm_T1_eq_covDerivK`
(`Evolution/NablaRiemannT1Bound.lean`, axiom-clean), thin over
`nablaLapComm_T1_eq_covDeriv_curvatureAction`.  The bound `|Tâ‚| â‰¤ CÂ·|Rm|Â·|âˆ‡Rm|`
needs `âˆ‡K` as a `âˆ‡Rm âˆ— Rm + Rm âˆ— âˆ‡Rm` contraction; after Step A this reduces to a
sharply-isolated residual (recorded in full in the header of
`Evolution/NablaRiemannT1Bound.lean`):

1. **`(1,3)` route:** `âˆ‡rm13` has no `totalNabla*RS` realization for `S.base.rm13`,
   and Step A's `nabla0SFun` product-Leibniz covers `(0,s) âŠ— (0,q)` **products**, not
   the `Hom`-**contraction** of the `(1,3)` `rm13`.  Identifying `âˆ‡rm13 = raise(âˆ‡Rm04)`
   is A.3 â€” gated by the missing `nabla0SFun â†” tensor0SCovariantDerivative` rank-`â‰¥1`
   agreement above.
2. **Raise-form route (avoids `âˆ‡rm13`):** `curvatureAction0SAt_eq_rm04_raise`
   (`RmRaisingBridge.lean`) gives `K = -Î£_q rm04(â€¦, gâ™¯ Î²q)` using **only** the realized
   `Rm04` and the metric raising `gâ™¯`.  Differentiating it via
   `nabla0SFun_eval_smooth_slots` for `nablaRm04Field` needs (a) the **sharp-parallelism**
   `âˆ‡(gâ™¯ Î²) = gâ™¯(âˆ‡Î²)` â€” proved for one-forms in `Tensor0SRiemannian/Smooth.lean`
   (`cotangentSharp_cov_eq_sharp_curry_of_mdiffAt`) but **`private`**; and (b) a
   **frozen-slot covariant Leibniz** `âˆ‡(oneFormAtSlot0S Rm04 slots q)` in terms of
   `âˆ‡Rm04` â€” **absent**.  This route is the most promising and needs only (a) exposed +
   (b) built; it does **not** hit the `âˆ‡rm13` wall.
3. **Frame reconciliation:** `Tâ‚ = âˆ‡_a K` is proved at the **smooth** `coordinateFrameAt xâ‚€`
   (differentiation needs a smooth frame), but the bound must be in the
   **`g`-orthonormal** frame of `exists_orthoFrameAt`, which is only *pointwise*
   orthonormal at `xâ‚€` (a constant transport off-centre).  Reconciling the two is a
   third, separate piece.

This is the task's **second stop condition** ("closing Tâ‚ needs a `nabla0SFun â†”
totalNabla0S`/`tensorRS` formalism bridge at `r â‰¥ 1` that is absent"), reached *after*
Step A's contraction-Leibniz, exactly as the task anticipated.  `Tâ‚‚` (the bare
curvature action, no curvature derivative) is unaffected and is closed in
`Evolution/NablaRiemannT2Bound.lean`.

### Net

* **Step A.1/A.2 (the `nabla0SFun` contraction-Leibniz + `âˆ‡(g^{âŠ—r}) = 0`) â€” DONE**,
  refuting the prior "Step A is the wall".  Reusable tensor-layer primitives.
* **Step A.3 (the `(1,3)` raising-parallelism *as stated* in the lowering formalism)
  and Step B (`|Tâ‚| â‰¤ CÂ·|Rm|Â·|âˆ‡Rm|`) â€” second stop condition**, localised to: the
  missing `nabla0SFun â†” tensor0SCovariantDerivative` rank-`â‰¥1` agreement (route 1) /
  a public sharp-parallelism + frozen-slot Leibniz (route 2), plus the smoothâ†”orthonormal
  frame reconciliation (route 3).

Files added: `Tensor/RSTensor/ContractionLeibniz.lean`,
`Evolution/NablaRiemannT1Bound.lean` (no existing file edited).  Focused
`lake-locked build` of both: EXIT 0.  `BernsteinShiSolution.lean` remains parametric
in `IteratedRmTowerOn`.

## 2026-06-06 sixth follow-up: the `Tâ‚‚` quantitative bound is BUILT (`|Tâ‚‚| â‰¤ C(card)Â·|Rm|Â·|âˆ‡Rm|`)

This pass took the dedicated `Tâ‚‚` task â€” the bound on the **second** reaction summand
`Tâ‚‚ = curvatureAction0SAt rm13 (âˆ‡Rm) (frame a)(frame c)(slots)` (the bare `(0,5)`
curvature commutator `[âˆ‡_a,âˆ‡_c](âˆ‡_b Rm)`, **no** curvature derivative).  It is now
**closed, sorry-free, axiom-clean** in a new file `Evolution/NablaRiemannT2Bound.lean`.
`#print axioms` on every public theorem is `[propext, Classical.choice, Quot.sound]`.

### The route (no missing tensor-norm lemma â€” neither stop condition is hit)

The task's two stop conditions were (i) the curvature-action fibre-norm â†”
frame-component-norm bridge needing a missing tensor-norm lemma, and (ii) `|rm13| â‰¤
C|Rm04|` needing a missing raising-norm comparison.  **Both are avoided** by *not*
working in fibre norms at all and *not* comparing `|rm13|` to `|Rm04|` as norms.
Instead the curvature action is rewritten as a **plain frame-index component
contraction** before any norm is taken:

1. `curvatureAction0SAt rm13 Î± (e_a)(e_c)(slots) = -âˆ‘_q rm13 (Î²_q)(vec3 e_a e_c slots_q)`
   (definition), `Î²_q = oneFormAtSlot0S Î± slots q`;
2. the pointwise **raising bridge** `rm13_apply_eq_rm04_raise` (`RmRaisingBridge.lean`)
   rewrites each pairing as `rm13 (Î²_q)(vec3 â€¦) = rm04(e_a, e_c, slots_q, gâ™¯ Î²_q)`;
3. in a `g`-orthonormal **basis**, `cotangentSharp_eq_sum_inv_gen` (specialised to
   `gáµƒáµ‡ = Î´` via `MetricInverseInBasis_gen`, immediate from orthonormality) gives the
   simple orthonormal reconstruction `gâ™¯ Î²_q = âˆ‘_e (Î²_q e_e) â€¢ e_e`, and multilinearity
   of `rm04` in its last slot (`MultilinearMap.map_update_sum`) pushes it through:
   `rm04(e_a,e_c,slots_q, gâ™¯ Î²_q) = âˆ‘_e (Î±(update slots q e_e)) Â· rm04(e_a,e_c,slots_q,e_e)`.

After step 3 **every factor is a plain frame component** â€” `rm04(eáµ¢,eâ±¼,eâ‚–,e_l)` (a
`compNormSq4` entry) and `Î±(eâ€¦)` (a `compNormSqMulti` entry); the metric raising is
gone, so there is **no** raising-norm comparison to supply, refuting stop condition
(ii).  Cauchyâ€“Schwarz over the `(q,e)` index pair (`sÂ·card` terms, here `5Â·card`),
with the per-entry domination `abs_le_sqrt_compNormSq4`/`abs_le_sqrt_compNormSqMulti`,
gives the bound directly in the producer's component norms, refuting stop condition (i).

### What was proved (`Evolution/NablaRiemannT2Bound.lean`, all sorry-free, axiom-clean)

* `curvatureAction0SAt_orthoBasis_eq_sum` â€” the curvature action on basis vectors as
  the plain double sum `-âˆ‘_q âˆ‘_e Î±(update sidx q e) Â· rm04(e_a,e_c,e_{sidx q},e_e)`
  (raising bridge + orthonormal `gâ™¯` reconstruction + last-slot multilinearity).
* `abs_curvatureAction0SAt_orthoBasis_le` â€” **the abstract point-level bound**: for any
  `Module.Basis`, `g`-orthonormality, and lowering relation `Rm04LowersRm13At`,
  `|curvatureAction0SAt rm13 Î± (basis a)(basis c)(basisâˆ˜sidx)|
     â‰¤ s Â· card Â· âˆš(compNormSq4 R) Â· âˆš(compNormSqMulti A)`,
  with `R i j k l = rm04(eáµ¢,eâ±¼,eâ‚–,e_l)`, `A idx = Î±(eâˆ˜idx)`.  The honest constant is
  `s Â· card` (the genuine number of contraction terms), not a forced `cardÂ²`.
* `exists_orthoBasisFrameAt` â€” a `g`-orthonormal frame of `T_{xâ‚€}M` whose **centre
  values are a `Module.Basis`** (the `exists_orthoFrameAt` `letI â€¦ ofCore` Gramâ€“Schmidt,
  additionally exposing `stdOrthonormalBasis.toBasis` and `frame i xâ‚€ = basis i`).
* `compNormSqMulti_eq_compNormSq5` â€” the reindexing `âˆ‘_{idx:Fin 5â†’Idx}(A idx)Â²
  = âˆ‘_{m a b c d}(A ![m,a,b,c,d])Â²` (iterated `Fin.consEquiv`), the bridge from the
  rank-uniform `compNormSqMulti` to the producer's nested `compNormSq5` /
  `nablaRm04NormSqInFrame_eq_compNormSq5`.
* `abs_nablaLapComm_T2_orthoBasis_le` â€” the **solution-facing `Tâ‚‚` bound** in plain
  component norms, instantiating the abstract bound at `S.base.rm13`/`nablaRm04Field`
  with `solution_rm04LowersRm13At`, slot tuple `Fin.cons b m`.
* `abs_nablaLapComm_T2_orthoFrame_le` â€” **the assembled `Tâ‚‚` bound** in the producer's
  convention: at `xâ‚€` there exist a genuine `g`-orthonormal frame and the Kronecker-delta
  inverse metric with `InverseMetricOrthonormalAt` holding **honestly**, such that
  `|Tâ‚‚| â‰¤ 5 Â· card Â· âˆš(rm04NormSqInFrame) Â· âˆš(compNormSqMulti of frame âˆ‡Rm)`,
  i.e. `|Tâ‚‚| â‰¤ C(card)Â·|Rm|Â·|âˆ‡Rm|` with the `Rm`-factor in the producer's
  `rm04NormSqInFrame` (via `rm04NormSqInFrame_eq_compNormSq4`) and the `âˆ‡Rm`-factor in
  the plain `compNormSqMulti` (chainable to `nablaRm04NormSqInFrame` through
  `compNormSqMulti_eq_compNormSq5` + `nablaRm04NormSqInFrame_eq_compNormSq5`).

### Why the `Tâ‚‚` frame issue (route-3 of the fifth follow-up) does not arise

The fifth follow-up's "smoothâ†”orthonormal frame reconciliation" (route 3) is a
**`Tâ‚`-only** problem: `Tâ‚ = âˆ‡_a K` must be *differentiated*, which needs a smooth
frame, clashing with the pointwise-at-`xâ‚€` orthonormal frame.  `Tâ‚‚` is a **bare**
curvature action (no differentiation), evaluated only at `xâ‚€` on basis vectors, so the
*pointwise* `g`-orthonormal basis of `exists_orthoBasisFrameAt` is exactly sufficient â€”
no smooth global frame is needed, and the bound lands directly in the producer's
orthonormal convention.

### Net (the frontier after this pass)

* **`Tâ‚‚` quantitative bound â€” DONE.**  `|Tâ‚‚| â‰¤ C(card)Â·|Rm|Â·|âˆ‡Rm|` in the genuine
  orthonormal frame's component norms, sorry-free and axiom-clean.  Neither task stop
  condition was hit: the fibre-norm/component-norm bridge was *bypassed* (the action is
  a component contraction *before* norming), and the `|rm13|`-vs-`|Rm04|` comparison is
  *unnecessary* (the raising `gâ™¯` is eliminated into the contraction).
* **`Tâ‚` quantitative bound â€” UNCHANGED, separate (fifth follow-up's second stop
  condition).**  Still gated by the missing `nabla0SFun â†” tensor0SCovariantDerivative`
  rank-`â‰¥1` agreement / public sharp-parallelism + frozen-slot Leibniz, plus the
  smoothâ†”orthonormal frame reconciliation â€” all orthogonal to `Tâ‚‚`.

Files added: `Evolution/NablaRiemannT2Bound.lean` (no existing file edited).  Focused
`lake-locked build` of the new module: EXIT 0.  `BernsteinShiSolution.lean` remains
parametric in `IteratedRmTowerOn`.

## 2026-06-06 seventh follow-up: the `Tâ‚` route is UNBLOCKED (prior "frozen-slot Leibniz absent" verdict refuted); sharp-parallelism exposed

This pass took the dedicated `Tâ‚` quantitative-bound task (`|Tâ‚| â‰¤ CÂ·|Rm|Â·|âˆ‡Rm|`,
the **first** reaction summand `âˆ‡_a([âˆ‡_b,âˆ‡_c]Rm) = âˆ‡_a(Rm âˆ— Rm)`).  After tracing
the only `âˆ‡rm13`-free route (route 2, the `gâ™¯` raise form
`curvatureAction0SAt_eq_rm04_raise`) end-to-end against the existing tree, the
finding is that **the route is not blocked** â€” every tool it needs already exists â€”
and the prior follow-ups' verdict that the **frozen-slot covariant Leibniz is
absent** is **incorrect**.  One verified, minimal unblocking change was made; the
full assembly is large and was not completed this pass (it would have required new
`sorry`s, forbidden).

### The route, with every tool now located (correcting the prior reports)

`Tâ‚ = âˆ‡_a K`, `K = curvatureAction0SAt (rm13)(Rm04)` (`nablaLapComm_T1_eq_covDerivK`).
Route 2 writes `K = -Î£_q rm04(X, Y, slots_q, gâ™¯ Î²q)` with `Î²q = oneFormAtSlot0S Rm04
slots q` (`RmRaisingBridge.curvatureAction0SAt_eq_rm04_raise`), **no** `rm13`.
Differentiating it covariantly:

1. **Sharp-parallelism `âˆ‡(gâ™¯ Î²) = gâ™¯(âˆ‡Î²)`** â€” `cotangentSharp_cov_eq_sharp_curry_of_mdiffAt`
   (`Tensor/RSTensor/Tensor0SRiemannian/Smooth.lean`).  It was `private`; **this pass
   made it public** (the precise content the fifth follow-up's route-2(a) and the task's
   third stop condition flagged as "private, not citable").  Axiom-clean
   (`#print axioms` = `[propext, Classical.choice, Quot.sound]`), focused build EXIT 0.
2. **Frozen-slot covariant Leibniz `âˆ‡(oneFormAtSlot0S Rm04 slots q)` â†¦ frozen slot of
   `nablaRm04Field`** â€” declared "absent" by the second/third/fifth follow-ups, but its
   exact template is **`middleFreezeNabla`** (`Tensor/RSTensor/MetricTrace/Higher.lean`):
   it differentiates a slot-frozen `(0,4)` field and rewrites the derivative through
   `nablaA` by choosing the frozen-slot sections **covariantly constant at `xâ‚€`** via
   `TensorLieDeriv.exists_cov_zero_at_apply`
   (`Tensor/RSTensor/NablaOnTensors/Connection/OneJet.lean`), so all frozen-slot
   Christoffel corrections vanish.  The frozen one-form field itself is built like
   `freezeMiddle04Field` (`Tensor/RSTensor/MetricTrace/NablaTrace02.lean`).  The
   freeze/`âˆ‡` machinery is present and reusable â€” not absent.
3. **Smoothness of the sharp field `p â†¦ gâ™¯ (Î²q p)`** (the `MDiffAt` hypothesis of
   the sharp-parallelism) â€” `metricSharp_contMDiff_total`
   (`Geometry/Operator/MetricSharpSmooth.lean`), from chart-basis component
   smoothness of `Î²q` (a frozen evaluation of the smooth `Rm04` against smooth frame
   fields).  Needs a `metricSharp â†” cotangentSharp_gen` identification at the
   component level.
4. **Frame reconciliation (smooth `coordinateFrameAt` â†¦ pointwise orthonormal)** â€”
   **not a wall**: `âˆ‡_a K` is a genuine tensor value at `xâ‚€` (`nabla3Rm04Field`
   antisymmetrised), so bounding it on orthonormal-frame vectors realises *those*
   vectors by cov-zero sections (`exists_cov_zero_at_apply`) and applies the same
   Leibniz at `xâ‚€`; no smooth orthonormal field is needed.
5. **Final estimate** â€” the two resulting `Rm04 âˆ— âˆ‡Rm04` raise-contraction summands
   are evaluated in the orthonormal basis at `xâ‚€` (where `gâ™¯ Î² = Î£_e (Î² e_e) e_e`,
   `cotangentSharp_orthoBasis_expand`) and bounded by the **exact Cauchyâ€“Schwarz of
   `NablaRiemannT2Bound.lean`** (`abs_le_sqrt_compNormSq4`/`abs_le_sqrt_compNormSqMulti`),
   landing in the producer's `rm04NormSqInFrame`/`compNormSqMulti` norms.

The fifth follow-up's "second stop condition" (a missing `nabla0SFun â†”
tensor0SCovariantDerivative` rank-`â‰¥1` agreement) applies **only** to the `(1,3)`
route (1) â€” differentiating `rm13` directly â€” which route 2 **sidesteps** by raising
`Rm04` instead.  So that stop condition is *not* on the critical path.

### What was changed this pass (verified)

* `Tensor/RSTensor/Tensor0SRiemannian/Smooth.lean`:
  `cotangentSharp_cov_eq_sharp_curry_of_mdiffAt` changed from `private` to a public
  theorem (with docstring).  No proof change.  Focused `lake-locked build`: EXIT 0;
  `#print axioms` = `[propext, Classical.choice, Quot.sound]`.
* `Evolution/NablaRiemannT1Bound.lean`: header docstring corrected to record that
  route 2 is viable and to point at the freeze/`âˆ‡` and sharp-smoothness tools (no code
  change; the re-export theorem is unchanged).  Focused `lake-locked build`: EXIT 0.

### What remains (large but unblocked)

The assembly is genuinely framework-scale and was **not** completed (no `sorry` was
introduced): a bundled freeze-all-but-slot-`q` one-form field for `Rm04` with its
`(0,1)` `TotalNabla0SRealizes` (template `freezeMiddle04Field` + `middleFreezeNabla`,
for `q âˆˆ Fin 4`); the `metricSharp â†” cotangentSharp_gen` component-smoothness bridge
for those one-forms (the highest-risk piece); the assembled covariant Leibniz for `K`
combining (1)+(2)+cov-zero slot sections; and the orthonormal evaluation + the `Tâ‚‚`
Cauchyâ€“Schwarz (5).  Estimated ~600â€“1000 LOC across these layers.  None is blocked by
a missing tensor-API/realization frontier â€” the genuine remaining cost is the size of
this concrete assembly, not an absent lemma.

`BernsteinShiSolution.lean` remains parametric in `IteratedRmTowerOn`.

## 2026-06-06 eighth follow-up: piece (1) of the `Tâ‚` route-2 assembly is BUILT â€” the frozen-slot one-form field of `Rm04` with its `(0,1)` covariant derivative

This pass took the dedicated **piece (1)** of the (now-unblocked) route-2 `Tâ‚`
assembly named in the seventh follow-up: the bundled **freeze-all-but-slot-`q`
one-form field for `Rm04`** plus its `(0,1)` covariant-derivative realization
(`TotalNabla0SRealizes`).  It is now **closed, sorry-free, axiom-clean**, in a new
file `Evolution/RmFrozenSlotField.lean`.  `#print axioms` on every public
declaration is `[propext, Classical.choice, Quot.sound]`.  Focused
`lake-locked build` of the new module: EXIT 0 (3633/3633 jobs).

### Why this refutes the prior "frozen-slot Leibniz is large/risky" framing

The seventh follow-up correctly identified the templates (`freezeMiddle04Field` +
`middleFreezeNabla`) but estimated the frozen one-form field + its `(0,1)`
realization + the `metricSharp â†” cotangentSharp_gen` smoothness bridge together as
~600â€“1000 LOC and flagged the smoothness bridge as "the highest-risk piece".  In
fact the **frozen one-form field and its `(0,1)` covariant derivative need no
sharp-smoothness bridge at all**: the field is the slot-frozen one-form
`oneFormAtSlot0S (Rm04 p)(frozen slots)(q)` itself (a `dualToCotangent_gen` of an
`Rm04`-evaluation), whose smoothness is the **exact** `freezeMiddle04Field`
coordinate-frame proof at rank `(0,1)` (one slot, `Fin 1`), and whose covariant
derivative is the **exact** `middleFreezeNabla` device at rank `(0,4) â†’ (0,1)`.  The
`metricSharp â†” cotangentSharp_gen` bridge is a *separate* concern of piece (2) (the
`gâ™¯ Î²q` sharp-field smoothness, the `MDiffAt` hypothesis of
`cotangentSharp_cov_eq_sharp_curry_of_mdiffAt`), **not** of piece (1) â€” the
covariant derivative of `Î²q = oneFormAtSlot0S Rm04 slots q` is taken *before* any
sharp is applied.  Piece (1) is â‰ˆ430 LOC and hit **no** wall.

### What was proved (`Evolution/RmFrozenSlotField.lean`, all sorry-free, axiom-clean)

Reusable tensor-layer (namespace `Integral.Connection`, arbitrary `(0,4)` field
`A`, not Ricci-flow-specific):

* `freezeAllBut04Field A q Y` â€” the smooth `(0,1)` field
  `p â†¦ oneFormAtSlot0S (A p)(fun i => Y i p) q` freezing all but slot `q` of a
  smooth `(0,4)` field `A` against a tuple `Y : Fin 4 â†’ section` (slot `q`'s frozen
  value is overwritten, hence irrelevant) â€” uniform in `q` via `Function.update`.
  Smoothness by the `contMDiff_multilinearSection_iff_coord` +
  `contMDiffAt_section_apply_gen` route of `freezeMiddle04Field`.
* `freezeAllBut04Field_apply` / `freezeAllBut04Field_apply_vec` â€” its fibre value
  is `oneFormAtSlot0S (A x)(Y Â· x) q`, i.e.
  `(fun _ : Fin 1 => W) â†¦ A x (update (Y Â· x) q W)` â€” exactly the one-form
  `curvatureAction0SAt_eq_rm04_raise` pairs with `gâ™¯`.
* `allBut04FreezeNabla` (private) â€” the **frozen-slot covariant Leibniz**:
  `totalNabla0SFun 1 cov (freezeAllBut04Field A q Y) x (vec2 (X x) U)
     = totalNabla0SFun 4 cov A x (Fin.cons (X x)(update (Y Â· x) q U))`,
  when the frozen sections `Y i` (`i â‰  q`) are covariantly constant at `x` along
  `X`.  This is `middleFreezeNabla` at `(0,4) â†’ (0,1)`: `nabla0SFun_eval_smooth_slots`
  on both sides, the live `B`-correction matched to the `a = q` `A`-correction, the
  three frozen `A`-corrections killed by `exists_cov_zero_at_apply` +
  `metricTrace_tensor0S_update_zero`.

Solution-facing (namespace `PDE.RicciFlow`):

* `rmFrozenSlotField S t q Y` (+ `_apply`/`_apply_vec`) â€” the frozen one-form field
  of the solution's lowered Riemann tensor `S.base.rm04 t` at slot `q`.
* `nablaRmFrozenSlotField S t q Y` â€” its canonical bundled `(0,1)` covariant
  derivative (rank 2), built through `totalNabla0S` exactly like
  `nablaRm04Field`; `nablaRmFrozenSlotField_realizes` is its `TotalNabla0SRealizes`.
* `nablaRmFrozenSlot_eval` â€” the **solution-facing covariant-derivative identity**
  the K-Leibniz (piece 3) consumes: at any `xâ‚€`, for a regular time, with the
  frozen `Y i` (`i â‰  q`) cov-constant at `xâ‚€` along `X`,
  `nablaRmFrozenSlotField S t q Y xâ‚€ (vec2 (X xâ‚€) U)
     = nablaRm04Field S t xâ‚€ (Fin.cons (X xâ‚€)(update (Y Â· xâ‚€) q U))`,
  i.e. `âˆ‡(oneFormAtSlot0S Rm04 Â· q) = (frozen-slot contraction of) âˆ‡Rm04`.  The RHS
  is the realized `âˆ‡Rm04` (`nablaRm04Field`) with the live slot `q` carrying `U` and
  the derivative slot leading â€” exactly the `âˆ‡Rm04`-with-frozen-slots form that
  chains with `cotangentSharp_cov_eq_sharp_curry_of_mdiffAt`
  (`Tensor0SRiemannian/Smooth.lean`, now public) and `nabla0SFun_product_eval`
  (`Tensor/RSTensor/ContractionLeibniz.lean`).

### Net (what remains of route 2 after piece (1))

* **Piece (1) (frozen one-form field + its `(0,1)` `TotalNabla0SRealizes`) â€” DONE.**
  No wall: both stop conditions of the piece-(1) task were avoided
  (`middleFreezeNabla`/`exists_cov_zero_at_apply` generalise verbatim to the
  `(0,4) â†’ (0,1)` slot positions, and the field's realization needs **no** missing
  smoothness/realization fact â€” only the canonical `totalNabla0S` producer).
* **Piece (2) (the `metricSharp â†” cotangentSharp_gen` component-smoothness bridge
  for the sharp field `p â†¦ gâ™¯ Î²q`) â€” next, separate.**  Discharges the `MDiffAt`
  hypothesis of `cotangentSharp_cov_eq_sharp_curry_of_mdiffAt`; the
  seventh follow-up's "highest-risk piece", orthogonal to piece (1).
* **Piece (3) (the assembled K-Leibniz: `âˆ‡K = âˆ‡Rm04 âˆ— gâ™¯Rm04 + Rm04 âˆ— gâ™¯âˆ‡Rm04`)
  and the final orthonormal Cauchyâ€“Schwarz** â€” combine `nablaRmFrozenSlot_eval` (1)
  + the sharp-parallelism + piece (2) + `nabla0SFun_product_eval`, then the
  `NablaRiemannT2Bound.lean` `abs_le_sqrt_compNormSq*` estimate.

Files added: `Evolution/RmFrozenSlotField.lean` (no existing file edited).
`BernsteinShiSolution.lean` remains parametric in `IteratedRmTowerOn`.

## 2026-06-06 ninth follow-up: the `metricSharp ↔ cotangentSharp_gen` component-smoothness bridge is BUILT (route-2 piece (3)'s `MDiffAt` hypothesis is dischargeable)

This pass took the dedicated **highest-risk piece** of the (now-unblocked) route-2
`T₁` assembly named in the seventh/eighth follow-ups: the **component-smoothness
bridge** relating the bundled smooth sharp field `metricSharp_contMDiff_total`
(`Geometry/Operator/MetricSharpSmooth.lean`) to the component sharp
`cotangentSharp_gen`/`cotangentSharp_eq_sum_inv_gen` consumed by B's
`curvatureAction0SAt_orthoBasis_eq_sum` (`Evolution/NablaRiemannT2Bound.lean`,
`Tensor/RSTensor/CotangentRiemannian.lean`), so the sharp applied to a smooth
one-form is `MDiffAt`, discharging the `hSharp` hypothesis of
`cotangentSharp_cov_eq_sharp_curry_of_mdiffAt`
(`Tensor/RSTensor/Tensor0SRiemannian/Smooth.lean`).  It is now **closed,
sorry-free, axiom-clean**, in a new file `Geometry/Operator/CotangentSharpSmooth.lean`
(no existing file edited).  `#print axioms` on every public theorem is
`[propext, Classical.choice, Quot.sound]`.  Focused `lake-locked build`: EXIT 0.

### Route decision: a SHORT real lemma, not `rfl` and not a wall

Neither STOP condition was hit.  The two maps are **not** the same map (so not
`rfl`) but are connected by a one-line Riesz-uniqueness lemma, and the bundled
smoothness **does** yield the needed `MDiffAt` (so no wall):

* The two interfaces have **different domains**: `metricSharp g x` (the one in
  `Gradient.lean`, namespace `…DivergenceTheorem`, used by
  `metricSharp_contMDiff_total`) takes `TangentSpace I x →ₗ[ℝ] ℝ`, while
  `cotangentSharp_gen g x` takes a realized `Tensor0SSpace 1 I x`.  They are **both**
  the Riesz raising of `g`: `inner_metricSharp` gives `g(metricSharp g x α, w) = α w`
  and `cotangentSharp_inner_gen` gives `g(cotangentSharp_gen g x β, w) =
  cotangentToDual_gen β w`.  With `α = cotangentToDual_gen β` these coincide, so by
  `metricFlatLinear_injective` (uniqueness of the representative) they are **equal**:
  `cotangentSharp_gen g x β = metricSharp g x (cotangentToDual_gen β)`
  (`cotangentSharp_gen_eq_metricSharp`).
* `Module.Dual ℝ V` is an `abbrev` for `V →ₗ[ℝ] ℝ` (reducible), so the field
  `cv b := cotangentToDual_gen (β b)` has **exactly** the type
  `Π b, TangentSpace I b →ₗ[ℝ] ℝ` that `metricSharp_contMDiff_total` consumes — no
  coercion plumbing needed.
* `metricSharp_contMDiff_total`'s chart-basis smoothness hypothesis
  `b ↦ cv b (chartBasisVecFiber α j b)` is, for `cv = cotangentToDual_gen ∘ β`,
  definitionally `b ↦ β b (fun _ => chartBasisVecFiber α j b)`
  (`cotangentToDual_apply_gen`) — the smooth chart-basis evaluation of the realized
  one-form field.  So the bundled-`ContMDiff` form **does** yield the `MDiffAt (T% …)`
  the sharp-parallelism needs, via `.contMDiffAt.mdifferentiableAt`.

### What was proved (`Geometry/Operator/CotangentSharpSmooth.lean`, all sorry-free, axiom-clean)

* `cotangentSharp_gen_eq_metricSharp` — the pointwise map identity
  `cotangentSharp_gen g x β = metricSharp g x (cotangentToDual_gen β)` (Riesz
  uniqueness via `metricFlatLinear_injective`, `inner_metricSharp`,
  `cotangentSharp_inner_gen`).
* `cotangentToDual_gen_chartBasis_eval` — the component bridge
  `cotangentToDual_gen (β b) (chartBasisVecFiber α j b)
     = β b (fun _ => chartBasisVecFiber α j b)`.
* `cotangentSharp_gen_contMDiff_total` — on a boundaryless model, the bundled raised
  field `b ↦ TotalSpace.mk' E b (cotangentSharp_gen g b (β b))` is `C^∞`, given
  chart-basis smoothness of `b ↦ β b (fun _ => chartBasisVecFiber α j b)`
  (`metricSharp_contMDiff_total` for `cv = cotangentToDual_gen ∘ β`, transported
  through the map identity).
* `cotangentSharp_gen_mdiffAt` — the **`MDiffAt (T% …)` corollary**, the exact
  predicate `cotangentSharp_cov_eq_sharp_curry_of_mdiffAt` needs for `hSharp`.

An end-to-end integration check (throwaway probe, EXIT 0, not committed) confirmed
that `cotangentSharp_gen_mdiffAt g hβ x` discharges the `hSharp` argument of
`cotangentSharp_cov_eq_sharp_curry_of_mdiffAt` verbatim — no renamed/axiomatized
smoothness, the bridge genuinely closes the gap.

### Net (route-2 `T₁` frontier after this pass)

* **Piece (1) (frozen-slot one-form field + `(0,1)` `∇`) — DONE** (eighth follow-up,
  `RmFrozenSlotField.lean`).
* **Sharp-parallelism (route-2(a)) — public** (seventh follow-up).
* **Component-smoothness bridge (this pass, the highest-risk piece) — DONE**
  (`CotangentSharpSmooth.lean`): the sharp of a smooth one-form is `MDiffAt`, and its
  orthonormal-basis component form is exactly B's `cotangentSharp_gen`/
  `cotangentSharp_eq_sum_inv_gen` (the same map, related by the proved map identity).
* **Still remaining (route-2 piece (3)): the assembled `K`-Leibniz**
  `∇K = ∇Rm04 ∗ g♯Rm04 + Rm04 ∗ g♯∇Rm04` combining
  `nablaRmFrozenSlot_eval` (1) + the sharp-parallelism + the frozen-slot Leibniz (2)
  + `nabla0SFun_product_eval`, then the `NablaRiemannT2Bound.lean`
  `abs_le_sqrt_compNormSq*` Cauchy–Schwarz.  Not blocked by a missing tensor API —
  the remaining cost is the size of this concrete assembly.

One downstream note for piece (3): the bridge inherits `[InnerProductSpace ℝ E]`
from `metricSharp_contMDiff_total`; `Evolution/NablaRiemannT2Bound.lean` already
carries it, but `Evolution/NablaRiemannT1Bound.lean` currently does not, so the final
`T₁` assembly file will need to add `[InnerProductSpace ℝ E]` (harmless; the model
fibre carries an inner product everywhere the orthonormal frame is used).

Files added: `Geometry/Operator/CotangentSharpSmooth.lean` (no existing file edited).
`BernsteinShiSolution.lean` remains parametric in `IteratedRmTowerOn`.

## 2026-06-07 tenth follow-up: route-2 piece (3) is ASSEMBLED — `nablaLapCommReactionTerm` is FULLY bounded `|reaction| ≤ C(card)·|Rm|·|∇Rm|`

This pass took the dedicated **piece (3)** assembly (the K-Leibniz, the `T₁`
quantitative bound, the full `T₁+T₂` reaction bound, and the spatial-commutator
connection).  It is now **closed, sorry-free, axiom-clean**, in a new file
`Evolution/NablaRiemannReactionBound.lean` (no existing file edited).  `#print axioms`
on every public theorem is `[propext, Classical.choice, Quot.sound]`.  Focused
`lake-locked build`: EXIT 0 (3691 jobs).  **`nablaLapCommReactionTerm` is now fully
bounded.**

### One environmental wall found and dissolved (not anticipated by follow-ups 5–9)

The banked pieces were each built in ISOLATION (in files without
`[InnerProductSpace ℝ E]`).  Combining them in one file with `[InnerProductSpace ℝ E]`
(required by `cotangentSharp_gen_mdiffAt`) exposed a `Tensor0SModel` model-fibre
instance diamond: accessing `(Tensor0SField).contMDiff` fails `NormedSpace ℝ
(Tensor0SModel s ℝ E)` synthesis in the downstream file (the bundle's `CMDiff`
notation wants the Defs.lean `instNormedAddCommGroupTensor0SModel`, while the global
`tensor0SModel_normedSpace` provides a non-syntactically-matched one).  **Fix:**
`set_option backward.isDefEq.respectTransparency false` (the same option
`freezeAllBut04Field` uses), which unifies the instances.  This is recorded in
`rmFrozenSlot_chartBasis_contMDiffOn`.

### What was proved (`Evolution/NablaRiemannReactionBound.lean`, all sorry-free, axiom-clean)

* `solution_isMetricCompatible` — `IsMetricCompatible_gen (S.family.connection t)
  (S.base.metric t)` (Levi-Civita), the metric-compat discharge for the sharp
  parallelism and Step A.
* `rmFrozenSlot_chartBasis_contMDiffOn` / `rmFrozenSlotSharp_mdiffAt` /
  `rmFrozenSlotSharpSection` — **piece (2) closed in the solution context**: the
  chart-basis smoothness of the frozen one-form, hence the `MDiffAt` of the raised
  sharp field `y ↦ g♯βq`, discharging `cotangentSharp_cov_eq_sharp_curry_of_mdiffAt`'s
  `hSharp` (via `cotangentSharp_gen_mdiffAt`, follow-up 9), and the bundled sharp
  section.
* `rmRaise_summand_covDeriv` — the **per-`q` contraction Leibniz**: the covariant
  derivative of one raise-form summand `Rm04(…, g♯βq)` splits into `(∇Rm04)(…,g♯βq) +
  Rm04(…, g♯(∇βq))`, via `nabla0SFun_eval_smooth_slots` on cov-constant slots + the
  sharp-parallelism + `nablaRmFrozenSlot_eval`.
* `nabla3_antisym_eq_covDeriv_curvatureAction_covConst` — the **generic-frame `T₁`
  reduction on cov-constant sections** (route 3): `∇³Rm(X,b,c) − ∇³Rm(X,c,b) =
  extDerivFun(K)` for the curvature-action field `K`, via `eval_smooth_slots` (cov-const
  ⟹ no Christoffel corrections) + the pointwise `(0,4)` Ricci identity.  This
  reconciles the smooth-frame differentiation with the pointwise orthonormal frame.
* `nablaLapComm_T1_eq_rm04_raise_leibniz` — **the assembled K-Leibniz**:
  `T₁ = -Σ_q [(∇Rm04)(X,b,c,m_q,g♯βq) + Rm04(b,c,m_q,g♯(∇_X βq))]`, the covariant
  Leibniz `∇(Rm ∗ Rm) = ∇Rm ∗ Rm + Rm ∗ ∇Rm` for the curvature action through the
  metric-raising form (**no `∇rm13`** — route 2 sidesteps the `(1,3)` raising
  parallelism entirely).
* `abs_tensor05_sharp_last_le` / `abs_tensor04_sharp_last_le` /
  `sum_sq_update_le_compNormSqMulti` — the orthonormal-basis Cauchy–Schwarz on a
  last-slot raise contraction (mirror of B's `abs_curvatureAction0SAt_orthoBasis_le`).
* `abs_nablaLapComm_T1_covConst_le` / `abs_nablaLapComm_T1_orthoBasis_le` — the **`T₁`
  quantitative bound** `|T₁| ≤ 8·card·√|∇Rm|·√|Rm|` on cov-const sections, then in the
  genuine `g`-orthonormal frame (frame vectors realised by cov-const sections via
  `exists_cov_zero_at_apply`).
* `abs_nablaLapCommReactionTerm_diag_orthoBasis_le` — **the full reaction bound**:
  `|Σ_a reactionF a a c m| ≤ 13·card²·√(rm04 compNormSq4)·√(∇Rm compNormSqMulti)`
  = `C(card)·|Rm|·|∇Rm|`, combining the `T₁` bound with B's
  `abs_nablaLapComm_T2_orthoBasis_le`.
* `abs_spatialCommNablaRm_orthoFrame_le` — **the spatial-commutator bound in the
  producer's convention**: at `x₀`, in a genuine `g`-orthonormal frame with
  `InverseMetricOrthonormalAt` (`gᵃᵇ = δ`) holding honestly,
  `|Δ(∇Rm)(c) − ∇(ΔRm)(c)| ≤ 13·card²·√(rm04NormSqInFrame)·√(nablaRm04NormSqInFrame)`,
  assembling `nablaLapCommF_orthonormalTrace` (the diagonal trace) with the full
  reaction bound, in the producer's `rm04NormSqInFrame`/`nablaRm04NormSqInFrame` norms.

### Net (the `k = 1` frontier after this pass)

* **`T₁` quantitative bound — DONE.**  Route 2 (the `g♯` raise form) assembled
  end-to-end; the `(1,3)` raising-parallelism wall (bound obstruction #1) is
  **sidestepped**, not solved — it is never needed.
* **`nablaLapCommReactionTerm` — FULLY bounded** `|reaction| ≤ C(card)·|Rm|·|∇Rm|`,
  and the **spatial commutator** `[Δ,∇_c]Rm` is bounded in the producer's orthonormal
  component-norm convention (`abs_spatialCommNablaRm_orthoFrame_le`).

### Remaining for the full `k = 1` producer (a SEPARATE frontier — the time-derivative side)

The full `NablaRm04NormHeatEquationOn` / `nablaRm04NormHeatBoundOn_of_components`
(`Evolution/NablaRiemannHeat.lean`) is a `HasDerivWithinAt` (time-derivative)
statement.  Its **spatial** reaction input is now discharged
(`abs_spatialCommNablaRm_orthoFrame_le`).  What remains is the **time-derivative
assembly**: `iteratedRmComp_one_hasDerivWithinAt` (`Evolution/NablaRiemannTimeDeriv.lean`)
still takes `hrm`/`hchr`/`hswap` (the level-0 time derivative, the Christoffel time
derivative `∂ₜΓ = ∇Ric`, and the time/spatial derivative swap) as **input shapes**;
their concrete instantiation from the solution, plus the `MultiNormHeat` Bochner
norm-square assembly, is the separate analytic frontier.  This is orthogonal to the
reaction bound and was **not** in scope here.  `BernsteinShiSolution.lean` remains
parametric in `IteratedRmTowerOn`.

Files added: `Evolution/NablaRiemannReactionBound.lean` (no existing file edited).

## 2026-06-07 eleventh follow-up: the time-derivative side mapped — `hchr` is solution-dischargeable, `hrm` is an UNBUILT-but-UNBLOCKED assembly (banked `∂ₜRm13` found), and `hswap` + the frame reconciliation are the two genuine walls

This pass took the dedicated **time-derivative assembly** task: discharge
`NablaRm04NormHeatEquationOn` for a real `SolutionOn` by instantiating
`iteratedRmComp_one_hasDerivWithinAt`'s `hrm`/`hchr`/`hswap`
(`Evolution/NablaRiemannTimeDeriv.lean:249`) from the solution and feeding the
Bochner producer.  After an end-to-end trace of every input against the tree, the
finding **corrects two earlier verdicts** and isolates the genuine walls precisely.
No Lean code was changed (a faithful assembly needs new `sorry`s at the walls,
forbidden); the deliverable is the precise frontier.

### Correction 1 — `hchr` (`∂ₜΓ`) IS dischargeable from the solution (not a black box)

`hchr` needs `∂ₜ(realizedChr) = ∂ₜΓ` in the **time-independent `coordinateFrameAt`**.
This is exactly `ChristoffelEvolutionEquationInFrameOn`, and it is **proved from
`S, hS` alone**:
* `coordMetricDeriv` (`Ricci/CoordinateRegularity.lean:870`) discharges the metric
  fixed-base swap `FixedBaseExtDerivTimeDerivativeOnRegular(metric, −2·Ric)` from
  `IsSolutionOn` via `fixedBaseOnReg_of_timeDerivWithin`, whose `hTime` is the
  genuine `∂ₜg = −2 Ric` (`metricCompInFrame_hasDerivWithinAt`, the realized
  `MetricVariationEquationOn`);
* `coordMetricMix` + `coordGammaEvol` (`…/CoordinateRegularity.lean:906, 937`) then
  give `ChristoffelEvolutionEquationInFrameOn` (= `∂ₜΓ`), all from `S, hS`;
* `coordGammaMix` (`…/CoordinateRegularity.lean:1255`) gives the **mixed** Γ swap
  `ChristoffelVariationMixedDerivativeInFrameOnRegular` (= `∂ₜ∂ₓΓ`) from `S, hS`
  (again `fixedBaseOnRegLocal`, `hTime` = the just-built `∂ₜΓ`).

So the prior follow-ups' framing of `∂ₜΓ`/Lemma 6.2 as a `BlackBox.lean` frontier is
**inaccurate for the coordinate frame**: it is a *closed* producer chain.  The
realized Ricci evolution (Lemma 6.3) is likewise closed: `coordRicciEvol`
(`Ricci/CoordinateIdentities.lean:876`) gives `∂ₜ(ricciCompInFrame)` in
`coordinateFrameAt` from `S, hS` (sorry-free; no `sorry`/`admit` in
`CoordinateRegularity.lean`/`CoordinateIdentities.lean`).

### Correction 2 — `hrm` (`∂ₜRm`) is NOT an Uhlenbeck-shape wall; the `∂ₜRm13` coordinate producer is already BANKED

`hrm` needs `∂ₜ(realizedRmBase) = ∂ₜ(S.base.rm04)` frame components in
`coordinateFrameAt`.  The recipe's Uhlenbeck route does **not** supply this:
`UhlenbeckCurvatureEvolutionInFrameOn` is about the *pulled-back* components, and
`uhlenbeckCurvatureEvolution{InFrameOn_of_ricciFlow,_of_solution_components}`
(`Uhlenbeck.lean:987,1122`) themselves take the standard-slot Riemann evolution
`Riemann04BTensorWithRicciDriftEvolutionInFrameOn` as an **input hypothesis** —
which is *only ever consumed*, never discharged.  So the Uhlenbeck `hrm` route is a
genuine shape mismatch (stop condition 2 *for that route*).

**But there is a second, banked route**, mirroring `coordRicciEvol`: the `(1,3)`
Riemann coordinate coefficient `christoffelCurvCoeffAt` (= `∂Γ − ∂Γ + ΓΓ − ΓΓ`,
`Geometry/Curvature/Components/Christoffel.lean:67`) has its time derivative
**already proved**:
`christoffelCurvCoeffAt_hasDerivWithinAt_of_christoffelVariation`
(`Ricci/GammaCoord.lean:141`) gives `∂ₜ(Rm13^m_{ikj})` in `coordinateFrameAt` from
`hvar` (`∂ₜΓ`) + `hmix` (`∂ₜ∂ₓΓ`) — both discharged from `S, hS` above.  (Indeed
`coordRicciEvol`'s `∂ₜRic` is *built by summing this exact Riemann-coefficient
derivative*, `GammaCoord.lean:318`.)  Combined with the pointwise realization
`rm13_eval_eq_christoffelCurvCoord` (`Geometry/Curvature/Components/RicciIdentity.lean`)
and lowering `rm04 = g·Rm13` with the metric time derivative
(`metricCompInFrame_hasDerivWithinAt`), `∂ₜ(rm04)` in `coordinateFrameAt` is
**assemblable with no missing primitive** — it is the unbuilt `(0,4)` analogue of the
closed `coordRicciEvol`.  This refutes the tenth follow-up's "the time-derivative side
is a separate analytic frontier [whose `hrm`] is deferred": `hrm` is unblocked, only
unbuilt (a bounded ~Lemma-6.1 assembly).

### The two GENUINE walls (the assembly is not closable as-is)

1. **`hswap` for `rm04` needs an UNBANKED second-order mixed space-time Christoffel
   derivative `∂ₜ∂²ₓΓ`.**  `hswap`
   (`NablaRiemannTimeDeriv.lean:267`) needs
   `∂ₜ(extDerivFun(rm04 component))`, i.e. a
   `FixedBaseExtDerivTimeDerivativeOnRegular` for `rm04`.  Since
   `rm04 ~ ∂ₓΓ + Γ·Γ`, the spatial derivative `∂ₓ(rm04) ~ ∂²ₓΓ + ∂ₓΓ·Γ`, so
   `∂ₜ∂ₓ(rm04) ⊇ ∂ₜ∂²ₓΓ`.  The banked Γ swaps stop at **first** order in `∂ₓ`
   (`coordGammaMix` = `∂ₜ∂ₓΓ`); there is **no** `∂ₜ∂²ₓΓ` /
   `christoffelCoordSecondDeriv` mixed producer in the tree (searched).  *Exact
   theorem needed next*: a second-order mixed space-time Christoffel derivative
   `FixedBaseExtDerivTimeDerivativeOnRegular` for `christoffelCoordDerivAt`
   (i.e. `∂ₜ(∂ₓ ∂ₓΓ)`), the one-order-higher analogue of `coordGammaMix`, in
   `Ricci/CoordinateRegularity.lean`.  This is a bounded but real new producer, not
   currently present.

2. **Frame reconciliation — the KEY SUBTLETY, unresolved.**  The time derivative
   `iteratedRmComp_one_hasDerivWithinAt` is hardwired to the **time-independent
   `coordinateFrameAt`** (so `∂ₜ` does not pick up a moving-frame term), where the
   inverse metric `gInv` is the *actual* `coordInv`, **not** `δ`.  But:
   * the producer `nablaRm04NormHeatBoundOn_of_components`
     (`NablaRiemannHeat.lean:634`) requires `horth : InverseMetricOrthonormalAt gInv`
     (`gInv = δ`) — its reaction bound `abs_nablaRmReactionInFrame_le` is hardwired to
     `compNormSq*` (plain component sums) and genuinely needs `gInv = δ`;
   * the spatial commutator bound `abs_spatialCommNablaRm_orthoFrame_le`
     (`NablaRiemannReactionBound.lean:1326`) is proved **only** in the *time-dependent*
     `g(t)`-orthonormal frame of `exists_orthoBasisFrameAt` (whose frame vectors
     depend on `t`).
   These two frames are incompatible:
   * **Route (a)** (everything in `coordinateFrameAt` with the real `gInv`): the
     spatial commutator identity `nablaLapCommF_trace` *is* frame-generic and holds
     for general `gInv`, but (i) the producer's `horth` is then *unsatisfiable*
     (`coordinateFrameAt` is the chart frame, never `g`-orthonormal at its centre —
     `Geometry/Coordinates/CoordinateFrame.lean`), and (ii) the *quantitative* bound
     `abs_spatialCommNablaRm_orthoFrame_le` exists **only** in the orthonormal frame,
     not for a general `gInv` (the sixth/tenth follow-ups built it via the
     orthonormal-basis Cauchy–Schwarz; a general-`gInv` reaction bound is the absent
     fibre-norm↔component-norm machinery, the previously-rejected route (b) of the
     fourth follow-up).  So route (a) needs **both** a `horth`-free producer variant
     **and** a general-`gInv` reaction bound — neither exists.
   * **Route (b)** (everything in the `g(t)`-orthonormal frame): then the time
     derivative `iteratedRmComp_one_hasDerivWithinAt` picks up an **unbanked
     moving-frame `∂ₜ(frame)` correction term** (the theorem is stated for a
     time-independent frame; `exists_orthoBasisFrameAt`'s frame is `t`-dependent
     through the fibre metric).  No moving-frame covariant-derivative time-derivative
     correction exists in the tree.

   *Exact theorem(s) needed next*: **either** (a) a `horth`-free / general-`gInv`
   restatement of `nablaRm04NormHeatBoundOn_of_components` **plus** a general-`gInv`
   reaction bound (the fibre-norm bridge), **or** (b) a moving-frame correction to
   `iteratedRmComp_one_hasDerivWithinAt` carrying the `∂ₜ(frame)` term for a
   `t`-dependent orthonormal frame.  Both are framework-scale; neither is a one-lemma
   gap.

### Net (the `k = 1` producer frontier after this pass)

* **`hchr` (`∂ₜΓ`, `∂ₜ∂ₓΓ`) — solution-dischargeable, closed** (`coordGammaEvol` /
  `coordGammaMix`, from `S, hS`).  Earlier "black-box" framing corrected.
* **`hrm` (`∂ₜrm04`) — UNBLOCKED, unbuilt.**  Banked `∂ₜRm13`
  (`christoffelCurvCoeffAt_hasDerivWithinAt_of_christoffelVariation`) + realization +
  metric lowering give it with no missing primitive; it is the `(0,4)` analogue of the
  closed `coordRicciEvol`.  Earlier "Uhlenbeck shape mismatch" is correct only for the
  Uhlenbeck route, which is not the only route.
* **`hswap` (`∂ₜ∂ₓrm04`) — WALL 1**: needs an unbanked second-order mixed space-time
  Christoffel derivative `∂ₜ∂²ₓΓ` (one order above `coordGammaMix`).
* **Frame reconciliation — WALL 2 (the key subtlety)**: the clean-`∂ₜ`
  `coordinateFrameAt` (general `gInv`) and the quantitative orthonormal spatial bound
  (`g(t)`-frame, `gInv = δ`) are incompatible; closing it needs either a
  `horth`-free/general-`gInv` producer+reaction-bound or a moving-frame `∂ₜ(frame)`
  correction.

`BernsteinShiSolution.lean` remains parametric in `IteratedRmTowerOn`.  No files
changed this pass (a faithful assembly would require `sorry` at walls 1–2).

## Claude prompt

```text
Work in E:\testdifferential-geometry. DifferentialGeometry/ is primary;
RicciFlower/ is reference only.

Goal:
Continue the k = 1 Bernstein-Shi producer behind
DifferentialGeometry/Geometry/Flow/RicciFlow/Evolution/IteratedNablaRmTower.lean.
Do not start the all-k induction yet.

Current checked progress:
- MultiNormHeat.lean exists and checks.
- RmRealizationBridge.lean proves rm04_ricciIdentityAt,
  nablaRm04_ricciIdentityAt, iteratedRmComp_one_eq_nablaRm04Field, and
  covDerivStepComp_frameComp_eq.
- NablaRiemannCommutator.lean proves nablaLapComm_orthonormalTrace.
- NablaRiemannTimeDeriv.lean proves iteratedRmComp_one_hasDerivWithinAt, but it
  still takes hrm/hchr/hswap as input shapes.
- NablaRiemannCommutatorBound.lean proves
  nablaLapCommReactionTerm_eq_covDeriv_curvatureAction_add_curvatureAction.
- Axiom audit for those declarations is clean: only propext, Classical.choice,
  Quot.sound.

Honesty constraints:
- The k = 1 quantitative bound is not closed.
- BernsteinShiSolution.lean must remain parametric in IteratedRmTowerOn until a
  real producer exists.
- Do not solve the bound by adding a renamed starBound/heatEq assumption.
- Do not assume coordinateFrameAt is orthonormal.

Task:
Close the next smallest missing producer for the k = 1 quantitative reaction
bound. Start by building the tensor/metric bridge that the current wall needs:

1. Prove or identify the pointwise raising bridge rm13 = raise(rm04) in a
   metric-compatible basis/frame.
2. Prove or identify the covariant derivative bridge
   nabla(rm13) = raise(nabla rm04), using Levi-Civita metric compatibility.
3. Use those to state an orthonormal-frame component estimate for
   curvatureAction0SAt and nabla(curvatureAction0SAt):
   |curvature action| <= C(card) * |Rm04| * |A|
   and
   |nabla(curvature action)| <= C(card) * |Rm04| * |nablaRm04|.
4. Only then return to NablaRiemannCommutatorBound.lean and connect the proved
   commutator decomposition to the required k = 1 star/reaction bound.

Stop if the first missing item is one of:
- no (1,3) lowering/raising parallelism;
- no nabla rm13 bridge;
- no orthonormal-frame norm comparison rm13 vs rm04;
- no frame-change bridge from coordinateFrameAt to an orthonormal frame;
- no concrete instantiation of hrm/hchr/hswap for iteratedRmComp_one_hasDerivWithinAt.

When stopping, report the exact theorem statement needed next, the file where it
belongs, and why the coordinate-frame shortcut is invalid. Do not add new
assumptions or wrappers that merely rename the frontier.

Verification:
Run focused lake-locked checks for touched files. If adding public theorem(s),
run #print axioms and require only [propext, Classical.choice, Quot.sound].
Update IteratedNablaRmTower.md with what was proved or the exact remaining
blocker.
```
