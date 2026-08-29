# RegRangeBall

## Role

`lRegRange_unif` is the noncompact first-exit/range producer between the
ball-local speed/metric estimates and the later uniform L-exponential map.
Its constants are chosen before the flow and the actual controlled ball.

The theorem has no ambient `CompactSpace M` assumption.  It assumes
completeness only on the shorter working slab and uses the terminal member of
that family to make the terminal radius-`1/32` closed ball compact.

## Proof route

1. Combine `lRegSpeed_unif` with the source bound
   `sqrt (g_T Z Z) <= 1 / (128 * sqrt eps)` to bound moving speed by
   `1 / (2048 * eps)` on every already-existing prefix which remains in the
   moving radius-`1/16` ball.
2. Use `lMetric_ball` to convert the terminal radius-`1/32` closed-ball prefix
   to that moving open-ball prefix and to bound terminal-metric speed by
   `1 / (1536 * eps)`.  The slightly sharper displayed constant retains the
   strict margin needed at a first exit; it implies the coarser
   `1 / (1024 * eps)` budget used in the plan.
3. Apply `first_exit_to`.  Terminal energy and `lExp_mem_ball` put the alleged
   first boundary point strictly inside the terminal ball, a contradiction.
4. Use `RiemannianMetricComplete.closedEBall_isCompact` and the generic
   noncompact continuation theorem `lRegDomain_of_cpt` to close the maximal
   domain at `b = sqrt eps * radius`.  Downward domain closure then gives all
   earlier parameters.

## Static status

Source-written on 2026-08-28.  The upstream `lMetric_ball` accepts terminal
distance `<= radius / 32`, and the public `edistTo_terminal` supplies the
pointwise-to-distance bridge without pretending that a local metric comparison
is global.  Both upstream interfaces were focused-checked and refreshed before
this source was finalized.

Both public theorems, `lRegRange_unif` and `lExp_ball_unif`, are **100%
focused-verified**.  The final full-file focused check including the adapter was
warning-free GREEN in 37.7 seconds.  The file contains no `sorry` or `admit`.
The structural private producer `edist_move_lt` isolates the terminal-to-moving
distance estimate consumed by the range theorem.  The next exact theorem is
`redVolume_ball_unif`.  `smooth_nlc` remains **0%** as a theorem endpoint;
dedicated L8--L9 machinery is approximately **94--96%**, while reused generic
infrastructure for this stage is **100%**.

## Endpoint adapter

`lExp_ball_unif` preserves the exact uniform quantifier order and assumptions
of `lRegRange_unif`.  It specializes the range theorem at
`b = sqrt eps * radius`, rewrites
`sqrt (eps * radius^2) = b`, takes the terminal radius-`1/32` bound, and uses
its strict inclusion in the radius-`1` ball to conclude membership of the
L-exponential endpoint.  It does not repeat any domain, speed, metric,
first-exit, energy, Jacobi, or Jacobian argument.  Its source is complete but
focused-verified as part of the warning-free full-file check.

## First focused diagnostics

The first focused elaboration reached this new module and exposed only four
front-layer local diagnostics.  The `RealTimeInterval` occurrences were not
visible because this file had not opened
`DifferentialGeometry.Geometry.Curvature`, and
`continuous_riemannianEDist` was not visible because it had not opened
`DifferentialGeometry.Geometry.Riemannian`.  The remaining subset proof had a
`let`-defined membership mismatch: `hy.le` had the right inequality but Lean did
not unfold `O` and `K` automatically.  The source now opens the two canonical
namespaces and proves that subset by `simpa only [O, K] using hy.le`.

No alternate mathematical route or stronger hypothesis was introduced.  This
was a namespace/definitional elaboration repair only; the next exact step is a
second focused check of `lRegRange_unif`.

## Second focused diagnostics

The second focused pass confirmed that the namespace fixes worked and exposed
only local elaboration cleanup before the distance bridge.  The subset proof
still attempted `.le` while `hy` had an opaque `O`-membership type, so it now
uses explicit `change` steps for both the strict and weak terminal-distance
goals.  One `field_simp` already closed its field identity, making the following
`ring` a no-goals error.  The lower endpoint of `hstB` is now proved exactly by
`(sub_lt_sub_left hqLt time).le.trans ht.1`, avoiding an unnecessary arithmetic
search.  Finally, both deprecated `mul_le_mul_left'` calls were replaced by the
canonical right-multiplication theorem plus commutativity.

The two later heartbeat timeouts occurred at the `edistTo_terminal` bridge
after these earlier errors and are provisionally classified as cascades.  The
call now states `s` and `t` explicitly to reduce inference work, but its
mathematical route and hypotheses are unchanged.  The next exact step remains
a focused check of this file; if either timeout survives after the front errors
are gone, that bridge application is the precise next local frontier.

## Third focused diagnostics

The third pass reduced the first real type error to ENNReal multiplication
monotonicity: the commuted `mul_le_mul_right` expression did not elaborate to
the displayed left-multiplied goal.  Both occurrences now use
`mul_le_mul_of_nonneg_left` directly, with `bot_le` as the ENNReal
nonnegativity proof.

The next two diagnostics were heartbeat timeouts while `nlinarith` was
normalizing the full geometric context around the `ofReal` bounds.  The real
arithmetic is now isolated before those goals: `hPr` proves
`P * (radius / 32) < radius`, and `hPr16` proves the sharper
`P * (radius / 32) < radius / 16`, each by one monotonicity step from
`P <= 4/3` and a small `nlinarith only [radius_pos]`.  The ENNReal goals merely
apply `ofReal_lt_ofReal_iff` to these facts.  No heartbeat limit, hypothesis, or
mathematical route changed; any remaining timeout after this split is the next
exact elaboration frontier.

## Fourth focused diagnostics

The fourth pass showed that `positivity` did not infer the sign of the two
`radius / 32` factors inside the isolated real inequalities.  Both calls now
receive the direct proof
`div_nonneg radius_pos.le (by norm_num)`.  This is only explicit sign plumbing.

The initial metric norm-square branch was a real elaboration timeout rather
than a cascade from the distance estimates.  Its zero-vector case now copies
the already verified native reduction from `NLCEndpoint`: rewrite the first
linear slot by `inner.map_zero`, then the remaining application by
`ContinuousLinearMap.zero_apply`.  The right side of the source square bound
also has a named nonnegativity proof `hZrhs`, built from `hsqrteps`, rather than
asking `positivity` to normalize the entire surrounding context.  Later
timeouts remain provisionally downstream cascades; no heartbeat setting or
proof route was changed.

## Fifth focused diagnostics

The fifth pass left one real diagnostic: the scalar identity
`4 * (1 / (128 * sqrt eps))^2 = 1 / (4096 * eps)` timed out while `field_simp`
was working under the full manifold/flow theorem context.  The same calculation
shape is already verified in `NLCEndpoint`.  It is now isolated as the private
theorem `source_sq_eq` before all universe and geometry variable declarations,
so it carries only `eps : Real` and `0 < eps`.  The main proof invokes this
helper directly.  The calculation and constants are unchanged, and no public
API or heartbeat setting changed.  The top-level timeout is still classified
as a cascade until this performance-local refactor is rechecked.

## Sixth focused diagnostics

After the scalar helper refactor, the only local timeout moved to `hone`.  The
goal after `le_div_iff₀` is a pure linear consequence of
`eps <= 1 / 8192`, but unrestricted `nlinarith` was scanning the full geometric
context.  It now uses `nlinarith only [hepsTiny]`.  This preserves the exact
bound and proof route while preventing irrelevant normalization work.  The
top-level timeout remains classified as a cascade pending the next focused
check; the heartbeat setting is unchanged.

## Seventh focused diagnostics

Even `nlinarith only [hepsTiny]` timed out during its preprocessing phase in the
large theorem context.  The proof of `hone` now uses no arithmetic automation:
after `le_div_iff₀`, it rewrites the leading `1`, applies
`mul_le_mul_of_nonneg_left hepsTiny` with the explicit nonnegative factor
`8192`, and closes the numeral identity by `norm_num`.  This is the same linear
argument with its normalization fully exposed.  No bound, assumption,
heartbeat, or mathematical route changed.

## Fourteenth focused diagnostics

The first-exit block then timed out in two broad `simpa [alpha]` calls before
any first-exit mathematics was elaborated.  All three nearby definitional
conversions are now directional.  In the zero-parameter branch the proof
substitutes `s`, changes only the target to `lRegCurve ... 0 ∈ K`, rewrites
`lRegCurve_zero`, and applies `interior_subset hcenterK`.  Continuity changes
its target directly to `ContinuousOn (lRegCurve ...) (Icc 0 s)` and takes the
existing `lRegCurve_c1On` result.  The initial interior point similarly changes
only its target, rewrites `lRegCurve_zero`, and uses `hcenterK`.  No full
simplification, local-definition unfolding, statement change, or heartbeat
change was introduced.

## Fifteenth focused diagnostics

The dependent `subst s` in the zero-parameter branch triggered a large-context
weak-head normalization timeout.  The branch now applies `hsK`, rewrites the
target by `hs0`, and then performs the same directed `lRegCurve_zero` proof;
no dependent context is substituted.  The annotated `ContinuousOn alpha` goal
also timed out while Lean normalized its expected type.  `halpha` is now inferred
directly from the native `lRegCurve_c1On` result, and `halpha0` is stated in the
native `lRegCurve ... 0` form.  The reducible local name `alpha` is left for the
single unification at `first_exit_to`.  If that unification itself remains too
large, the next strictly local repair is to state `htermRange` with
`lRegCurve` directly; no such broad rewrite was made in this pass.

## Root cause: cache before terminal instances

Comparison with the verified first-exit proof in `NLCEndpoint` identified the
instance-order root cause.  This file was asking for `lRegCurve_c1On` only after
installing terminal-metric `RiemannianBundle` and
`IsContinuousRiemannianBundle` instances.  Weak-head normalization then had to
reconcile the curve theorem with those later local instances and exhausted the
heartbeat budget.

Immediately after defining `alpha`, and before defining the terminal ball or
installing either local metric instance, the proof now caches
`halpha_zero : alpha 0 = center` and the prefix-continuity producer
`halpha_of`.  The first-exit block consumes only these cached facts:
zero-parameter branches rewrite by `halpha_zero`, while continuity is
`halpha_of hsDom`.  It no longer calls or unfolds any `lRegCurve` API after the
terminal instances are installed.  This matches the verified native ordering;
no public statement, hypothesis, constant, or mathematical route changed.

## Seventeenth focused diagnostics

Another full-context scalar calculation timed out while turning the source
norm-square bound into the initial speed budget.  The private theorem
`source_speed_le`, placed before every universe and geometry variable, now
accepts only `eps`, a scalar `U`, positivity of `eps`, and
`U <= (1 / (128 * sqrt eps))^2`.  It applies scalar multiplication monotonicity
in the small context and closes with the existing `source_sq_eq`.  After
rewriting `hU0`, the geometric proof invokes this helper directly.  No public
statement, assumption, constant, route, or heartbeat changed.

## Eighteenth focused diagnostics

The next timeout occurred while elaborating the terminal-metric speed statement,
after the proof had globally installed terminal-metric `RiemannianBundle` and
`IsContinuousRiemannianBundle` instances.  Those instances were needed only to
invoke `continuous_riemannianEDist` in the proof that `O` is open; every later
speed, metric, and energy API already carries `S.base.metric` explicitly.

Both instances now live inside the `hOopen` proof immediately before that
continuity call.  They disappear when the proof closes, so the first-exit,
speed, and energy blocks no longer inherit the irrelevant metric-instance
diamond.  `hKcompact` remains before the local instances, while `hOK` and
`hcenterO` require none.  The `hterm` statement and all mathematics are left
unchanged for a clean next diagnostic; public assumptions and heartbeat are
unchanged.

## Nineteenth focused diagnostics and structural split

The next reported timeout was no longer tied to one local tactic: the public
theorem had accumulated enough elaboration work that the terminal-speed block
hit the declaration heartbeat wall.  Further line-by-line tuning would not
address that declaration-level cost.

The terminal-to-moving distance argument is now the private producer
`edist_move_lt`.  Its statement contains only the solution and controlled ball,
the full regular interval and terminal completeness, `eps` and `q` with the
parabolic square bound and shortness conditions, the dimension-exponent
smallness bound, and one point in the terminal radius-`1/32` closed ball.  It
concludes that the same point lies in the moving radius-`1/16` open ball.  The
proof uses the public `edistTo_terminal` bridge and the same strict exponent
margin as before.  It has no `theta`, `rho`, `Z`, `alpha`, `K`, or compactness
hypothesis, so it is a genuine local metric-distance producer rather than a
consumer wrapper.

The main theorem's `hKmove` block now only derives
`q^2 <= eps * radius^2` from `q <= b`, unfolds terminal-ball membership at the
call boundary, and applies `edist_move_lt`.  This resets the heartbeat at a
mathematically natural boundary without changing any public statement,
assumption, constant, or route.  The split and its consumer are focused-verified.

## Post-split back-half diagnostics

After the distance producer split, elaboration reached the first-exit energy
block.  The prefix supplied to `hspeedBound` must be restricted from
`Icc 0 q` to the `Icc 0 t` domain of `hstay`; it now passes
`u <= q <= t` explicitly.  The module also opens `MeasureTheory`, matching the
native `NLCEndpoint` environment so the interval-integrability statement sees
`volume` directly.

The square-root reach estimate was another pure scalar calculation embedded in
the full geometric context.  It is now the private theorem `reach_small`,
placed before all universe and geometry variables.  Its only inputs are
`0 < t`, `0 < eps`, `t^2 <= eps * r^2`, and `0 < r`; it proves the strict
radius-`1/32` reach bound by the existing squared inequality route, with all
nonnegativity facts explicit and the final arithmetic restricted to the two
needed inequalities.  The main proof derives `htSq`, changes the local
`Bsmall.radius` target to `B.radius / 32`, and invokes the helper.  The later
diagnostic at the `lExp_mem_ball` call is intentionally unchanged for a fresh
post-refactor check.  No public statement, assumption, constant, or heartbeat
changed.

The post-split focused check subsequently elaborated the full file and found
only one helper typo: `sq_pos_of_pos` had been passed the scalar `r` instead of
its positivity proof `hr`.  This is corrected to `sq_pos_of_pos hr`.  No other
diagnostic remained in that pass; the exact next step is one focused recheck of
the corrected file.

That recheck reduced the file to one scalar obligation inside `reach_small`.
After clearing denominators, the goal is the strict constant comparison
corresponding to `1024 * t^2 < 1536 * eps * r^2`.  The weak bound
`t^2 <= eps * r^2` alone does not expose the strict slack to linear arithmetic;
it also needs `0 < eps * r^2`.  The helper now records
`hscalePos := mul_pos heps (sq_pos_of_pos hr)` and the final
`nlinarith only` receives exactly `htSq` and `hscalePos`.  This is the remaining
elementary scalar proof, not an API or route issue; all constants and public
assumptions remain unchanged.

## Eighth focused diagnostics

The remaining timeout was precisely the elaboration of the generic
`mul_le_mul_of_nonneg_left` application, not the surrounding arithmetic.  The
step now uses the ordered-field equivalence
`(mul_le_mul_left (show (0 : Real) < 8192 by norm_num)).2 hepsTiny`, and every
`8192` and `1 / 8192` in the local calculation is explicitly typed as `Real`.
This removes generic instance search while preserving the identical inequality;
there is still no automation or heartbeat change.

## Ninth focused diagnostics

The ordered-field iff still timed out when elaborated inside the full theorem,
confirming that the obstruction was context size rather than the chosen
monotonicity lemma.  The complete scalar statement is now the private theorem
`one_le_scaled`, placed before all universe and geometry variable declarations.
It depends only on `eps : Real`, its positivity, and
`eps <= 1 / 8192`, and proves the result with the same typed `le_div_iff₀`
calculation.  The main proof now invokes this helper directly.  The helper name
is within the project budget and cannot inherit unused section variables; no
public API, constant, assumption, heartbeat, or mathematical route changed.

## Tenth focused diagnostics

Inside the small `one_le_scaled` helper, the remaining generic iff elaboration
was replaced by the direct
`mul_le_mul_of_nonneg_left hsmall (show (0 : Real) <= 8192 by norm_num)`;
the small scalar context avoids the full-theorem performance problem.

The next timeout came from simplifying the entire quantified moving-ball
hypothesis and then the complete speed theorem result merely to unfold the
local name `alpha`.  The proof now constructs a pointwise-normalized `hmove'`:
each application unfolds `alpha` separately before passing it to
`lRegSpeed_unif`.  The following calculation uses `change` to expose the
`lRegCurve` form of its single goal and then takes `hqSpeed` exactly.  No large
quantified proposition is sent through `simpa`; the statement, constants,
assumptions, and heartbeat remain unchanged.

## Eleventh focused diagnostics

The timeout occurred while elaborating the expanded statement of `hmove'`
itself, before its pointwise proof.  Explicit normalization therefore made the
term larger without helping inference.  That adapter has been removed.  The
original `hmove`, stated with the reducible local definition `alpha`, is passed
directly to `lRegSpeed_unif`, allowing the unifier to delta-reduce only when
needed.  Likewise, the first calculation step now takes `hqSpeed` directly;
the explicit `change` to the full `lRegCurve` expression was removed.  This is
a definitional-equality simplification only, with no statement, assumption,
constant, route, or heartbeat change.

## Twelfth focused diagnostics

The next timeout moved to the scalar tail of `hspeedBound`, where the full
geometric context surrounded the calculation absorbing the initial speed and
the additive `1` into `1 / (2048 * eps)`.  That entire calculation is now the
private theorem `speed_absorb`, placed before all universe and geometry
variables.  It carries only `eps`, a scalar `U`, positivity of `eps`, and the two
input inequalities.  In this small context it uses the existing monotonicity
step followed by the same field normalization.  The main proof is now simply
`hqSpeed.trans (speed_absorb heps hU0le hone)`.  The helper cannot inherit
unused section variables, and no public API, constant, assumption, heartbeat,
or mathematical route changed.

## Thirteenth focused diagnostics

The next timeout occurred at `by_contra hsK` before the first-exit proof body:
the tactic was normalizing and pushing negation through a proposition containing
the local definitions `K` and `alpha`.  The proof now enters contradiction by
the term-level `Classical.byContradiction` and introduces `hsK` directly.  No
local definition is unfolded, and the first-exit argument itself is unchanged.
This is a tactic-elaboration repair only; no statement, hypothesis, constant,
heartbeat, or mathematical route changed.
