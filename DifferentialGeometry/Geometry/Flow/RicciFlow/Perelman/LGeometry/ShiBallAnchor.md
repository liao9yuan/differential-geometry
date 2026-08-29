# ShiBallAnchor

## Route

Fix a minimizing geodesic for the metric at the later slice and let `L(s)` be
the length of that same curve in the metric at time `s`. The scaled length
`exp(Lambda * s) * L(s)` has nonnegative derivative whenever it is at most the
controlled radius: positive time supplies strict room between `L(s)` and the
radius, every curve prefix therefore stays in the open flow ball, and
`ricci_abs_of_rm` applies along the whole curve.

A genuine first-hit argument is applied after reversing time. If the scaled
length had left the controlled range at an earlier time, the first hit of the
reversed function would give a final tail on which the scaled length is at
most the radius. Monotonicity on that tail contradicts the strict later-slice
inequality. The resulting full-window monotonicity anchors the initial
distance by the later scaled distance.

For the two-slice comparison, time translation reuses that backward anchor but
cannot produce the forward inequality: reversing time does not preserve the
Ricci-flow equation.  The ordered core therefore adds the symmetric upper
path-length derivative bound from the same absolute Ricci estimate and runs a
forward first-exit argument on
`exp (Lambda * (t - q)) * L(q)`.  A doubled strict start-slice bound first keeps
the start-minimizing geodesic inside the controlled ball and proves the forward
distance bound.  Multiplying that bound once more supplies the strict
later-slice room needed by the shifted old anchor, which proves the reverse
bound.  Thus no minimizing-curve containment is added as an assumption.

## Status

`dist0_le_scaled` is source-written and passed a warning-free focused check.
Its public endpoint is the ENNReal inequality
`d_0(center, x) <= ofReal (exp (Lambda * t)) * d_t(center, x)`.  The
regularity window remains `Ioc 0 t`: continuity of the fixed-curve length
closes the zero endpoint.  The only public completeness input is completeness
of the later Riemannian slice used to choose the minimizing geodesic.  No
whole-manifold curvature bound is used.  The module has not been given a named
artifact refresh in this lane.  Its warning-free named refresh subsequently
passed, and the real downstream consumer `ShiBallCutoff.lean` also passed its
focused check against the refreshed declaration.

`distPair_scaled` has now been source-written as the ordered two-slice public
endpoint.  For `s <= t`, regularity on `Ioc s t`, both slice completeness
inputs, and containment of `Icc s t` in the controlled time cylinder, its one
strict hypothesis is
`ofReal (exp (2 * Lambda * (t - s))) * d_s(center,x) < ofReal radius`.
It concludes both
`d_s <= ofReal (exp (Lambda * (t - s))) * d_t` and
`d_t <= ofReal (exp (Lambda * (t - s))) * d_s` exactly in `ENNReal`.
The old theorem keeps its original signature as a specialization of the
private zero-slice core.  The first focused verification failed.  The first
error was an invalid `omit` wrapper on the new upper path-length derivative
helper; the same pass then reached a local shifted-ball structure-construction
parse failure.  Both received static source repairs after the guard was
returned, but those repairs have not been checked.  There is still no `sorry`
or `admit`; exact elaboration of the repaired helper and shifted-ball transport
remains the verification blocker.

The second focused verification also failed. Its first independent error was
the new helper spelling the existing tangent-lift API's Greek named argument
`γ` as `gamma`; that call received a static spelling correction after the
second guard was returned. The same pass exposed a later definitional-shape
mismatch in the upper Ricci bound, which remains untouched as the next known
elaboration error. The spelling repair has not been rechecked.

Before the next guard, that known scalar-shape mismatch received a static
repair: the absolute Ricci estimate is still rewritten only through the local
`Ric`, `G`, and `v` abbreviations, and the remaining
`-(A * G u)` versus `(-A) * G u` difference is closed by `neg_mul`. The same
static pass replaced the forward exponential derivative's sequence-focus
tactic with `all_goals ring` and migrated the two deprecated ordered
multiplication lemmas to `mul_le_mul_left` and `mul_le_mul_right`. None of these
repairs has been checked yet.

The third focused verification passed, so the repaired file and
`distPair_scaled` are now elaboration-verified with no `sorry` or `admit`. The
pass emitted one linter warning: the private `pathLength_deriv_le` automatically
includes unused `NeZero` and `SigmaCompactSpace` section variables. Therefore
the current status is focused GREEN but not yet warning-free; no named artifact
refresh has been run for the new export.

That warning has since received a narrow static repair: only `NeZero` and
`SigmaCompactSpace` are omitted around `pathLength_deriv_le`; the referenced
`I.Boundaryless` instance remains in scope. This linter-only repair has not been
rechecked, so the last observed verification result remains GREEN with the
warning above.

The fourth focused verification passed with no warnings. The complete anchor
file, including `distPair_scaled`, is now warning-free focused GREEN and remains
`sorry`/`admit`-free. No named artifact refresh or downstream consumer check was
run in this lane.

The subsequent explicit named module refresh completed successfully. It emitted
one style warning for an empty line inside the private zero-slice core, so the
exported artifact is current but the named build was not warning-free. No
downstream consumer or other module was checked in this lane.

That reported command-internal empty line has been removed statically. This is
a style-only source change with no theorem, proof, or export change; it has not
been rechecked, and no second named refresh is needed for downstream declaration
availability.

The final style-only focused verification passed with no warnings. The current
source is therefore warning-free focused GREEN; the previously completed named
refresh remains the current exported declaration artifact because the only
subsequent edit removed whitespace inside a command.

Progress accounting: verified `dist0_le_scaled` remains 100%; the new
`distPair_scaled` theorem and its dedicated source machinery are now 100%
focused-verified. They are dedicated machinery toward
the finite fixed-ball cutoff and
`shiRm1_ball`; `shiRm1_ball`, `smooth_nlc`, P2, and the final Poincare endpoint
remain 0% theorem endpoints until their own declarations are stated and
checked.  The latest plan-level estimate before integrating this brick puts
dedicated L8--L9 machinery at about 80--82%, reused generic infrastructure at
100%, and whole P0--P9 infrastructure at 15--25%; this note does not inflate
those aggregate figures for one verified helper.
