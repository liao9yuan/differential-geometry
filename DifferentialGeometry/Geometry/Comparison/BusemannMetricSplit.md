# Busemann metric split

## Scope

This module completes the metric part of the Cheeger--Gromoll product assembly.
Starting from the verified smooth product diffeomorphism, it constructs the
regular zero-level metric, proves the horizontal, vertical, and mixed metric
blocks, and identifies the pullback ambient metric with the standard product
metric.  All transported Morse-model and regular-level instances remain local;
no global instance or new hypothesis is introduced.

The first public producer is `busemannProd_mfderiv`.  For the product map
`Phi(z,t) = busemannFlow (-t) z`, it splits the differential at `(z,t)` on
`(v,s)` into the spatial differential of the fixed-time flow, applied to the
differential of the regular-level inclusion, minus `s` times the Busemann
gradient at `Phi(z,t)`.  The proof route is the native product derivative
decomposition, followed by the chain rule for the horizontal component and
the integral-curve derivative of `busemannFlow` composed with negation for the
time component.

The next source-written producer, `busemannLevelMetric`, constructs the
induced smooth metric on the regular zero level by applying the native
`immersionPullMetric` API to the level-set inclusion.  The required source
`T2Space` instance is inherited from the ambient manifold, while
`SigmaCompactSpace` comes from the zero level being closed by smoothness of
the Busemann function.  Injectivity of the inclusion derivative is obtained
without a new immersion assumption: compose the zero-time product inclusion
with `busemannProdDiffeo`, use the chain rule and `mfderiv_prod_left`, then
combine injectivity of the diffeomorphism derivative with injectivity of the
standard product inclusion.

The public endpoint `busemannMetricSplit` states the resulting global
Riemannian product identity without requiring a caller-supplied model
equivalence.  The file introduces no `sorry`, `admit`, axiom, wrapper predicate,
or additional public assumption.

The source-written horizontal block `busemannProd_horiz` compares the ambient
metric on the two horizontal derivatives of the product diffeomorphism with
the induced zero-level metric.  It specializes `busemannProd_mfderiv` at
zero time components, applies `busemannFlow_inner` to remove the spatial
  flow, and unfolds the induced metric only through `immersionPull_inner`.
The vertical and mixed terms are supplied by the following dedicated blocks.

The source-written vertical block `busemannProd_vert` compares the two pure
time derivatives with the standard flat metric on `Real`.  It specializes
the differential split to zero horizontal components, uses the unit
Busemann-gradient identity at the flowed point, expands bilinearity, and
normalizes the real inner product.  `busemannProd_cross` proves mixed
orthogonality by differentiating the Busemann flow-value and level-set
identities.  The private four-block bilinear helper then assembles these three
blocks into `busemannMetricSplit` after choosing the codimension-one Morse model
from the ambient finite dimension.

## Verification state

The first focused check stopped in the theorem statement before the proof body:
Lean did not identify the dependent tangent space at the explicit flow value
with the tangent space at `Phi(z,t)`, so subtraction could not synthesize an
`HSub` instance.  The later apparent binder/type errors are cascading from that
ill-typed statement.  The smallest static repair is to state the gradient at
the explicit, definitionally matching point `busemannFlow (-t) z.1` (which is
the value of `Phi(z,t)`), or equivalently to transport all terms through
`NormedSpace.fromTangentSpace`; the former keeps the formula shortest and is
better suited to the next inner-product consumer.  This shortest repair is now
applied, and the second focused check accepted the statement.  It then stopped
at the first proof-body use: tactic introduction consumed the dependent
result-type `let` binders (`b`, `J`, `hbJ`, and `hregJ`) instead of the intended
quantified variables `(z,t,v,s)`.  All later type errors are cascading from
those shifted names.  The minimal local repair is to reduce the expected
result-type lets at the start of the tactic block before `intro`; the derivative
route itself still had not been elaborated far enough to assess.  After that
repair, the third focused check reached the intended route and reduced the
remaining failures to two definitional shapes: the time-slice goal still shows
the opaque reused diffeomorphism `Phi(z,r)` rather than the explicit flow
`flow(-r,z)`, and the final goal retains the local abbreviation `b` on one side
versus `busemann gamma` on the other.  The product derivative split,
horizontal chain rule, and negated integral-curve derivative all elaborated.
The next repair is therefore only an explicit `change` of the time slice to the
flow function and a final unfolding of `b`.  The fourth focused check accepted
that `change`; the remaining time-slice mismatch is now exactly the application
normal form of the composed continuous-linear maps from the integral-curve and
negation derivatives.  Rewriting directly with `hchain.mfderiv` and simplifying
the resulting `smulRight`/composition application is the narrow next step.
The final main goal becomes literally reflexive after unfolding `b`, so it only
needs an explicit closing `rfl`.  The fifth focused check confirmed the final
goal closure, but `rw [hchain.mfderiv]` did not match the extensionally equal
time functions `fun r => flow (-r) z` and `(fun u => flow u z) comp Neg.neg`.
The remaining repair is purely syntactic: `change` the derivative function to
the latter composition form immediately before the rewrite, then use the
already prepared continuous-linear-map simplification.  The sixth focused
check confirmed that the rewrite now matches and leaves one closed algebraic
goal: the composed `smulRight` map applied to `s` equals `-(s smul grad)`.
Generic simp does not unfold that displayed continuous-linear-map term in this
dependent tangent fibre.  The smallest final repair is an explicit `change` to
`(-s) smul grad = -(s smul grad)`, followed by `neg_smul`; the four attempted
CLM simp arguments are unused and should be removed.  The seventh focused
check showed that this `change` jumps one definitional layer too far: Lean still
sees the left side as `(one.smulRight grad).comp (-one)` applied to `s`.
The remaining local step is to `change` only to
`(one ((-one) s)) smul grad = (-s) smul grad`, which directly unfolds the
`comp` and `smulRight` applications; scalar simplification and unfolding `b`
then close it.  With that final one-layer change, the complete
`busemannProd_mfderiv` producer passes a warning-free focused check.  The
downstream-required named refresh also passes, so the export is available to
the subsequent metric consumer from a fresh artifact.

`busemannLevelMetric` is source-written on top of that refreshed
diffeomorphism and the native immersion-pullback metric API.  Its first focused
check reached the final injectivity closure and stopped only because
`ContinuousLinearMap.inl_injective` is not an exported constant (the similarly
named theorem belongs to `LinearMap`).  Replacing that name with the direct
`Prod.fst` injectivity proof closes the producer, and the second focused check
is warning-free GREEN.  Thus the local Morse-model instances, closed-level
sigma compactness, transported inclusion smoothness, product chain rule, and
diffeomorphism derivative equivalence are all verified together.

`busemannProd_horiz` is source-written.  Its first focused check stopped at
the declaration start with a deterministic `whnf` heartbeat timeout before
any proof-local error was reported.  The likely cause is repeated reduction of
the full dependent `let` chain while elaborating the RHS call to
`busemannLevelMetric`, rather than a mathematical obstruction.  No
vertical/cross code was added.  The smallest next step is a theorem-local,
reasoned heartbeat allowance or an equivalent proof-shape reduction that
shares the already established local instances without unfolding the metric
definition during statement elaboration.  The scoped heartbeat allowance
clears that timeout and the next check reaches the intended proof.  It now
stops at the `busemannFlow_inner` rewrite because the metric base point remains
displayed as the opaque local diffeomorphism value `Phi (z,t)`, while both
derivative arguments are already in explicit fixed-time flow form.  This is a
local definitional-shape mismatch: changing only that base point to
`busemannFlow (-t) z` before the flow-isometry rewrite is the smallest next
step.  That explicit base-point change makes the native flow-isometry theorem
match, and the complete horizontal block now passes a warning-free focused
check with its scoped elaboration budget.

## Project accounting

The metric Cheeger--Gromoll splitting endpoint `busemannMetricSplit` is now
formally stated and proved, so that endpoint is **100% source-verified**.  Its
dedicated metric-splitting machinery is likewise **100% focused-verified**:
the derivative producer, induced level metric, and all three metric blocks are
warning-free focused GREEN.  The final module artifact is also refreshed and
exports the endpoint; the unified project axiom audit remains the downstream
verification step.

`busemannProd_vert` is source-written and introduces no new assumption; the
local finite-rank nonzero instance is derived directly from the existing
dimension hypothesis.  Its first focused check reaches the proof and stops
because the attempted simplification of the two zero-horizontal differential
formulas leaves both nested continuous-linear-map applications to zero
unchanged.  The following explicit `change` to pure gradient multiples
therefore cannot match, and all three supplied simp arguments are reported
unused.  This is a local proof-shape issue, not a mathematical/API blocker.
Deriving each pure vertical equality through separately typed zero derivatives
resolves that mismatch.  The dependent declaration then needs the same scoped,
reasoned elaboration allowance as the horizontal block.  Finally, the flat
real metric is normalized through the native scalar-inner formula after
unfolding the vector-space metric.  With these changes the complete vertical
block passes a warning-free focused check.  The next frontier is mixed
orthogonality from level-set tangency.

`busemannProd_cross` now supplies that mixed block with the horizontal vector
first and the vertical vector second.  Its proof differentiates the fixed-time
flow identity for the Busemann function, transports the resulting differential
back to the zero level, and differentiates the level-set inclusion identity to
show that the horizontal differential annihilates the Busemann function.  The
native `inner_gradFun_right` bridge then turns this tangency statement into
orthogonality, while the pure-vertical derivative is obtained from the same
typed zero-map reduction used by the vertical block.  The first check exposed
only three local zero-normal-form mismatches; after replacing them with direct
linear-map simplification and explicit additive/multiplicative zero closures,
the complete cross block passes a warning-free focused check.  No artifact
refresh was run.  The remaining local frontier is the final product-metric and
isometry assembly from the three verified metric blocks.

That final assembly is now implemented.  The private `splitModelEquiv` chooses
the canonical codimension-one Morse model from the ambient finite dimension;
the existing dimension hypothesis proves the required subtraction identity.
The private `busemannMetric_aux` installs the same transported model, regular
zero-level, Hausdorff, and sigma-compact instances as the preceding producers,
then applies metric extensionality pointwise.  Each product tangent vector is
split into horizontal and vertical summands, and the four pairings are supplied
by `busemannProd_horiz`, `busemannProd_cross`, symmetry plus the cross theorem,
and `busemannProd_vert`.

The first assembly shape timed out deterministically while repeatedly reducing
the dependent metric and bilinear-map expression.  Target-directed rewriting,
single reduction of the result-type lets, and a temporary larger local budget
confirmed that this was an elaboration-shape wall rather than a missing
geometric fact.  Factoring only the generic four-block bilinear expansion into
the private lowest-layer `inner_add_blocks` helper brought the auxiliary theorem
back under its reasoned 800k theorem-local allowance.  The public
`busemannMetricSplit` then removes the explicit model equivalence argument by
choosing dimension minus one internally.  The complete file passes a
warning-free focused check.  The subsequent targeted named refresh built its
single prerequisite but the target Lean process terminated after 675 seconds
with Windows exit code 3221225477 and no Lean source diagnostic, during a host
resource-pressure episode.  A single-thread retry avoided that process crash,
but the stricter artifact build then reached two deterministic typeclass-search
timeouts in the two product-derivative `map_add` closures, where placeholders
left the additive homomorphism class underconstrained.  It also reported that
three older scoped heartbeat explanations must be placed after, rather than
before, their option commands to satisfy the build linter.  Thus the source
verification remains GREEN, while the module artifact is not confirmed
refreshed.  Replacing both generic `map_add` applications with the explicitly
typed differential map's `.map_add`, and moving all four reason comments into
the linter-required option scope, restores a warning-free single-thread focused
check.  The final single-thread targeted refresh also passes warning-free, so
the module artifact now exports the verified metric-splitting endpoint for the
downstream axiom audit.
