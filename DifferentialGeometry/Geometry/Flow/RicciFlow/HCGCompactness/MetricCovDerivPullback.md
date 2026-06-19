# MetricCovDerivPullback

2026-06-17: started the pullback bridge for the HCG/P4 source-domain
seminorm comparison.  The first target is
`metricCovDeriv_one_pullback_sections`, an order-one metric-covariant-
derivative naturality theorem on smooth section slots.  The proof route uses
`metricCovDeriv_one_eval_smooth_slots`, `directionalDeriv_pullback`, and
`metricCov_pullback`.

Focused verification passed.  The section-slot order-one theorem, its pointwise
slot wrapper, and the all-orders pointwise theorem `metricCovDeriv_pullback`
all elaborate.

The pointwise wrapper uses `ContMDiffSection.exists_eq_at_gen` to extend the
leading direction and the two metric slots to smooth sections, then specializes
`metricCovDeriv_one_pullback_sections`.

The all-orders proof uses pointwise induction: arbitrary slots are first
extended to smooth sections, the leading derivative term is transported by
`extDerivFun_comp_diffeomorph`, and each connection-correction term uses the
induction hypothesis plus `metricCov_pullback`.

The next local step is to turn this pointwise tower naturality theorem into the
source-domain seminorm comparison needed by the P4 compactness layer.

Added the evaluated algebraic bridge
`metricDiffCovDerivAt_pullback`: the difference tower itself transports under
pullback when evaluated on arbitrary slots.  It is a direct specialization of
`metricCovDeriv_pullback` to the two metric towers and is the input the future
`metricDerivNorm` transport lemma needs before invoking tensor-norm invariance.
Verification for this added bridge is pending because the global Lake lock is
currently owned by another build.

Added the HCG-local tensor norm transport lemma
`normSq0S_pullback_eval_of_orthonormal`.  It proves equality of source
`normSq0S` under a pullback metric and target `normSq0S`, assuming an
orthonormal source basis and an evaluated pullback relation for the tensor.  The
proof uses `Diffeomorph.mfderivToContinuousLinearEquiv`, maps the source basis
to the target, rewrites both norms as orthonormal component sums, and matches
the sums term-by-term.  Verification is pending behind the same global Lake
lock.

Added `metricDerivNorm_pullback_of_orthonormal`, the pointwise scalar transport
for `metricDerivNorm` under pullback.  It combines the evaluated
`metricDiffCovDerivAt_pullback` bridge with the tensor norm transport lemma.
The theorem still takes the source orthonormal basis as an explicit input; the
next packaging step is to choose such a basis and lift the equality through
`metricDerivNormSupOn`/source compact sets.  Verification is pending behind the
same global Lake lock.

Added the no-basis pointwise corollary `metricDerivNorm_pullback`, choosing the
source orthonormal basis via the existing `exists_gOrthonormalBasis` producer.
If this verifies, the remaining source-domain bridge is no longer tensor
naturality; it is the `metricDerivNormSupOn` lift over `sourceCompactSet`.
Verification is pending behind the same global Lake lock.

Added `metricDerivNormSupOn_pullback_image`, lifting pointwise pullback
invariance to the raw supremum over a source set `K`, with target set
`Phi '' K`.  This is the natural input for the P4 source-domain convergence
constructor once the image-compact/domain hypotheses are wired.  Verification
is pending behind the same global Lake lock.

Targeted module-build refresh for this new file timed out twice without a Lean
diagnostic, and a later axiom-print pass was blocked by a separate global Lake
build.  So the checked source theorem is in place, but the downstream `.olean`
refresh and all-orders axiom print remain a verification-performance follow-up.

Continuation note: the focused check for the added seminorm transport lemmas is
still blocked by the same active global Lake build.  Process inspection shows
the build is live and advancing through unrelated modules, so this is a shared
verification scheduling blocker rather than a Lean proof error in this file.

2026-06-18 continuation: the earlier lock cleared, but a new active global Lake
build for `ExtendedSolutionRegularity` is holding the lock.  Text-only hygiene
found no `sorry`/`admit` in this file or its two upstream touched files.  The
focused check for the seminorm transport lemmas still has not run.

Second resumed check: the same global build remains active and the Lean worker
set/CPU counters are still moving.  The focused check is still queued behind
shared verification rather than blocked by a known local proof error.

Third resumed check: the same global build is still live; Lean worker CPU
counters increased again.  This satisfies the repeated-tooling-blocker stop
condition for the current goal.  No new Lean diagnostic for this file is
available yet because the focused check still cannot be started safely.
