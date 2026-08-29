# Busemann line solution

## Role

`busemann_chart_data` is the full local weak-harmonicity producer for one
Busemann function of a supplied minimizing line.  Under the same complete,
connected, boundaryless Riemannian hypotheses as `buse_pair_eq_zero`, dimension
greater than two, and nonnegative Ricci curvature, it returns a Euclidean chart
ball, a normalized metric coefficient, and a positive scalar for which the
coefficient is the scalar multiple of `weightedInvGramOnEuclid` on the ball and
the positive Busemann raw pushforward is a `DeGiorgi.IsSolution`.

`busemann_chart_sol` keeps its existing public signature and is now the direct
projection which forgets only the scalar and coefficient-provenance equality.

The theorem adds no endpoint hypothesis.  In particular, local Sobolev
membership, the chart radius, the coefficient, and both weak inequalities are
constructed inside the proof.

## Source route

The positive Busemann function is intrinsically one-Lipschitz.  The generic
`Chart.raw_memW1p_of_lip` producer supplies its raw pushforward in `W^{1,2}` on
one chart ball.  This reuses the cutoff implementation extracted from
`BusemannLineEnergy`; no second cutoff argument is copied here.

That radius is intersected with half of a chart-target radius, so the closure
of the resulting common ball lies in the Euclidean chart target.  The global
identity `buse_pair_eq_zero` gives equality of the negative raw pushforward
with the pointwise negative of the positive raw pushforward, including outside
the chart target where both zero extensions vanish.  Multiplying the positive
Sobolev witness by `-1` therefore supplies the negative raw `W^{1,2}` input on
the same ball.

`busemann_lap` gives the two distributional Laplacian inequalities.  A single
call to `exists_metric_coeff` constructs one normalized coefficient on the
common ball, and two calls to `chart_super_of_lap` make the positive and
negative raw functions supersolutions for that same coefficient.  The negative
supersolution is transported to the pointwise negative of the positive raw
function by `IsSupersolution.congr_ae`; `IsSupersolution.neg_ball` then gives the
positive subsolution.  Pairing that subsolution with the positive
supersolution produces `IsSolution` in its canonical sub/super order.  The
producer now retains the already-constructed `s`, its positivity proof, and the
coefficient equality instead of discarding them at this final step.

## Verification

Source-only implementation completed while the shared elaboration guard was
occupied.  No Lean or Lake check was run.  There is no known mathematical gap;
the remaining risks are local elaboration shapes: unfolding the raw
pushforward equality, simplifying the `-1` Sobolev witness, and dependent
alignment of the existential coefficient with the final chart-ball center.
The source route did not encounter a failed alternative proof.
`raw_memW1p_of_lip` and its Euclidean producer have passed warning-free focused
verification and named refresh, and the shortened `buse_pair_memW1p` consumer
has passed its warning-free focused check.  `buse_pair_eq_zero` has also now
passed warning-free focused verification and its explicit named refresh.  The
upstream chain is fresh; this file itself must not yet be reported as verified
because of the local diagnostics below.

The first focused check of this file stopped on six local signature/namespace
and let-unfolding diagnostics, before reaching a PDE proof obligation:

- line 41: unknown `RicciBoundedBelow`; open
  `Geometry.Riemannian.BonnetMyers`, as in the now-verified Minimum producer;
- lines 43 and 47: the dependent public result mentions
  `NormalizedEllipticCoeff (finrank ℝ E)`, whose abbreviation requires
  `NeZero (finrank ℝ E)` before the proof-body `letI` is available.  The
  smallest assumption-preserving repair is to move the instance derived by
  `omega` from `hd` into a `letI` in the dependent result type, not to add a
  public `[NeZero]` binder;
- line 69: unknown `intrinsic_lip_cont`; open
  `Analysis.Sobolev.IntrinsicLp`;
- lines 112 and 117: `rw [bnE, bpE, ...]` treats applied local lets as rewrite
  proofs.  Unfold `bnE` and `bpE` first with `dsimp only`, then rewrite only by
  the two `chartPushedRaw_apply` lemmas.

No source repair, second check, named refresh, or other-file check was run after
these diagnostics.  The Solution claim remains held for the next authorized
static repair.

The subsequent source-only repair first searched `DifferentialGeometry` for an
existing dimension-derived `NeZero` instance in a dependent existential result.
No exact `hd`/`omega` analogue was present, but the canonical dependent-result
pattern is used by declarations such as `lambdaNet_cover`: install the instance
with `letI` in the result type, then repeat the same local installation in the
proof body.  `busemann_chart_sol` now follows that pattern with the `NeZero`
witness derived from `hd`; no public typeclass assumption was added.

The Bonnet--Myers and intrinsic-Lipschitz namespaces are now open.  Both raw
equality branches unfold `bnE` and `bpE` with `dsimp only` before rewriting by
the actual chart-pushforward application lemmas.  These are static repairs only
and the subsequent authorized focused retry passed without warnings.  The
explicit named refresh also completed successfully.  No downstream consumer
check has been run.

The subsequent coefficient-provenance extraction was initially written
source-only while the shared elaboration guard was occupied by P2.  The
original proof body was moved unchanged to `busemann_chart_data`, except that
its existing `A`, `s`, `hs`, and `hA` outputs are retained.
`busemann_chart_sol` now only projects that result.  No assumptions, predicates,
`sorry`, or imports were added.  The later authorized focused check passed
without warnings, and the explicit named refresh also passed completely
(9056/9056); the refreshed artifact now exports both declarations.

## Project status

`busemann_chart_data` and the unchanged-signature `busemann_chart_sol`
projection are warning-free focused and named-refresh GREEN, and are therefore
100% verified-complete as local producers.  The supplied-line splitting theorem
remains unstated and therefore 0% complete.  Its dedicated machinery remains
about 45--50%, since harmonic regularity, parallel-gradient/Bochner, flow, and
global product-isometry remain separate stages.  The whole P1c machinery
remains about 60--65%, the whole P0--P9 Poincare infrastructure about 15--25%,
and the final Poincare endpoint remains 0%.
