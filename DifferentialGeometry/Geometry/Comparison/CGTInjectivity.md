# CGTInjectivity

## State — 2026-07-27

The canonical route is the direct Cheeger--Gromov--Taylor
collision/overlap estimate, not a universal-cover/deck-displacement
construction.

`intrPullVol` is the pullback Riemannian volume of an intrinsic framed tangent
ball.  `intrPullVol_le_hyp` isolates the analytic half: radial nonconjugacy and
a Ricci lower bound control this pullback volume by the hyperbolic model ball.

The first draft of a direct `intrInj_ge_cgt` was re-audited against
Cheeger--Gromov--Taylor, Theorem 4.3, before any downstream use. Its initial
`2r`-ambient / coefficient-`r` statement was too strong and has been removed.
The first public target is now the original loop theorem
`intrLoop_ge_cgt`. It uses a larger nonsingular radius `R`, assumes the
project-native global `Rm04` norm bound `K` and curvature scale
`R ≤ π / √K`, and concludes

`ℓ ≥ (r₀ / 2) * Vol(B(p,s)) /
  (Vol(B(p,s)) + intrPullVol(p,r₀+s))`

for a based radial loop of length `2ℓ`, under
`r₀ + 2s < R` and `r₀ < R / 4`. The desired injectivity estimate is a later
corollary using a separate local collision-to-loop lemma. At the HCG
specialization `r₀ = s = r`, its coefficient is `r / 2`, its pullback radius
is `2r`, and a safe strict ambient choice is `R = 5r`.

The loop theorem's proof is the file's single intentional `sorry`. The source
is focused-green with only that intentional warning. During the check, the
tangent norm instance had to follow the established project order: disable the
legacy tangent instances before introducing the `RiemannianBundle`; the
Euclidean almost-everywhere argument also needs the locally derived
`Nontrivial E` witness. These were elaboration repairs, not new mathematics.

The live tree now has the length-bounded homotopy relation, compact-fenced
short exponential lifts, homotopy lift endpoints, right cancellation, a short
flat-path selector, the canonical flat radial lift, and the actual inverse
fiber injection of paper Lemma 4.5.  It still has no CGT propeller theorem.  The
remaining chain is:

1. iterated loop classes are distinct by the small pullback-ball
   convex-center argument;
2. these classes produce disjoint inverse sheets over the radius-`s` ball;
3. finite additivity plus the area formula gives the multiplicity estimate.

After this theorem, `loop_of_not_inj` must turn noninjectivity on a strict
subball into a nonzero short radial loop. Only then should
`intrInj_ge_cgt` be stated as a corollary.

The global `Rm04` hypothesis is the stronger project-native source of the
sectional upper bound used in the classical theorem. The convex-center fact
must be derived from this curvature/radius data;
it must not be introduced as a new HCG input. A universal-cover/deck route does
not remove the bounded-length or no-early-torsion step.

The short-path lift and inverse-fiber producers are complete.  The
multi-sheeted intrinsic exponential ball now also has a focused/exact-green
genuine pullback metric without assuming whole-ball injectivity.
`rm04_localPull` is focused/exact current, and `intrPull_rm04` is
focused-green; together they close the local curvature-identity API.  The
deepest remaining producer is now strict convexity and a unique finite-family
center in the small pullback ball, derived from the curvature/radius data.  The
propeller step additionally needs the canonical loop-transport action; the
arbitrary injection of Lemma 4.5 does not encode that action.

Current honest accounting:

- `intrPullVol_le_hyp`: theorem 100% after focused verification;
- `intrLoop_ge_cgt`: corrected statement, proof 0%;
- `intrInj_ge_cgt`: not yet stated, theorem 0%;
- paper Lemma 4.4 endpoint cancellation: theorem 100%, machinery 100%;
- paper Lemma 4.5 even cover: theorem 100%, dedicated machinery 100%;
- CGT pullback metric packaging: theorem/API 100%, focused and exact current;
- local pullback curvature identity: theorem/API 100% focused, generic theorem
  exact current and CGT specialization exact refresh pending;
- paper Lemma 4.6 propeller: theorem 0%, dedicated machinery about 62%;
- dedicated pointwise CGT machinery: about 58--62%;
- sequence-level `InjRadiusDecayInput` producer: theorem 0%;
- unconditional metric compactness theorem: 0%;
- whole HCG supporting machinery: about 61%.

## State - 2026-07-28

The direct CGT route is now complete.  The multiplicity-sensitive area bridge
from `SegmentArea` / `SegmentMeasure` combines the sharp fibre count with the
intrinsic exponential Jacobian integral.  `flatLoop_ge_cgt` factors the common
propeller/area argument; `intrLoop_ge_cgt` is its radial-loop specialization.
`collision_ge_cgt` turns a strict framed-exponential collision into the loop
estimate, and `intrInj_ge_cgt` is the final pointwise injectivity-radius
theorem.

No global `ConnectedSpace` assumption, pullback-ball completeness assumption,
or new injectivity/cut-time input was introduced.  The formerly intentional
`sorry` in `intrLoop_ge_cgt` is gone, and the older public statement is
preserved.

Focused verification and the exact module refresh passed.  Direct axiom audits
of `flatLoop_ge_cgt`, `collision_ge_cgt`, `intrLoop_ge_cgt`, and
`intrInj_ge_cgt` contain only `propext`, `Classical.choice`, and `Quot.sound`.

Honest accounting:

- `intrPullVol_le_hyp`: theorem 100%;
- paper Lemma 4.6 propeller/fibre count: theorem 100%, machinery 100%;
- `intrLoop_ge_cgt`: theorem 100%, dedicated machinery 100%;
- `intrInj_ge_cgt`: theorem 100%, dedicated machinery 100%;
- sequence `InjRadiusDecayInput` producer: theorem 100%, dedicated machinery
  100%;
- unconditional Theorem 3.9: theorem 0%; CGT is no longer its blocker;
- whole HCG supporting machinery: about 67%.
