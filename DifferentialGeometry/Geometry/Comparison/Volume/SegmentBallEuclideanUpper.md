# SegmentBallEuclideanUpper

## `gBall_model_eucl`

The source-written theorem identifies the complete zero-curvature polar model
factor with canonical Euclidean ball volume. It first reverses
`gBall_model_int`, where `q = 0` makes the model density constant. The constant
set integral is then evaluated as the pole density times `modelHaar` of the
metric tangent ball.

The new `normalHaar_eq` bridge converts that weighted chart-model measure to
the pushforward of canonical volume by `normalFrame`. The preimage of the
closed metric tangent ball is the canonical closed ball by
`normalFrame_sqrt`; pushforward evaluation and
`Measure.addHaar_closedBall_eq_addHaar_ball` finish the normalization. No
Ricci bound, metric-norm realization, or dimension-lower-bound hypothesis is
introduced.

The first focused attempt failed on five local elaboration shapes: unqualified
`sphere`, a missing local `Nontrivial E` witness, incomplete simplification of
the zero-curvature model density, an implicit measure-scalar coercion, and
under-specified parameters at the `normalHaar_eq` call. The source has been
statically repaired by using `Metric.sphere`, installing the finrank witness,
isolating the constant-integrand equality with `simp [hypDensity, hypSn]`,
making the ENNReal measure scalar explicit, and specifying `E`, `M`, and `I`.
These repairs were subsequently exercised by the later successful check.

The second focused attempt narrowed the remaining failures to two local
items. The scalar-to-multiplication step carried an unused
`ENNReal.smul_def`; it now uses the exact `smul_eq_mul` rewrite. The other
failure exposed an upstream assumptions bug: `normalHaar_eq` inherited an
analytic `IsManifold I ω M` binder, which cannot be obtained from the smooth
structure. The producer's file-level binder has been weakened to the
notation-free smooth grade, and the invalid local instance bridge has been
removed here.

The corrected smooth-binder `normalHaar_eq` producer is now warning-free
focused green, and its explicitly named module refresh completed successfully;
its direct axiom audit is standard-three-axiom clean. With that refreshed producer,
`gBall_model_eucl` elaborated successfully. The only diagnostics were the
unused section variables `[T2Space M]` and `[SigmaCompactSpace M]`; the theorem
is now wrapped in the corresponding declaration-local `omit`. After that
repair, the consumer passed warning-free focused verification and its explicitly
named module refresh completed successfully. Its direct unified axiom print is
also standard-three-axiom clean.

The `gBall_model_eucl` proof implementation, focused verification, and named
artifact refresh are 100%. It completes
the model-factor normalization producer, not the separate strict-volume
rigidity wrapper; this is roughly 5% of that dedicated rigidity branch and
well below 1% of the full Morgan--Tian/Poincare program.

## `segBall_vol_pow`

The global zero-curvature specialization is complete.  The theorem reuses
`segBall_vol_rel` and `hypRadVol_zero`, rewrites the model radial volume as
`t ^ n / n`, and cancels the common positive finite factor `ENNReal.ofReal n⁻¹`.
No additional geometric hypothesis or consumer-side assumption was introduced.

Focused verification passed after the named `BishopBall` module refresh.

Progress boundary: `segBall_vol_pow` is 100%, and its dedicated global `q = 0`
adapter machinery is 100%.  The distinct local compact-closure endpoint is
handled separately by `ball_vol_le_eucl` below.

## `ball_vol_le_eucl`

The local compact-closure endpoint is source-written.  It imports the
completeness-free raw producer `rawDens_le_zero`, applies it pointwise on the
compact raw minimizing locus used by `rawBall_vol_le_int`, and integrates the
constant pole-density bound.  A public `rawSpeed_sq` identity keeps the raw
radial curve inside the smaller closed metric ball, so the theorem consumes
only Ricci nonnegativity on that ball rather than a global Ricci predicate.

The final normalization uses `normalHaar_eq`, the normal-frame preimage of the
closed metric tangent ball, and equality of Haar measure on open and closed
Euclidean balls.  It does not use `ConnectedSpace M`, `CompleteSpace M`, an
injective exponential map, a no-conjugate assumption, or a positive-radius
hypothesis.  Compactness is required only for the strictly larger buffer ball.

The first focused check reached the complete proof and stopped on three local
elaboration shapes only: a tangent-space coercion before the radial norm
rewrite, ambiguity of the smoothness-order top notation under the ENNReal
scope, and the definitional `mfderiv`/`curveVelocity` form of the speed-square
identity.  The source now makes each of these forms explicit.

The second focused check cleared the coercion and speed forms and found only
the second occurrence of the same top-notation ambiguity in the explicit
smoothness-order inequality.  It is now written without overloaded infinity
notation; no mathematical or API change was needed.

The final focused check is warning-free GREEN, and the exact named artifact
refresh is GREEN (3998/3998).  Thus `ball_vol_le_eucl` is a proved and refreshed
endpoint with the intended compact-buffer and local Ricci hypotheses.  The
196-declaration unified audit directly prints it and every new raw-density
producer; all depend only on `propext`, `Classical.choice`, and `Quot.sound`.
This closes the eighth P1a endpoint.
