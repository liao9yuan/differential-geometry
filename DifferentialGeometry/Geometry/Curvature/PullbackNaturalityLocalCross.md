# PullbackNaturalityLocalCross

## State — 2026-07-27

`rm04_localPull` is the intended cross-model curvature naturality theorem for
`localPullMetric`.  Its proof selects the local partial diffeomorphism already
contained in `IsLocalDiffeomorph`, restricts it with
`PartialDiffeomorph.toOpensDiffeoCross`, and composes:

- germ locality under open restriction;
- global cross-model pullback naturality;
- equality of the selected branch with the original map on its open source.

After the separate curvature artifact chain finished rebuilding the direct
imports, the source passed focused verification with no diagnostics.  The
targeted artifact is exact-current (`3612/3612`).  The earlier failures were
therefore only transient missing-artifact failures, not proof regressions.

Honest accounting:

- `rm04_localPull`: theorem 100%, focused and exact current;
- its dedicated API/setup: 100%;
- CGT Lemma 4.6: theorem 0%, dedicated machinery about 60%;
- whole HCG supporting machinery: about 61%.
