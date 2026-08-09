# Rm04ProducerTail

The two `Rm04Producer` evolution endpoints, instantiated on a strictly
positive-time tail so that their last input disappears.

| Declaration | Content |
|---|---|
| `rm04EvolTail_at` | `∂ₜRm = ΔRm − 2(B−B+B−B) − drift` at the frame centre, from `S`/`hS` and the tail parameters only |
| `rm04EvolFamTail` | `hev` = `Riemann04BTensorWithRicciDriftEvolutionInFrameOn` for the per-point-centred families, same inputs |

Both are three-line compositions: `subst` the tail equation, then apply
`rm04Evol_at` / `rm04EvolFam` with `gInvDt := coordInvDt` and
`hmetricReg := tailCoordFrameReg`.  All the content is in `tailCoordFrameReg`
(see `Metric/TailFrameRegularity.md`) and in ruling R11, which made
`MetricFrameTimeRegularityInFrameOnLocal.inverseMetricDerivative` `u`-local.

## Why this is a separate module (the only real lesson here)

The natural home is the end of `Rm04Producer.lean`, and that is where these were
first written.  It does not work, for an instance-spine reason:

- `Rm04Producer.lean` declares **both** `[NormedSpace Real E]` and
  `[InnerProductSpace Real E]` in its variable block, so its `SolutionOn`s are
  elaborated with the standalone `NormedSpace` variable.
- `SolutionOn.timeRestrict` and every tail producer (`SolutionTimeRestrict.lean`,
  `Metric/TailFrameRegularity.lean`, `Connection/TailChristoffel.lean`) live in
  files with an `InnerProductSpace`-only block, so their `SolutionOn` argument has
  `InnerProductSpace.toNormedSpace` baked into the type — there is no `NormedSpace`
  slot left to unify.

Writing `S.timeRestrict …` inside `Rm04Producer.lean` therefore fails with

```
has type      @SolutionOn ?E ?_ InnerProductSpace.toNormedSpace …
but expected  @SolutionOn E inst✝¹⁵ inst✝¹⁴ …
```

and no amount of `(I := I)` pinning fixes it, because the two spines are
genuinely different terms.  Applying `rm04Evol_at` *from* an
`InnerProductSpace`-only file is fine — its `[NormedSpace Real E]` binder is then
instantiated with `toNormedSpace`, and everything agrees.  So the split is the
fix: this file uses the `InnerProductSpace`-only block, exactly as
`Connection/TailChristoffel.lean` does when it feeds the `NormedSpace`-based
`Connection/Producers.lean`.

Diagnostic rule of thumb: a "`?m` in the expected type that `(I := I)` will not
pin" means the two files disagree on the model-space instance spine, not that the
elaborator needs more hints.  Check the two variable blocks first.

## Status

Verification passed (full locked build).  No `sorry`, no new axioms beyond
`propext`, `Classical.choice`, `Quot.sound`.
