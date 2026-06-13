# MapConvergenceDeriv.lean — derivative-closure for `MapCInfConvOnCompacts` (P3 C-II-final-B2)

**Status (2026-06-13): DONE + verified** — focused check + targeted build green
(2323 jobs); both endpoints `#print axioms` clean = `[propext, Classical.choice,
Quot.sound]`.

## What landed

This is the **Gap A producer (1)** the covariant-tower bridge `a ≥ 1` needs (see
`MetricPreconvDiag.md`, "Gap B remaining"): the analytic derivative-closure of the
Euclidean `C^∞`-on-compacts convergence notion.

The stop condition (definition does not retain derivative data) is **NOT**
triggered: `MapCInfConvOnCompacts U Φ Φinf` is `∀ K compact ⊆ U, ∀ p, MapCPConvOn
K p Φ Φinf`, and `MapCPConvOn K p` controls `mapDerivNorm r = ‖iteratedFDeriv ℝ r
(Φₖ - Φ_∞)‖` uniformly on `K` for every `r ≤ p` — i.e. the FULL Fréchet-derivative
tower is retained.  So the closure lemma is provable.

- `mapDerivNorm_fderivApply_le (r) (v) (hk hinf : ContDiff ℝ ∞ ·) : mapDerivNorm r
  (fun z => fderiv ℝ Φk z v) (fun z => fderiv ℝ Φinf z v) x ≤ ‖v‖ * mapDerivNorm
  (r+1) Φk Φinf x`.  Proof: `fderiv` is linear ⇒ `fderiv Φk z v − fderiv Φinf z v =
  fderiv (Φk − Φinf) z v` (`fderiv_sub`, pointwise, via a lambda-ascribed `have`
  since `rw [fderiv_sub]` won't unify the `fun y => …` with the `HSub` form); then
  `norm_iteratedFDeriv_clm_apply_const` peels off `· v` (`≤ ‖v‖ · ‖∇ʳ(fderiv g)‖`)
  and `norm_iteratedFDeriv_fderiv` raises the order (`‖∇ʳ(fderiv g)‖ =
  ‖∇ʳ⁺¹ g‖`).
- `MapCInfConvOnCompacts.fderivApply (h) (hΦ : ∀ k, ContDiff ℝ ∞ (Φ k))
  (hΦinf : ContDiff ℝ ∞ Φinf) (v) : MapCInfConvOnCompacts U (fun k z => fderiv ℝ
  (Φ k) z v) (fun z => fderiv ℝ Φinf z v)`.  At order `p`/`K` it consumes the
  order-`(p+1)` content of `h` with the threshold `ε/(‖v‖+1)`, then the pointwise
  bound closes `mapDerivNorm r (∂…) ≤ ‖v‖·mapDerivNorm (r+1) … ≤ ε`.

`ContDiff ℝ (∞ : WithTop ℕ∞)` matches the Brick-B engine output
(`exists_engine_frameCInfConv`'s `Φinf`/`Φ k` are `ContDiff ∞`), so the lemma is
directly applicable to the order-0 chart-component convergence.

## Lean gotchas
- `ContDiff.differentiable` takes `(hn : n ≠ 0)`, NOT `1 ≤ n` — at `∞` discharge
  with `by simp`.
- `norm_iteratedFDeriv_clm_apply_const` / `norm_iteratedFDeriv_fderiv` live in
  `Mathlib.Analysis.Calculus.ContDiff.Bounds` / `…/FTaylorSeries`; needed an
  explicit `import …ContDiff.Bounds` (not transitive through `MapConvergence`).
- `ContDiff.fderiv_right (hmn : m + 1 ≤ n)`: `(↑r) + 1 ≤ ∞` closes with
  `by exact_mod_cast le_top`.
- `‖v‖ * (ε/(‖v‖+1)) ≤ ε`: `← mul_div_assoc` (the goal is already `a*(b/c)`), then
  `div_le_iff₀` + `nlinarith`.

## Placement note (layering)
This is generic Euclidean analysis with NO manifold content; it belongs IN
`MapConvergence.lean` (the Euclidean AA layer).  It is in this adjacent file only
because `MapConvergence.lean` is currently owned/dirty in another session
(off-limits per P3_PLAN §3).  Candidate to fold back into `MapConvergence.lean`
when that file is free.

## Remaining for Gap B `a ≥ 1` (NOT in this brick)
Producer (1) is now DONE.  The covariant-tower bridge still needs producer (2):
the rank-≥3 / tower coordinate covariant-derivative component formula (a recursive
`component0S (metricCovDerivStep gRef a A) = directional-deriv(component0S A) + Σ
Christoffel · component0S A` generalising `nabla0SFun_two_eval_coordFrame` past
rank 2).  Then `componentConv_covDeriv` for general `a` assembles from (1)+(2) by
induction.
