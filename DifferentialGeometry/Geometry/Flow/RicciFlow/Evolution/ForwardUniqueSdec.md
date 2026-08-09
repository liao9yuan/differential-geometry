# ForwardUniqueSdec — brick K6c (the `sdec` member)

Status: **OUTCOME (A) — full composition green, 0 sorry, 25 public decls, 1008 lines.**
Verification: focused check green; targeted module build green; axiom audit clean.

Endpoint: `sdec_of_uhlenbeck` produces the `sdec` field of
`ForwardUniqueAssembly.ForwardUniqueInputs` verbatim, for the **same** `Svec = uhlRmDiffSpeed`
that K6b's `rm_of_uhlenbeck` produces for the `rm` field, with `Uflux = sdecUflux` and
`rem = sdecRemFam` **constructed** (not assumed).

## The route that worked (planner ruling R7, realized)

The decisive move was **argument-swapping the K2.6c re-lowering operator**, not building
anything new.

`S₀₄ = rmDiffLowAt g₁ g₂` lowers both curvatures with `g₁`; the honest R1 interfaces describe
each flow's own-lowered `Rm04ᵢ`.  Split `S₀₄ = D + G`, `D = Rm04₁ − Rm04₂`, `G` the lowering
gap.  Put `P = Rm04₁ − S₀₄` (a field: `Tf₁ t - Sfield t`), which realizes `g₁♭Rm¹³₂`.  Then

```
G = reLower g₂ g₁ P − P            (reLower with the metric arguments SWAPPED)
```

so the operator's **trace metric and connection are both `g₁`**.  Consequences:

* `lapComm_reLower_eq g₂ g₁ P` produces a **`g₁`** divergence — the divergence the Kotschwar
  energy integrates by parts against.  With the un-swapped orientation one gets `div₂`, and
  converting `div₂ → div₁` costs a `∇¹` of the flux carrier, i.e. a `∇A` term in `rem`, which
  the density cannot bound.  **This was the whole risk of the brick and the swap dissolves it.**
* The key identity is the mirror of `nabla2_metric1`, and is free by the same swap:
  `nabla1_metric2 : ∇¹g₂ = lapDiffFlux g₁ g₂ g₂` (two-line proof, `metricNabla0S_self g₂`).
  Both commutator carriers are therefore `A₀₃`-flux algebra against the background `P`.
* `∂ₜG` never needs the `reLower` machinery at all: pointwise `G(X,Y,Z,W) = −h₀₂(Rm¹³₂(X,Y)Z, W)`,
  so the moving-carrier product rule gives
  `∂ₜG = 2(Ric₁ − Ric₂)(Rm¹³₂ ·,·) − h₀₂(∂ₜRm¹³₂ ·,·)` — manifestly (difference × background).
* `Δ₁D = Δ₁S₀₄ − Δ₁G` is **free algebra** (`Tf₁ − Tf₂ = Sfield − (reLower g₂ g₁ P − P)` is an
  identity of fields once `reLower g₂ g₁ P = Tf₂`), so no second decomposition is needed.

Final shapes:

```
U′ = lapDiffFlux g₁ g₂ Rm04₂ − reLowerPair g₁ P (lapDiffFlux g₁ g₂ g₂)
rem′ = rmDotRem(tensorised) + ∂ₜG − (reLower g₂ g₁ − id)(Δ₁P) − tr₁(reLowerPair g₁ (∇¹P) (∇¹g₂))
```

Every `rem′` summand is a difference carrier (`h₀₂`, `A₀₃`, `Ric₁ − Ric₂`, `B₁ − B₂`,
drift-difference) against a bounded background factor; no derivative of a difference carrier
appears outside the divergence.  Norm bounds are out of scope (bundle field `bounds`), but the
shapes are bound-statable.

## Residual hypothesis set of `sdec_of_uhlenbeck`

Exactly the R1 standing inputs plus what `rm_of_uhlenbeck` / `rmDiffComp_deriv` already carry:

* `hev₁`, `hev₂` — the two per-flow **own-lowered** `Riemann04BTensorWithRicciDriftEvolutionInFrameOn`;
* `hPDE₁`, `hPDE₂` — the two per-flow Ricci-flow equations (`HasDerivWithinAt … D.carrier`);
* `hreal₁`, `hreal₂`, `hcont₁`, `hcont₂` — `rmVecComp_deriv`'s realization/continuity inputs
  (each flow's own lowering only);
* `hT₁`, `hT₂` — the supplied `(0,4)` fields realize each flow's own curvature;
* `hL₁`, `hL₂` — `rmDiffComp_deriv`'s supplied-rough-Laplacian realizations;
* `hcar` — the bundle's own `car` field;
* `hreg : Ioo a b ⊆ D.regular`.

New relative to K6b: only the two field realizations `hT₁`/`hT₂` (unavoidable — the *intrinsic*
`roughLap0SField` needs an actual smooth field to differentiate, exactly as the bundle's own
`Sfield`/`car` pair does) and `[DecidableEq Idx]` is **not** required (avoided via `classical`).

## What was built (and where it should eventually live)

Relocation TODOs (protocol forbade editing existing files):

* `inner_raiseAt` (`g(raiseAt g x b a, b m) = a m`) — belongs next to `raiseAt_lower`
  (`ForwardUniqueRmBridge.lean`).  Proof: `basisInvMetric_symm` + the first conjunct of
  `MetricInverseInBasis_gen`.
* `inner_sharpFlat` (`g₁(V, sharpFlat g₂ g₁ x W) = g₂(V, W)`) — the pointwise content of
  `mixLow_eq_rm04`, belongs next to it.
* `rm04mix_inner` — the two-metric companion of `metricRm04At_inner`; it was previously only an
  inline `have` inside `rmDiffLowAt_eq_lowerTri`.
* `vec3_deriv_basis` — the **generic** form of `rmDiffVec_hasDerivAt_of_basis`
  (`ForwardUniqueLifts.lean`); that lemma is the `F r = rmDiffVec …` instance.
* `innerCurve_deriv` — the invariant moving-metric/moving-vector product rule previously
  inlined in `rmDiffLow_hasDerivAt` (`ForwardUniqueRmDot.lean`).
* `lowOfComp` / `lowOfComp_eval` — the `(0,4)` analogue of `quadOfComp`: raise the component
  family with `g`, package with `quadOfComp`, lower with `g`.  This is the componentwise →
  invariant lift the Assembly docstring flagged as missing for `sdec`; it is what tensorises
  `rmDotRem` (whose `B`-quadratic and Ricci-drift summands exist only as component families).

## Lean lessons

* **`reLower` reuse, never re-derive.**  Nothing about the K2.6c slot layout had to be touched:
  `reLower_apply`, `reLower_rm2Low` (via `inner_sharpFlat`), `lapComm_reLower_eq` and
  `reLowerPair` were all used with the two metric arguments swapped.  Generalising `reLower`'s
  *factor* argument to an arbitrary `(0,2)` field was **not** needed, because the factor we
  wanted (`h₀₂ = g₁ − g₂`) is a difference of two metrics and the operator is affine in it:
  `reLower g₂ g₁ − id` already *is* the `h₀₂`-contraction.
* **IPS/NormedSpace split is a section split** (K6b lesson, confirmed).  All the mathematics is
  in a `NormedSpace ℝ E` section ending in `sdec_core` (stated with `rmDiffDot`); only the
  restatement with `rmSpeed` needs Assembly's `InnerProductSpace ℝ E` context, and it is a
  bare term-mode `sdec_core …` across the diamond — no `rw`, no `convert`.
* **`Module.Basis.ext_multilinear`** (Mathlib, `LinearAlgebra/Multilinear/Basis.lean`) composed
  with `ContinuousMultilinearMap.toMultilinearMap_injective` is the clean way to reduce a
  `Tensor0SSpace 4` identity to frame tuples.  Then
  `simp only [ContinuousMultilinearMap.coe_coe, hw]` with
  `hw : (fun p => basisAt x (w p)) = frameVec4 (fun m z => basisAt z m) x (w 0) (w 1) (w 2) (w 3)`
  (`funext`, `fin_cases`, `simp [frameVec4, vec4]`) lands exactly on `rmDiffComp_deriv`'s tuple.
* **Do not `set` the frame family.**  `set frame := fun m z => basisAt z m` makes
  `frameVec4 frame x i j k l = vec4 (basisAt x i) …` non-`rfl` at reducible transparency; write
  the lambda inline and the reduction is definitional.
* Private `fieldSub_eval` / `fieldAdd_eval` (`(A ± B) x v = A x v ± B x v`, via
  `(A ± B) x = A x ± B x := rfl` then `Tensor0SSpace.sub_apply`/`add_apply`) turn every
  field-level identity into a real-number `have`, after which the whole assembly closes with
  one `ring`.  Without them the final step is a `rw` maze.
* Derivative uniqueness (`HasDerivAt.unique`) is what glues the componentwise interface fact to
  the invariant speed: `∂ₜS₀₄` is known invariantly (K6b) and as `∂ₜD + ∂ₜG`; equating the two
  at frame tuples is the entire "componentwise → invariant" content for `sdec`.

## Nothing was blocked

No new framework was needed (gate (C) never fired); no instance, axiom, notation or `sorry` was
introduced.  The one design decision taken without asking: `Tf₁`, `Tf₂` are extra *data* (with
realization hypotheses) rather than being constructed, because a smooth `(0,4)` field realizing
`metricRm04At` is not available as a producer in the tree — the same gap the bundle already
papers over with its `Sfield`/`car` pair.  If a `metricRm04Field` producer ever lands,
`hT₁`/`hT₂` discharge instantly.
