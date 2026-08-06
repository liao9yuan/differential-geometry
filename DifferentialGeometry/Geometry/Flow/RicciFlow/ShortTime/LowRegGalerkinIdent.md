# LowRegGalerkinIdent

## 2026-08-04 — created: the identification, instantiated at `IsLowSolve`

### What is proved (both axiom-clean, focused check green)

* `lowreg_proj_tendsto` — a low solve `fLo` is the `L²([0,T]; H^1)` limit of a
  sequence `fseq N` of forcings each fixed by the spectral truncation `Π_N`.
* `lowreg_projMode_tendsto` — the same, descended to every eigen-coordinate at
  every `t ∈ Icc 0 T`:
  `perModeConv λᵢ (timeModeCoeff (fseq N) i) t → perModeConv λᵢ (timeModeCoeff fLo i) t`.
  This is *exactly* the `hconv` input of `fatou_sq_mass`.

### Proof shape (no surprises, one pass green)

Unpack `IsLowSolve`; renormalise the six numbers into `partial_sol_tame`'s
`(A, B, C)` exactly as `lowreg_partial_sol_of_bounds` does
(`A = toNNReal (Ctop·lowregOuterRad / R)`, `B = toNNReal B0`,
`C = toNNReal B1`, `R = lowregStateRad Ctop B1 ρ P`), so that
`A·R = Ctop·lowregOuterRad ≤ 1/16` and `C·R = B1·R ≤ 1/16`.  The horizon cap
`T ≤ lowregHorizon …` gives both `T ≤ T₀` (after `rw [hT₀eq, hBcoe]` the two
closed formulas are *syntactically* the same term) and
`T ≤ 1/(64(B+1)²)`.  For each `N`, `proj_partial_sol_tame` yields `gforce`;
`projForce_fixed` gives `Π_N gforce = gforce` and `projFixTame_le_two` gives
`‖gforce − fLo‖ ≤ 2‖Π_N fLo − fLo‖`.  `choose`, then `projFix_tendsto` with
`K = 2`.

The mode corollary is one line of continuity: `timeModeCoeff · i` is
definitionally `(tensorHsCoeffL i).compLpL 2 (timeMeasure T)` applied to the
field, so `simpa only [timeModeCoeff] using hcl.comp hconv` transports the
limit, then `tendsto_perModeConv_of_tendsto_timeL2`.

### Why this is not an adapter

It consumes no new hypothesis.  Every input is a field of `IsLowSolve`, which is
already discharged at the campaign call site (`isLowSolve_of_sol`, and
`lowreg_solve_two` is axiom-clean *after* the widening).  The output is a
statement about `fLo` alone.

### What it does NOT do

It does not bound anything.  `lowreg_loMass` needs, in addition, an `N`-uniform
bound on the truncated partial sums
`∑_{i ∈ eigenIdxFinset N} w_σ(i) · (perModeConv λᵢ (timeModeCoeff (fseq N) i) t)²`,
and that requires three order-one producers that today exist only above the
Lipschitz gate `2·finrank ℝ E + 10 ≤ a`:

1. the Galerkin ODE system in `V_N` for `lowregNfun` — analogue of
   `deTurckGalerkin_solution_existsSymm`
   (`HeatSemigroup/GalerkinParabolicEnergyDeTurck.lean:733`).  It should be
   reachable at `a = 1`: on a finite-dimensional ball the tame estimate *is*
   Lipschitz, which is exactly what `tame_lip_balls`
   (`TameForcingFixedPoint.lean:64`) provides;
2. the identification of that ODE's coordinates with `perModeConv` of the
   projected forcing — analogue of `galerkinPerMode_eq_perModeConvSymm`;
3. the per-scale closure `(Cδ, Cmid, seed, B0)` at base order `1` — analogue of
   `deTurckGalerkin_forcing_closure_perScaleSymm`
   (`…DeTurck.lean:1484`), whose only available route at `a = 1` is
   `a1_ladder` / `a2_ladder` (`Spectral/Intrinsic/DeTurck/LowRegLadderRung.lean`)
   calibrated into the `(α, β, D)` of `two_mul_sum_ladder_le`.

Only after (3) is the `(α, β, D)` calibration meaningful; it was **not** reached
this session, so there is still no `(α, β, D)` outcome to report.

## J0a (2026-08-04): `IsLowSolve` destructuring re-patterned

`lowreg_proj_tendsto` is the tree's ONLY destructuring consumer of `IsLowSolve`.
The pattern lost `g_bg` (the package is now self-background) and gained three
fields, taken as `-` because this proof does not use them yet:
`0 ≤ δ`, `δ ≤ 1/3`, and `coreN`-continuity.  The single `g_bg` occurrence in the
body (`set Nfun := lowregNfun g₀ g_bg …`) became `g₀ g₀`.  Nothing else changed;
`lowreg_projMode_tendsto` passes `hlo` through untouched.  Focused check green.

When the rung-3 energy closure lands, the two δ-range fields and `hcore` are what
it will read off `hlo` — that is why they are in the package rather than being
re-derived at each consumer.

## 2026-08-05 — the forcing-sequence widening (PSTOP §6.4 Fatou seam)

Both theorems now expose the **whole projected trajectory**, not just `fseq`.
The class numbers `δ, Ctop, B1, ρ, P` and their certificates are bound *once*,
outside the `∀ N`, so every constant in the package is `N`-free; per `N` the
statement carries the six conjuncts `proj_partial_sol_tame` already produced and
the old proof discarded at `:141`:

1. `Π_N`-fixedness of `fseq N`;
2. the a-priori state ball `U_N(t) ∈ lowerState g₀ 1 (lowregStateRad Ctop B1 ρ P)`
   a.e. — i.e. `‖U_N(t)‖_{H²} ≤ R`, PSTOP §6.1(i);
3. the truncated Nemytskii identity `fseq N =ᵐ Π_N ∘ lowregNfun` along `U_N`;
4. the zero seed `trace0 = 0`;
5. the equation `∂_t U_N = Δ U_N + fseq N`;
6. the forcing ball `‖fseq N‖ ≤ R/4`.

`U_N` is written as `maxRegDuhamelSolField … 0 (fseq N)` rather than being
existentially quantified: the destructured `u` satisfies
`u = maxRegDuhamelMap … gforce`, so `subst` removes it and the package depends
on `fseq` alone.  `lowreg_projMode_tendsto` additionally keeps the `L²` limit
alongside the per-mode limit, so a Fatou closure needs exactly one call.

Widened **in place** (no `'`-siblings): a repo-wide grep found no Lean consumer
of either theorem — only prose references in `LowRegAllOrderJet.lean/.md` and the
Codex audit notes.  Same proofs, more conclusion; census unchanged (three
standard axioms).

Lean note: `SmoothCcTensor`, `gFibreOpBound` and `ccTensorBilinSymm` are **not**
in scope unqualified in this file (its `open` list is narrower than
`UnifClassBounds.lean`'s).  Write `Integral.L2.SmoothCcTensor` and
`MetricRealization.gFibreOpBound` / `MetricRealization.ccTensorBilinSymm` in new
statements here rather than widening the `open` list.

## 2026-08-05 — F1 GAP-CERT: the certificate widening (third in-place widening)

### The gap it closes

`lowregRung3` (`ShortTime/LowRegRungThree.lean:747`) and the `tame_lip_balls →
hK` derivation (`TameForcingFixedPoint.lean:64`, consumed by
`galTameForce_contOn`, `GalerkinTameSol.lean:674`) both need `IsLowSolve`'s
nonlinearity certificates **at the constants this theorem binds**.  A consumer
that re-destructured `hlo` itself would obtain a *different* witness tuple
`(δ', Ctop', …)`, incomparable with the `(δ, Ctop, B1, ρ, P)` under which
`fseq`, the state ball and the forcing ball are stated — which is exactly what
would wedge the F2 instantiation.  So the certificates must travel *inside* the
package.

### Exported (all verbatim `IsLowSolve` fields, no derivation)

Seven new ∃-binders, inserted **between `hreal` and `fseq`** so the existing
binders keep their relative order and the `Tendsto … ∧ ∀ N …` body is
byte-identical:

`(_hδ0 : 0 ≤ δ) (_hδ3 : δ ≤ 1/3) (_hcore : Continuous (coreN g₀ g₀ hδ
(lowregRealRad g₀ hP.le hreal))) (B0 : ℝ) (_hB0 : 0 ≤ B0) (_hcont : Continuous
(lowregNfun g₀ g₀ hδ hCtop hB1 hρ hP hreal)) (_htame : three-arm estimate on
lowerState g₀ 1 (lowregStateRad Ctop B1 ρ P))`.

`htame` forced `B0` to be exported as a bound real — it is the middle arm's
coefficient — so the constant block is now `δ, Ctop, B0, B1, ρ, P` in
information content (though `B0` sits later in the telescope, after `hcore`,
precisely so that the *existing* binder positions did not move).

The diff on the proof is three lines: `-, -, -` at the `obtain` became
`hδ0, hδ3, hcore`, and both `refine`s thread the seven new items.  Same route,
same witnesses; `lowreg_projMode_tendsto` re-exports what `lowreg_proj_tendsto`
exports, as the J4-PREP widening did.

### NOT exported (deliberate, and why)

`D` and `hzero : ‖lowregNfun ⟨0,…⟩‖ ≤ D`, and `hTτ : T ≤ lowregHorizon Ctop B0
B1 D ρ P`.  These are cleanly exportable by the *same* pattern (add `(D : ℝ)`
after `B0`, then the two facts) — nothing obstructs them; they were simply not
in F1's dispatch and no named downstream consumer asks for them at the
package's constants.  `lowRegSeedMass` takes its own `D`-free seed bound, and
the horizon cap is already consumed inside this proof.  If F3's `hL2H3`
discharge turns out to need the horizon cap at these constants, the extension
is two more binders and two more names in the `obtain`/`refine`.

### Lean notes

* The certificates are **statement-only** binders, so the `unusedVariables`
  linter fires on all six proof-valued ones.  Underscore-prefix them
  (`_hδ0`, `_hcore`, …) — the tree already uses that idiom
  (`LowRegBgC0Pair.lean:671`, `LowRegAllOrderJet.lean:1840`).  `B0` is *used*
  (inside `_htame`), so it keeps its bare name.  Destructuring is positional, so
  the underscore costs a consumer nothing.
* `coreN` and `lowregRealRad` both live in
  `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral`, i.e. this file's own
  namespace — unqualified names resolve, unlike `SmoothCcTensor` &c.
* `hcore`'s type mentions `hδ` (a proof of `δ < 1`) as a *term* argument of
  `coreN`.  Proof irrelevance is definitional, so the rung's own `hδ` slot
  unifies with this one; no `Subsingleton.elim` bridge is needed.
* Copy `_htame` **verbatim from `IsLowSolve`** (with `u.1`/`v.1`, not the
  `(u : …)` coercion this file's `hsingle` uses), so the destructured field
  discharges the binder by `exact`.

### Verification

Focused check green and warning-free; targeted build
`+…ShortTime.LowRegGalerkinIdent` completed successfully with zero errors;
`ScratchIdentCensus.lean` prints `[propext, Classical.choice, Quot.sound]` for
all twenty censused declarations — both widened theorems included — with no
`sorryAx`.  Repo-wide grep re-confirmed **zero** external Lean consumers of
either theorem (only prose mentions), so the widening is safe in place.

The stale sentence in `LowRegForceArms.lean`'s module docstring ("routing
through `lowreg_proj_tendsto`, whose export discards them") was corrected in the
same pass, since this widening made it false; that file re-checks green.

### Honest denominator

This is a certificate **export**, not mathematics: it moves no proof obligation
and is worth ≈**0pp** of the campaign's machinery.  Its whole value is that F2
can now instantiate `lowregRung3` on the projected trajectory without a
constant mismatch.

## 2026-08-05: exact solve package projection

`lowreg_proj_at` now consumes one literal `IsLowSolveAt` package and exports the
projected trajectory at exactly the package's `δ`, coefficient constants,
realization radius, and state cap.  `lowreg_projMode_at` adds pointwise mode
convergence without reselecting any existential witness.  The original
`lowreg_proj_tendsto` and `lowreg_projMode_tendsto` interfaces remain as
compatibility wrappers.  Focused verification passed, warning-free.
The targeted module refresh also passed.
