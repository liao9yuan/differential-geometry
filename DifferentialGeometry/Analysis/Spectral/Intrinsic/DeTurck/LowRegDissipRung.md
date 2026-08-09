# LowRegDissipRung.lean — E0, the `k = 0` dissipation rung

Status: **GREEN, sorry-free** (2026-08-03).  Focused check clean (no warnings);
one targeted module build clean.

Brick: E0 of `ShortTime/F6_ESTIMATE_RECON.md` §5 — the `k = 0` rung of the
base-order-2 dissipation ladder that F6's Galerkin energy closure consumes.

## What is proved

`n_diff_h1_rung` (`:76`), gate-free, dim-3-explicit (`hDim : finrank ℝ E = 3`),
same-background (`g_bg = g₀`):

```
∀ R₀, ∃ ρ Cδ₀ C₀, 0 < ρ ∧ 0 ≤ Cδ₀ ∧ Cδ₀ < 1 ∧ 0 ≤ C₀ ∧
  ∀ T symmetric, ∀ δ ≤ 1/3 with the two `gFibreOpBound` certificates,
    ‖T‖_{H²} ≤ ρ → ‖T‖_{H³} ≤ R₀ →
      ‖N T − N 0‖_{H¹} ≤ Cδ₀ ‖T‖_{H³} + C₀ ‖T‖_{H²}
```

with `N = deTurckSmoothRemainder g₀ g₀ ·` and every norm spelled
`‖ccTensorToHs g₀ 2 (σ : ℝ) ·‖`.  This is L4's shape
`‖N T − N 0‖_{H^{a+k−1}} ≤ Cδ₀‖T‖_{H^{a+k+1}} + Crem k ‖T‖_{H^{a+k}}` at
`a = 2`, `k = 0`.

Realized constants: `Cδ₀ = Capp · Cc2 · ρ` with
`ρ = min ρ₂ (1 / (2(Capp·Cc2 + 1)))`, so the contraction is bought purely by
shrinking the `H²` ball; `C₀ = 2·Csp·Ca1·B·Chs2` with
`B = √(Ka1 (1 + (Chs3 R₀)²)⁶)`, so `C₀` depends on `R₀` only (allowed: L4's
`Crem` is `k`-dependent).

Helper: `jetSq_le_hs` (`:48`, private) — the order-generic form of `hs2_low2`,
`lowJetSq g n T ≤ (C‖T‖_{H^n})²` for every `n`.  If the `k`-ladder lands this
should be promoted into `Analysis/Spectral/Tensor/Estimates/H2Pointwise.lean`
next to `hs2_low2` (its canonical home) rather than stay private here.

## Producers used → summand map

| summand | producer | file:line |
|---|---|---|
| the identity `N T − N 0 = a₂ T + a₁ T` | `lowData_split` | `DeTurck/DeTurckRemainderLowBaseAction.lean:3841` |
| `a₂` coefficient smallness (pointwise **and** `H²` jet, both `≤ Cc2·‖T‖_{H²}`) | `c2_h2_small` | `…LowBaseAction.lean:13268` |
| `a₂` arm `H³ → H¹` | `appCc_h2_h3_h1` | `Tensor/Estimates/H2H3Principal.lean:189` |
| `a₁` coefficient envelope `jet₂ C0 + jet₂ C1 ≤ K(1 + jet₃ T)⁶` | `lowData_a1_coeff` | `…LowBaseAction.lean:13609` |
| `a₁` arm `H² → H¹` (jet form) | `a1_h2_h1` | `…LowBaseAction.lean:13189` |
| jet ↔ spectral bridges | `hsJet_le`, `hs_le_jet` | `Tensor/SobolevScale/IteratedCovGradHsJetBound.lean:834`, `:855` |
| linearity of the embedding | `ccTensorToHs_add` | (via `ccToHsLin`, `Tensor/SobolevScale/SmoothCcDense.lean:36`) |

Nothing was reproved; E0 is pure assembly.  `remainder_diag_h2`
(`…LowBaseAction.lean:13555`) was **not** used — its `a₁` clause is an `H²`
bound in terms of `‖T‖_{H³}`, i.e. the wrong shape for the ladder's lower-order
term; `lowData_split` + `a1_h2_h1` + `lowData_a1_coeff` give the right one.
`principal_arm_h2` / `principal_arm_h4_h2` (`DeTurck/PrincipalCoeffH2.lean:589`,
`:622`) were **not** used either: routing the top arm through
`deTurckPrincipalCometricArm` leaves the "`a₂ T − Arm T`" third arm with no
low-order producer, whereas `c2_h2_small` already delivers exactly the
smallness `principal_coeff_h2` would have supplied, directly on `a₂`'s own
coefficient.  (`principal_arm_h2` remains the right tool if the arm has to be
named separately later.)

## Home

Placed in `Analysis/Spectral/Intrinsic/DeTurck/`, not in `ShortTime/`:

* every producer lives at or below this layer (four of them in
  `DeTurckRemainderLowBaseAction.lean`, which is 13k lines and cannot absorb a
  new declaration under the 3000-line rule);
* `PrincipalResidualH2.lean` is the exact sibling — same layer, same job
  (assembling the low-base split into named residual statements);
* F6's consumer is `HeatSemigroup/GalerkinParabolicEnergyDeTurck.lean`, which
  imports `DeTurck/` but not `ShortTime/`.  Putting E0 in `ShortTime/` would
  have needed a new `HeatSemigroup → ShortTime` import edge.

Single import: `DeTurck.DeTurckRemainderLowBaseAction` (it already pulls in
`PrincipalCoeffH2 → H2H3Principal → H2Pointwise` and the Sobolev-scale bridges).

## Does the `k`-ladder generalize from here?  Early-signal verdict

**The decomposition generalizes; the `k`-uniform constant is not yet in hand,
but the ingredient that makes it possible exists.**

* `lowData_split`'s identity is completely order-free — no `a`, no `k`, no
  Sobolev index appears in it.  Both arms are `appCc` applications of two fixed
  coefficient bundles (`C2` at valence `(4,2)`; `C0, C1` at `(2,2)`, `(3,2)`).
  So rung `k` is *literally* "apply an `appCc_·_h(k+3)_h(k+1)` estimate to `C2`
  and an `appCc_·_h(k+2)_h(k+1)` estimate to `C0, C1`".  No new algebra is
  needed at any rung.  This is the good half of the signal.
* The bad half: at `k = 0` the contraction constant came from `c2_h2_small`,
  which bounds *both* the pointwise norm and the whole `H²` jet of `C2` by
  `Cc2‖T‖_{H²} ≤ Cc2 ρ`.  That works because two derivatives of `C2` cost only
  two derivatives of `T`, and `‖T‖_{H²}` is exactly the small ball radius.  At
  rung `k` the envelope needed by a naive `appCc_h(k+2)_h(k+3)_h(k+1)` is the
  `H^{k+2}` jet of `C2`, which costs `‖T‖_{H^{k+2}} ≤ R₀` — bounded, **not**
  small.  Feeding that into a one-envelope estimate gives
  `Cδ₀(k) ≈ Capp(k)·Cc2(k)·R₀`, which is not `< 1`.
* But the escape is already stocked: `lowData_split`'s second clause caps the
  **pointwise** fibre norm of `C2` by `κ · δ/(1−δ)²` with `κ` independent of
  `T`, of `δ`, and of any order — a genuinely `k`-free small quantity.  So the
  `k`-uniform `Cδ₀` exists in principle; what is missing is a **tame/Moser**
  `appCc` estimate in which the coefficient's pointwise norm and its jet norm
  enter with *different* data factors:

  ```
  ‖appCc Φ (∇²U)‖_{H^{k+1}} ≤ C k · (‖Φ‖_{C⁰} · ‖U‖_{H^{k+3}} + ‖Φ‖_{H^{k+1}} · ‖U‖_{H^{k+2}})
  ```

  All existing low-order members of the family (`appCc_h2_h3_h1`,
  `appCc_h2_h4_h2`, `appCc_h2_h2_h1`, …) take a *single* envelope `A` bounding
  both, and `appCc_c1_h2_h1` (`H2H3Principal.lean:346`) — the only two-constant
  member — *adds* the two constants (`C·(A+B)·‖U‖_{H²}`) instead of pairing
  each with its own data order.  That pairing is the whole content of E0b.
* Per recon §5.3 this is a **normal estimate gap, not a route obstruction**:
  clause 1 ("the constant necessarily degrades") is not established, because
  the `k`-free pointwise cap on `C2` is available; nothing forces the
  degradation, only the current shape of the `appCc` family does.

**Next brick (E0b, revised target).**  Not "induct on `k`" but: add the
split-envelope member of the `appCc` family at the `Tensor/Estimates/` layer,
in the shape above, then instantiate it at every `k` against
`lowData_split`'s pointwise cap plus an `H^{k+1}`-jet envelope for `C2`
(the `k`-generic analogue of `c2_h2_small`'s second clause, which will be the
second real sub-brick).  `appCc_h2_h4_h2` remains the `k = 1` top-order rung to
mirror.

## Hotspots / Lean lessons

* **`lowBaseData …` must be made opaque immediately.**  The first version kept
  the coefficient bundle as a `set`-bound (hence unfoldable) local; `nlinarith`,
  `linarith` and `calc` then compared atoms containing the full path-integral
  witness and blew the 200k heartbeat budget at `isDefEq`/`whnf` — three
  timeouts, none of them a real proof failure.  Wrapping the producers in a
  single `obtain ⟨A, …⟩ : ∃ A : LowBaseActionData g₀, …` (witness
  `lowBaseData …`, four conjuncts) makes `A` a genuine opaque fvar and the file
  checks in 20 s with **no** `maxHeartbeats` bump at all.  Record this as the
  default pattern for any consumer of the low-base coefficient bundle.
* Stating the existential's first conjunct with the *same* spelling of
  `(lt_of_le_of_lt hδ_le (by norm_num))` as the theorem statement makes the
  final `rw [hsplitA]` match syntactically; no `congrArg`/proof-irrelevance
  gymnastics needed.
* `a² + b² ≤ X²  ⟹  a + b ≤ 2X` is out of reach for a single `nlinarith` call.
  Split it: `le_of_sq_le_sq (by linarith only [hjetY, sq_nonneg _]) hX` twice,
  then `linarith only [h0, h1]`.
* `hsJet_le`/`hs_le_jet` produce `‖ccTensorToHs g s ((n : ℕ) : ℝ) ·‖`.  For
  `n = 1, 3` this is not syntactically `(1 : ℝ)`, `(3 : ℝ)`; use
  `rw [show ((1 : ℕ) : ℝ) = (1 : ℝ) by norm_num]` or `norm_num at h`.  (`n = 2`
  needs no repair.)
* `hR₀ : 0 ≤ R₀` turned out to be unused (`‖T‖_{H³} ≤ R₀` already forces it) and
  was dropped — weakest-assumptions rule.  `hT` and `hδ0` are consumed by the
  proof but not by the statement, so the declaration carries
  `set_option linter.unusedVariables false in`, matching the 84 uses of the same
  marker in the direct producer file.  Note this marker is *not* a vestigiality
  signal here in the sense of `F6_ESTIMATE_RECON.md` §4: `n_diff_h1_rung` binds
  no `2n+10`/`4n+10` gate at all.
