# L4 `k`-uniformity autopsy — how the supercritical `Cδ₀ < 1` is bought, and whether it transplants to `a = 2`

Read-only recon, 2026-08-03.  No Lean was run.  Every claim carries a `file:line`.
Companion to `F6_ESTIMATE_RECON.md` §§1, 2, 5.1a, 5.1b and
`Analysis/Spectral/Tensor/Estimates/AppCcSplitEnvelope.md`.

---

> **STATUS (executed 2026-08-03, brick E0a′).**  The verdict **(β)** is
> **confirmed and the ladder is landed**:
> `Analysis/Spectral/Intrinsic/DeTurck/LowRegLadderRung.lean` (note:
> `LowRegLadderRung.md`), `a2_ladder` (`:192`), one named frontier `sorry`
> (`c2_jet_tower`).  The `m`-form adapter `appCc_cap_hs_le` (`:75`) is
> axiom-clean, and de-gates the shipped wrapper from `2n+10 ≤ a` to the
> engine's own `n+5 ≤ a` (the wrapper's `_le_zero` half never uses its gate;
> `_le_succ` forwards it through one `by omega`), dropping
> `deTurckArmFibreConst` from the top constant as well.
>
> **Two corrections to this report.**
> 1. §3.3 clause **(c) is wrong**: the `H^{a+2}` ball is *not* replaceable by
>    the dim-3 sharp `H³` ball.
> 2. §5 risk 2's "bookkeeping, but pervasive" **understates the leaf**: at
>    `a = 2` the budget step is not merely wide, it is arithmetically FALSE.
>    In `master_appCc_jet_le_sharp` (`ConnLapCommutatorCoefficientTame.lean:469`)
>    region one needs `t + (w−1) + dc ≤ a + 2`, i.e. `4 + 2 + 3 = 9 ≤ a + 2` in
>    dim 3 at the `(dc,dd) = (3,2)` call site (`:1004`) — so `a ≥ 7`, and at
>    `a = 2` the obligation reads `9 ≤ 4`.  `hs_extreme_interp` (`:306`) rescues
>    region two (`hsum_ok` needs only `dc+(w−1)+dd ≤ a+5`, i.e. `7 ≤ 7` at
>    `a = 2`) but cannot rescue region one, which needs a *numeric* coefficient
>    sup bound and has no `f γ` on the right to trade against.  Parameterizing
>    the leaf's split threshold `t` gives `0 ≤ t' ≤ a−3` and `1 ≤ t' ≤ a−2` at
>    the two `master_…` call sites: both close **iff `a ≥ 3`** (ball `H⁵`), and
>    no lower.  So §2's "the `n+5 ≤ a` leaf is bookkeeping" is right about the
>    *kind* of obligation and wrong about its *reachability at `a = 2`*.
>
> **UPDATE (same day, brick E0a″ — the `a ≥ 3` threshold brick is DONE).**
> The parameterization of correction 2 is landed.  `master_appCc_jet_le_sharp`
> (`ConnLapCommutatorCoefficientTame.lean:475`) now takes `t : ℕ` with the two
> budgets it actually consumes (`ht1` for region one, `ht2` for region two) and
> **no `ha` at all**; the three public theorems of that file gate on the sharp
> `max 2 (finrank ℝ E / 2 * 2 + 1) ≤ a`, and `a2_ladder` (`:196`) now reads
> **`ha : 3 ≤ a`** — ball `H⁵`, down from `H^{10}`.  The predicted windows were
> exactly right.  One thing the prediction did *not* say: the six windows have
> **empty intersection** until `a ≥ 4`, so `t` had to become per-call-site, not
> a single better global constant.  The `k`-uniform top constant is unchanged
> (`t` only shifts mass between `S1`/`S2`, which feed the lower-order constant).
> See `ConnLapCommutatorCoefficientTame.md` and `F6_ESTIMATE_RECON.md` §5.1d.
>
> Everything else in this report held, including the headline mechanism (§1),
> the four gate-free ingredients (§1.2), and risk 1 — `c2_jet_tower` is now the
> single remaining frontier.

**Headline.**  The mechanism is **(i)**, in a stronger form than the question
supposed: the top-order coefficient never meets a Leibniz grid *at all*.  The
`k`-uniform smallness is the **pointwise fibre cap on the coefficient**, and the
`k`-induction is a **commutator induction against the resolvent power
`(1−Δ)^p`**, not a Leibniz expansion.  Consequently E0b′ is **not** a new
inequality: the exact order-generic, coefficient-abstract, split-envelope
statement F6 needs **already exists** as
`exists_appCc_secondCovGrad_fibreSmallCoeff_Hs_family_le`
(`Sobolev/TensorHilbert/ConnLapCommutatorCoefficientTame.lean:1323`), with `εC`
(the `C⁰` cap) as the top constant at *every* order.  Its only obstacle at
`a = 2` is a bookkeeping gate `finrank ℝ E + 5 ≤ a`.  **Verdict: (β), close to
(α).**

---

## 1. The mechanism: (i), and specifically "pointwise cap + spectral commutator"

### 1.1 The top constant is a scalar bound outside the `∀ k`

L4 (`DeTurck/DeTurckRemainderRealizeBallUniformSplit.lean:204`) produces
`Cδ₀ = 1/2 + Cbudget` (`:253`), where the two summands are:

* `1/2` — from the principal cometric arm, via
  `deTurckArmFibreConst_mul_div_le_half` (`DeTurckRemainderDefs.lean:195`):
  `deTurckArmFibreConst n * (δ / (1 - δ)) ≤ 1 / 2`, and
  `deTurckArmFibreConst n = Real.sqrt ((n : ℝ) ^ 3)` (`DeTurckRemainderDefs.lean:112`)
  — **dimension only, no `k`, no `a`.**
* `Cbudget = 32 C²/(2(1+32C²))` (`:243`), capping `εwrap` from L5
  (`DeTurckRemainderPrincipalArmOpNorm.lean:9271`), whose bound is
  `εwrap ≤ 32 * deTurckArmFibreConst n ^ 3 * (δ / (1 - δ))` (`:9279`) — again a
  scalar, `k`-free.

`εwrap` itself is built as `deTurckArmFibreConst n * εC + εB` (`:9320`), where
`εC` and `εB` are **pointwise (C⁰) fibre-smallness scalars** of the two
sub-coefficients.  All the `k`-dependence in the whole tower lives in
`Cthird k = Cop (a+k-1) + CopB (a+k-1)` and `Ctame k` (`:9324`), which multiply
only `‖T₀‖_{H^{a+k}}` — the **lower** order.

### 1.2 Where the top-order coefficient factor is actually bounded, and by what

Chain, top arm: L4 `:250` → `deTurckPrincipalCometricArm_realize_ballUniform_spectralShift_le`
(`same file :134`) → `…_Hs_norm_le` (`:28`) →
`exists_smoothCcToTensorHs_deTurckPrincipalCometricArm_principal_le`
(`DeTurckPrincipalArmSpectralGarding.lean:55`) →
`deTurckPrincipalCometricArm_realize_Hs_norm_le`
(`DeTurckPrincipalArmEnergyCrossTerm.lean:1867`), which splits into a base case
`arm_realize_Hs_norm_zero_le` (`:218`) and the step
`deTurckPrincipalCometricArm_realize_Hs_norm_succ_le` (`:1585`).

**Four `k`-free ingredients, each with an absolute constant:**

1. **Pointwise operator bound on the coefficient** —
   `riemannianFiberNormSq_deTurckPrincipalCometricCoeff_le`
   (`DeTurckPrincipalCometricExtraction.lean:551`):
   `rfns g₀ 4 2 x (C.toSection x) ≤ (finrank ℝ E : ℝ)^3 * (δ/(1-δ))^2`
   at **every** `x`, no derivatives, no `k`, no `a`.

2. **Pointwise composition with constant exactly 1** —
   `riemannianFiberNormSq_compRS_le_mul`
   (`Geometry/Connection/TensorNabla/OperatorFieldCovariantCalculusRS.lean:614`):
   ```
   rfns g a c x (Φx.comp Wx) ≤ rfns g b c x Φx * rfns g a b x Wx
   ```
   valence-generic, dimension-free, gate-free.  Composed with (1) this gives
   `riemannianFiberNormSq_deTurckPrincipalCometricArm_le` (`:615`) and then, after
   integrating with `normSq_le_integral_of_pointwise_fiberNormSq_le_rs`,
   `arm_l2_le` (`DeTurckPrincipalArmEnergyCrossTerm.lean:512`):
   `‖arm S‖_{L²} ≤ √(n³)·(δ/(1−δ))·‖∇²S‖_{L²}` — **no `a`, no gate, no grid.**

3. **Gårding / Weitzenböck with constant 1 at the top** —
   `iteratedCovGrad_le_connLap_add` (`ConnLapCommutatorCoefficientTame.lean:228`):
   `‖∇^{k+2}S‖ ≤ ‖Δ_raw S‖_{H^k} + Cj·‖S‖_{H^{k+1}}`, built from the gate-free
   `weitzenbock_integrated_covGrad_l2_normSq`
   (`Elliptic/…/IntegratedOrder2Weitzenbock.lean:196`) and
   `exists_Ccross_for_secondCovGrad` (`…/ChartH2GardingConstant.lean:154`).  Neither
   takes `a` or a dimension hypothesis.

4. **Spectral order shift with constant 1, all real `σ`** —
   `smoothCcToTensorHs_rawTensorConnLapSmooth_le`
   (`DeTurckRemainderPrincipalArmOpNorm.lean:48`):
   `‖Δ_raw T‖_{H^σ} ≤ ‖T‖_{H^{σ+2}}`.  Its proof is one eigenvalue inequality,
   `λ² ≤ (1+λ)²` (`:101`,`:127`), on the spectral weights.  No `a`, no gate,
   works for every `σ : ℝ`.

### 1.3 The `k`-induction is a commutator induction, not Leibniz

`deTurckPrincipalCometricArm_realize_Hs_norm_succ_le` (`:1585`) sets
`CEκ := deTurckArmFibreConst n * (δ/(1−δ))` **once** (`:1610`) and proves

```lean
have hG : ∀ (j : ℕ) (S : SmoothCcTensor g₀ 0 2),
    (∃ p : ℕ, S = oneMinusConnLapSmoothIter (I := I) g₀ 0 2 p T₀) →
    ‖…(deTurckPrincipalCometricArm … g₁ S)‖_{H^j} ≤
      CEκ * ‖…(rawTensorConnLapSmooth … S)‖_{H^j} +
        ClowerFn j * ‖…S‖_{H^{j+1}}                                    -- :1645
```
with `ClowerFn j = Mbase + ∑ i ∈ Finset.range j, CEcomm i` (`:1621`).

That is the whole answer.  `H^j` is realized *spectrally* as `(1−Δ)^p` applied
to `T₀` (`oneMinusConnLapSmoothIter`, `Garding/SobolevScaleSummable.lean:116`),
so raising the order does **not** differentiate the product: it conjugates the
arm by `(1−Δ)^p` and pays a **commutator**,
`arm_commutator_Hs_family_tame` (`:1121`), whose conclusion is

```
‖Δ_raw (arm S) − arm (Δ_raw S)‖_{H^j} ≤ CEcomm j * ‖S‖_{H^{j+3}}       -- :1144
```

i.e. purely a *lower-order-in-`Cδ₀`* contribution: it is **added to `ClowerFn`**,
never multiplied into `CEκ`.  The top constant is therefore **literally the same
scalar at every rung** — that is the source of `k`-uniformity, and nothing else.

### 1.4 The grid is used, but only at `j = 0`, where its weight is 1

The general Leibniz grid `appCc_iteratedCovGrad_diagonalProductGrid_le`
(`Spectral/Tensor/CovGrad/OperatorFieldFibreNormJet.lean:885`) does appear on the
top-order path — but only at `j = 0`.  Verbatim, in
`exists_smoothCcToTensorHs_appCc_fibreSmallCoeff_opNorm_le_zero` (`:4875`):

```lean
    have hgrid := appCc_iteratedCovGrad_diagonalProductGrid_le
      (I := I) (M := M) g₀ (2 + 2) 2 C₂ W₂ 0 x                          -- :4915
    …
    rw [show appCcGdiag (E := E) 0 = 1 by simp [appCcGdiag], one_mul] at hgrid  -- :4919
```

`appCcGdiag j = (2*((finrank ℝ E : ℝ) + 1))^j` (`OperatorFieldFibreNormJet.lean:704`),
so `appCcGdiag 0 = 1` and the grid degenerates to exactly (2) above.  **At `j ≥ 1`
the weight `(2(n+1))^j` multiplies the entire double sum including the diagonal
cell `(i = 0, l = j)`** — read the statement at `:885`.  That is precisely why
E0b's asymmetric reading of the same grid (`AppCcSplitEnvelope.md`, "the `k`-growth
honesty note") cannot be `k`-uniform: the diagonal cell inherits `(2(n+1))^{j}`.

### 1.5 Not (ii), not (iii)

* **Not (ii)** (Moser/tame two-weight per rung): no `C⁰` window is paid on the
  data at the top order at any rung.  The only `C⁰` objects on the top-order path
  are the *coefficient*'s pointwise fibre caps (`εC`, `εB`, `√(n³)δ/(1−δ)`), and
  they are order-independent.  The `C⁰` windows that do appear (`jet_fibreNormSq_sup_le_sharp`,
  `ConnLapCommutatorCoefficientTame.lean:443`, window `finrank/2 + 2`) sit inside
  the **commutator** producers only.
* **Not (iii)** (supercritical Banach-algebra structure): the four ingredients of
  §1.2 are dimension-free and gate-free.  Nothing about them "dies at `a = 2`".

---

## 2. Where the base order `a` actually enters — the analytic steps

Positive result: `a` never touches a top-order step.  Exhaustively, the analytic
`a`-consumers are:

| producer | file:line | gate | what `a` buys |
|---|---|---|---|
| `arm_commutator_Hs_family_tame` | `DeTurckPrincipalArmEnergyCrossTerm.lean:1121` | `4n+10 ≤ a` | the `[Δ_raw, arm]` commutator constants `CEcomm j` |
| `arm_covGrad_coeffLower_l2_tame` | `same:1429` | `4n+10 ≤ a` | the `∇C · ∇²S` lower term `Cgrad` |
| `deTurckPrincipalCometricCoeff_perOrder_l2_tame_generic` | `Sobolev/TensorHilbert/AppCcJetWindowTame.lean:1008` | `2n+10 ≤ a` | the coefficient's `‖∇^i C‖_{L²}` tower (Neumann series) |
| `exists_iteratedCovGrad_fiberNormSq_le_smoothCcToTensorHs_sq g₀ 1 (a+2)` | `same:202` | `2*(2*(n/2+1)+q) ≤ m` | a `C⁰` bound on `∇T₀` from the `H^{a+2}` ball |
| `exists_appCc_secondCovGrad_fibreSmallCoeff_Hs_family_le` | `ConnLapCommutatorCoefficientTame.lean:1323` | **`n+5 ≤ a`** | forwards to the two producers below |
| `exists_rawConnLap_appCc_secondCovGrad_commutator_Hs_family_le` | `same:969` | `n+5 ≤ a` | commutator constants |
| `exists_appCc_covGradCoeff_secondCovGrad_l2_le` | `same:856` | `n+5 ≤ a` | `Finset.range (a+2+1)` monotonicity when reading the ball |

The sharpest quantitative `a`-entry is row 4: at `q = 1`, dim 3, it demands
`2*(2*(3/2+1)+1) = 10 ≤ a+2`, i.e. **`a ≥ 8`** — a *doubled* (lossy) window
(`N := 2*(2*K + q)`, `AppCcJetWindowTame.lean:214`) for what is morally
`‖∇T₀‖_{C⁰}`.  Compare the dim-3 sharp route `hs3_grad_low2`
(`Estimates/H2Pointwise.lean:229`), which delivers the same `C⁰` gradient bound
from `H³`.  Recon §2.2's "8-order saving" is exactly this row.

Gate-free on the top-order path, for the record: `arm_realize_Hs_norm_zero_le`
(`:218`) has **no `ha_super`** in its signature at all; `arm_l2_le` (`:512`) has
no `a`; `iteratedCovGrad_le_connLap_add`, `weitzenbock_integrated_covGrad_l2_normSq`,
`exists_Ccross_for_secondCovGrad`, `smoothCcToTensorHs_rawTensorConnLapSmooth_le`,
`exists_iteratedCovGrad_l2NormSq_le_smoothCcToTensorHs_succ_add_lower`
(`SobolevScale/DirichletSpectralBochnerGap.lean:1568`), `jet_fibreNormSq_sup_le_sharp`
(`:443`) — none takes `a`.

---

## 3. The `a = 2` transplant

### 3.1 The two arms are the *same* object

```lean
-- supercritical (DeTurckPrincipalCometricExtraction.lean:206)
def deTurckPrincipalCometricArm (g₀ g₁) (S) : SmoothCcTensor g₀ 0 2 :=
  appCc g₀ 4 2 (deTurckPrincipalCometricCoeff g₀ g₁) (iteratedCovGrad g₀ 0 2 2 S)

-- low base (DeTurckRemainderLowBaseAction.lean:3339)
noncomputable def LowBaseActionData.a2 (A) (W) : SmoothCcTensor g 0 2 :=
  appCc g 4 2 A.C2 (iteratedCovGrad g 0 2 2 W)
```

Identical shape, identical valence `(4,2)` acting on `∇²`.  And **both coefficients
carry a `k`-free pointwise cap**: `√(n³)·δ/(1−δ)` for the supercritical one
(`Extraction.lean:551`), and `K·δ/(1−δ)²` for `A.C2` from `lowData_split`'s second
clause (`DeTurckRemainderLowBaseAction.lean:3864`).  The `a = 2` lane therefore has
**exactly the hypothesis the supercritical mechanism consumes.**

### 3.2 The diagonal-Leibniz question, answered

> *Does the Leibniz expansion of `∇^{k+1}(appCc C2 ∇²U)` bound its top term
> `appCc C2 ∇^{k+3}U` by `‖C2‖_{C⁰}‖U‖_{H^{k+3}}` with an absolute constant?*

**Through the existing grid: NO.**  `appCc_iteratedCovGrad_diagonalProductGrid_le`
(`:885`) puts the weight `appCcGdiag j = (2(n+1))^j` in front of the *whole* grid,
diagonal cell included.  Reading it asymmetrically (E0b's route) therefore leaves
`C k ≳ (2(n+1))^{(k+1)/2}` on the top order — the honest correction already recorded
in `AppCcSplitEnvelope.md`.  A "diagonal-only" refinement of `:885` would be a
genuinely new pointwise lemma.

**But it is the wrong question**, because the supercritical route does not
Leibniz-expand.  The pointwise product lemma with absolute constant **already
exists and is already the one used**: `riemannianFiberNormSq_compRS_le_mul`
(`OperatorFieldCovariantCalculusRS.lean:614`), constant exactly 1, applied at
`j = 0` only, with the order raised spectrally afterwards.

### 3.3 E0b′ already exists, coefficient-abstract and order-generic

`exists_appCc_secondCovGrad_fibreSmallCoeff_Hs_family_le`
(`ConnLapCommutatorCoefficientTame.lean:1323`), verbatim conclusion:

```lean
    ∀ (C₂ : SmoothCcTensor g₀ (2 + 2) 2) (T₀ : SmoothCcTensor g₀ 0 2),
      ‖…g₀ ((a : ℝ) + 2) T₀‖ ≤ R₀ →
      (∀ x, riemannianFiberNormSq … x (C₂.toSection x) ≤ εC ^ 2) →
      (∀ i, ‖iteratedCovGrad g₀ (2+2) 2 i C₂‖ ^ 2 ≤ Kc i * (1 + ∑ …)) →
      ∀ (j : ℕ) (S), (∃ p, S = oneMinusConnLapSmoothIter g₀ 0 2 p T₀) →
        ‖…g₀ (j : ℝ) (appCc g₀ (2+2) 2 C₂ (iteratedCovGrad g₀ 0 2 2 S))‖ ≤
          εC * ‖…g₀ (j : ℝ) (rawTensorConnLapSmooth g₀ 0 2 S)‖ +
            Clower j * ‖…g₀ ((j+1 : ℕ) : ℝ) S‖
```

The coefficient is **arbitrary**; the top constant is **exactly `εC`, the `C⁰`
cap, at every `j`**; the jet tower `Kc` feeds only `Clower j`.  Its `m`-form
wrapper `exists_smoothCcToTensorHs_appCc_fibreSmallCoeff_opNorm_le` (`:5129`)
already reads

```
‖appCc C₂ (∇²T₀)‖_{H^m} ≤ √(n³)·εC·‖T₀‖_{H^{m+2}} + Cop m·‖T₀‖_{H^{m+1}}
```

— which **is** the literal E0b′ shape of `F6_ESTIMATE_RECON.md` §5.1a, with the
`k`-uniform top constant that E0b could not deliver.

**Therefore E0b′ is a de-gating task, not a new estimate.**  The precise statement
to land at `a = 2` (dim 3), stated in the low-base vocabulary:

> **E0b′ (target).**  Let `hDim : finrank ℝ E = 3`, `g₀` a smooth metric.  There is
> `Clower : ℕ → ℝ`, `0 ≤ Clower j`, such that for every `C₂ : SmoothCcTensor g₀ 4 2`,
> every `T₀ : SmoothCcTensor g₀ 0 2`, every `εC ≥ 0` and `Kc : ℕ → ℝ` with
> (a) `∀ x, rfns g₀ 4 2 x (C₂.toSection x) ≤ εC²`,
> (b) `∀ i, ‖∇^i C₂‖² ≤ Kc i * (1 + ∑_{j < i+2} ‖∇^j T₀‖²)`,
> (c) `‖T₀‖_{H³} ≤ R₀`   ← **the `H^{a+2}` ball replaced by the dim-3 sharp `H³` ball**,
> and every `j : ℕ` and `S` in the resolvent family `S = (1−Δ)^p T₀`:
> `‖appCc C₂ (∇²S)‖_{H^j} ≤ εC·‖Δ_raw S‖_{H^j} + Clower j·‖S‖_{H^{j+1}}`.

Route: copy `ConnLapCommutatorCoefficientTame.lean:1323`'s proof skeleton, replacing
the two `n+5 ≤ a` consumers (`:969`, `:856`) by the dim-3 sharp windows
`hs2_fiber_sq` (`H2Pointwise.lean:166`) and `hs3_grad_low2` (`:229`).  Everything
else in `:1323`'s body (`iteratedCovGrad_le_connLap_add`, the `Mbase`/`ClowerFn`
bookkeeping, the `oneMinusConnLapSmoothIter` induction) is already gate-free and
dimension-free and transfers verbatim.

**The `n+5 ≤ a` gate is confirmed bookkeeping, not an embedding threshold.**
Traced to the leaf: `:969` forwards `ha` only to `master_appCc_jet_le_sharp` (`:469`)
and `appCc_term_Hs_bound_sharp` (`:749`); `:856` uses it only for a
`Finset.range_mono (by omega)` on `range (a+2+1)`.  Inside `:469` the *only*
consumption of `a` is

```lean
      have hbound : i + m + dc ≤ a + 2 := by omega                      -- :558
      have hfle : f (i + m + dc) ≤ R₀ := hballf _ hbound                -- :559
```

with `w := n/2 + 2` (`:494`, the sharp window), `m < w`, `dc ≤ 3` — i.e. exactly the
`bal_gridcore` derivative-budget shape that `F6_ESTIMATE_RECON.md` §1.3 identified:
"the coefficient jet index fits inside the ball's budget `a+2`".  The embedding it
protects is the gate-free `jet_fibreNormSq_sup_le_sharp` (`:443`), window
`finrank ℝ E / 2 + 2` — `= 3` in dim 3, i.e. sharp `H² ⊂ C⁰`.  At `a = 2` the budget
predicate simply has no `a` to exceed; the ball must instead be read at the fixed
dim-3 orders (`H²`/`H³`/`H⁴`).

The second still-open sub-brick is **unchanged and is now the real one**: hypothesis
(b), the `k`-generic jet tower for `A.C2` (the `m = 0` case is `c2_h2_small`,
`DeTurckRemainderLowBaseAction.lean:13268`).  Note the supercritical analogue
(`deTurckPrincipalCometricCoeff_perOrder_l2_tame_generic`,
`AppCcJetWindowTame.lean:1008`) exists because its coefficient is *algebraic* — a
cometric difference with a Neumann-series tower.  `A.C2` is
`rhsRefoldTopInt + selfTopInt − deTurckPhiMetTotal`
(`DeTurckRemainderLowBaseAction.lean:3359`), i.e. **path integrals**; its `i`-th jet
requires differentiating under the integral sign.  That is the genuine remaining
work, and it feeds only `Clower`, so it may grow arbitrarily in `i`.

---

## 4. Verdict

**(β), with most of the work already banked — not (γ).**

* `F6_ESTIMATE_RECON.md` §5.3 clause 1 ("E0b's constant must degrade") is now
  **refuted for the mechanism that matters**: the supercritical `Cδ₀` is `k`-uniform
  because the top constant is a pointwise cap held outside the induction, and every
  ingredient that makes that work (§1.2 items 1–4) is gate-free and dimension-free.
  Clause 1 was only ever established for the *Leibniz-grid* route, which is not the
  route L4 uses.
* Clause 2 and 3 are untouched and now moot: no completed σ-generic Nemytskii
  operator is involved anywhere on the top-order path; the whole mechanism is
  smooth-core and `ℕ`-indexed.
* Remaining distance for E0/E0a: (a) de-gate `:1323` to the dim-3 sharp windows
  [routine, ~1 file]; (b) the `A.C2` jet tower under path integrals [the real
  estimate work]; (c) assemble with `lowData_split` + the `a₁` arm, which
  `n_diff_h1_rung` (`DeTurck/LowRegDissipRung.lean:76`) already shows how to do at
  `k = 0`.

---

## 5. Top three risks

1. **The `A.C2` jet tower under path integrals.**  Hypothesis (b) of E0b′ is the
   only genuinely new estimate.  `c2_h2_small` gives `i = 0`; `i ≥ 1` needs jets of
   `rhsRefoldTopInt`/`selfTopInt`, i.e. differentiation under the integral sign for
   a path-integral witness.  `AppCcSplitEnvelope.md`'s "E0 opacity lesson" (a bound
   `set` after binding a path-integral witness folds wrongly) is a live hazard here.
   If this turns out to be blocked, the fallback is to route the top arm through
   `deTurckPrincipalCometricArm` (whose tower is algebraic and already exists,
   `AppCcJetWindowTame.lean:1008`) and pay the third arm — but §5.1a records that
   this leaves an unproducible `a₂ T − Arm T` at low order, so that fallback is a
   design fork, not a drop-in.

2. **Budget-predicate rewrite at `a = 2` is bookkeeping, but it is *pervasive*
   bookkeeping.**  §3.3 confirms `n+5 ≤ a` is a derivative-budget `omega` step, not
   an embedding threshold — so nothing is mathematically blocked.  The risk is
   volume: `master_appCc_jet_le_sharp` (`:469`) is called at four different
   `(dc, dd)` slot signatures from `:969` alone (`:1004`,`:1008`,`:1014`,`:1017`,
   `:1021`,`:1025`), each with its own `by omega` budget obligation that must be
   re-derived against fixed dim-3 orders instead of a free `a`.  Expect the de-gating
   to be mechanical but wide, and to expose the exact ball order (`H²` vs `H³` vs
   `H⁴`) that recon §6 left undecided.

3. **The `H^{a+2}` ball → `H³` ball substitution changes the `Kc` contract.**
   Hypothesis (b) is stated relative to `∑_{j < i+2} ‖∇^j T₀‖²`, i.e. the data's
   *full* jet tower, and is currently discharged from the `H^{a+2}` ball.  At `a = 2`
   the ball is `H⁴` (or `H²` for the retraction — recon §6 leaves this open), so the
   producer of (b) must supply jets beyond the ball's order from the coefficient
   structure alone.  This is the same margin the recon flagged as "zero slack".

**Not a risk:** the `appCcGdiag` exponential growth.  It is confined to the
lower-order/commutator constants and to E0b's superseded route; it never multiplies
the top order in L4's mechanism, and E0b′ as stated does not use it at `j ≥ 1` on
the top-order path.
