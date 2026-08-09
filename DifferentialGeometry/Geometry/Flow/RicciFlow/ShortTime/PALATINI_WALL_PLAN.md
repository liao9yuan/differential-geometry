# PALATINI_WALL_PLAN — field-level Palatini difference identity

Recon pass 2026-08-02, read-only.  Scope: the wall recorded in
`UNIF_EXISTENCE_PLAN2.md` No. 77/78 and still listed as open in No. 95.

---

## 0. VERDICT — the wall is CLOSED; the ledger line that says otherwise is STALE

The field-level Palatini difference identity, and all three items it was said to
block, are **proved and `sorry`-free in the working tree**.  No new mathematics is
owed on this lane.  The task that remains is **ledger hygiene**, not proof.

| Item (as stated in No. 77/78/79) | Status | Evidence |
| --- | --- | --- |
| field-level Palatini difference identity | **CLOSED** | `CurvatureOperator/DifferentiatedPalatini.lean:380` `covDerivPal_eq`; `HCGCompactness/UnifPalatiniDiff.lean:319` `curvCovDerivOf_sub_base` |
| (a) `a = 1` curvature envelope | **CLOSED** | `HCGCompactness/UnifCurvatureJetOne.lean:876` `unifRmJetOne`, `:938` `unifRmSecOne` |
| (b) class-uniform `Ksup` at `j = 1` | **CLOSED** | `HCGCompactness/UnifDeTurckRHSOne.lean:1538` `unifKsupLeOne` |
| (c) `unifFc` | **DISSOLVED, not owed** | No. 85 removed the `Fc/hFc/hcurv` packet; `grep -c hcurv ShortTime/UnifNZeroBound.lean` = **0** |

Sorry-audit of the whole chain (`grep -c sorry`, all **0**):
`UnifPalatiniDiff` (357 ln), `UnifPalatiniJet1` (428), `UnifCurvatureJetOne`
(962), `UnifDeTurckRHSOne` (1613), `UnifDeTurckRHSZero` (660),
`UnifCurvatureJet1Diff` (264), `UnifCurvaturePack` (257),
`UnifCurvatureJetsLow` (391), `DifferentiatedPalatini` (459),
`RicciConnDiffPalatini` (138).

**Three stale documents must be corrected** (§9).  A future agent reading only
`UNIF_EXISTENCE_PLAN2.md:1130` would re-attempt a solved brick.

---

## 1. THE EXACT WALL, as recorded

`UNIF_EXISTENCE_PLAN2.md:366-379` (No. 77), verbatim:

> THE WALL, now precisely located: term 2, `covStep gB 4 (metricRm04 g0 -
> metricRm04 gB)`.  Its analytic inputs ALL EXIST (covDConnDiff2_gJet_le
> for nabla^2 A, unifCovConnDiffSup for nabla A, unifConnDiffSup for A,
> covStepDiff_norm_le).  The single obstruction is that
> `riemannSec_difference` - the order-0 Palatini - is an EVAL-level
> identity on smoothExtensionTangent-extended fields, so differentiating it
> drags nabla^{gB}(extension) corrections into every slot.  Needed: the
> Palatini difference as a BUNDLED (0,4)/(1,3) field identity so covStep
> applies directly.

`HCGCompactness/UnifCurvatureJet1Diff.md:97-103`, the missing statement as the
recon agent wrote it:

> ```
> ∃ C (closed in Λ, gBase), ∀ x,
>   √ normSq0S g₀ x 5 (covStep gBase 4 (metricRm04 g₀ − metricRm04 gBase) x) ≤ C
> ```
> under `hcomp` + `MetricCovDerivOrderBoundOn univ a g₀ gBase Λ` for `a ≤ 3`.

and its two sub-obstructions (`UnifCurvatureJet1Diff.md:110-136`): **W1**
tensorial (bundled) Palatini — "the whole frontier"; **W2** the analytic inputs —
"this half is not a wall", already existing.

Form demanded: a **`(1,3)` / `(0,4)` bundled FIELD identity** relating the
Riemann curvature fields of two metrics through the connection-difference tensor
`A = connDiff g₀ gBase` and its covariant jets, with **no curvature on the
right-hand side** (that is what makes the route non-circular —
`UnifPalatiniDiff.lean:296-298`).

---

## 2. THE RECONSTRUCTED STATEMENT — and what actually discharges it

Classical content (difference of curvatures of two connections; the order-0
"Palatini" split, differentiated once by `∇^{gB}`):

```
Pal(X,Y)Z      := R^{g₀}(X,Y)Z − R^{gB}(X,Y)Z
               = (∇^B_X A)(Y,Z) − (∇^B_Y A)(X,Z) + A(X,A(Y,Z)) − A(Y,A(X,Z))
(∇^B_D Pal)(X,Y,Z) = ∇²A-terms + (∇A)⋆A-terms         ← the order-1 identity
```

The repo realizes this in **two layers**, both public and both `sorry`-free.

**(i) Canonical, in the curvature layer** —
`Geometry/Curvature/CurvatureOperator/DifferentiatedPalatini.lean`:
`palatiniDiffSec` (:79) the order-0 `(1,3)` difference section; `covDerivPalatini`
(:292) the differentiated Palatini vector; `mixedCurvDeriv` (:309),
`mixed_sub_eq_pal` (:331); and **`covDerivPal_eq` (:380)**, the endpoint — its
right-hand side is exactly `covDerivConnDiff2 gB g₀ D X Y Z x −
covDerivConnDiff2 gB g₀ D Y X Z x` plus four `covDerivConnDiff`/`diffSec` cross
terms (:380-398), with **no curvature on the right**.  (`covDerivConnDiff2` (:52)
is `∇²A`; `diffSec` is `A`; `covDerivConnDiff` is `∇A`.)  This is the W1 object.

**(ii) HCG-side bundling** — `HCGCompactness/UnifPalatiniDiff.lean`:
`palSec` (:288) `= R^{g₀}(X,Y)Z − R^{gB}(X,Y)Z` as a field; `covDerivPal` (:299)
the *tensorial* base derivative, docstring (:296-298) "a combination of `∇^{gB,2}A`
and `(∇^{gB}A)⋆A`, with no curvature on the right-hand side — which is why the
route is not circular"; **`curvCovDerivOf_sub_base` (:319)** — `∇^{gB}Rm(g₀) −
∇^{gB}Rm(gB) = ∇^{gB}(Rm(g₀) − Rm(gB))`, proved by `cov_apply_sub` + `palSec`
unfolding + `abel`.  Also `covDerivConnDiff_congr` (:170) and
`covDerivConnDiff_eq_ext` (:219) — **precisely the "eval-level ⇒ tensorial" bridge
W1 asked for**: tensoriality of `∇A` in the extended-section presentation, which
kills the `∇^{gB}(extension)` corrections No. 77 named as the obstruction.

**How the two sides meet the consumer.** `UnifCurvatureJetOne.lean:78`
`nablaRm_split`, verbatim:

```
nablaRiemannOp g₀ x D X Y Z =
  curvConnAt gBase g₀ x D X Y Z
  + covDerivPalatini gBase g₀ (extSec1 x D) (extSec1 x X) (extSec1 x Y) (extSec1 x Z) x
  + nablaRiemannOp gBase x D X Y Z
```

i.e. connection-insertion + differentiated Palatini + fixed background — exactly
the three-term split No. 78 dispatch (ii) asked for.

---

## 3. CONSUMER PRODUCTION MAP (hypothesis by hypothesis)

**(a) The `a = 1` curvature envelope.** `UnifCurvatureJetOne.lean:876`
`unifRmJetOne`, conclusion verbatim:

```
∃ K : ℝ, 0 ≤ K ∧ ∀ x : M,
  Real.sqrt (normSq0S g₀ x 5 (iterCov g₀ 4 (metricRm04 g₀) 1 x)) ≤ K
```

under `hΛ : 1 ≤ Λ`, `hcomp`, `hjet1/hjet2/hjet3`
(`MetricCovDerivOrderBoundOn Set.univ a g₀ gBase Λ`, `a = 1,2,3`) — the exact
currency and exact jet budget No. 77's missing statement demanded.  The
constant-before-`g₀` form is `unifRmJetOne_of` (:839) with explicit `rmOneC Λ Kb₀
Kb₁` (:313).  Section currency: `unifRmSecOne_of` (:904) / `unifRmSecOne` (:938).

| envelope term | producer | file:line |
| --- | --- | --- |
| term 1 — connection insertion | `curvConnAt` + `unifCurvSup_of` | `UnifCurvatureJetOne.lean:65`, `UnifCurvatureJetBound.lean:481` |
| **term 2 — the wall** | `covDerivPalatini` + `unifPalatini1` | `DifferentiatedPalatini.lean:292`, `UnifPalatiniJet1.lean:402` |
| term 3 — fixed background | `exists_curvJet_sup` (compactness) | `UnifCurvatureJet1Diff.lean` |

`unifPalatini1_le` (`UnifPalatiniJet1.lean:144`) with constant `palatiniOneC Λ`
(:138) is the class-uniform quadrilinear bound on `covDerivPalatini`, using
metric jets only through order three, discharged from the W2 inputs
(`covDConnDiff2_gJet_le`, `unifCovConnDiffSup`, `unifConnDiffSup`).

**(b) Class-uniform `Ksup` at `j = 1`.** `UnifDeTurckRHSOne.lean:1538`
`unifKsupLeOne`, verbatim head:

```
theorem unifKsupLeOne (gBase : SmoothRiemannianMetric I M) {Λ : ℝ} (hΛ : 1 ≤ Λ) :
    ∃ Kstar : ℝ, 0 ≤ Kstar ∧ ∀ g₀ : SmoothRiemannianMetric I M, … →
      ∀ j : ℕ, j ≤ 1 → ∀ x : M,
        riemannianFiberNormSq g₀ 0 (2 + j) x
          ((iteratedCovGrad g₀ 0 2 j (deTurckRHSSection gBase g₀)).toSection x) ≤ Kstar ^ 2
```

`∃ Kstar` stands **before** `∀ g₀`, for arbitrary `Λ ≥ 1` — the quantifier order
No. 85 said was still missing, closed by No. 86.  Assembly is `unifKsupZero_of`
(j = 0, frozen-frame route) `+` `unifKsupOne_of` (j = 1) under one sum
coefficient `ksupZeroC + ksupOneC` (:1557-1566).

**Why the frozen-frame route sufficed at `j = 0` but broke at `j = 1`:** at
`j = 0` (No. 79) the DeTurck vector field is a *trace* of `A` against a
`g₀`-orthonormal frame, and `smoothOrthoFrame` is a genuinely smooth section, so
the estimate stays at the `A`-level — no curvature difference is ever formed.  At
`j = 1` the derivative `∇Ric(g₀)` appears, forcing `∇^{gB}(Rm(g₀) − Rm(gB))`, the
wall term.  No frame trick reaches it: the difference of curvature *fields* must
be expressed through `A`-jets, which is exactly `covDerivPal_eq`.

**(c) `unifFc`.**  Never defined, and **no longer owed on the live path**.
No. 85 replaced the artificial packet with the curvature-free order-one identity
`hsOne_sq`; verified: `grep -c hcurv` is **0** in both `ShortTime/UnifNZeroBound.lean`
and `ShortTime/UnifRealizeRadius.lean`, and neither calls the `hcurv`-carrying
`H2PointwiseUnif` theorems.  See §5 for what survives.

---

## 4. INVENTORY OF THE PALATINI-ADJACENT LAYER

**Curvature layer** (`Geometry/Curvature/`): `CurvatureOperator/DifferentiatedPalatini.lean`
(7 public decls, §2(i)); `CurvatureOperator/RicciConnDiffPalatini.lean` (order-0
Ricci face); `PerturbedRiemannOpDifferenceBound.lean:88` (order-0 `(1,3)` split via
`riemannSec_difference` — the asset that was *not* differentiable in place);
`ConnDiffDeriv2Bound.lean:814` `covDConnDiff2_gJet_le` (`∇²A`).

**Λ-class curvature-jet files** (`HCGCompactness/`): `UnifCurvatureJetBound.lean`
— `unifCurvSup` (:515) / `unifCurvSup_of` (:481), order-0 operator sup, **`1 ≤ Λ`
only**; `UnifCurvatureJetsLow.lean` — low-order connection/Ricci coefficients with
supplied background caps; `UnifCurvatureJet1Diff.lean` — `curvJet1_diff_eq`,
`unifRm04Sup` (first Λ-class bound on the `(0,4)` field), `unifCurvJet1Conn`
(term 1), `exists_curvJet_sup`; `UnifCurvaturePack.lean` — `ccOfField`,
`rfns_ccOfField_eq`, `rmSection` (field→section transport, all orders);
`UnifCurvatureJetOne.lean` — the `a = 1` envelope (§3a); `UnifPalatiniDiff.lean`,
`UnifPalatiniJet1.lean` — the wall itself.

**`RiemannCoefficientPalatiniRefold.lean`** (`Analysis/Parabolic/RicciLinearization/`,
19 573 ln, `sorry`-free) is a **different lane** and does *not* contain the wall
identity, despite the name.  It is the DeTurck **coefficient-field refold**:
`deTurckLieCovDerivArmField` (:90) / `deTurckLieEndoArmField` (:106) with the
arm-split `deTurckLieCoeffField_eq_covDerivArm_add_endoArm` (:124); monomial
coefficient-field algebra (`curvatureRefoldMonomialCoeffField_unitValue_*`
:1000-1159); the `lieCovPair`/`lieCovArm2`/`lieBgLow`/`lieBgCore` tower; per-order
`L²` tame envelopes (:6673).  Its currency is **`L²`/`H^s` coefficients for the
linearized operator**, not the pointwise `iterCov`/`normSq0S` Λ-class currency the
wall needed.  Nothing here was reusable for the wall, and nothing the wall
produced feeds it.

---

## 5. THE GENUINE RESIDUAL (small, and OFF the critical path)

`Analysis/Spectral/Tensor/SobolevScale/UnifBochnerGap.lean` still carries an
**abstract, all-order** curvature hypothesis, `bochner_step_unif` (:304),
verbatim:

```
(hcurv : ∀ (r p : ℕ) (S : SmoothCcTensor g₀ 0 r),
    ‖iteratedCovGrad g₀ 0 (r + 1) p (pointwiseTensorCurv g₀ r S)‖ ≤
      Fc p * ∑ a ∈ Finset.range (p + 2), ‖iteratedCovGrad g₀ 0 r a S‖)
```

and its header (:13-14) still says "Downstream (brick 2a, `HCGCompactness/`)
discharges `hcurv` … via `sup_x ‖∇^{g₀,a} Riemann(g₀)‖ ≤ F(Λ,n)`".

Discharging it would need two things the tree does **not** have: (1) a
Leibniz/Kato product estimate for the curvature **action** `pointwiseTensorCurv`
(`Geometry/Curvature/Bochner/PointwiseTensorBochner.lean:95`); (2) the
class-uniform sup of `∇^a Rm` for **every** `a ≥ 2` (only `a ≤ 1` exists — §3a
closes `a = 1`).

**But it is not owed.**  `hcurv` is a *parameter* of `UnifBochnerGap` and
`H2PointwiseUnif`, threaded and never discharged; the two live ShortTime consumers
(`UnifNZeroBound`, `UnifRealizeRadius`) reach zero `hcurv` occurrences.  Treat as
**dormant machinery**, revived only if a future spectral route re-imports the
`Fc`-parameterized Bochner recursion.  It is *not* the Palatini wall: that was
order-1 and pointwise; this is all-order and `L²`.

---

## 6. CLASSIFICATION

**Palatini wall proper: RESOLVED — no classification owed.**  For the record, the
original recon's call (`UnifCurvatureJet1Diff.md:105`, "**missing groundwork / new
math**, not a local proof failure … a design + bookkeeping brick on the scale of
the order-0 asset itself") was **accurate**: closure cost ~1 250 new lines across
`DifferentiatedPalatini` + `UnifPalatiniDiff` + `UnifPalatiniJet1`, plus the 962-line
envelope file.  It did not close as a leaf, exactly as predicted.

**Residual of §5: missing API lemma + missing all-order estimate** (Kato/Leibniz
for `pointwiseTensorCurv`, then `a ≥ 2` envelopes).  Dormant, no live consumer.

**The one thing actually owed by this lane: documentation correctness** (§9) —
routine, ~15 minutes, zero Lean risk.

---

## 7. ROUTE, AS EXECUTED (for the record)

1. Make `∇A` tensorial in the extended-section presentation
   (`covDerivConnDiff_congr`, `covDerivConnDiff_eq_ext`) — this removed the
   `∇^{gB}(extension)` corrections that blocked differentiating
   `riemannSec_difference` in place.
2. Bundle the order-0 Palatini as a field (`palSec` / `palatiniDiffSec`), then
   differentiate by `∇^{gB}` with the three Leibniz slot corrections
   (`covDerivPal`, `curvCovDerivOf_sub_base`), landing on `∇²A + (∇A)⋆A`
   (`covDerivPal_eq`) — no curvature on the right, hence non-circular.
3. Split `∇Rm(g₀)` into insertion + differentiated Palatini + background
   (`nablaRm_split`); estimate the Palatini arm class-uniformly from the
   pre-existing W2 inputs (`unifPalatini1`); transfer `gBase → g₀` by
   comparability; convert operator → rank-5 tensor norm → section currency
   (`unifRmJetOne`, `unifRmSecOne`).
4. Feed the static `j = 1` DeTurck packet and reverse the quantifiers
   (`unifKsupOne_of`, `unifKsupLeOne`).

**Source note, honest:** the `RicciFlow/` LaTeX tree (Morgan–Tian, GSM books) is
**not present in this checkout** (untracked), so no book/section citation is made
rather than inventing one.  The identity used is the standard
difference-of-connections curvature formula, and the repo's derivation in
`DifferentiatedPalatini.lean` is self-contained.  Cross-check against the books in
the primary tree if a citation is ever needed.

---

## 8. PRIOR FAILED-ROUTE NOTES

No *failed*-route note exists for this lane — the wall closed on its first
dedicated attempt.  Three durable rulings:

- `UnifCurvatureJet1Diff.md:138` — "Do NOT re-attempt by adding hypotheses to
  `unifCurvJet1Conn`", echoed at `UNIF_EXISTENCE_PLAN2.md:378-379`: an envelope
  carrying the identity as an `hpal` hypothesis "would move no mathematics".
  **Honored** — no `hpal` slot exists anywhere.
- `UNIF_EXISTENCE_PLAN2.md:358-364` (ROLE SWAP): `diffStep_jet_one_le g1 g2`
  measures in `g2` and consumes the jets of `g2` against `g1`; taking
  `g1 = gBase, g2 = g₀` makes the jet hypothesis *be* the class `hjet1`, lands the
  norm in `g₀`, and needs no cross-metric `Λ^{s/2}` conversion.
- Calibration: No. 71's "orthonormal frame cannot be differentiated" was **FALSE**
  (No. 79); No. 77's "towers unbridged" was **STALE** (No. 78).  Three-for-three
  on walls smaller than first reported — matches the standing
  `ricciflow-agents-overcount-walls` lesson.

---

## 9. FIRST BRICK — ledger reconciliation (documentation only)

**Name:** No. 97 planner entry, "Palatini wall verified CLOSED; stale open-wall
line corrected".  **Home:** `ShortTime/UNIF_EXISTENCE_PLAN2.md` (append), plus two
same-name note fixes.  **No Lean edit, no build.**

Three corrections, each with the evidence already gathered above:

1. `UNIF_EXISTENCE_PLAN2.md:1130-1131` (No. 95) lists "open mathematical walls
   unchanged: field-level Palatini difference identity, class-uniform `Ksup` at
   `j = 1`, E7, Lane F".  The first two are closed (§0).  Correct to "E7, Lane F".
2. `HCGCompactness/UnifPalatiniJet1.md:25-37` — "Remaining frontier" says
   consumers "still carry the staged `Λ < 2` argument" and that "`unifKsupLeOne`
   … is still unstated (0%)".  **Both false now**: `unifRmJetOne` takes only
   `hΛ : 1 ≤ Λ`; the only `Λ < 2` strings left in the chain are a doc line
   (`UnifCurvatureJetOne.lean:13`, "no perturbative `Λ < 2` gate remains") and a
   superseded single-link variant (`UnifCurvatureJetBound.lean:1008`);
   `unifKsupLeOne` is proved at `UnifDeTurckRHSOne.lean:1538`.
3. `HCGCompactness/UnifCurvatureJet1Diff.md:91-138` — retitle §4 from "THE WALL"
   to "THE WALL (CLOSED …)" with pointers to `covDerivPal_eq` and
   `curvCovDerivOf_sub_base`, keeping the W1/W2 analysis as the historical record.

**Acceptance:** `grep -n "Palatini" UNIF_EXISTENCE_PLAN2.md` yields no line
asserting the identity is open; the two notes point at the proved endpoints.

**Optional follow-on brick, only if a consumer appears** (do not build
speculatively — §5): `pointwiseTensorCurv_leibniz_le`, home
`Geometry/Curvature/Bochner/PointwiseTensorBochner.lean` (canonical home of
`pointwiseTensorCurv`, :95) — the Kato/Leibniz product estimate `hcurv` needs;
then `a ≥ 2` envelopes by iterating `nablaRm_split`.  **Warning:** the `a ≥ 2`
iteration needs `∇^{k}A` bounds for `k ≥ 3`, i.e. metric jets past order three,
which the class hypothesis `a ≤ 3` **does not supply** — so it forces a
class-strengthening decision.  Planner ruling, not a leaf.

---

## 10. RISK REGISTER

| # | Risk | Evidence | Mitigation |
| --- | --- | --- | --- |
| 1 | **A future agent re-attacks the solved wall.**  Highest-probability failure mode: the newest ledger entry (No. 95, 2026-08-02) is *more recent* than the closure entries (No. 84/86, 2026-07-30/31) and contradicts them. | `UNIF_EXISTENCE_PLAN2.md:1130-1131` vs `:628-656`, `:693-724` | §9 brick 1, immediately. |
| 2 | **`hcurv` is mistaken for a live obligation.**  `UnifBochnerGap.lean:13-14` still advertises "Downstream (brick 2a, `HCGCompactness/`) discharges `hcurv`" — but the ShortTime consumers dropped it. | `grep -c hcurv UnifNZeroBound.lean` = 0; No. 85 (`:658-666`) | §5; annotate the `UnifBochnerGap` header as dormant when someone next touches that file. |
| 3 | **Class jet budget caps the lane at `a = 1`.**  The endpoint hypothesis is `∀ a ≤ 3` (`ExtendViaUniqueness.lean:85`) and the `a = 1` envelope already consumes `hjet1/hjet2/hjet3`.  Any `a ≥ 2` curvature envelope needs jets past order 3 — a strengthening of `(N)`'s own hypothesis, not a lemma. | `UnifCurvatureJetOne.lean:880-884`; `ExtendViaUniqueness.lean:85` | Do not open `a ≥ 2` without a planner ruling on the class definition. |

---

## 11. HONEST DENOMINATOR

- **`ricci_flow_unif_existence` (the `(N)` theorem)**: stated at
  `Evolution/ExtendViaUniqueness.lean:80`, `sorry` at `:98`. **Proof 0%.**
- **Palatini-wall lane specifically**: **100%** — identity, `a = 1` envelope, and
  `Ksup j ≤ 1` all proved and `sorry`-free.  No. 95 (`:1130-1131`) names four open
  walls; **two of the four are this lane**, so the honest open-wall list is
  halved to `E7, Lane F`.
- **`(N)` dedicated machinery**: ~85% per No. 96 (`:1225`).  This recon does not
  raise that number — it *confirms* a component already counted in it, and
  removes a phantom from the open-wall list.
- **Whole HCG compactness project**: low single digits, unchanged.

Closing this lane changes the campaign's *direction*, not its percentage: the
next fronts are No. 95's list minus the two now-closed walls — the a-posteriori
fixed-horizon bootstrap (owned by a concurrent lane), then the class-uniformity
layer for `τ₀`, E7, and Lane F.
