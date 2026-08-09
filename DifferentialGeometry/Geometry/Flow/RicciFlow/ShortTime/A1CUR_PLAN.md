# A1-CUR — radius-free per-order currency for `low1Ker_jet` / `selfLow_jet`

Recon-only design plan (no Lean run, no `.lean` edit, no claim taken).  Written
against `UNIF_EXISTENCE_PLAN3.md` planner entries No. 111–112 and the A1a/A1b
executor report.  Every claim below carries `file:line` evidence.

## 0. Lead with the finding: A1-CUR is TWO bricks, not one, and one of them requires a statement change

**`selfLow_jet` as landed is FALSE.**  Not "unproved by this route" — false.
Its `C0` integrand contains summands that are **quadratic in `∇P`**, and the
`range (i + 2)` budget with constants chosen before `T` cannot hold for such a
summand when the only smallness input is `δ ≤ 1/3` (which caps `P`, never `∇P`).
See §5.2 for the counterexample and §5.3 for the repo's own corroboration.

**`low1Ker_jet` is true and is a small radius-free brick.**  Its `C1` integrand
is **linear in `∇P`** — it has exactly the shape of the already-proved public
`wOmega_lowOrder_jetL2_radiusFree`, which lands on `range (i + 2)` ball-free.

So the fork asked for in the dispatch is answered *per arm*:

| arm | ball needed? | brick size |
|---|---|---|
| `low1Ker_jet` (C1) | **no** | small (≈ 1 session) |
| `selfLow_jet` (C0) | **yes, and the statement must change** | large (≈ 3–4 sessions) + a planner ruling |

## 1. The base engine, verified

`connDiffSection_lowOrder_jetL2_radiusFree`
(`DifferentialGeometry/Analysis/Sobolev/TensorHilbert/DeTurckVFJetRadiusFree.lean:581`).
Conclusion, verbatim (`:592–596`):

```lean
        ∀ (i : ℕ), i ≤ a + 1 →
          ∑ q ∈ Finset.range (i + 1),
              ‖iteratedCovGrad (I := I) g₀ 1 2 q (connDiffSection (I := I) g₁ g₀)‖ ^ 2 ≤
            Flow i * (1 + ∑ j ∈ Finset.range (i + 2),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2)
```

Verified: ball-free (no `R`, no `smoothCcToTensorHs` hypothesis), affine, sharp
at `range (i + 2)` (order `i` of `∇P` ↔ order `i+1` of `P`).  Its only cap is
`hsup : ∀ x, riemannianFiberNormSq g₀ 0 2 x (P.toSection x) ≤ Λ₀ ^ 2` (`:591`),
with `Λ₀` bound **before** `∃ Flow` (`:584`) — a radius-free order-0 cap on `P`.

**Gate `2 * Module.finrank ℝ E + 10 ≤ a` (`:583`) is free.**  Confirmed against
`moserWin_sharp`
(`Analysis/Spectral/Intrinsic/DeTurck/LowRegOpJetWindows.lean:684`), which
instantiates the sibling engine at `a := 2 * Module.finrank ℝ E + 10 + n` for
each requested order `n` (`:704`) and then `choose`s (`:711`).  Copy that idiom
verbatim; the gate costs a `by omega`.

### Radius-free inventory (`grep '_radiusFree'`, 13 declarations)

Public, offset `+1` (order `i` ← `range (i+2)` in `P`), all ball-free:
`connDiffSection_…` (`DeTurckVFJetRadiusFree.lean:581`), `wXi_…` (`:733`),
`wOmega_…` (`:1117`), `mcd_l2_radiusFree`
(`LieCorr0CoeffDiffRadiusFree.lean:2107`).  Offset `0` + order-0 sup:
`cometricCastG0_order0sup_jetL2_radiusFree` (`DeTurckVFJetRadiusFree.lean:66`),
`sharpFlatEndoCc_…` (`:428`).  **Top-separated at `+2`** (§3):
`lieCorr0Field_…` (`LieCorr0CoeffDiffRadiusFree.lean:3104`),
`deTurckLieCoeffField_…` (`DeTurckLieCoeffDiffRadiusFree.lean:273`),
`ricciArmOrder0BaseCoeff_…`
(`Analysis/Spectral/Tensor/CovGrad/CurvatureCoeffDiffRadiusFree.lean:127`).
Workhorse: `antidiagonalTupleGrid_integral_radiusFree`, now at
`…/CovGrad/CurvatureCoefficientDifferenceJetTower/Residual.lean:1336` (the split
has LANDED; umbrella is 23 lines).  Its conclusion is
`∫ grid_b i ≤ K i * (1 + ‖∇^i P‖²)` with `b l = rfns (∇^l P)` and `P` of valence
`0 2` only.
Top-separated integrator: `boundedFactorGridWindow_integral_radiusFree_topSeparated`
(used at `CurvatureCoeffDiffRadiusFree.lean:155`).

The **pointwise** currency underneath all of these is
`Combinatorics.antidiagonalTupleGridWindow`
(`Analysis/Sobolev/AntidiagonalTupleProductGrid.lean:263`) with the product rule
`antidiagonalTupleGridWindow_mul_le` (`:296`):
`atgw b (a+1) * atgw b (c+1) ≤ MulConst a c * atgw b (a+c+1)`.
Producers: `rfns_iCG_cometricCastG0_atgw_rf` (`DeTurckVFJetRadiusFree.lean:824`),
`rfns_iCG_connDiffSection_atgw_rf` (`:968`), `rfns_iCG_wXi_atgw_rf` (`:1047`),
`rfns_iCG_wOmega_atgw_rf` (`:1990`), and the `b4_*_atgw` family
(`LieCorr0CoeffDiffRadiusFree.lean:533/1779/1901/2017/2222/2333/2494/2749`).
**This is the answer to "which product step needs which cap": at the `atgw`
level, products need NO cap on either factor — the single integration at the end
consumes `Λ₀` once.**  That is why `wOmega` (a product) is ball-free.

## 2. The four private `lc0*_perOrder_rf` pieces — per-piece decision

All four in `Analysis/Sobolev/TensorHilbert/LieCorr0CoeffDiffRadiusFree.lean`.

| piece | line | shape | decision |
|---|---|---|---|
| `lc0Base_perOrder_rf` | 113 | `Ktop * ‖∇^{i+2}P‖² + Flow i * (1 + ∑_{j<i+3})`, gated `i ≤ a` | **promote** |
| `lc0Diff_perOrder_rf` | 164 | `Flow i * (1 + ∑_{j<i+3})`, ungated | **promote** |
| `lc0Riem_perOrder_rf` | 258 | `Flow i * (1 + ∑_{j<i+3})`, gated `i ≤ a + 1` | **promote** |
| `lc0VBAMix_perOrder_rf` | 3061 | `‖∇ⁱlc0VB‖² + ‖∇ⁱlc0AMix‖² ≤ Flow i * (1 + ∑_{j<i+3})`, gated `i ≤ a` | **promote** |

Promote, do not re-derive: each is a thin composition over already-public
engines (`wAlpha_L2_topsep_rf`, `wAlphaB_L2_perOrder_rf`,
`cometricCastG0_order0sup_jetL2_radiusFree`, `lc0VB_perOrder_rf` `:2652`,
`lc0AMix_perOrder_rf` `:2956`), so `selfLow_split`-style public re-derivation
would duplicate 200+ lines for nothing.

**Size blocker:** `LieCorr0CoeffDiffRadiusFree.lean` is **3410 lines**, already
over the 3000-line cap.  Promotions therefore go to a NEW sibling file
`Analysis/Sobolev/TensorHilbert/LieCorr0PieceRadiusFree.lean`, which imports the
current file and re-states the four pieces publicly (moving the `private`
bodies there, leaving the composite at `:3104` to import back).  Do not add
lines to `LieCorr0CoeffDiffRadiusFree.lean`.

### The executor's "`range (i+3)` is slack" claim is NOT verified — it is REFUTED for `lc0VB`

The claim (PLAN3 `:1143–1146`) rests on `lc0VB_h2_rf`
(`DeTurckRemainderLowBaseAction.lean:8025`).  Its actual conclusion is

```lean
      lowJetSq (I := I) (M := M) g 2 (lc0VB (I := I) (M := M) g g₁) ≤
        K * (1 + lowJetSq (I := I) (M := M) g 3 P) ^ 5
```

— a **quintic**, not an affine envelope.  It is a different currency and is no
evidence at all that the affine `range (i+3)` can be sharpened to `range (i+2)`.
It cannot: `lc0VB` is quadratic in `∇P` (§5.2), and the `+3` is real.

## 3. The composite trap — reading corrected

`lieCorr0Field_perOrder_l2_radiusFree` (`LieCorr0CoeffDiffRadiusFree.lean:3104`)
and `deTurckLieCoeffField_perOrder_l2_radiusFree`
(`DeTurckLieCoeffDiffRadiusFree.lean:273`) both conclude in the shape

```lean
          Atop i * ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2)
              (symmS (I := I) (M := M) g₀ T)‖ ^ 2 +
          Alow i * (1 + ∑ j ∈ Finset.range (i + 2),
            ‖iteratedCovGrad (I := I) g₀ 0 2 j (symmS (I := I) (M := M) g₀ T)‖ ^ 2)
```

The executor's instruction "assemble through the PIECES, never the composites"
is **correct but for a different reason than stated**.  The mapping is:

* `deTurckLieCoeffField`'s `Atop` comes from `dLbField_perOrder_rf` = the
  `wAlpha` head of the `DLb` arm (`DeTurckLieCoeffDiffRadiusFree.lean:265–272`).
* `lieCorr0Field`'s `Atop` comes from `lc0Base_perOrder_rf` alone (`:113`, the
  only top-carrying piece); the other three are top-free.
* `insert_base` (`Analysis/Spectral/Intrinsic/DeTurckCoefficients/LieCorr0Split.lean:118`)
  is exactly `lc0Insert g₀ g₁ g_bg + deTurckLieEndoArmField g₀ g₁ g₀ =
  lc0Insert g₀ g₁ g_bg − lc0Insert g₀ g₁ g₀`, i.e. `lc0Base` cancels the
  `deTurckLieEndoArmField` half of `deTurckLieCoeffField`.  **That is precisely
  the head cancellation `selfLow_split` encodes**, and it is why the split's
  second summand is `deTurckLieCovDerivArmField − edgeLiePairFam` (the
  covariant-derivative arm survives; the endo arm is gone) and why `lc0Base`
  does not appear among the split's five summands.

So the pieces DO cover the composites, and the `Atop` heads are genuinely
disposed of by `selfLow_split`.  **But this only removes the `∇^{i+2}P` heads of
the Lie/`lc0Base` arms.  It does not touch the quadratic-in-`∇P` summands, which
are a different obstruction entirely (§5).**

## 4. The two private splits

* `ricci1_split` (`Analysis/Spectral/Intrinsic/DeTurck/DeTurckRemainderLowBaseAction.lean:12380`,
  other-lane-claimed, read-only).  Its proof is five `permApp_eq_rs` rewrites
  then `SmoothCcTensor.ext / ContMDiffSection.ext / rfl` — **no private API is
  used**; `permApp_eq_rs`, `reindexCoeffGen`, `rsDomDomCongrSection`,
  `connDiffContrInsertionField` and the five permutation constants
  (`r1o0312`, `r1o0213`, `r1o2301`, `r1o1302`, `r1o1203`, `r1i102`, `r1i120`) are
  all reachable.  **Public re-derivation is a copy of a ~25-line proof** — the
  `selfLow_split` template is more than sufficient.  Home: a new
  `Analysis/Sobolev/TensorHilbert/RicciOrder1KernelSplit.lean`, or beside the
  order-1 envelope in `RicciConnDiffOrder1TameEnvelope.lean` (1373 lines, room).
* `kernelField_eq_neg_arm_combination` — two copies,
  `Analysis/Sobolev/TensorHilbert/LieFieldJetL2Summed.lean:136` (430 lines) and
  `Analysis/Sobolev/TensorHilbert/RicciConnDiffOrder1TameEnvelope.lean:738`
  (1373 lines).  Neither file is claimed (§6).  **Promote the
  `LieFieldJetL2Summed` copy** — it is the lower, thinner module and the
  `TameEnvelope` copy already imports that layer; then delete the duplicate at
  `RicciConnDiffOrder1TameEnvelope.lean:738` and repoint its single use at
  `:1266`.  This is identical in content to `ricci1_split`, so re-derive ONE of
  them and alias the other.

## 5. Product-step cap audit — and the inert-ball verdict

Per the standing lesson: every factor of every product step, with the exact
producer of its order-0 cap, radius-free vs ball-based.

### 5.1 `low1Ker_jet` (C1) — all steps radius-free, GREEN

`rhsLow1Coeff` (`Analysis/Spectral/Intrinsic/DeTurckCoefficients/RHSThreeArmCancel.lean:300`):

```lean
  (-2 : ℝ) • linearizedRicciConnDiffOrder1Coeff (I := I) g₀ T T' hδ hδ' s +
    deTurckLieArm1Coeff (I := I) (M := M) g₀
      (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg
```

| step | factor A | cap producer | factor B | cap producer | verdict |
|---|---|---|---|---|---|
| `appCcRS(ricciCometricFourTraceCastG0, kernel)` | cometric cast, offset 0 | `cometricCastG0_order0sup_jetL2_radiusFree` (`DeTurckVFJetRadiusFree.lean:66`) — **radius-free** | kernel = 5 permuted `connDiffContrInsertionField`, offset +1 | **no cap needed** — fold at `atgw` level, `rfns_iCG_connDiffSection_atgw_rf` (`:968`) | GREEN |
| `lieArm1Piece(…, connDiffSection g₁ g₀)` and the `lieArm1ConnDiffBgCc` / `lieArm1PsiB` siblings | metric-algebraic wrapper, offset 0 | same | one `connDiffSection`, offset +1 | same | GREEN |
| single `∫` at the end | — | `antidiagonalTupleGrid_integral_radiusFree` with `Λ₀` from `δ ≤ 1/3` | — | — | GREEN |

Both summands are **linear in `∇P`** — verified: `ricci1_split` (§4) shows the
Ricci kernel is a SUM of five copies of one `connDiffContrInsertionField`, and
`deTurckLieArm1Coeff_realizedFam_jetL2_perOrder_ballUniform`
(`Analysis/Sobolev/TensorHilbert/DeTurckLieArm1CoeffL2JetBound.lean:4917`)
decomposes into `lieArm1Piece(…, connDiffSection)`,
`lieArm1Piece(…, lieArm1ConnDiffBgCc)`, `lieArm1Piece(…, lieArm1PsiB)` — one
connection difference each.  This is exactly the shape of
`wOmega = appCc(cometricCastG0, wXi)`, whose radius-free engine already lands on
`range (i + 2)` (`DeTurckVFJetRadiusFree.lean:1117`, conclusion `:1128–1131`).
**No RED flags.  No ball.**

### 5.2 `selfLow_jet` (C0) — RED, and the statement is false

`selfLow_split` (`LowRegC01JetTower.lean:105`) five summands:
`(-2)•ricciGoodLow g gm (s•T)`, `deTurckLieCovDerivArmField − edgeLiePairFam`,
`lc0VB`, `lc0AMix`, `lc0Riem`.

Two of these are **quadratic in `∇P`**:

* `ricciGoodLow = ccInputSymm (ricciLow)` and
  `ricciLow = ricciAAArm + ricciDALow`
  (`Analysis/Spectral/Intrinsic/DeTurck/DeTurckRemainderLowBaseAction.lean:3616`,
  `:3609`).  `ricciAAArm` is
  `appCcRS g 2 4 2 (ricciCometricFourTraceCastG0 g gm) (ricciAAKer g gm)`
  (`Analysis/Spectral/Intrinsic/DeTurck/EdgeRicciPairing.lean:227`) — the `A·A`
  arm of the Ricci variation, quadratic in the connection difference.
* `lc0VB`: `lc0VB_perOrder_rf` (`LieCorr0CoeffDiffRadiusFree.lean:2652`) lands on
  `range (i + 3)`, and its `lc0VB_h2_rf` route is `riemLive × mcd × wOmega`
  (`DeTurckRemainderLowBaseAction.lean:8045–8050`) — `mcd` and `wOmega` are both
  offset `+1`, so the product is offset `+2`.

**Counterexample to the landed statement.**  Take `i = 0`.  `low1Ker`-style
budget is `Kk 0 * (1 + ‖T‖² + ‖∇T‖²)`, with `Kk` chosen before `T`.  Let
`T = A · φ((x − x₀)/λ) · Θ` for a fixed symmetric `Θ` and `A` fixed at the
`δ = 1/3` ceiling.  Then `‖T‖_{L²} = O(λ^{3/2})`, `‖∇T‖_{L²} = O(λ^{1/2})` — the
whole RHS stays bounded as `λ → 0` — while the quadratic head satisfies
`‖ |∇T|² ‖_{L²} = ‖∇T‖_{L⁴}² = Θ(A² λ^{−1/2}) → ∞`.  LHS → ∞, RHS → `Kk 0`.
Only `‖P‖_∞ ≤ δ` is available, and Gagliardo–Nirenberg gives exactly
`‖∇^{j₁}P ∇^{j₂}P‖_{L²} ≲ ‖P‖_∞ ‖∇^{i+2}P‖_{L²}` — one order OVER budget.  The
alternative GN split `‖∇P‖_∞ ‖∇^{i+1}P‖_{L²}` is in budget but needs a cap on
`∇P`, which `δ ≤ 1/3` does not give.  This is the executor's own diagnosis
(PLAN3 `:1114–1120`), one level deeper: it is not only that the *route* fails,
the *statement* fails.

### 5.3 The repo corroborates independently

`ricciArmOrder0BaseCoeff_perOrder_l2_radiusFree`
(`Analysis/Spectral/Tensor/CovGrad/CurvatureCoeffDiffRadiusFree.lean:127`) is
the radius-free engine for exactly the order-0 curvature arm, and it is
**top-separated at `+2`** (`:142–146`), i.e. the tree already concluded, with a
proof, that with an order-0 cap on `P` only, the C0 curvature arm cannot avoid
`‖∇^{i+2}P‖²`.  Same for `lieCorr0Field` and `deTurckLieCoeffField` (§3).
**Every radius-free engine over a C0-shaped object in this repo is
top-separated.  None lands on `range (i+2)`.**

### 5.4 Verdict on the inert ball: it IS honestly available, and C0 needs it

Settled affirmatively, with four pieces of evidence:

1. `c0_jet_tower` binds `(a : ℕ) {R₀ : ℝ} (hR₀ : 0 ≤ R₀)` **before** `∃ Kc`
   (`LowRegC01JetTower.lean:267–268`), so a ball-dependent constant is legal.
2. `hball` is in scope at the exact point where the integrand lemma is applied
   (`:295` `intro T hT δ hδ0 hδ_le hδg hδZ hball i`, used at `:313–316`) — it is
   introduced and currently discarded.  Threading it costs one argument.
3. The downstream consumer already carries and consumes it: `a2_ladder`
   (`Analysis/Spectral/Intrinsic/DeTurck/LowRegLadderRung.lean:232`) has
   `(a : ℕ) (ha : 3 ≤ a) {R₀ : ℝ} (hR₀ : 0 ≤ R₀)` and the hypothesis
   `‖smoothCcToTensorHs g₀ ((a : ℝ) + 2) T‖ ≤ R₀`, which it feeds to
   `appCc_cap_hs_le` (`:77`).
4. The Hs-ball → jet-ball bridge that the ball-uniform producers want
   (`∀ j ≤ a + 2, ‖iteratedCovGrad g₀ 0 2 j T‖ ≤ R`) already exists:
   `exists_iteratedCovGrad_sum_le_smoothCcToTensorHs_general`, used inline at
   `Analysis/Spectral/Intrinsic/DeTurck/DeTurckRemainderPrincipalArmOpNorm.lean:1735`
   with the conversion spelled out at `:1770–1786`.  **Promote that inline
   `have` to a named lemma — it is repeated at `:2134` and `:2692`.**

One residual constraint, and it is cheap: the ball gives `‖∇P‖_∞ ≲ C(R₀)` only
if `H^{a+2} ↪ C¹`, i.e. `a + 2 > 1 + finrank/2`, i.e. `a ≥ 1` in dimension 3.
The consumer's existing `3 ≤ a` covers it.  If instead the implementation reuses
the existing ball-based order-0-sup producers (`connDiffContrInsertionField_order0sup_…`,
`linearizedRicciConnDiffOrder1KernelField_order0sup_…` at
`RicciConnDiffOrder1TameEnvelope.lean:982/1240`), those demand
`2 * finrank ℝ E + 10 ≤ a` (= 16), which **would** force `a1_ladder` to `16 ≤ a`.
Prefer a bespoke `‖∇P‖_∞` producer at `a ≥ 1` over inheriting the `16 ≤ a` gate.

**Important negative result:** the *flat* ball-uniform per-order producers
(`linearizedRicciArm0BaseCoeff_realizedFam_jetL2_perOrder_ballUniform`,
`Analysis/Sobolev/TensorHilbert/RemainderCoeffL2JetMoser.lean:53`;
`deTurckLieArm1Coeff_…`, `DeTurckLieArm1CoeffL2JetBound.lean:4917`) are gated
`i ≤ a` and therefore **cannot** discharge the towers, whose `∀ i` is genuinely
required — `appCc_cap_hs_le` (`LowRegLadderRung.lean:77`) consumes the jet
hypothesis at `∀ i : ℕ` with no gate.  The C0 fix must be an all-orders
`∇P`-capped engine, not a re-use of the flat producers.

## 6. Claim and size audit

`lake-locked status`: eight file claims, **none** on any file A1-CUR touches.
Seven are dead pids (stale, other lanes — leave them);
`Geometry/Connection/LeviCivita/MetricKoszul.lean` (pid 12328) is live and
irrelevant here.

Lines: `LieCorr0CoeffDiffRadiusFree.lean` **3410 — over cap, no additions**;
`DeTurckVFJetRadiusFree.lean` 2287 (near); `LowRegOpJetWindows.lean` 1421;
`RicciConnDiffOrder1TameEnvelope.lean` 1373; `DeTurckLieCoeffDiffRadiusFree.lean`
509; `CurvatureCoeffDiffRadiusFree.lean` 459; `LieFieldJetL2Summed.lean` 430;
`AntidiagonalTupleProductGrid.lean` 321.  `DeTurckRemainderLowBaseAction.lean`
13839 — other-lane, READ-ONLY.  `…/CurvatureCoefficientDifferenceJetTower/`:
9 chunks, 1158–2395 each, split LANDED, workhorse in `Residual.lean`.

## 7. Brick decomposition

### A1-CUR-1 (FIRST DISPATCHABLE) — `low1Ker_jet`, radius-free, no statement change

Difficulty: **routine-to-moderate**; one session.  No new mathematics — a
re-instantiation of the `wOmega` fold at two new kernels.

Steps:
1. Public re-derivation of `ricci1_split` (§4) at
   `Analysis/Sobolev/TensorHilbert/RicciOrder1KernelSplit.lean` (new), plus
   promotion of `kernelField_eq_neg_arm_combination` from
   `LieFieldJetL2Summed.lean:136` and deletion of the
   `RicciConnDiffOrder1TameEnvelope.lean:738` duplicate.
2. `rfns_iCG_ricciOrder1Kernel_atgw_rf` — pointwise `atgw` bound at offset `+1`,
   from `rfns_iCG_connDiffSection_atgw_rf` (`DeTurckVFJetRadiusFree.lean:968`)
   through the five permutations (fibre-norm isometry under
   `rsDomDomCongrSection` / `reindexCoeffGen` — the isometry lemmas used by
   `lc0Diff_perOrder_rf` at `LieCorr0CoeffDiffRadiusFree.lean:186–198` are the
   template).
3. `linearizedRicciConnDiffOrder1Coeff_perOrder_l2_radiusFree` — fold
   step 2 against `rfns_iCG_cometricCastG0_atgw_rf` via
   `antidiagonalTupleGridWindow_mul_le`, integrate once with
   `antidiagonalTupleGrid_integral_radiusFree`.  Model the whole proof on
   `wOmega_lowOrder_jetL2_radiusFree` (`DeTurckVFJetRadiusFree.lean:1117–1150`).
4. `deTurckLieArm1Coeff_perOrder_l2_radiusFree` — same fold at the three
   `lieArm1Piece` arguments.
5. `low1Ker_jet` = `jetAdd`/`jetSmul` over 3+4, with the `moserWin_sharp`
   `choose`-over-`a` idiom to remove the `i ≤ a + 1` gate.

Verification: focused check of the new file and of `LowRegC01JetTower.lean`
(`scripts/lake-locked.ps1 check -Files … -NoLakeLock`), then a targeted
`build -NoLakeLock +…` refresh of the two edited upstream modules before
re-checking the tower.  Budget for a `CurvatureCoefficientDifferenceJetTower`
olean rebuild (PLAN3 `:1200–1213`); the split makes that cheaper now.

### A1-CUR-2 — planner ruling required BEFORE any Lean work

`selfLow_jet` must be restated.  Three candidates, in ascending cost:

* **(a) Thread the ball.**  Add `(a : ℕ) (ha : 1 ≤ a) {R₀} (hR₀)` before the
  existential and `‖smoothCcToTensorHs g ((a : ℝ) + 2) T‖ ≤ R₀` after `T`.
  `c0_jet_tower` then passes its own `hball` (already in scope, `:295`).  No
  change downstream.  Cost: a `∇P`-capped (`Λ₁`) sibling of the grid workhorse
  and of the `b4_*_atgw` folds for the two quadratic summands.
* **(b) Top-separate the tower** as `Ktop i * ‖∇^{i+2}T‖² + Kc i * (1 + …)` and
  push the head into an `a1_ladder` of `a2_ladder`'s shape
  (`κ * (δ/(1-δ)²) * ‖T‖_{H^{m+2}} + Clower m * ‖T‖_{H^{m+1}}`,
  `LowRegLadderRung.lean:253–256`).  Mathematically sound — the quadratic head's
  coefficient really is `O(‖P‖_∞) = O(δ)` — but it requires extracting
  `Λ₀`-linearity from `Atop` in the existing engines, which none of them state.
* **(c) Both**: (a) for the two quadratic summands, unchanged radius-free for
  the other three.

Recommendation: **(a)**.  It is the standard quasilinear-energy device, it
matches what the tree already does everywhere ball-uniform, it needs no change
to `a2_ladder`'s established shape, and the required ball is provably in scope.

Difficulty: **substantial** — a new order-1-capped currency layer.  3–4 sessions.
Do not dispatch before the ruling.

### Stop-signal

This campaign is at route-error 2/3.  For A1-CUR-1, **iterate** on: rewrite-shape
failures, `rsDomDomCongr` slot mismatches, `atgw` index bookkeeping, gate
`omega`s.  **Stop and report** if: (i) any summand of `rhsLow1Coeff` turns out to
carry a second `connDiffSection` factor (that would make C1 quadratic too, and
`low1Ker_jet` false as well — grep the *definition*, never the name); (ii) the
`atgw` fold for the Ricci kernel lands on `atgw (i+3)` rather than `atgw (i+2)`
after the permutation isometries; (iii) `antidiagonalTupleGrid_integral_radiusFree`
turns out to need `P` at valence `0 2` in a way the kernel cannot supply.  Any of
those is a statement-level problem, not a tactic problem.

## 8. Honest denominators

* `low1Ker_jet`: **0%** (stated, `sorry` at `LowRegC01JetTower.lean:88`).  Its
  dedicated machinery: ≈ 70% (base engine, `atgw` currency, product rule, the
  workhorse and the `wOmega` template all exist; the two new folds do not).
* `selfLow_jet`: **0%, and negative** — the statement is false as landed and must
  be replaced.  Its dedicated machinery: ≈ 35% (the radius-free layer exists but
  is top-separated at `+2` for every C0-shaped object; the `Λ₁`-capped layer does
  not exist at all).
* A1-CUR as a whole: ≈ **10%** (this recon plus the four promotable pieces).
* `c1_jet_tower` / `c0_jet_tower`: derivations proved, integrands 0% ⟹ ≈ 15% / 20%
  (unchanged from the A1a/A1b report).
* F6: revise DOWN again, ≈ **60%** — PLAN3 No. 111 scoped A1-CUR as "packaging";
  it is one small brick plus one statement-change brick with a new currency layer.
* Front 2 ≈ 50%.  (N) `ricci_flow_unif_existence`: **0%** — not stated in the
  form the campaign targets.  Machinery ≈ 92%.  Whole HCG compactness project:
  low single digits.
* New stocked-wall instances found: **two**.  (1) "`range (i+3)` is slack" —
  refuted, the sole cited witness `lc0VB_h2_rf` is a quintic in a different
  currency.  (2) "the pieces cover everything the composites cover, so the
  assembly is packaging" — true for the `Atop` heads, false for the budget: the
  quadratic-in-`∇P` summands are a separate, statement-level obstruction that no
  regrouping removes.

## 9. STATUS 2026-08-03 — A1-CUR-1 partially executed; §7 steps 1–2 done, 3–5 open

Executed against §7.  **`low1Ker_jet` is still `sorry`.**

### Done and verified sorry-free

* §7 step 1 — public re-derivation of `ricci1_split` and promotion of
  `kernelField_eq_neg_arm_combination`.  **Correction to §4/§7:** the plan named
  the `LieFieldJetL2Summed.lean:136` copy, but that module is **not** in
  `LowRegC01JetTower`'s import chain while
  `RicciConnDiffOrder1TameEnvelope.lean:738` **is**.  The envelope copy was
  promoted (with `slotPermCc` and the seven `kOutPerm*`/`kInPerm*`); the
  `LieFieldJetL2Summed` copy was left untouched; no duplicate, no new import.
  The `rsDomDomCongrSection` form is `ricci1Split`, obtained via a public
  re-derivation `permAppEqRs` of the read-only-file `private` `permApp_eq_rs`.
  Home: new `Analysis/Sobolev/TensorHilbert/RicciOrder1RadiusFree.lean`.
* §7 step 2 — `ricciKerAtgw` (the plan's `rfns_iCG_ricciOrder1Kernel_atgw_rf`),
  via `insertAtgw`.  Lands at **`atgw(l + 2)`**, i.e. the plan's stop-signal
  (ii) did NOT fire.
* `rfns_iCG_connDiffSection_atgw_rf` promoted `private` → public
  (`DeTurckVFJetRadiusFree.lean`); §7 step 2 needs it and a new file cannot see
  a `private`.
* **NEW, not in §7 — the generic composer.**  §7 steps 3 and 4 were each
  budgeted at a ~225-line re-instantiation of
  `wOmega_lowOrder_jetL2_radiusFree`.  Inspection showed that proof is entirely
  generic in its two arms, so it was extracted once as
  `Analysis/Sobolev/TensorHilbert/AtgwArmFold.lean`: `atgwFold` (pointwise
  two-arm Leibniz fold, generic left rank / valences / offsets) and `atgwToJet`
  (the integration step).  This also serves A1-CUR-2's five C0 summands and
  supersedes the eight duplicated `b4_*_atgw` folds of
  `LieCorr0CoeffDiffRadiusFree`.  Steps 3 and 4 are now ~60 lines each.

### Open — the exact remaining frontier

1. `ricciCometricFourTraceCastG0` `atgw` at offset `+1`: a valence-`(4,2)` clone
   of `rfns_iCG_cometricCastG0_atgw_rf` (`DeTurckVFJetRadiusFree.lean:824`,
   ~134 lines).  Inputs already radius-free:
   `rfns_iteratedCovGrad_slotInsertEndoCc_zero_gInvDiffRaisedEndoField_diagonalProductGrid_le`
   and `exists_bound_riemannianFiberNormSq_smoothCcTensor` on
   `cometricDoubleTraceField g₀ 2`; structure from
   `ricciCometricFourTraceCastG0_eq_reindex_combination` +
   `ricciArmPrincipalCoeffPure_eq_doubleTrace_add_appCcRS`.
2. §7 step 3 = `atgwFold (u := 0) (v := 1)` of 1 against `ricciKerAtgw`, then
   `atgwToJet (w := 2)`.
3. §7 step 4 = the same for the three `lieArm1Piece`s.  **At the tower's call
   site `g_bg = g₀`**, so `lieArm1ConnDiffBgCc g₀ g₁ g₀ = connDiffSection g₁ g₀`
   is already covered by the promoted lemma; only `lieArm1PsiB`
   (`connDiffLoweredCc` against `sharpFlatEndoCc`) and
   `deTurckLieTraceCoeff` (at `+1`) are new.
4. §7 step 5 = assembly.  `IsPathPert` (`LowRegOpJetWindows.lean:547`) is the
   exact bridge to the engines (it carries `htie`, `Λ₀ = finrank·δ₀`, and
   `lowJetSq g n P ≤ lowJetSq g n T`); `pathPert_rad` produces it for the radial
   path; `moserWin_sharp` (`:684`) is the `choose`-over-`a` template that
   removes the `i ≤ a + 1` gate.

### Correction to §8 denominators

`low1Ker_jet` still **0%**; its dedicated machinery ≈ 70% → ≈ **85%**.
A1-CUR overall ≈ 10% → ≈ **30%**.  F6 ≈ **62%**.  `selfLow_jet` unchanged at
0%, but its statement is now honest (ball threaded, gate `1 ≤ a`, option (a) as
ratified).

### Trap found while executing

`rfns_iteratedCovGrad_appCcRS_diagonalProductGrid_le` is **left-rank-0 only**.
Both the Ricci outer arm (rank 4) and the Lie outer arm (rank 3) need
`…_rankLeft_le` (`MetricArmCoeffJetTower.lean:2361`).  `atgwFold` was
generalised accordingly.

## 10. STATUS 2026-08-04 — A1-CUR-1 **CLOSED**; only A1-CUR-2 remains

`low1Ker_jet` is proved sorry-free; `c1_jet_tower` is now unconditional
(`[propext, Classical.choice, Quot.sound]`).  §7's five steps are all done.
No statement anywhere was changed.

### How the four open items of §9 actually closed

1. *(§9 item 1, budgeted ~134 lines)* — **not needed as planned.**  The existing
   `rfns_iteratedCovGrad_ricciCometricFourTraceCastG0_diagonalProductGrid_le`
   (`RicciConnDiffOrder0KernelJetGrid.lean:1037`) already *is* the `+1` window:
   its RHS `C n * ∑_{k<n+1} atg b k` is `C n * atgw b (n+1)` by `rfl`.
   `fourTrAtgw` is 12 lines.  A `pureAtgw` (window of
   `ricciArmPrincipalCoeffPure`, ~65 lines via `atgwFold`) *was* written, but for
   the **Lie** outer factor, not the Ricci one — see item 3.
2. *(§9 item 2)* `ricci1Atgw` = `atgwFold (u := 0) (v := 1)` of `fourTrAtgw`
   against `ricciKerAtgw`, ~30 lines as predicted.
3. *(§9 item 3)* **`deTurckLieTraceCoeff g₀ g₁ σ = reindexCoeffGen (ricciArmPrincipalCoeffPure g₀ g₁) σ`**
   (`dltcEqPure`) — both are the moving cometric double trace read through a
   fixed source-slot permutation.  So the Lie outer factor's `+1` window is
   `pureAtgw` composed with `rfns_iteratedCovGrad_reindexCoeffGen_eq`.  This is
   the structural fact §7 did not anticipate; it is why the Ricci and Lie arms
   cost one window between them rather than two.
   `lieArm1PsiB` was closed **without** promoting anything out of
   `DeTurckLieArm1CoeffL2JetBound.lean`: it is
   `appCcRS (raised κ) (sharpFlatEndoCc)` with
   `κ = -metricConnDiffLoweredCc` (public `metricConnDiffLoweredCc_eq_neg_kappa`),
   whose `+2` window already existed as the `private` `b4_mcd_atgw` in
   `LieCorr0CoeffDiffRadiusFree.lean`.  Promoting that one lemma was the **only**
   edit outside the new module.  `sharpFlatEndoCc`'s `+1` window is the public
   `exists_rfns_iteratedCovGrad_sharpFlatEndoCc_tgrid`.
4. *(§9 item 4)* Assembly used `pathPert_rad` + `atgwToJet (w := 2)` exactly as
   §9 predicted.  `moserWin_sharp` was **not** needed — the radius-free windows
   carry no order gate, so there is nothing to `choose` over.  The `le_abs_self`
   trick was also unnecessary: `Kk i = ∑_{q<i+1} Kw q · (∑_{k<q+2} Kint k)` is
   manifestly nonnegative.

Home: new `Analysis/Sobolev/TensorHilbert/Low1KerRadiusFree.lean` (12 public
declarations, all axiom-clean; see `Low1KerRadiusFree.md` for the map and the
traps).

### Denominators after this session

* `low1Ker_jet` / A1-CUR-1: **100%** (stated and proved).
* `c1_jet_tower`: **100%** — unconditional, `sorryAx`-free.
* `selfLow_jet` / A1-CUR-2: **0%**, unchanged.  Its dedicated machinery ≈ 35% →
  ≈ **45%**: `atgwFold`/`atgwToJet`/`pureAtgw`/`sfEndoAtgw`/`pieceAtgw`/
  `b4_mcd_atgw` are directly reusable for the three *linear* summands of
  `selfLow_split`, but the `Λ₁`-capped (`∇P`-capped) currency the two
  **quadratic** summands need (the `A·A` arm inside `ricciGoodLow`, and `lc0VB`)
  still does not exist anywhere in the tree.  That, not packaging, is the
  remaining brick.
* `c0_jet_tower`: ≈ **20%**, unchanged (derivation proved, integrand 0%).
* A1-CUR overall ≈ 30% → ≈ **45%**.
* F6 ≈ 62% → ≈ **66%**.

## 11. STATUS 2026-08-04 (session 2 of A1-CUR-2 prep) — the `Λ₁`-capped currency EXISTS

Recommendation **(a)** of §7 was executed.  The `∇P`-capped currency is built,
verified and smoke-tested; `selfLow_jet` itself is still `sorry`.

Key correction to §7's cost model: the capped layer is NOT a "capped sibling of
the `b4_*_atgw` folds".  A pointwise/combinatorial repair is impossible (the
over-budget term `∫|∇^αP|²|∇^βP|²` with `α ≈ β ≈ n/2` has neither factor
capped).  The capped currency is the SAME radius-free currency run on the base
tensor `∇P` at valence `(0,3)`, with `Λ₁ = ‖∇P‖_∞` where `Λ₀ = ‖P‖_∞` sits at
`(0,2)`.  That required generalizing `grid_prod_int_le` /
`antidiagonalTupleGrid_integral_radiusFree` / `gridBase`/`atgwFold`/`atgwToJet`
in base valence — done in place, with the old `(0,2)` statements kept as
one-line instances so no call site changed (one lives in a READ-ONLY file).

Landed, all axiom-clean:

* `GradCapAtgw.lean` — `gradCapOfJets`/`gradCapOfBall` (the `Λ₁` producer at
  gate `1 ≤ a`; §5.4's "bespoke `‖∇P‖_∞` producer at `a ≥ 1`" — the `a ≥ 16`
  producers were NOT inherited), `atgwShift` (the base shift), `armShift`,
  `atgwCapToJet`, `atgwCapArm`, `atgwCapFold`.
* `Lc0VBCapWindow.lean` — `lc0VB` on `range (i+2)`.  One promotion
  (`b4_wOmega_atgw`).

### Denominators after this session

* `selfLow_jet` / A1-CUR-2: **0%**, unchanged.  Machinery ≈ 45% → ≈ **70%**.
* `c0_jet_tower`: ≈ **20%**, unchanged.  A1-CUR overall ≈ **60%**.  F6 ≈ **70%**.

### Remaining frontier (the ONE blocker for the assembly)

`ricciAAArm` is not reachable by shifting its folded window: `ricciAAKer` is a
single arm that is itself quadratic, and the shift is sharp only when every grid
entry of the bound carries a factor.  Session 2 needs a public two-arm split of
`ricciAAKer` (`aaKer_eq` + the six `aa*`, all `private` in the READ-ONLY
`DeTurckRemainderLowBaseAction.lean:4400`) and `armShift` on each nest.

---

## 2026-08-04 — A1-CUR CLOSED (session 3)

The frontier recorded above (the `ricciAAKer` two-arm split) was resolved in
session 2 by public re-derivation (`aaKerSplit`), and the two per-arm windows
it left, `ricciDACap` and `lieCovCap`, were proved in session 3.

**A1-CUR: 100%.**  `selfLow_jet` and `c0_jet_tower` are unconditional and
axiom-clean; `c1_jet_tower` was already.  Both towers of the F6 estimate chain
now stand on no `sorry`, so **the F6 estimate chain is closed**.

* Code: new `Analysis/Spectral/Intrinsic/DeTurck/SelfLowArmCaps.lean` (both
  windows, sorry-free); `GradCapArms.lean` gained `capOfP`, `capOfDP`,
  `capDdc0`; `LowRegC01JetTower.lean` lost both private stubs and is
  sorry-free.
* Route, traps and the corrected wall census: `SelfLowArmCaps.md` and
  `LowRegC01JetTower.md` (session N+4 entry).
* Executor report and honest denominators: `UNIF_EXISTENCE_PLAN4.md`
  (PLAN3 hit the 3000-line limit).

Next in F6: **A1c `a1_ladder`** then **A1d `n_diff_hm_rung`**, routine assembly
over the two towers, both unwritten (0%).  `a1_ladder`'s binder shape, adapted
from `a2_ladder` (`DeTurck/LowRegLadderRung.lean:232`), is spelled out at the
end of `UNIF_EXISTENCE_PLAN4.md`.
