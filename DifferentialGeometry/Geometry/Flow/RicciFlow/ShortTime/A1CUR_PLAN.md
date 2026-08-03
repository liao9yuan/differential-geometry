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
