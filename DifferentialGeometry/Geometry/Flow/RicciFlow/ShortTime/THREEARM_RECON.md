# THREEARM_RECON — item-2 PROPER (threeArm/Ψ₀ assembly + smooth-core tame lemma)

State-before-prove recon for UNIF (N) night-charter №28 queue item 3. RECON ONLY
— no proof campaign launched, no in-flight lane file touched, no `.lean` written.
Home justified below (§10). All line refs verified against the ste-align tree
HEAD (`codex/short-time-existence-align`) on 2026-07-25.

Companion notes (do not duplicate; this consolidates across both subtrees):
- `Analysis/Sobolev/TensorHilbert/ThreeArmTopSeparated.md` — the (stale, 2026-07-22)
  constituent-map forensics. **This recon corrects two of its claims (§4).**
- `Analysis/Spectral/Intrinsic/DeTurck/SobolevNonlinearityExistence.md` — the route
  test (verdict (a) FEASIBLE). **This recon finds a currency gap its verdict glossed (§5).**

---

## 0. LEAD FINDINGS (read first — these contradict the plan's premises)

**LF-1 (decisive). The "6/7 constituents closed" scoreboard is misleading: the
landed deTurckLie constituent is closed in a shape the smooth-core assembly
cannot consume.**  The route needs, per C₀ field, `Ktop·(a+2 window) + Kc·(1 +
a+1 LOW window)` with **both `Ktop` and `Kc` R-independent** (this is exactly what
the arm0Base producer delivers, `ArmBaseCoeffJetL2Summed.lean:139`, docstring
confirms R-independence).  The landed combined deTurckLie producer
(`DeTurckLieCoeffL2JetBound.lean:799`) instead delivers `Ktop·(a+2 window) +
Kc·(1 + a+2 FULL window)` with **`Kc` R-DEPENDENT** — its `Kc` routes through
`boundedFactorGridWindow_integral_ballUniform_tameWindow`
(`CurvatureCoefficientDifferenceJetTower.lean:13180`), whose output constant is
`(∑_{k<i+3} Kt k)·(1 + R²)` (:13207) with `Kt` the antidiagonal grid ~`R^{7k}`.
Two independent defects: (i) `Kc` carries `R`; (ii) `Kc` multiplies the top
`a+2` window (includes `‖∇^{a+2}T‖²`), not the low `a+1` window.

**LF-2 (why LF-1 is fatal, not cosmetic).**  In the R-free smooth-core target the
`H^{a+2}` ball is REMOVED, so `R` must be instantiated by the actual jet sup
`≈ ‖T‖_{a+2}`.  Then the deTurckLie term contributes, to the coefficient of
`‖T−T'‖_{a+2}` (orientation 1), a factor `Kc(R)·∑_{j≤a+2}‖∇^jT‖² ⟹
‖T‖_{a+2}²·(…)`, i.e. it puts `‖T‖_{a+2}` into orientation-1's coefficient.  That
is precisely the ruling's forbidden shape `‖T‖_{a+2}·‖T−T'‖_{a+2}` /
pointwise-`H^{a+2}` STOP SIGNAL (`UNIF_N_PRO_RULING.md`; route-test stop signal,
`SobolevNonlinearityExistence.md:14`).  The route test verified R-independence
ONLY for arm0Base (its cited exemplar); it did not check that the deTurck-Lie /
lieCorr0 constituents achieve the same R-free-`Kc`-on-low-window shape.  They do
not.  This is the same "tame-envelope generic is R-dependent" trap that already
forced one plan correction (plan status log 2026-07-22, "route-test over-claimed").

**LF-3 (in-flight lieCorr0 is being built into the SAME defect).**  lieCorr0 is
the last "top-window" C₀ constituent (`LieCorr0CoeffL2JetBound.lean`, atoms 2/4).
Its top piece is `deTurckLieDLbCoeffField_..._topSeparated @ g_bg:=g₀` (:107) and
its Kc atoms use the same ballUniform-window integrator family.  So finishing
lieCorr0 as planned yields another R-dependent-`Kc`-on-`a+2`-window producer — it
will inherit LF-1.  Completing lieCorr0 does NOT unblock the assembly.

**LF-4 (good news — the "missing C₁ producers" the stale note demanded are NOT
needed).**  `ThreeArmTopSeparated.md:122` claims `deTurckLieArm1Coeff` (and
`arm1Corr`) need new top-separated producers for C₁.  FALSE: their committed
tame-envelope bounds (`…deTurckLieArm1Coeff_realizedFam_allOrder_tameEnvelope`
frozen :38298; `exists_corrArm0Field_…_tameEnvelope` :1539;
`exists_corrArm1Field_…` :193) are all pure `K·(1 + ∑_{j≤i+1})` with **Ktop = 0
structurally** (window `i+1`, no `∇^{a+2}` term) — the traceHessian "absorbed"
shape.  These fields carry no top data-weight, so they need no top-separated
producer.  BUT their `K` is R-dependent (same converter, :1321), so they still
need an R-FREE low-only bound for the R-free target (see §4/§5) — a much smaller
task than a topSeparated producer, if it exists at all.

**Net:** item-2 proper is NOT "assemble the 7 landed constituents."  The correct
next question is the **`Kc`-currency fork** (§6): either the covariant-tame lift
absorbs R-dependent `Kc` (route survives, assemble), or the deTurckLie/lieCorr0
constituents must be reworked to arm0Base's R-free-`Kc`-on-low-window shape (large
reopen; possibly route-dead if those fields do not admit the R-free
background-difference engine arm0Base uses).  This fork is the campaign's main
risk and is consult-worthy (§7).

---

## 1. What the threeArm/Ψ₀ assembly IS (verified anatomy)

The symmetric Ricci–DeTurck remainder difference `N(T) − N(T')` is decomposed by
the frozen reference
`deTurckSmoothRemainderDiff_threeArm_coeffC0_jetL2_fibreWeighted_ballUniform_of_symm`
(`DeTurckRemainderTameLipschitz.lean:36054`) into three "arms":

```
N(T) − N(T') = appCc g₀ 2 2 C₀ (∇⁰(T−T'))
             + appCc g₀ 3 2 C₁ (∇¹(T−T'))
             + appCc g₀ 4 2 C₂ (∇²(T−T'))
```

with coefficient valences C₀:(2,2), C₁:(3,2), C₂:(4,2).  The coefficients come
from the `canonicalTop` sub-lemma
`deTurckRHSArmDiff_threeArm_canonicalTop_coeffC0_jetL2_ballUniform_of_symm`
(`:34758`), which builds each Cₘ as a path integral `pathIntegralCoeffField g₀
(2+m) 2 Ψₘ` of an integrand `Ψₘ : ℝ → SmoothCcTensor g₀ (2+m) 2` (`:34827`):

```
Ψ₀ s = (-2)•arm0Field s + ( deTurckLieCoeffField (realizedFam s) g_bg
                          + lieCorr0Field       (realizedFam s) g_bg )      -- (2,2)
Ψ₁ s = (-2)•arm1Field s +   deTurckLieArm1Coeff (realizedFam s) g_bg        -- (3,2)
Ψ₂ s =                      deTurckPhiMetTotal   (realizedFam s)            -- (4,2)
```

plus `C₀ = pathIntegralCoeffField Ψ₀ + K₀` where `K₀` is a T-independent
background curvature-fold (`:36087`, absorbed as a constant).  In the reference,
`C₂` is re-expressed as the deviation `deTurckPhiTotPathIntegral − deTurckPhiMetTotal(g₀)`
(`:36144`), which is already the R-independent top-arm object (§3).

Here `arm0Field = arm0BaseCoeff + arm0CorrField`,
`arm1Field = arm1BaseCoeff + arm1CorrField` (frozen `:2047`).

**The "threeArm/Ψ₀ assembly" = re-derive `:34758`→`:36054` producing the SAME
identity but with the coefficient jet-L² bounds in the data-weighted
top-separated currency** (`Ktop·top + Kc·(1+low)`, both R-free) **instead of the
opaque ballUniform `Γ²`/`ΛC²`**.  This is layer 1 of 3 (§2).

The reference's ballUniform proof consumes, per field (`:34788`–`:34809`): the
combined-arm `linearizedRicciArm_concreteField_jetL2_ballUniform` (arm0+arm1,
base+corr together), and per-field `deTurckLieCoeffField_…`, `lieCorr0Field_…`,
`deTurckLieArm1Coeff_…` ballUniform producers.  The topSeparated assembly must
replace each with the R-free currency (§4 inventory).

---

## 2. Target chain (three layers) — pseudo-Lean specs

The final currency is the H^a smooth-core estimate (`SobolevNonlinearityExistence.md:9`):

```
‖N(T) − N(T')‖_{Hᵃ} ≤ K · ( (1 + max‖T‖_{a+1} ‖T'‖_{a+1}) · ‖T−T'‖_{a+2}
                          +      max‖T‖_{a+2} ‖T'‖_{a+2}  · ‖T−T'‖_{a+1} )
```
with **K R-INDEPENDENT and NO `H^{a+2}` ball hypothesis**.  The existing
ballUniform endpoint `smoothRemainderDiff_ballLipschitz_Ha1_dataWeighted_of_symm`
(`SobolevNonlinearityExistence.lean:1924`) already has this bilinear SHAPE but
carries the ball hyps and K~R (hidden).  The three layers, each mirroring a
committed ballUniform lemma:

**Layer 1 — data-weighted threeArm coefficient bound** (topSeparated analogue of
`:36054`; the "Ψ₀ assembly").  For each Cₘ:
```
-- NOT YET STATED anywhere in Lean. Pseudo-Lean:
theorem deTurckSmoothRemainderDiff_threeArm_coeff_jetL2_summed_topSeparated_of_symm
    (g₀ g_bg) (a) (ha_super) (hδ₀ : δ₀ < 1) :
  ∃ (Ktop Kc c : ℝ) (0 ≤ …), ∀ T T' … (symm, fibreOpBound),   -- NO R, NO ball hyp
    ∃ C₀ C₁ C₂,
      N(T) − N(T') = appCc C₀ ∇⁰(T−T') + appCc C₁ ∇¹(T−T') + appCc C₂ ∇²(T−T')  ∧
      -- top arm C₂: sup ≤ (c·max βT βT')², c R-free (deviation, §3)              ∧
      rfns(C₂) ≤ (c · max βT βT')² ∧
      -- low arms C₀,C₁ jet-L² in DATA-WEIGHTED top-separated currency:
      ∑_{i≤a} ‖∇ⁱ C₀‖² ≤ Ktop·∑_{j≤a+2}(‖∇ʲT‖²+‖∇ʲT'‖²) + Kc·(1 + ∑_{j≤a+1}(…)) ∧
      ∑_{i≤a} ‖∇ⁱ C₁‖² ≤ Ktop·∑_{j≤a+1}(…)              + Kc·(1 + ∑_{j≤a}(…))
```
Assembled from the per-field summed producers by a triangle/Cauchy–Schwarz over
`Ψ₀ = −2·arm0 + deTurckLie + lieCorr0` etc.  **Blocked by LF-1/LF-3**: the
deTurckLie/lieCorr0 inputs are not in this currency (their `Kc` is R-dependent and
on the `a+2` window).

**Layer 2 — covariant tame estimate** (analogue of
`deTurckSmoothRemainderDiff_iteratedCovGrad_l2_dataWeighted_ballUniform_of_symm`,
`SobolevNonlinearityExistence.lean:1421`).  Feed the layer-1 bound through the
two-arm tame product `appCcTwoArmQUniform` (`:1222`) KEEPING the top arm's `c` and
the low arms' `Hd`/`rem` split, instead of lumping into `base ~ Γ²+ΛC² ~ R²`.
Output = iteratedCovGrad-level two-orientation estimate.

**Layer 3 — smooth-core lift** (analogues of
`deTurckRemainderDiff_iteratedCovGrad_ballLipschitz_dataWeighted_of_symm` `:1810`
→ `smoothRemainderDiff_ballLipschitz_Ha1_dataWeighted_of_symm` `:1924`).  Convert
iteratedCovGrad L² sums ↔ smooth-core `H^σ` norms via
`exists_{smoothCcToTensorHs_le_iteratedCovGrad_sum,iteratedCovGrad_sum_le_smoothCcToTensorHs}_general`,
dropping the `hball_conv` step (`:1970`) that manufactured the R-ball.  Output =
the final endpoint above.

Layers 2–3 are structurally settled (mirror committed proofs, keep weights
explicit).  **Layer 1 is where all the risk lives** (LF-1..LF-4).

---

## 3. C₂ (top arm) — already R-free, do not touch

`C₂` sup bound is `rfns(C₂) ≤ (c·max βT βT')²` with `c = √(8·CTH 0 + 8·CR 0)·
(dim/(1−δ₀))` R-free, from
`deTurckPhiTotPathIntegral_deviation_fibreWeighted_jetL2_ballUniform`
(`DeTurckRemainderTameLipschitz.lean:35645/35700`), `CTH/CR` from
`traceHessianCoeff_sub_background_perOrder_rfns_le_gInvDiffSlotCoeff_rfns`
(`RemainderCoeffL2JetMoser.lean:345`) called with only `g₀`.  `βT ≈ ‖T‖_{a+1}`
(LOW).  This is orientation-1's `(1+…)·‖T−T'‖_{a+2}` and is the ONE piece the
route test verified cleanly.  traceHessian (`TraceHessJetL2Summed.lean:181`,
Ktop=0) folds into C₂'s low part — absorbed, R-currency to be checked like §4.

---

## 4. Corrected constituent inventory (top-window? R-free-Kc? exists?)

Legend: **TW** = genuine top-window (`∇^{a+2}`) contributor, needs Ktop≠0 data
weight; **ABS** = Ktop=0, absorbable into orientation-1 low factor.  R-free-Kc =
whether its low/`Kc` constant is R-independent (required for the R-free target).

| Ψ | field | valence | class | landed producer | shape OK? |
|---|-------|---------|-------|-----------------|-----------|
| Ψ₀ | arm0BaseCoeff | (2,2) | TW | `ArmBaseCoeffJetL2Summed:139` | **YES** — `Ktop`(a+2)+`Kc`(1+**a+1**), both R-free (docstring) |
| Ψ₀ | arm0CorrField | (2,2) | ABS | only `…_tameEnvelope:1539` | **NO** — Ktop=0 ✓ but `Kc` R-DEP (converter :1321); needs R-free low bound |
| Ψ₀ | deTurckLieCoeffField | (2,2) | TW | `DeTurckLieCoeffL2JetBound:799` | **NO** — `Ktop`(a+2)+`Kc`(1+**a+2**), `Kc` **R-DEP** (LF-1) |
| Ψ₀ | lieCorr0Field | (2,2) | TW | in flight `LieCorr0CoeffL2JetBound` (2/4 atoms) | **NO (projected)** — same converter family (LF-3) |
| Ψ₁ | arm1BaseCoeff | (3,2) | TW(a+1) | `ArmBaseCoeffJetL2Summed:196` | **YES** — `Ktop`(a+1)+`Kc`(1+a), R-free |
| Ψ₁ | arm1CorrField | (3,2) | ABS | only `…_tameEnvelope:193` | **NO** — as arm0Corr |
| Ψ₁ | deTurckLieArm1Coeff | (3,2) | ABS | only `…_tameEnvelope` frozen :38298 | **NO** — Ktop=0 ✓ but `Kc` R-DEP |
| Ψ₂ | deviation/traceHess | (4,2) | — | frozen :35645 / `TraceHessJetL2Summed:181` | **YES** — R-free (§3) |

Intermediate engines NOT direct Ψ constituents (they build deTurckLie):
`connDiffContrInsertionField_…_summed_topSeparated` (`ConnDiffJetL2Summed:501`),
`linearizedRicciConnDiffOrder1KernelField_…` (`LieFieldJetL2Summed:362`),
`covGradConnDiffSection_…` (`DLaTopSeparated:474`), `deTurckLieWEndoInsert_…`
(`DeTurckVectorFieldL2JetBound:4551`), DLa/DLb (`DeTurckLieKernelL2JetBound:5966`,
`DeTurckLieCoeffL2JetBound:483`).  The plan's line 1028 records connDiff's `Kc`
"carries the converter … accepted house R-pattern" — this is the R-dependence that
propagates up into deTurckLie (LF-1) and will into lieCorr0 (LF-3).

**Corrected constituent picture:** only arm0Base, arm1Base, deviation/traceHess
are in route-usable currency.  Every deTurck-Lie-flavoured field (deTurckLie,
lieCorr0, deTurckLieArm1) and both Corr fields carry R-dependent `Kc`.

---

## 5. Where the route test's verdict (a) glossed the currency

`SobolevNonlinearityExistence.md` demonstrated R-independence via arm0Base's
engine `ricciArmOrder0BaseCoeff_…_topSeparated_generic`
(`CurvatureCoefficientDifferenceJetTower.lean:14447`) sourced from
`…_backgroundDifference_topSeparated_le` (called with only `g₀,hδ₀` — genuinely
R-free).  It then wrote "Analogues exist for arm1 and the DeTurck
connection-difference/Lie fields (`RicciConnDiffOrder1TameEnvelope.lean`)" and
asserted their `Ktop,Kc` are R-independent.  **That assertion is only half true:**
their `Ktop` (top data-weight) is R-free (protected, verified), but their `Kc`
routes through the `boundedFactorGridWindow`/`antidiagonalTupleGrid` ballUniform
converters whose constants are `(∑Kt)·(1+R²)`, `Kt ~ R^{7k}` — R-DEPENDENT, and
they place it on the `a+2` window.  The route test's stop-signal discipline
watched only `Ktop`; the R-dependence hid in `Kc`.  The `arm0Base` vs `deTurckLie`
producer-shape diff (`:158` `range (a+2)` low window with R-free Kc vs `:819`
`range (a+3)` window with R-dep Kc) is the concrete fingerprint.

This does not by itself kill R1τ — IF layer 2's tame lift can route the entire
`Kc·(a+2 window)` into orientation 2 (weighted against `‖T−T'‖_{a+1}`, where an
extra `‖T‖_{a+2}` is a legal data weight) rather than orientation 1.  Whether it
can is the fork (§6).

---

## 6. THE FORK (decides the whole campaign size and viability)

**Fork A — R-dependent `Kc` is absorbable downstream.**  Claim: the covariant-tame
lift (layer 2) can send deTurckLie/lieCorr0's `Kc·(1 + a+2 window)` entirely into
orientation 2 `max‖T‖_{a+2}‖T'‖_{a+2}·‖T−T'‖_{a+1}` (a legal data weight), leaving
orientation 1's `‖T−T'‖_{a+2}` coefficient free of `‖T‖_{a+2}`.  If true, the
landed constituents assemble as-is (after lieCorr0 finishes) and the "house
R-pattern" is vindicated.  Cost: layers 1–3 as in §2, ~10–18 sessions.

**Fork B — R-dependent `Kc` is fatal; constituents must be reworked.**  If the
`Kc·(a+2 window)` cannot avoid landing (even partly) in orientation 1, the STOP
SIGNAL fires (LF-2).  Then deTurckLie, lieCorr0, and the connDiff engine beneath
them must be re-derived to arm0Base's shape: `Kc` R-free and on the `a+1` LOW
window.  This requires an R-free background-difference engine for the
connDiff/deTurck-Lie fields analogous to arm0's `…_backgroundDifference_topSeparated_le`.
**It is unknown whether such an engine exists or is derivable** — if the DeTurck-VF
`≈ g₁⁻¹∂g₁` Neumann expansion genuinely forces the `R^{7k}` grid, there may be NO
R-free route, and R1τ would be in jeopardy at the assembly (a genuine (c)-class
outcome).  Cost: +6–12 sessions if feasible; route-reconsideration if not.

The fork is NOT resolvable by more grepping: it hinges on the analytic behaviour
of the tame time-integration `‖A·B‖_{L²_t} ≤ ‖A‖_{L^∞_t H^{a+1}}‖B‖_{L²_t H^{a+2}}`
against an R-dependent zeroth-order-coefficient `Kc`, and on whether the DeTurck-Lie
fields admit an R-free background-difference decomposition.  This is exactly a
"wrong choice wastes weeks" fork ⟹ consult (§7).

---

## 7. CONSULT-TRIGGER VERDICT: FIRE (prompt drafted, §8)

Classification of the smooth-core tame lemma: **(b) large-but-shaped Lean campaign
(mirrors `1421→1810→1924`) WITH a live (c)-risk gated on the §6 fork.**  The math
route (R1τ) is Pro-ratified and layers 2–3 are settled; but LF-1/LF-2 expose that
the "closed" C₀ constituents are in the wrong currency, and the resolution is a
real fork whose Fork-B branch may be route-dead.  Per CLAUDE.md ("a fork a wrong
choice would waste a week on"), a Pro consult is warranted BEFORE any layer-1
assembly.  Prompt in §8; planner submits via Chrome per protocol.  Push
`codex/short-time-existence-align` to origin first (Case 2 — several files matter).

Do NOT, pending the consult: (a) finish lieCorr0 expecting it to unblock the
assembly (LF-3); (b) start the layer-1 re-derivation of `:34758` (Fork-B would
discard it); (c) build new `deTurckLieArm1`/`arm*Corr` topSeparated producers
(LF-4 — they are ABS, not TW; at most they need an R-free low bound, which is the
same §6 question).

---

## 8. GPT Pro consult prompt (ready; gated on §7)

```text
I am working in a large Lean 4/mathlib Ricci–DeTurck project. Do not write code first.
Diagnose the analytic obstruction and give a small lemma frontier.

Context: I am proving a second-order TAME smooth-core difference estimate for the
symmetric Ricci–DeTurck remainder N (the R1τ route, item 2), target:
  ‖N(T)−N(T')‖_{Hᵃ} ≤ K·((1+max‖T‖_{a+1}‖T'‖_{a+1})·‖T−T'‖_{a+2}
                       +   max‖T‖_{a+2}‖T'‖_{a+2} ·‖T−T'‖_{a+1})
with K R-INDEPENDENT and NO H^{a+2}-ball hypothesis. Forbidden (stop signal):
any ‖T‖_{a+2}·‖T−T'‖_{a+2} term or a pointwise H^{a+2} radius.

N(T)−N(T') decomposes (committed) as
  appCc C₀ ∇⁰(T−T') + appCc C₁ ∇¹(T−T') + appCc C₂ ∇²(T−T'),
C₀ = pathIntegral of Ψ₀ = −2·arm0 + deTurckLieCoeff + lieCorr0 (all (2,2)).
Each coefficient field has a summed jet-L² "top-separated" bound
  ∑_{i≤a}‖∇ⁱ C‖² ≤ Ktop·(top window) + Kc·(1 + low window).

The problem: the constituent fields split into two currencies.
- arm0Base: Ktop on the a+2 window, Kc on the a+1 (low) window, BOTH R-independent.
  (route-compatible.)
- deTurckLieCoeff, lieCorr0 (the DeTurck-Lie flavoured fields): Ktop R-independent
  on the a+2 window, but Kc is R-DEPENDENT (= (∑ grid)·(1+R²), grid ~ R^{7k}, from a
  ballUniform tame-window integrator over the g₁⁻¹=(g₀+P)⁻¹ Neumann expansion) AND Kc
  multiplies the a+2 window (includes ‖∇^{a+2}T‖²).

Since the R-free target removes the ball, R must be instantiated by ≈‖T‖_{a+2}. Then
the deTurckLie Kc·(a+2 window) threatens to put ‖T‖_{a+2} into orientation-1's
coefficient of ‖T−T'‖_{a+2} — the forbidden shape.

Tasks:
1. Classify: is the R-dependent Kc (on the a+2 window) ABSORBABLE by the covariant
   tame lift into orientation 2 (max‖T‖_{a+2}‖T'‖_{a+2}·‖T−T'‖_{a+1}, where an extra
   ‖T‖_{a+2} is a legal data weight), so the landed producers assemble as-is?
   Or does it irreducibly land in orientation 1 (stop signal), forcing an R-free-Kc
   re-derivation of the DeTurck-Lie fields?
2. If a re-derivation is forced: does the DeTurck-Lie coefficient (built from the
   connection difference of g₁ and the vector field ≈ g₁⁻¹∂g₁, so its jets involve a
   Neumann series in P=g₁−g₀) ADMIT an R-free "background-difference" jet bound with
   Kc on the a+1 LOW window (analogous to the linearized-Ricci arm0 background split),
   or does the Neumann expansion genuinely force an R^{7k}-type constant?
3. State the smallest lemma frontier that decides this, in Sobolev-jet terms.
4. Tell me the failure signal that should make me abandon R1τ at the assembly.

GitHub reference to inspect before answering:
- Branch: https://github.com/liao9yuan/differential-geometry/tree/short-time-existence
- Ψ₀/threeArm: .../DeTurckRemainderTameLipschitz.lean (:34758 canonicalTop, :36054 threeArm)
- arm0Base (route-compatible currency): .../ArmBaseCoeffJetL2Summed.lean:139
- deTurckLie (wrong currency): .../DeTurckLieCoeffL2JetBound.lean:799
- R-dependent converter: .../CurvatureCoefficientDifferenceJetTower.lean:13180
- Target chain + stop signal: .../SobolevNonlinearityExistence.lean:1421/1810/1924 + .md

Constraints: preserve public APIs unless mathematically wrong; prefer small helper
lemmas; no broad refactors; no blind automation; give only the next implementation step.
```

---

## 9. Honest size estimate

Denominator: (N) `ricci_flow_unif_existence` is 0% (unstated); item-2 proper is the
main remaining mathematical risk of a 15–25-session (N) discharge.

- **(i) Definition layer** — state layers 1–3 targets + the corrected constituent
  currency targets, flagged sorries: **1–2 sessions**, doable now, but the layer-1
  home (frozen file vs new TensorHilbert leaf) needs a planner call (§10).
- **(ii) Layer-1 assembly green** — GATED on the §6 fork.
  Fork A: ~**3–5 sessions** (re-derive `:34758→:36054` in topSeparated currency over
  the landed producers) + lieCorr0 finish (~2–4, in flight).
  Fork B: **+6–12 sessions** to rework deTurckLie/lieCorr0/connDiff to R-free-Kc — or
  route-reconsideration if the DeTurck-Lie fields admit no R-free background engine.
- **(iii) Smooth-core green** (layers 2–3) — ~**4–8 sessions** mirroring
  `1421→1810→1924` with weights kept explicit.

Total item-2 proper: **Fork A ≈ 10–18 sessions; Fork B ≈ 18–30+ (or route-dead).**
**Main risk = the §6 `Kc`-currency fork** (the consult target).  Secondary = the
sheer size of the frozen-file layer-1 re-derivation.  The "6/7 constituents closed"
figure overstates readiness: only 3 of the Ψ-constituents (arm0Base, arm1Base,
deviation/traceHess) are in usable currency; the 3 DeTurck-Lie-flavoured ones plus
2 Corr fields are not (§4).

---

## 10. Home + verification

This note lives at `ShortTime/THREEARM_RECON.md` (next to `UNIF_EXISTENCE_PLAN.md`):
the recon spans BOTH the threeArm subtree (`TensorHilbert/`,
`DeTurckRemainderTameLipschitz.lean`) and the smooth-core subtree
(`SobolevNonlinearityExistence.*`), so neither companion note is a natural sole
home; the plan is where the campaign is driven, so the planner-facing deliverable
sits beside it as the item-2-proper resume anchor.  Cross-links added at the top.
Per the plan's parallel-recording rule (§ "Parallel lanes"), this session did NOT
edit `UNIF_EXISTENCE_PLAN.md`.

Verification: RECON — no `.lean` written or built (the layer-1 target's home is
ambiguous and its inputs are not in usable currency, so a stub would not elaborate
and "finish-or-don't-start" applies).  All statement shapes are transcribed from
green committed lemmas at the cited lines.  No in-flight lane file touched
(`ConnDiffDeriv2Bound.lean`, `ChristoffelDiffKoszulDeriv2.lean`,
`LieCorr0CoeffL2JetBound.lean`, `DeTurckVectorFieldL2JetBound.lean`,
`UnifCovSumCross.lean`, `Evolution/*`, `AllTimesBounds.lean` all read-only or
untouched); no model-space `InnerProductSpace` introduced.
```

---

## 11. GPT Pro ruling (2026-07-26, chat 6a65adf2) — VERBATIM-DISTILLED

**The §6 fork was a false dichotomy.**  Full answer archived in the ChatGPT
project; the operative content:

1. **Orientation routing is fine — §4/§6's contamination claim was WRONG.**
   The low arms m=0,1 contain no a+2 difference derivative; the committed
   two-arm product bound (SobolevNonlinearityExistence :1222-1235, harmLow
   :1661-1732) routes ALL coefficient jets onto D_{a+1}.  Even a coefficient
   bound ~K(1+H) yields K·D_{a+1} + K·H·D_{a+1} — both legal (orientation 2).
2. **What fails is the CONSTANT**: after removing the ball R ≈ H, so
   Kc(H)·(1+H)·D_{a+1} with Kc an unbounded polynomial ⟹ exceeds the allowed
   fixed-K·H·D_{a+1}.  "Orientation-absorbable, constant-not-absorbable."
3. **Second inventory error (Pro-found): arm0Base's Kc is ALSO R-dependent on
   the live branch** — the :135-138 docstring is stronger than the
   implementation (hR is passed into the per-order producer; the converter's
   constant is (∑Kt)·(1+R²) at :13180-13208).  ⟹ the repair is GENERIC (the
   converter), not DeTurck-Lie-specific.
4. **R^{7k} is a wrapper artifact, not intrinsic.**  The inverse map is a
   smooth tame composition; the fibre-small pointwise bound |g₁⁻¹g₀|² ≤
   (dim E)²(1−δ₀)⁻² (InverseMetricRaisedEndomorphismJetBound :979-990) and the
   differentiated-inverse convolution recursion (:1158-1183) are already
   R-free.  The radius enters ONLY where the ball-uniform wrapper sets
   Λ = C_emb^{a+2}·R before `grid_prod_int_le` (:8556-8598, also :14045-14076).
   Instantiating `grid_prod_int_le` (:8154-8178) with R := ‖∇^k P‖₂ (explicit
   top jet on the RHS) and FIXED Λ₀ = Λ₀(dim E, δ₀) removes it.
5. **Smallest lemma frontier (the GATE):** a radius-free top-separated
   integrator for `boundedFactorGridWindow` in
   CurvatureCoefficientDifferenceJetTower.lean — the sibling of :14417-14444
   with the opposite constant choice: layers 0..i+1 → the LOW window
   (K_low·(1+∑_{j≤i+1}‖∇^j P‖²)), layer i+2 → the explicit top leak
   (K_top·‖∇^{i+2}P‖²); constants depend only on g₀, a, dim E, δ₀.  Plus the
   fibre-small zero-order bridge b_P(x,0) ≤ Λ₀².  Consumer gate after: the
   sibling coefficient theorem with no R binder (wire-in point
   DeTurckVectorFieldL2JetBound :4233-4256).
6. **Failure signal for abandoning R1τ:** only if, AFTER the fixed-Λ₀ fix,
   a superlinear-in-H coefficient bound (‖C₀‖_{H^a} ≁ 1+H) or H·D_{a+2} /
   F(H)·H·D_{a+1} with F→∞ remains.  Diagnostic: fibre-small high-frequency
   family P_N with bounded X_{a+1}, X_{a+2}→∞ — linear growth = route survives.

**Pro's explicit next-step gate:** implement ONLY the radius-free integrator;
do NOT modify DeTurckLieCoeffL2JetBound.lean, do NOT finish lieCorr0, do NOT
start the threeArm assembly until that generic lemma is exact-green.

### §11 addendum — the §4 pointwise-head caveat (for the CONSUMER brick)

The full ruling adds a design constraint the distillation above under-stated:
the R-free coefficient theorem must NOT be forced through the current
pointwise-head API (`∇ⁱC = H_d + low residual` with `|H_d(x)|² ≲ |∇^{i+2}P(x)|²`).
Differentiating `g⁻¹∇P` produces `g⁻¹(∇P)g⁻¹(∇P)g⁻¹`-type terms that are NOT
pointwise-bounded by `|∇²P|` and are not naturally H¹-only residuals; what is
true is the radius-free Gagliardo–Nirenberg `‖(∇P)²‖₂ ≤ C(‖P‖∞)·‖∇²P‖₂ + lower`.
Such capped antidiagonal terms belong in the TOP L² ENVELOPE.  Consequence: the
consumer sibling is a NEW small theorem beside the existing public top-head
APIs (which stay untouched), not a strengthening of them.

---

## 11b. STATUS (2026-07-26): THE GATE IS EXACT-GREEN

The gate lemma and its fibre-small bridge are landed and verified in
`Analysis/Spectral/Tensor/CovGrad/CurvatureCoefficientDifferenceJetTower.lean`
(next to the ballUniform sibling at `:14417`):

- `boundedFactorGridWindow_integral_radiusFree_topSeparated` — THE GATE (deliverable 2).
  Radius-free, top-separated: `∫ window ≤ Klow i·(1 + ∑_{j≤i+1}‖∇ʲP‖²) + Ktop i·‖∇^{i+2}P‖²`,
  `Klow`/`Ktop` R-free, parametrized by an abstract fixed `Λ₀` (statement-level) + a per-`P`
  pointwise `hsup : ∀ x, rfns g₀ 0 2 x (P x) ≤ Λ₀²`.
- `antidiagonalTupleGrid_integral_radiusFree` — the per-order workhorse it is built from.
- `rfns_symmS_zero_le_fibreSmall` — deliverable 1, the public δ₀ fibre-small bridge
  (`Λ₀ := (dim E)·δ₀`), a thin wrapper over the existing private `rfns_symmS_zero_le_of_ball`.

All three: targeted module build GREEN (`9387 jobs`); `#print axioms` = `[propext,
Classical.choice, Quot.sound]`.  The R^{7k} disease was confirmed a wrapper artifact
(Pro point 4/5): the committed `grid_prod_int_le` (`:8154`) is already radius-free-capable;
instantiate with `R := ‖∇ᵏP‖` and fixed `Λ₀`.  The top-layer subgrid argument goes through
with NO resisting term — the antidiagonal constraint `∑ eₘ = i+2` forces the GN interpolation
onto the top jet, so every capped top cell (incl. the `n=1, e=(i+2)` cell) is bounded by
`C·‖∇^{i+2}P‖²` with no intermediate norm.  This is consistent with §11-addendum: the capped
antidiagonal top terms land in the explicit `Ktop i·‖∇^{i+2}P‖²` top L² envelope, exactly the
place the addendum reserves for them.

Consumer note (NEXT brick, `DeTurckVectorFieldL2JetBound :4233`): the bridge only controls the
SYMMETRIC part, so the gate must be consumed at `P := symmS g₀ T` (the geometrically correct
perturbation), not raw `T`; committed raw-`T` grids (`bdOmRecover_gridWindow`) switch to
`symmS T`.  The gate is on a general `P` and does not force this — it is the consumer's choice.
Per-file lessons + exact statements in `CurvatureCoefficientDifferenceJetTower.md`.

## 11c. STATUS (2026-07-26): THE CONSUMER SIBLING IS EXACT-GREEN (brick 2)

Landed in the NEW small leaf
`Analysis/Spectral/Tensor/CovGrad/CurvatureCoeffDiffRadiusFree.lean` (imports the monolith;
a new file because the L²-route uses only public API — the 15.4k-line monolith would
re-elaborate on every focused check, and the alternate pointwise-`hpt` clone route needed the
monolith-private `tsRfns_sub_le` / `exists_backgroundJet_rfns_bound`):

- `ricciArmOrder0BaseCoeff_summed_l2_radiusFree` — THE DELIVERABLE.  R-free sibling of
  `ricciArmOrder0BaseCoeff_perOrder_l2_topSeparated_generic` (the `:14447`/now-`:14808`
  generic whose `Kc` routed through the ball-uniform converter):
  `∑_{i≤a}‖∇ⁱ(RiemannCoeff g₀ g₁ − CurvCoeff g₀ g₁)‖² ≤ Ktop·∑_{j≤a+2}‖∇ʲ(symmS g₀ T)‖²
  + Klow·(1 + ∑_{j≤a+1}‖∇ʲ(symmS g₀ T)‖²)`, `Ktop/Klow` depend only on `g₀,a,dim E,δ₀`; NO R,
  NO ball hyp.  Hyps: `gFibreOpBound g₀ (ccTensorBilinSymm g₀ T) δ`, `δ ≤ δ₀`, `htie`.
- `ricciArmOrder0BaseCoeff_perOrder_l2_radiusFree` — per-order engine (abstract Λ₀ + `hsup`,
  mirroring the gate's design decision 1).

Both `#print axioms` = `[propext, Classical.choice, Quot.sound]`; targeted module build GREEN
(`9388 jobs`, module built clean).  The two binding design constraints are honoured: capped
antidiagonal top terms land in the explicit `Ktop` L² envelope via the gate's top leak (NOT the
pointwise-head API — the existing top-head theorems are untouched), and the grids/RHS jets run
over `symmS g₀ T` (background-difference lemmas instantiated at `T := symmS g₀ T`; `htie`/`hbound`
transfer via local copies of `ccTensorBilinSymm_symmS_app` / `gFibreOpBound_ccTensorBilinSymm_symmS`).
No unreceivable term arose — every leaked top cell is absorbed by the gate's `Ktop·‖∇^{i+2}‖²`.

Scope note for brick 3 (DeTurckLie wire-in): this deliverable is the arm0 constituent
(`RiemannCoeff − CurvCoeff`) of Ψ₀ and the reusable EXEMPLAR.  The deTurckLie / lieCorr0 fields
are DIFFERENT coefficients, so they need their own R-free siblings built by the SAME pattern
(gate + symmS bridge + L² 5-term triangle); they cannot consume this arm0 theorem verbatim.

## 11d. STATUS (2026-07-26): BRICK 3 (DeTurckLie) — STATEMENT LANDED, FORK CLOSED, 1 FRONTIER

New leaf `Analysis/Sobolev/TensorHilbert/DeTurckLieCoeffDiffRadiusFree.lean` (per-file note
`DeTurckLieCoeffDiffRadiusFree.md`).  Focused check GREEN; `#print axioms` on both public theorems
= `[propext, sorryAx, Classical.choice, Quot.sound]` (honest partial — one flagged `sorry`).

- `deTurckLieCoeffField_summed_l2_radiusFree` — **the deliverable, STATEMENT LANDED**, single-tensor
  (`g₁`+`htie`), RHS over `symmS g₀ T`, top window `a+2` / low `a+1` (brick-2 shape), hyps
  `ha_super`+`gFibreOpBound`+`δ≤δ₀`+`htie`, NO `R`, NO ball.  Summed→per-order reduction PROVED
  (verbatim clone of brick 2's summed proof).
- `deTurckLieCoeffField_perOrder_l2_radiusFree` — **the SINGLE frontier (1 `sorry`).**

**The §6 fork is CLOSED (confirmed no wall / no unreceivable term).**  The DeTurckLie field routes
through the private DeTurck-VF tower (`wAlpha`/`wOmega`/`wXi`/`wCA`) into exactly TWO ball-uniform
integrators: `diagonalProductGrid_rfns_integral_ballUniform_succ` (VF :996) and
`antidiagonalTupleGrid_integral_ballUniform_tameWindow` (monolith :8556).  BOTH have the
**byte-identical integrand** to the radius-free workhorse `antidiagonalTupleGrid_integral_radiusFree`
(:14455); R lives ONLY in their constant (`Λ = C_emb·R` before the `^{7k}` grid).  The fixed-`Λ₀` +
`hsup` workhorse is a drop-in for BOTH (the tameWindow's per-index top jets sum into the top/low
envelope).  Index bookkeeping gives EXACTLY `Atop·‖∇^{i+2}P‖² + Alow·(1+∑_{j≤i+1}‖∇ʲP‖²)`, no
cross-contamination.  The frontier's proof is therefore mechanical, NOT a wall — it is a large but
routine bottom→top re-derivation of the private tower with the integrator swap.

**Why not fully closed:** the tower needs the PRIVATE `wAlpha`/`wOmega`/`wXi` defs; it must live in
(or expose from) `DeTurckVectorFieldL2JetBound.lean` (already 4596 lines > limit ⟹ split first).
That is brick 3b (~3-5 sessions, ~1200-1500 lines).  Full producer table + placement plan in the
per-file `.md`.

**Brick 4 (lieCorr0) is mechanizable** from this pattern: same two integrators, same g₁⁻¹/connDiff
machinery, same engine+summed shapes — a clone once brick 3b's shared R-free tower exists.  No new
integrator, no new frontier expected.

### 11d.1 — brick 3b SESSION 1 (2026-07-26): tower BASE landed

New leaf `Analysis/Sobolev/TensorHilbert/DeTurckVFJetRadiusFree.lean` (per-file note
`DeTurckVFJetRadiusFree.md`), imports `DeTurckVFEndoInsertProducers` + `CurvatureCoefficientDifferenceJetTower`;
the three split parts stay read-only.  Two BOTTOM producers landed, targeted-build GREEN, axioms
EXACTLY `[propext, Classical.choice, Quot.sound]` (no `sorryAx`):

- `cometricCastG0_order0sup_jetL2_radiusFree` — flagship; all-public decomps
  (`cometricCastG0_eq_doubleTrace_add_appCcRS` + `rfns_iteratedCovGrad_slotInsertEndoCc_le_endo` +
  the gInvDiff grid + `appCcRS_diagonalProductGrid_rankLeft`).  Order-0 sup `Λ` R-free (fibre bound,
  grid₀=1); L² jets via the workhorse → low window `Flow i·(1+∑_{j≤i}‖∇ʲP‖²)`.
- `sharpFlatEndoCc_lowOrder_jetL2_radiusFree` — the `DiffIns+IdIns` split re-derived in-leaf (4
  helpers; originals private in Producers).  DiffIns L² via workhorse; IdIns `T`-free constant.

**Route reality (correction to "single-integrator swap" framing).**  Only cometricCastG0 and
sharpFlatEndoCc DIRECTLY call the ball-uniform integrator; they are clean workhorse swaps because
their appCcRS/product `S`-factor is `T`-INDEPENDENT (Φ / IdIns), so no `R`-dependent sup is needed.
The COMPOSERS `connDiffSection_lowOrder` / `wOmega_lowOrder` are NOT single-swap: they route
`∫ ∑rfns(∇ⁿS)·∑rfns(∇ˡT)` through the (R-free) two-arm integrator fed the ORDER-0 sups of S/T, and
for connDiffSection `S = raisedKoszul ~ ∇P` whose order-0 sup `ΛK = C·Csob·R` is genuinely
`R`-dependent (needs C² Sobolev of the `a+2` ball).  ⟹ the R-free composers must fold the two-factor
product into a SINGLE antidiagonal grid (`antidiagonalTupleGrid_mul_le` + `single_factor_mul_…`,
present in `AntidiagonalTupleProductGrid.lean`, already used by JetTower/Kernel) then hit the
workhorse.  Viable (infra exists — NOT a wall), but materially more than a clone; SESSION 2+ scope.
NO §6 unreceivable term or `R`-dependent constant at the cometricCastG0/sharpFlatEndoCc level.

**Next (session 2):** `raisedKoszul` R-free `F` (pointwise, keep `‖∇^{n+1}P‖²` explicit; its sup is
the R-dep term, dropped) → then `connDiffSection_lowOrder` R-free via the grid-mul route → `wXi` →
`wOmega`, then the `_L2_topsep` layer and the frontier assembly (final 3b session).  3b tower base
~2/≈8 producers; frontier 0% (unstated in-code beyond its `sorry`).

### 11d.2 — brick 3b SESSION 2 (2026-07-26): two composers landed; raisedKoszul unneeded

Two more producers landed in the same leaf, targeted-build GREEN, axioms EXACTLY `[propext,
Classical.choice, Quot.sound]` (no `sorryAx`):

- `connDiffSection_lowOrder_jetL2_radiusFree` — the grid-mul composer.
- `wXi_lowOrder_jetL2_radiusFree` — connDiffSection triangle + `g_bg` constant.

**PIVOT / correction to §11d.1's session-1 plan.**  `connDiffSection_lowOrder` R-free did NOT need the
appCcRS-rankLeft + two-arm route (nor `raisedKoszul`/`sharpFlatEndoCc` R-free).  It routes through the
PUBLIC R-FREE head engine `rfns_iteratedCovGrad_connDiffSection_topSeparated_le` (JetTower:1823), whose
constants are `g₀/δ₀`-only (`Ktop = 10·S 0`, `Kc` via `exists_..._sharpFlatEndoCc_tgrid`, no `R`) and
whose remainder is `antidiagonalTupleGrid` currency — it folds the raisedKoszul+sharpFlat product
INTERNALLY.  Corner `‖∇^{q+1}P‖²` + remainder `∑_{k<q}rfns(∇^{q-k}P)·grid(k+1)` fold into `grid(q+1)`
via `single_factor_mul_antidiagonalTupleGrid_le`; workhorse integrates → low window at order `i+1`.
⟹ **task item 1 (`raisedKoszul` R-free) is OFF the critical path**, and session-1's
`sharpFlatEndoCc_lowOrder_jetL2_radiusFree` is unconsumed by the connDiff/wXi/wOmega chain (kept
standalone).  Only cometricCastG0 (session 1) remains a live dependency (for wOmega's corner).

**Next (session 3): `wOmega_lowOrder` R-free — the genuine two-arm grid-mul.**  `wOmega =
appCc(cometricCastG0, wXi)`.  Corner (cometricCastG0 order-0 `ΛClow 0`, R-free) × `∇ⁿwXi` is R-free;
the lower two-arm sum in the R-dependent `wOmega_L2_topsep` (TopSep:1001) is integrated with `wXi`'s
order-0 sup `ΛX 0` which is `R`-DEPENDENT.  R-free fix: fold the lower `∑rfns(∇^{i'}cometricCastG0)·
∑rfns(∇ˡwXi)` into single grids via `antidiagonalTupleGrid_mul_le`, then workhorse — NEEDS a POINTWISE
cometricCastG0 grid bound (`rfns_iteratedCovGrad_cometricCastG0_gridWindow_le`, PRIVATE in
`CurvatureArm1KoszulTopSeparation.lean:35` → re-derive) + a pointwise wXi grid bound.  Full session;
`g₀/g_bg/δ₀`-only.  3b tower base 4/≈8-10 producers; frontier 0%.

### 11d.3 — brick 3b SESSION 3 (2026-07-26): wOmega LANDED; low-order tier COMPLETE

Four more declarations landed in the leaf, targeted-build GREEN, axioms EXACTLY `[propext,
Classical.choice, Quot.sound]` (no `sorryAx`): three pointwise `antidiagonalTupleGridWindow`-currency
grid bounds (`rfns_iCG_cometricCastG0_atgw_rf` — re-derives the private cometricCastG0 grid bound R-free;
`rfns_iCG_connDiffSection_atgw_rf` — head engine + `single_factor`; `rfns_iCG_wXi_atgw_rf`) + the
producer `wOmega_lowOrder_jetL2_radiusFree`.  The **entire `_lowOrder` tier is now R-free**
(cometricCastG0/sharpFlatEndoCc/connDiffSection/wXi/wOmega).

**wOmega done as planned (two-arm grid-mul).**  `rfns(∇ⁿwOmega) ≤ appCcGdiag n·∑_{i'}rfns(∇^{i'}cg)·
∑_l rfns(∇ˡwXi)` (public two-arm Leibniz `appCc_iteratedCovGrad_diagonalProductGrid_le`); per term
`atgw(i'+1)·atgw(l+2) ≤ Const·atgw(i'+l+2) ≤ Const·atgw(n+2)` via `antidiagonalTupleGridWindow_mul_le`
+ `_mono` (valid since `i'+l ≤ n`), folding into a single `atgw(n+2)`; the workhorse integrates it →
low window at order `n+1`.  No `R`, no `ΛX 0` sup.  **De-risk vs the §11d.2 plan:** `connLow_rfns`
(`connDiffLoweredCc ↔ connDiffSection` fibre-norm identity) is PUBLIC (`Analysis.Parabolic.TensorSpectral`,
reachable via Tower), so the wXi grid bound needed NO private valence-bridge re-derivation.

**Next (session 4): the `_L2_topsep` layer → `wAlpha` → frontier.**  `connDiff_L2_topsep` /
`wXi_L2_topsep` / `wOmega_L2_topsep` R-free (the head engine + `exists_rfns_connDiff_topsep` shape are
already R-free; swap the ball-uniform integrator for the workhorse, keep the top `‖∇^{i+2}P‖²`
separate).  Then `wAlpha_L2_topsep` (= `‖∇^{i+1}wOmega‖²` top arm + `wAlphaB` two-arm via the same
grid-mul) → lift through `norm_iCG_wEndoInsert_eq_wAlpha` + the DLa/DLb split → discharge the brick-3
frontier `deTurckLieCoeffField_perOrder_l2_radiusFree`.  Low-order tier COMPLETE (~5/≈8-10 producers);
frontier still 0% in-code (its `sorry` untouched).

### 11d.4 — brick 3b SESSION 4 (2026-07-26): the whole `_L2_topsep` layer + `wAlpha` (tower top) landed

Ten more declarations landed in the leaf, targeted-build GREEN (9433 jobs), `#print axioms` on all
publics/producer EXACTLY `[propext, Classical.choice, Quot.sound]` (no `sorryAx`).  The **entire
`_L2_topsep` tower is now R-free through the top**: four public siblings `connDiff_L2_topsep_rf` /
`wXi_L2_topsep_rf` / `wOmega_L2_topsep_rf` / **`wAlpha_L2_topsep_rf`** (THE TOWER TOP), plus six private
engines (`exists_rfns_connDiff_topsep_rf`, `cometricCastG0_wXi_twoArm_fold_rf`,
`exists_rfns_wOmega_topsep_rf`, `rfns_iCG_wOmega_atgw_rf`, `wCA_wOmega_twoArm_fold_rf`,
`wAlphaB_L2_perOrder_rf`).  Route as planned: clone each R-dependent `_L2_topsep` proof with the
ball-uniform tame-window integrator swapped for the radius-free workhorse, keeping the top data term
separate.  Shapes: `connDiff`/`wXi`/`wOmega` (n ≤ a+1) → `Ktop·‖∇^{n+1}P‖² + Flow n·(1+∑_{j<n+2})`;
`wAlpha` (i ≤ a) → `Ktop·‖∇^{i+2}P‖² + Flow i·(1+∑_{j<i+3})`.

**Heartbeat wall (the one real obstacle, resolved).**  The monolithic `wOmega_L2_topsep_rf` (corner-peel
pointwise + two-arm fold + workhorse in ONE theorem) blew `maxHeartbeats` — timeout at `whnf`, LINEAR
in the budget (1.6M→3.2M doubled the wall-clock without finishing ⟹ cumulative, not one pathological
defeq).  Fix = split the pointwise corner-peel envelope into a private lemma
(`exists_rfns_wOmega_topsep_rf`) so the corner-peel and the workhorse integration get SEPARATE budgets;
both then fit 1.6M (full file 51s).  (Replacing the giant `rw [show … from by …; rfl]` with the cheaper
`rw [SmoothCcTensor.toSection_add, ContMDiffSection.coe_add, Pi.add_apply]` helped but was NOT
sufficient alone.)  Other lessons in the leaf `.md`: docstring-after-`set_option`; `wOmega`'s pointwise
atgw bound needs NO `hsup` (take it from the full Leibniz fold, not the sup-bundled corner engine);
wAlphaB's fold lands at `atgw(i+3)` (both arms `+2` offset).

**What session 5 (the frontier discharge) consumes.**  `wAlpha_L2_topsep_rf` — top `Ktop·‖∇^{i+2}P‖²`,
low `Flow i·(1+∑_{j<i+3})` — lifted through `norm_iCG_wEndoInsert_eq_wAlpha`
(`‖∇ⁱwEndoInsert‖=‖∇ⁱwAlpha‖`, private in Producers) + the DLa/DLb split into
`deTurckLieCoeffField_perOrder_l2_radiusFree` (`DeTurckLieCoeffDiffRadiusFree.lean:89`, ONE `sorry`,
UNTOUCHED per task).  The frontier's low window is range `i+2` (top `i+2` excluded); my `wAlpha` low
window is range `i+3` (includes `i+2`), so session 5's remaining bookkeeping is a `Finset.sum_range_succ`
splitting `Flow i·‖∇^{i+2}P‖²` into `Atop`.  Tower COMPLETE; frontier still 0% in-code.
