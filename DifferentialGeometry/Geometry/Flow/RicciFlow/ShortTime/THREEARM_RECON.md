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
