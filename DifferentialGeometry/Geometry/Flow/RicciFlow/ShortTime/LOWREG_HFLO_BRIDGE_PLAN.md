# `hfLo` bridge — implementation plan

Recon 2026-07-30, checkout `E:\testdifferential-geometry-ste-align`, branch
`codex/short-time-existence-align`.  Read-only recon; no Lean file edited, no
file claimed.  Anchor: `UNIF_EXISTENCE_PLAN2.md` №72–75; this discharges the
"REMAINING (2) hfLo" item of №75.

**Headline.**  The bridge needs no new Nemytskii-continuity theorem and no
spectral-symmetry input.  It reduces to one *state-level* identity
`lowRegN w = lowBaseN w` on the `H3` state ball, proved by closed equalizer +
density of the smooth core.  Closedness needs continuity of the two completed
coefficient maps.  `Continuous (lowA2Lo …)` is **already proved**
(`lowA2_small`).  `Continuous (lowA1Lo …)` is the **single** open input.
Everything else in the chain exists.

---

## 1. The exact statement

### 1a. What `lowreg_lift_two` consumes (verbatim)

`ShortTime/LowRegLiftTwo.lean:169`, hypothesis at `:206–212`:

```lean
    (fLo : timeL2 (tensorHs (I := I) (M := M) g 0 2 aLo) T)
    (hfLo : fLo =
      nonautL2Map (I := I) (M := M) hT hT1
          (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2)
          A2Lo hA2Lo C2Lo hC2Lo A1Lo hA1Lo fLo + f0Lo)
```

An equality of **`Lp` elements**, not an a.e. statement.  At `aLo := (1:ℝ)`,
`aHi := (2:ℝ)`: `A2Lo : ℝ → tensorHs g 0 2 3 →L[ℝ] tensorHs g 0 2 1`,
`A1Lo : ℝ → tensorHs g 0 2 2 →L[ℝ] tensorHs g 0 2 1`,
`f0Lo fLo : timeL2 (tensorHs g 0 2 (1:ℝ)) T`.

`nonautL2Map` (`TensorMaximalRegularity/NonautonomousL2.lean:194`) is
`fun f => timeOp A2 … (maxRegDuhamelSolField a hT hT1 0 f) + a1L2Term … A1 … f`,
so pointwise a.e. `(nonautL2Map … f) t = A2 t (maxRegDuhamelSolField 1 hT hT1 0 f t)
+ A1 t ((zeroDuhamelCross hT hT1 _ f).repr t)`.

### 1b. What `lowreg_partial_sol` exports (verbatim)

`ShortTime/LowRegDenseSolve.lean:298`, forcing clause:

```lean
  gforce =ᵐ[timeMeasure T]
    (fun t => Nfun (aeSetLift (zero_mem_lowerState g₀ 1 hR.le) field t))
```

`Nfun := lowRegN g₀ g_bg hR hδ hreal : lowerState g₀ 1 R → tensorHs g₀ 0 2 ((1:ℕ):ℝ)`,
`field := maxRegDuhamelSolField ((1:ℕ):ℝ) hT hT1 0 gforce`.  The same theorem
also exports `Continuous Nfun`, `Continuous (coreN …)`,
`∀ᵐ t, field t ∈ lowerState g₀ 1 R`, `‖gforce‖ ≤ R/4`.

### 1c. Proposed bridge theorems

Home: **new** `ShortTime/LowRegLiftAffine.lean` — it must see
`DeTurckRemainderLowBaseFixedPoint` *and* `LowRegDenseSolve` /
`LowRegSmoothBridge`; `LowRegLiftNTerm` already sits at that junction and is
the sibling to import.

```lean
/-- (★) state level: the low-regularity Nemytskii IS the frozen affine action. -/
theorem lowreg_N_affine
    (hDim : Module.finrank ℝ E = 3)
    (g₀ : SmoothRiemannianMetric I M) {R δ ρ : ℝ}
    (hR : 0 < R) (hρ : 0 < ρ) (hRρ : R ≤ ρ)
    (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3) (hδ : δ < 1)
    (hreal  : ∀ S : SmoothCcTensor g₀ 0 2,
      ‖smoothCcToTensorHs g₀ (((1:ℕ):ℝ) + 1) S‖ ≤ R →
        gFibreOpBound g₀ (ccTensorBilinSymm g₀ S) δ)
    (hreal' : ∀ S : SmoothCcTensor g₀ 0 2,
      ‖ccTensorToHs g₀ 2 (2:ℝ) S‖ ≤ ρ →
        gFibreOpBound g₀ (ccTensorBilinSymm g₀ S) δ)
    (hcore : Continuous (coreN g₀ g₀ hδ hreal))
    (hA2 : Continuous (lowA2Lo g₀ hρ.le hδ0 hδ_le hreal'))   -- HAVE, §2b
    (hA1 : Continuous (lowA1Lo g₀ hρ.le hδ0 hδ_le hreal'))   -- OPEN, §4.1
    (w : lowerState g₀ 1 R) :
    tensorHsCongr g₀ 0 2 (show ((1:ℕ):ℝ) = (1:ℝ) by norm_num)
        (lowRegN g₀ g₀ hR hδ hreal w) =
      lowBaseN g₀ hρ.le hδ0 hδ_le hreal'
        (tensorHsCongr g₀ 0 2 (show ((1:ℕ):ℝ) + 2 = (3:ℝ) by norm_num) w.1)
```

and its time-level consequence `lowreg_hfLo`, taking the same data plus
`hT : 0 < T`, `hT1 : T ≤ 1`, `gforce`, `hforce` (the export of §1b at
`g_bg := g₀`) and `hball : ∀ᵐ t, field t ∈ lowerState g₀ 1 R`, concluding

```lean
    congrOp … gforce =
      nonautL2Map hT hT1 (tensorResolventL2_isCompactOperator g₀ 0 2)
          (lowAffA2 …) hA2meas C2 hC2 (lowAffA1 …) hA1memLp (congrOp … gforce)
        + liftForceLo g₀ g₀ T
```

with the two families **defined to mirror `lowBaseA` summand for summand**
(`DeTurckRemainderLowBaseFixedPoint.lean:110`):

```lean
lowAffA2 t := (lowA2Lo g₀ … (incl32 (vt t))).comp (radialCLM g₀ (0 ≤ 3) ρ (incl32 (vt t)))
lowAffA1 t := (lowA1Lo g₀ … (vt t)).comp        (radialCLM g₀ (0 ≤ 2) ρ (incl32 (vt t)))
vt t       := tensorHsCongr g₀ 0 2 (((1:ℕ):ℝ)+2 = 3) (field t)
```

Keeping `radialCLM` **inside** the families is deliberate: then
`lowAffA2 t (field t) + lowAffA1 t (incl32 (field t)) = lowBaseA (vt t) (vt t)`
holds *definitionally*, so **`hfLo` needs no radial-inactivity and no spectral
symmetry**.  Radial inactivity (`lowRadial_eq_self_sol`,
`ShortTime/LowRegRealizeTwo.lean:357`) is only needed downstream, to say the
frozen coefficients are the genuine ones.

**Hard constraint: `g_bg := g₀`.**  `lowBaseN`, `lowBaseForce`, `lowCoreData`
are all `lowBaseData g g …` (single metric), and `liftForceLo_lowBase`
(`LowRegLiftNTerm.lean:274`) is stated only at `g_bg = g`.  Specialize
`lowreg_partial_sol` to `g_bg := g₀`; do not attempt a general background.

---

## 2. Hypothesis-by-hypothesis production map

### 2a. Continuity of `v ↦ lowRegN v` on the ball — **HAVE, unconditional**

`lowreg_partial_sol` (`LowRegDenseSolve.lean:298`) exports `Continuous Nfun`
in its own conclusion, beside `Continuous (coreN …)`.  So: yes, **total**
continuity on the state-ball subtype exists, not merely an a.e. composition
with the field.  Engine: `lowRegN_outer` / `dense_cont_on_balls`
(`LowRegDenseSolve.lean:~230–295`).  Nothing to build.

### 2b. Continuity of `v ↦ (lowA2Lo v) v + (lowA1Lo v) v` — **the design answer**

**Ruling: the equalizer-along-the-field route does NOT avoid coefficient
continuity, and must not be attempted as a way around it.**

`hfLo` is an `Lp`-element equality; `Lp.ext` turns it into an a.e.-in-`t`
identity — that is already the best case.  But that identity is
`lowRegN (field t) = lowBaseForce + lowBaseA (vt t) (vt t)`, i.e. the *state*
identity (★) read along the field.  The essential range of `field` is an
arbitrary subset of the `H3` ball — the field is only `H3`, never smooth — so
an a.e.-`t` statement can only come from a statement true at *every* state of
the ball.  No measurable-selection or dense-in-time trick applies: the smooth
core is dense in the ball but bears no relation to a null set in `t`.  Hence
(★) for all `w`, hence closedness of `{w | lowRegN w = lowBaseN w}` plus
`smoothCore_dense`, hence continuity of both sides.

The required continuity is nevertheless *far weaker* than the `hLoPair` of
№74, and is mostly banked:

| fact | status | producer |
|---|---|---|
| `Continuous (lowA2Lo g …)` | **HAVE** (hDim = 3, shrunken ρ) | `lowA2_small`, `TensorMaximalRegularity/LowRegOperatorTime.lean:668` (2nd conjunct); engine `radialA2_lip`, `DeTurck/DeTurckRemainderLowBaseTimeA2.lean:370` |
| `Continuous (lowA1Lo g …)` | **MISSING** — §4.1 | `cont_extend_pair`, `Analysis/DenseExtension.lean:156` + a `D₄`-free ball-local `a1Lo` pair estimate |
| `Continuous (lowRadialH3 g ρ)` | HAVE | `DeTurck/DeTurckRemainderLowBaseTime.lean:885` |
| `Continuous (lowRadialHs g ρ)` | HAVE | same file `:1131` |
| operator application jointly continuous | HAVE (Mathlib) | `isBoundedBilinearMap_apply.continuous` |
| `incl32` continuous | HAVE | it is a `→L[ℝ]` |

`lowBaseN` is *defined* by exactly that expression
(`DeTurckRemainderLowBaseFixedPoint.lean:90–106`), so `Continuous lowBaseN` is
one `Continuous.add`/`.comp` assembly once `hA1` lands; `lowBaseN_frozen`
(`:131`) is a `module` repackaging into `lowBaseA` and is the lemma that
converts the `lowRadial*` spelling into the `radialCLM` spelling (via
`radialCLM_h3`, `radialCLM_h2`).

### 2c. The smooth-core value of (★)

For `x : smoothCore g₀ R`, `S := coreRep g₀ x`:

1. `lowRegN_on_smooth` (`ShortTime/LowRegSmoothBridge.lean:82`):
   `lowRegN … = deTurckSmoothN g₀ g₀ 1 (symmS g₀ S) …`, and `deTurckSmoothN`
   is the spectral embedding of `deTurckSmoothRemainder`
   (`DeTurck/SobolevNonlinearityExistence.lean:109`, `_coeff` at `:125`);
3. `lowCore_split` (`DeTurck/DeTurckRemainderLowBaseTime.lean:1723`):
   `deTurckSmoothRemainder g g S' − deTurckSmoothRemainder g g 0 =
   A.a2 S' + A.a1 S'`, `S' = lowRadial g ρ S`, `A = lowCoreData g … S`.
   **Zero-based and total** — no separate principal term (§4.2);
4. `lowRadial g ρ S = symmS g₀ S` under the ball bound — **MISSING**, §4.3;
   ball input `coreSymm_h2` (`ShortTime/LowRegDenseN.lean:~122`) + `hRρ`;
5. core realization of the coefficients: `a2Lo_core`
   (`DeTurck/DeTurckRemainderLowBaseA2.lean:211`) and `a1Lo_core_any`
   (`DeTurck/DeTurckRemainderLowBasePair.lean:494`, currently `private` — §4.4):
   `A.a2Lo (ccTensorToHs g 2 3 W) = ccTensorToHs g 2 1 (A.a2 W)` etc.;
6. dense-extension core values: `lowA2Lo (ccToHsLin g 2 2 T) = (lowCoreData … T).a2Lo`
   (`radialA2_lip` 4th conjunct); for `a1Lo` use `extend_pair_apply`
   (`Analysis/DenseExtension.lean:167`) — **not** `lowA1_lip`, whose `hHiPair`
   is false (§4.1);
7. radial core values `lowRadialH3_core` (`:895`), `lowRadialHs_core` (`:1149`),
   and `lowBaseForce_core` (`DeTurckRemainderLowBaseFixedPoint.lean:75`) for the
   zero-state term.

All present except items 4 and 5-privacy.

### 2d. Measurability and bounds of the two families

* measurability: `lowBaseA_aemeas` (`DeTurckRemainderLowBaseFixedPoint.lean:204`)
  is the engine for the sum; its proof (`radialCLM_aemeas`,
  `DeTurckRemainderLowBaseTime.lean:407`, composed with `hA2`/`hA1` continuity
  and `Lp.aestronglyMeasurable`) applies verbatim to each summand.
* `‖lowAffA2 t‖ ≤ ‖lowA2Lo (incl32 (vt t))‖`, likewise `A1`, by
  `radialCLM_norm ≤ 1` (`:395`); pattern inside `lowBaseA_le` (`:151`).
  Uniform `C2Lo`: `lowA2_small` 4th conjunct gives a *global*
  `∀ v, ‖lowA2Lo … v‖ ≤ C * ρ`, so `hC2Lo` is `Eventually.of_forall`.
* `hA1Lo : MemLp A1Lo 2`: template `lowRegA1Lo_memLp`
  (`LowRegOperatorTime.lean:502`); see §4.5 for the envelope shape.

---

## 3. Measure-theoretic route

`Lp.ext`, then `filter_upwards`.  Idioms already in the tree, in proof order:

1. `Lp.ext` / `Lp.coeFn_add` → `=ᵐ[timeMeasure T]` of coeFns;
2. `timeOp_apply_ae` (`TimeSobolev/TimeOperator.lean:138`) for the `A2` arm;
3. `timeOpL2_apply_ae` (`TimeSobolev/TimeOperatorL2.lean:60`) for the `A1` arm,
   through `a1L2Term` (`NonautonomousL2.lean:73`).  The path fed to it is
   `(zeroDuhamelCross … f).repr`, **not** the `H3` Duhamel field: bridge
   `repr t ↦ tensorHsInclusion (2 ≤ 3) (field t)` with
   `duhReprL2_ae` / `duhRepr_field_ae`, the pair used by `lowRegState_ae`
   (`ShortTime/LowRegPrincipalTime.lean:76`).  Reuse, do not reprove;
4. `aeSetLift_coe_ae` (`TensorMaximalRegularity/LocalNemytskii.lean:~40`) to
   drop the subtype lift in `hforce`;
5. `timeConstL2_coeFn` (`ShortTime/LowRegLiftNTerm.lean:93`) for `f0Lo t`;
6. exponent transport `((1:ℕ):ℝ) → (1:ℝ)` and `((1:ℕ):ℝ)+2 → (3:ℝ)`:
   `tensorHsCongrL` / `congrOp` / `congrOp_memLp`
   (`ShortTime/LowRegRealizeTwo.lean:~200–230`), `staticForce_congr`
   (`LowRegLiftNTerm.lean:158`), `orderOneH2Iso`
   (`LowRegPrincipalTime.lean:47`).  Do this transport **once**, on `gforce`,
   at the top — do not thread `((1:ℕ):ℝ)` through the coefficient families.

**`f0Lo` = `N 0`, confirmed, at `g_bg = g₀`.**  `liftForceLo g₀ g₀ T =
timeConstL2 T (lowBaseForce g₀)` is `liftForceLo_lowBase`
(`LowRegLiftNTerm.lean:274`), and `lowBaseForce` *is* the constant term of
`lowBaseN` by definition.  On the other side `nZero_h1_eq`
(`LowRegLiftNTerm.lean:206`) gives
`tensorHsCongr … (lowRegN … 0) = staticForce g₀ g_bg 1`.  The two match after
`liftForceLo_lowBase`; **no gap**.  At `g_bg ≠ g₀` there *is* a gap —
`lowBaseForce` is only the `g_bg = g` field.

---

## 4. Risk register

### 4.1 `Continuous (lowA1Lo …)` — **missing API, the only real blocker**

*Classification: missing API lemma (analytic estimate).  Not a wall.*

`Analysis/DenseExtension.lean` (landed, untracked) supplies `cont_extend_pair`
(`:156`).  With `j := ccToHsLin g 2 (3:ℝ)`, `F := lowA1LoCore` it needs

```
∀ R, ∃ K, ∀ T U, ‖ccToHsLin g 2 3 T‖ ≤ R → ‖ccToHsLin g 2 3 U‖ ≤ R →
  ‖(lowCoreData g … T).a1Lo − (lowCoreData g … U).a1Lo‖ ≤ K * ‖ccToHsLin g 2 3 (T − U)‖.
```

The banked `a1_pair_lip` (`DeTurck/DeTurckRemainderLowBaseA1Pair.lean:255`)
gives `K R · (1 + A + A₄) · (D₄ + D₃ + D₂ + N)`.  `D₄` is
`sqrt (lowJetSq g 4 (T−U))`, an **`H⁴`** norm of the *difference*
(`lowJetSq g m S = Σ_{q≤m} ‖iteratedCovGrad g 0 2 q S‖²`,
`DeTurckRemainderLowBaseAction.lean:2871`), which `‖ccToHsLin g 2 3 (T−U)‖`
does not control.  So **`a1_pair_lip` as stated does not feed
`cont_extend_pair`**.  The `A₄` on the *state* side is harmless (absorb into
`K R` on the `R`-ball); the `D₄` on the *difference* side is fatal.

Smallest unblock: №74's ruled follow-up (1), restricted to the `a1Lo` half —
`‖AT.a1Lo − AU.a1Lo‖ ≤ K_R · (D₃ + D₂ + N)` on `{lowJetSq g 3 · ≤ R²}`.  №74's
argument is that `a1Lo : H² → H¹` reads its coefficient at the `H¹` jet, so
`D₄` is a telescope artefact of `c0Diff_h2_tame`/`c1Diff_tame`, not intrinsic.
Commission it in `DeTurckRemainderLowBaseA1Pair.lean` next to `c1_pair_lip`;
per №74 it is blocked on the class-2 agent releasing `H2Pair`/`H2VB`.

Also needed: a jet↔spectral comparison converting that estimate's currency
into `cont_extend_pair`'s.  Grep first — the `a2` side already crossed this
inside `radialA2_lip`/`a2_pair_lip`; reuse, do not rebuild.

**Do not** route through `lowA1_lip` (`LowRegOperatorTime.lean:281`): its
`hHiPair` is *false* (№74 counterexample), so everything drawn from it is
vacuous.

### 4.2 Which `A2Lo` family? — **design decision, settle first**

*Classification: design choice with a mathematical fact behind it.*

`lowRegA2TotalLo` (`LowRegOperatorTime.lean:927`) is
`lowRegA2TimeLo (principal) + lowA2Lo (state)`.  But `lowCore_split` is
zero-based and *total*, and `lowBaseData.C2`
(`DeTurckRemainderLowBaseAction.lean:3359`) is a path-integrated coefficient
`rhsRefoldTopInt + selfTopInt − deTurckPhiMetTotal`, i.e. it already contains
the full second-order difference including the principal correction.  If so,
feeding `lowRegA2TotalLo` into `hfLo` would **double-count the principal arm**
and the identity would be false.

This plan therefore uses the `lowBaseA`-derived family (§1c), for which the
identity is definitional.  Before writing code, confirm the reading by
comparing `lowRegPrincipalLo` (`DeTurck/PrincipalLowRegPair.lean:654`) with
`lowBaseData.C2`.  Outcomes: (a) principal ⊆ `C2` (expected) — use `lowAffA2`;
`lowRegA2TotalLo_data` is then *not* the producer for this slot, only its
`lowA2Lo` half is reusable, and §75's remaining item (1) should be re-scoped.
(b) principal ⊄ `C2` — then `lowCore_split` is not the whole story, the bridge
statement needs the principal arm on both sides; stop and report.

### 4.3–4.4 Two trivial missing pieces

* **`lowRadial_eq_self` (smooth side), MISSING.**
  `lowRadial g ρ T = min 1 (ρ / ‖ccTensorToHs g 2 2 (symmS g T)‖) • symmS g T`
  (`DeTurckRemainderLowBaseTime.lean:457`).  Need
  `‖ccTensorToHs g 2 2 (symmS g T)‖ ≤ ρ → lowRadial g ρ T = symmS g T`:
  one `min_eq_left` + `one_smul`.  Place next to `lowRadial_norm` (`:492`).
  The `H`-level siblings exist (`lowRadialHs_eq_self` / `lowRadialH3_eq_self`,
  `ShortTime/LowRegLiftTwo.lean:63`/`:78`).
* **`a1Lo_core_any` is `private`** (`DeTurckRemainderLowBasePair.lean:494`)
  while its sibling `a2Lo_core` is public.  Drop `private`, or add a public
  `a1Lo_core` alias *in that file* (canonical home, not the consumer).

### 4.5 `hA1Lo : MemLp` needs an envelope, not only continuity

*Classification: statement shape, avoid a false target.*  `lowRegA1Lo_memLp`
(`LowRegOperatorTime.lean:502`) asks for
`hlin : ∀ v, ‖lowA1Lo … v‖ ≤ Φ (1 + ‖v‖)`.  Per №74's closing note the
envelope need only be **monotone**, not affine, once the state ball is
bounded — restate `hlin` as `‖lowA1Lo … v‖ ≤ Φ` for `v` in the `R`-ball and
use `MemLp.of_le_mul` against the constant.  Do **not** attempt the affine
version: the degree-six one-state envelope of `remainder_low_pair` contradicts
it.  `norm_extend_le` (`Analysis/DenseExtension.lean:200`) transports whatever
core envelope exists.

### 4.6–4.7 Bookkeeping (coercion class, cheap but check early)

* **δ-range mismatch.**  `lowRegN` carries `hδ : δ < 1`; `lowCoreData` /
  `lowA2Lo` / `lowA1Lo` carry `0 ≤ δ ≤ 1/3`.  `lowreg_partial_sol` uses
  `δ := deTurckArmContractionThreshold'' (finrank ℝ E)`, known `< 1`; whether
  it is `≤ 1/3` is **unchecked**.  State the bridge with `δ` a parameter under
  `0 ≤ δ ≤ 1/3` and let the caller shrink `θ` (the `realize_at_thr` + `min`
  pattern, `LowRegDenseSolve.lean:~340`).  If `θ ≤ 1/3` is false this is a
  producer-side change, not a bridge change — check it in the first hour.
* **Radius alignment.**  `lowRegN` uses `R` at
  `smoothCcToTensorHs g₀ (((1:ℕ):ℝ)+1)`; `lowCoreData` uses `ρ` at
  `ccTensorToHs g₀ 2 (2:ℝ)`.  Same map under the `htwo`/`ext` conversion in
  `coreN_outer` (`LowRegDenseSolve.lean:~200`).  Carry `hRρ : R ≤ ρ`; `lowA2_small`
  shrinks `ρ` again, so the final radius is a `min` of three.

### 4.8 Checked and cleared (not risks)

Spectral symmetry of the field — **not needed** for `hfLo` (§1c).
`lowRadialH3`/`lowRadialHs` continuity — exist (`:885`, `:1131`).
`Continuous (lowRegN …)` — exported by `lowreg_partial_sol`.
`f0Lo = N 0` — `liftForceLo_lowBase` + `nZero_h1_eq` at `g_bg = g₀`.
`Continuous (lowA2Lo …)` — `lowA2_small`, unconditional at `hDim = 3`.

---

## 5. Builder brief (self-contained)

> In `E:\testdifferential-geometry-ste-align` (branch
> `codex/short-time-existence-align`), create
> `DifferentialGeometry/Geometry/Flow/RicciFlow/ShortTime/LowRegLiftAffine.lean`
> and prove the `hfLo` slot of `lowreg_lift_two`
> (`ShortTime/LowRegLiftTwo.lean:169`, hypothesis at `:206`) at `aLo := (1:ℝ)`,
> `aHi := (2:ℝ)`, `g_bg := g₀`.  Two theorems: a state-level identity
> `lowreg_N_affine : lowRegN g₀ g₀ … w = lowBaseN g₀ … (congr w.1)` for every
> `w : lowerState g₀ 1 R`, and its time-level consequence `lowreg_hfLo`.
> Define the two coefficient families to mirror `lowBaseA`
> (`DeTurck/DeTurckRemainderLowBaseFixedPoint.lean:110`) summand for summand —
> `(lowA2Lo (incl32 vt)).comp (radialCLM (0≤3) ρ (incl32 vt))` and
> `(lowA1Lo vt).comp (radialCLM (0≤2) ρ (incl32 vt))`, `vt` the exponent-
> transported Duhamel field — so that
> `A2Lo t (field t) + A1Lo t (incl32 (field t)) = lowBaseA (vt t) (vt t)` is
> definitional and no spectral-symmetry or radial-inactivity input is needed.
> Prove the state identity by density: the equalizer is closed (continuity of
> `lowRegN` is exported by `lowreg_partial_sol`; continuity of `lowBaseN`
> assembles from `lowA2_small` (`TensorMaximalRegularity/LowRegOperatorTime.lean:668`,
> 2nd conjunct), `lowRadialH3_cont` / `lowRadialHs_cont`
> (`DeTurck/DeTurckRemainderLowBaseTime.lean:885`/`:1131`), and the one open
> input `Continuous (lowA1Lo …)` which you take as an explicit **hypothesis**
> of both theorems), and it contains `smoothCore` by `lowRegN_on_smooth`
> (`ShortTime/LowRegSmoothBridge.lean:82`) → `lowCore_split`
> (`DeTurckRemainderLowBaseTime.lean:1723`) → `a2Lo_core`
> (`DeTurck/DeTurckRemainderLowBaseA2.lean:211`) / `a1Lo_core_any`
> (`DeTurck/DeTurckRemainderLowBasePair.lean:494`, de-privatize) →
> `extend_pair_apply` (`Analysis/DenseExtension.lean:167`) →
> `lowRadialH3_core` / `lowRadialHs_core` (`:895`/`:1149`) →
> `lowBaseForce_core`.  Add the missing one-line `lowRadial_eq_self` next to
> `lowRadial_norm` (`DeTurckRemainderLowBaseTime.lean:492`).  For the time step
> use `Lp.ext`, `timeOp_apply_ae` (`TimeSobolev/TimeOperator.lean:138`),
> `timeOpL2_apply_ae` (`TimeSobolev/TimeOperatorL2.lean:60`),
> `duhReprL2_ae` / `duhRepr_field_ae` (the pair used by `lowRegState_ae`,
> `ShortTime/LowRegPrincipalTime.lean:76`) to relate the `a1L2Term`
> representative to the `H3` field, `aeSetLift_coe_ae`
> (`TensorMaximalRegularity/LocalNemytskii.lean`), and `liftForceLo_lowBase`
> (`ShortTime/LowRegLiftNTerm.lean:274`) for `f0Lo`.  Do the
> `((1:ℕ):ℝ) → (1:ℝ)` exponent transport once, on `gforce`, via `congrOp`.
> **Before writing code**, confirm §4.2: compare `lowRegPrincipalLo`
> (`DeTurck/PrincipalLowRegPair.lean:654`) against `lowBaseData.C2`
> (`DeTurckRemainderLowBaseAction.lean:3359`) and verify the principal
> correction is already inside `C2`; if it is not, stop and report.  **Never**
> route through `lowA1_lip` (`LowRegOperatorTime.lean:281`) — its `hHiPair` is
> false and everything downstream of it is vacuous.  Verify with a focused
> `scripts/lake-locked.ps1 check … -NoLakeLock`, then a targeted
> `build -NoLakeLock +…` for the new module; record findings in
> `LowRegLiftAffine.md`.

---

## Status

* Written 2026-07-30 by the recon pass.  No Lean edited, no file claimed.
* Buildable **now** up to the `Continuous (lowA1Lo …)` hypothesis: the whole
  bridge can land today with that continuity as an explicit, honestly named
  hypothesis, discharged the moment §4.1 lands.  Recommended sequencing — do
  not wait for the dense-extension/pair-estimate lane.
* Honest denominators: this bridge is 1 of the 3 remaining inputs of
  `lowreg_lift_two`'s application (№75 items 1–3), itself one rung of the
  low-regularity bootstrap.  The `(N)` theorem remains **0 %** (unstated).
