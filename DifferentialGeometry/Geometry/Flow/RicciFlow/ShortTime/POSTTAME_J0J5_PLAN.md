# Post-tame dispatch plan: J0 (`lowreg_loMass` third widening) and J5 (`N`-indexed `L¹` engine)

Read-only recon, 2026-08-04, checkout `E:\testdifferential-geometry-ste-align`
(branch `codex/short-time-existence-align`, HEAD `7f54201cf`).  No Lean was run;
no `.lean` file was touched.  Governing plan: `ShortTime/CODEX_LOMASS_AUDIT.md`
(§2 J-map, §4 statement audit, §5 brick plan).  Ledger: `ShortTime/UNIF_EXISTENCE_PLAN5.md`.

Every claim below was grep-verified against today's tree.  Where the audit's
line numbers had drifted, the re-anchored line is given.

---

## A. J0 — the third widening of `lowreg_loMass`

### A.1 Engine identity (over-count check first)

`partial_sol_tame` (`TameForcingFixedPoint.lean:332`) **is** the engine, not a
look-alike sibling: `lowreg_partial_sol_of_bounds`
(`ShortTime/UnifClassBounds.lean:263`) calls it directly at
`UnifClassBounds.lean:368`, and `IsLowSolve` (`UnifClassBounds.lean:407`) is
built from exactly that theorem's hypotheses+conclusions by `isLowSolve_of_sol`
(`UnifClassBounds.lean:458`).  The projected sibling `proj_partial_sol_tame`
(`EigenProjTameSol.lean:118`) is literally `partial_sol_tame` applied to
`projNfun` (`EigenProjTameSol.lean:158`), with an **`N`-free** horizon formula.
Audit §4.2 PASSES verbatim.

### A.2 Field-by-field: `IsLowSolve` vs `partial_sol_tame`'s actual slots

| `partial_sol_tame` slot | `IsLowSolve` field | status |
|---|---|---|
| `hR : 0 < R` | derived from `hCtop hB1 hρ hP` via `lowregStateRad_pos` | present |
| `Nfun` | `lowregNfun g₀ g_bg hδ hCtop hB1 hρ hP hreal` (`UnifClassBounds.lean:234`) | present |
| `hcont` | `Continuous (lowregNfun …)` | present |
| `A B C : ℝ≥0` | reconstructed from `Ctop, B0, B1` inside the bridge (`:329-331`) | derived |
| `hD : 0 ≤ D` | `(norm_nonneg _).trans hzero` | derived |
| `hzero` | present | present |
| `hsmallA`/`hsmallC` | `lowregOuterRad_small` / `lowregStateRad_small` | derived, unconditional |
| `hsingle` | the `htame` conjunct | present |

So the package is a **complete** and honest fixed-point/projection contract.
What it does **not** carry, and the four §4.1 repairs need, is: `hDim`; the fact
that the background is the metric itself; `0 ≤ δ` and `δ ≤ 1/3`; the smooth-core
continuity `hcore`; and an absorption certificate.

### A.3 The widened `lowreg_loMass`, VERBATIM

Current statement: `ShortTime/LowRegAllOrderJet.lean:1052`, `sorry` at `:1064`.
Only **one binder** changes; the conclusion is untouched (audit §2 is right that
the conclusion is exactly what `lowreg_spatialMass` transports at `:1180`):

```lean
theorem lowreg_loMass
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M)
    {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1)
    (fLo : timeL2 (tensorHs (I := I) (M := M) g 0 2 ((1 : ℕ) : ℝ)) T)
    (hlo : IsLowSolve (I := I) (M := M) g hT hT1 fLo)
    (σ : ℝ) :
    ∃ Cσ : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) T,
      Summable (fun i => tensorSobolevWeight (I := I) (M := M) i σ *
          (perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i)
            (fun u => (timeModeCoeff (I := I) (M := M) fLo i) u) t) ^ 2) ∧
        ∑' i, tensorSobolevWeight (I := I) (M := M) i σ *
            (perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i)
              (fun u => (timeModeCoeff (I := I) (M := M) fLo i) u) t) ^ 2 ≤ Cσ
```

`lowreg_spatialMass` (`:1117`) takes the same leading `hDim` and forwards it at
`:1180`.  Its caller `lowreg_forceJetMass` **already** binds `hDim` at `:1217`
and calls the spatial theorem at `:1316-1318`, so propagation is one argument at
one call site.  No other consumer exists (`lowreg_allOrderJet:1445` → `:1570`,
endpoint → `:1795`, both already carry `hDim`).

**The No. 133-era widening does not cover any of §4.1's list.**  That widening
(S0-bis, PLAN4 `:1334`, `:1516`) added the `fLo`/`hincl`/`hlo` transport slots to
`lowreg_spatialMass`; it added no dimension binder and did not touch `IsLowSolve`.
Verified: `LowRegAllOrderJet.lean:1052` has no `hDim`; `UnifClassBounds.lean:407`
has no dimension field.

### A.4 The `IsLowSolve` repairs, VERBATIM, and their satisfiability

`IsLowSolve` (`UnifClassBounds.lean:407-451`) is `∃ (binders…), (conjuncts…)`.
Repair (1) edits the **binder list**; repairs (2)-(3) are new **conjuncts**
(nothing consumes them as terms, so they must not become binders).  Binder line:

```lean
  ∃ (δ Ctop B0 B1 D ρ P : ℝ) (hδ : δ < 1)
    (hCtop : 0 ≤ Ctop) (hB1 : 0 ≤ B1) (hρ : 0 < ρ) (hP : 0 < P)
    (hreal : ∀ S : SmoothCcTensor g₀ 0 2,
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ (((1 : ℕ) : ℝ) + 1) S‖ ≤ P →
        gFibreOpBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ S) δ),
```

— i.e. `(g_bg : SmoothRiemannianMetric I M)` is **deleted** and every
`lowregNfun … g₀ g_bg …` / `coreN … g₀ g_bg …` occurrence becomes `g₀ g₀`.
Body prefix, inserted ahead of the current `0 ≤ B0 ∧ …`:

```lean
    0 ≤ δ ∧ δ ≤ 1 / 3 ∧
      Continuous (coreN (I := I) (M := M) g₀ g₀ hδ
        (lowregRealRad (I := I) (M := M) g₀ (Ctop := Ctop) (B1 := B1) (ρ := ρ)
          hP.le hreal)) ∧
      0 ≤ B0 ∧ …
```

with `coreN` at `LowRegDenseN.lean:152` and `lowregRealRad` at
`UnifClassBounds.lean:219`.  The `lowregRealRad …` spelling is deliberate: it is
the *same term* `lowregNfun` itself applies (`UnifClassBounds.lean:243-245`), so
`hcore` and `hcont` speak about the same realization.

**Satisfiability at the unique producer — GREEN, zero producer work.**  The only
`isLowSolve_of_sol` call site is `LowRegApplyTwo.lean:788`, inside
`lowreg_solve_two` (`LowRegApplyTwo.lean:615`).  In scope there:

* `hDim` — binder at `:616`;
* self-background — the call is `isLowSolve_of_sol … g g …` at `:788`, i.e.
  `g_bg` is *already* `g₀`;
* `hδ0 : 0 ≤ deTurckArmContractionThreshold'' …` at `:636-637`;
  `hδ_le : … ≤ 1/3` at `:638-639`;
* `hcore` — `hcoreN` at `:720`, obtained from `lowRegN_outer`
  (`LowRegDenseSolve.lean:188`) whose second conjunct is
  `Continuous (coreN g₀ g_bg hδ₀_lt (realizeOfLE g₀ hRQ hrealQ))`.  At `:720`
  the instantiation is `hRQ := le_rfl`, `hrealQ := hrealR`, and `hrealR` is
  *definitionally the term above*: `have hrealR := lowregRealRad g … hPpos.le
  hrealP` at `:718`.  `realizeOfLE g le_rfl hrealR` and `hrealR` prove the
  **same `Prop`**, so proof irrelevance closes it — `exact hcoreN`.

This is the S0/S0-bis precedent exactly: every new field is a `have` already
sitting in the producer's context.

Churn is bounded: `isLowSolve_of_sol` (`UnifClassBounds.lean:458`) drops its
`g_bg` argument and gains the three proofs; and there is exactly **one**
destructuring consumer to re-pattern,
`LowRegGalerkinIdent.lean:78-79` (`obtain ⟨g_bg, δ, Ctop, …⟩ := hlo`).

### A.5 Item (4), the absorption certificate — the audit's blocker is *half* real

Audit §4.1 defers item 4 entirely to J3/J4.  Grep says the **ordering** half is
already available and only the **inequality** half must wait:

* the ladders are already **κ-first**: `a2_ladder`
  (`LowRegLadderRung.lean:243`) and `n_diff_hm_rung` (`:565`) both have shape
  `∃ κ, 0 ≤ κ ∧ ∀ {δ} (hδ0) (hδ_le), ∃ Clower, …`, with top coefficient
  `κ * (δ / (1 - δ)^2)`;
* that `κ` is `lowData_split`'s constant, taken at `:270` before `δ` is bound;
  and `lowData_split` (`DeTurckRemainderLowBaseAction.lean:3841`) depends on
  `(g, g_bg)` **only** — no `a`, no `R₀`, no `δ`;
* the just-landed `c0_jet_tower_quad` (`LowRegC01JetTower.lean:1052`) and
  `selfLow_jet_quad` (`:664`) likewise choose `K0, K2` before `T`, before `δ`,
  with no `a` and no `R₀`.

So "choose `δ*` after `κ`" is not blocked by J4.  What blocks it today is a
**producer-side pin**, and it is a small one: the *only* place `lowreg_solve_two`
fixes `δ` is `realize_at_thr` (`LowRegDenseSolve.lean:43`), whose witness is
hard-coded `(θ/C, θ)` with `θ = deTurckArmContractionThreshold'' (finrank)`.
Everything else in that chain is already `δ`-generic:
`refold_aff` (`LowRegBgA1Refold.lean:488`, `{ρ δ}` with `0 ≤ δ ≤ 1/3`),
`radialA2_lip` (`DeTurckRemainderLowBaseTimeA2.lean:370`, same),
`lowA2_small`, `lowRegN_outer` (`0 ≤ δ₀`, `δ₀ < 1`), `lowreg_bounds_exist`
(`UnifClassBounds.lean:513`).

`realize_at_thr`'s proof uses `θ` only through `hdelta : C * ‖T‖ ≤ θ`
(`LowRegDenseSolve.lean:69-75`).  Generalizing it is mechanical.

### A.6 J0 dispatch, split into two bricks

**J0a — dispatchable now (≈1 session).**

1. `realize_at_delta` in `ShortTime/LowRegDenseSolve.lean`, next to
   `realize_at_thr`:

   ```lean
   theorem realize_at_delta (hDim : Module.finrank ℝ E = 3)
       (g : SmoothRiemannianMetric I M) {δ : ℝ} (hδ : 0 < δ) :
       ∃ R : ℝ, 0 < R ∧
         ∀ T : SmoothCcTensor g 0 2,
           ‖smoothCcToTensorHs (I := I) (M := M) g (((1 : ℕ) : ℝ) + 1) T‖ ≤ R →
             gFibreOpBound (I := I) (M := M) g
               (ccTensorBilinSymm (I := I) g T) δ
   ```

   witness `R := δ / C` from `hs2_op_bound hDim g`; recover `realize_at_thr` as
   the instance at `δ := deTurckArmContractionThreshold'' (finrank)`.
   Note `LowRegRealize.lean:32` (`lowreg_realize_h2`) and `:64`
   (`lowreg_realize`) are two more copies of the same proof, also pinning
   `p.2 = θ` via `le_rfl` — fold all three onto the new lemma.
2. Thread `{δ★ : ℝ} (hδ★ : 0 < δ★) (hδ★le : δ★ ≤ 1/3)` through
   `lowreg_solve_two` (`LowRegApplyTwo.lean:615`), replacing the three `have`s at
   `:636-641` by the parameter and `realize_at_thr` by `realize_at_delta`.  The
   realization radius enters `P` only as one more `min` component
   (`LowRegApplyTwo.lean:697`), so a smaller radius is absorbed with no
   structural change.
3. Widen `IsLowSolve` by §A.4 (1)-(3); discharge at `:788` as shown.
4. Widen `lowreg_loMass` + `lowreg_spatialMass` by `hDim` (§A.3); forward at
   `:1318`.

**J0b — deferred behind J4.**  The certificate itself.  Once J4 fixes the
`a = 1` top coefficient, name `κ` canonically (a `def` returning
`(lowData_split g₀ g₀).choose`, in the DeTurck layer, with a `_spec` lemma) and
add the absorption field as a plain real inequality in `κ` and `δ`; `δ★` is then
instantiated by the endpoint, not by the solve.  Do **not** add `habs` as an
opaque assumption before J4 — that is the frontier-wrapper failure mode.

**Missing API found in passing.**  The `δ`-monotone weakening of
`gFibreOpBound` exists three times, all `private`:
`RicciThreeArmAppCc.lean:1280` (`gFibreOpBound_mono_local`),
`DeTurckLieKernelL2JetBound.lean:333` (`gFibreOpBound_mono_of_le`),
`BoundsB.lean:1903` (`lc0b_gFibreOpBound_mono`).  J0b will want one public copy
at the `gFibreOpBound` definition site.  (It weakens `δ`; it does **not** give
realization at a *smaller* `δ` — that is what `realize_at_delta` is for.)

---

## B. J5 — the `N`-indexed `L¹` energy engine

### B.1 The audit's diagnosis, re-verified

`galerkin_energy_l1_bound` (`GalerkinParabolicEnergy.lean:494`) binds
`{A S : ℝ → ℝ}` at `:498` — one shared pair for all `N` — and `hclosure` uses
that same `A t` at `:510-517` (the coefficient itself at `:514`).  The audit's counterexample (moving disjoint
spikes: `∫ A_N ≤ c` for all `N` does not make `sup_N A_N` integrable) is
correct, so the engine genuinely cannot consume the projected family.

### B.2 The proof generalizes — verified by reading it

The body is:

```
  have hkey : ∀ N, ∀ k, ∀ t ∈ Set.Icc (0 : ℝ) T, …      -- :525
    intro N                                              -- :528
    …                                                    -- all of Mk, Mk', hdiss are per-N
    exact energy_hier_l1_bound (c := 2 - Cδ) … (A := A) (S := S) (Sbd := Sbd)
      hc hC hseed hS0 hSnn hScont hSderiv hSbd …         -- :570-573
  refine fun k => ⟨Real.exp Sbd * gronwallBound … , fun N t ht => ?_⟩   -- :574
```

`intro N` happens **before** any use of `A`/`S`, and the single call to
`energy_hier_l1_bound` (`:234`) sits inside that scope.  Replacing `A` by `A N`
and `S` by `S N` therefore changes nothing but the five `S`-hypotheses and
`hclosure`'s coefficient.  Crucially `Sbd` stays a **scalar**: it is the common
bound the audit asks for, and it is the only thing the final `Bound` at `:574`
depends on — so the **conclusion is unchanged**.

`energy_hier_l1_bound` itself needs **no** change: it is already stated for a
single family and is applied once per `N`.

### B.3 Verdict: IN-PLACE generalization, and the compat instance is unnecessary

`galerkin_energy_l1_bound` has **zero call sites** in the tree — the only
occurrence outside its own file is a docstring mention at
`LowRegAllOrderJet.lean:1037`.  So the "zero-call-site-churn" question is moot:
generalize in place, no deprecated alias, no `A := fun _ => A` shim.  Keep the
name.

Exact edit (binders only; body unchanged except `A`→`A N`, `S`→`S N`):

```lean
    {T σ₀ Cδ Sbd : ℝ} {Cmid seed B0 : ℕ → ℝ} {A S : ℕ → ℝ → ℝ}
    (hCδ : Cδ < 2) (hCmid : ∀ k, 0 ≤ Cmid k) (hseed : ∀ k, 0 ≤ seed k)
    (hS0 : ∀ N, S N 0 = 0)
    (hSnn : ∀ N, ∀ t ∈ Set.Icc (0 : ℝ) T, 0 ≤ S N t)
    (hScont : ∀ N, ContinuousOn (S N) (Set.Icc (0 : ℝ) T))
    (hSderiv : ∀ N, ∀ t ∈ Set.Ico (0 : ℝ) T,
      HasDerivWithinAt (S N) (A N t) (Set.Ici t) t)
    (hSbd : ∀ N, ∀ t ∈ Set.Icc (0 : ℝ) T, S N t ≤ Sbd)
```

and in `hclosure` (`:510-517`) the `(Cmid k + A t)` at `:514` becomes `(Cmid k + A N t)`;
the `exact energy_hier_l1_bound … (A := A) (S := S)` at `:570` becomes
`(A := A N) (S := S N)` with the five hypotheses applied at `N`.

Price: **≤ 1 session**, and realistically a fraction of one.  This is the
cheapest brick in the post-tame lane; it is also the one whose absence would
silently invalidate J2/J4's output, so it should be done early, not late.

---

## C. Sequencing and honest price for the whole post-tame lane

### C.1 Recon status per joint

| joint | audit § | recon status | note |
|---|---|---|---|
| J0a | §4.1 (1)-(3) + producer | **dispatch-ready** | §A.6 above; satisfiability GREEN |
| J0b | §4.1 (4) | **needs J4 first** | certificate shape unknown until the `a=1` top coefficient exists |
| J5 | §J5 | **dispatch-ready** | §B.3; in-place, zero call sites |
| J1 | §J1 | **dispatch-ready** | mechanical: `LowRegGalerkinIdent.lean:141` discards `_u,_hu,_hstate,_htr,_hpde`; widen the `hex` existential and `choose` more |
| J2 | §J2 | **needs design** | a.e.-vs-everywhere is the real content: either an AC energy engine or a continuous finite-mode representative |
| J4 | §J4 | **needs design; dominant risk** | no tower-direct pairing theorem at `a = 1`; `a1_ladder` gated `2 ≤ a` (`:428`), `a2_ladder`/`n_diff_hm_rung` gated `3 ≤ a` (`:246`, `:568`) |
| J6 | §J6 | recon-complete, blocked | pure calibration once J0b+J4 land |
| J7 | §J7 | recon-complete | small adapter; producers exist |

### C.2 Recommended order (deviates from audit §5 in two places)

1. **J5** (cheapest, and everything downstream is stated against it).
2. **J0a** (unblocks the honest contract without waiting for J4 — the audit
   sequenced the whole "honest producer" phase behind the viability gate, but
   only item (4) actually depends on it).
3. **J1** (mechanical, and J2 cannot be stated without the retained witness).
4. **J4** — the remaining mathematical frontier.
5. **J2** (its statement is cleanest once J4 fixes the coefficient shape).
6. **J0b**, then **J6**, then **J7**.

Audit §5's order was J0 → J1/J2 → J4 → J5 → J6 → J7 with J3 first.  The two
deviations are: J5 moves to the front (it is a binder edit, and it changes the
type every later brick must hit), and J0 splits so that its three free
certificates land immediately instead of waiting on J4.

### C.3 Honest session count

The audit priced 12-16, central 14, claiming a 2x adjustment for this lane's
optimism.  Since the audit was adopted (PLAN4 No. 136), **eight** executor
sessions have closed (No. 137, 138e, 139e, 140e, 141e, PLAN5 142e, 143e, 144e)
and a ninth (the final `gridIntHigh` assembly, No. 145e) has now CLOSED —
`gridIntHigh` is proved and the tame `C0` bottom is fully axiom-clean.  All nine
went to the **viability gate alone**, which the audit priced at 4-5.  So the
already-2x-adjusted estimate ran a further ~2x on the only phase we can measure.

That does **not** license a flat 2x on the remainder: J3 was the phase with
genuinely new mathematics, and J5/J0a/J1/J7 are plumbing whose satisfiability
this document has just verified line by line.  The honest split:

* J5 + J0a + J1: **2-3** sessions (verified dispatch-ready, low variance);
* J4: **4-7** (the only remaining frontier; the `a = 1` bottom closure with no
  `H⁵` radius and no same-rung radius in its own Grönwall coefficient — this is
  where a 2x overrun would land);
* J2: **2-3** (a.e.-vs-everywhere is a real design choice, not plumbing);
* J0b + J6: **2-3**;
* J7 + endpoint assembly: **1-2**.

**Post-tame remainder: 11-18 sessions, central 14.**  Total for the
`lowreg_loMass` lane from the audit's adoption: ≈ 23 sessions against the
audit's 14.  Report the remainder as 14, not as "14 − 9 = 5".

### C.4 Exhibit eleven?

One candidate, and it is a **sequencing** over-count rather than a wall
over-count, so it is weaker than exhibits one-ten:

> Audit §4.1 item 4 and §5's phase order put the entire "honest producer" phase
> (2-3 sessions) behind the viability gate.  Grep shows that three of the four
> repairs (self-background, `δ`-range, `hcore`) are already sitting as named
> `have`s in `lowreg_solve_two`'s context (`LowRegApplyTwo.lean:636-641`, `:720`,
> `:788`), that the ladders are already κ-first with a `δ`-free κ
> (`LowRegLadderRung.lean:270`, `:562`), and that the only genuine `δ`-pin in the
> producer is one hard-coded witness in `realize_at_thr`
> (`LowRegDenseSolve.lean:56`).  ~80% of the phase was dispatchable on day one.

Register it as **exhibit eleven (sequencing)** only if the J0a brick lands at or
under one session.  If it overruns, the audit's ordering was right and this was
recon optimism — which would itself be the lesson.

Two non-exhibits worth recording:

* §6's `galerkin_energy_l1_bound` "FAIL as the claimed ready engine" is
  **literally true** but reads heavier than it is: the fix is a binder edit on a
  theorem with zero call sites (§B.3).  The audit's 1-session price is if
  anything generous.
* §J1's "discards the state/PDE packet" is **confirmed at today's tree**
  (`LowRegGalerkinIdent.lean:141`).  No drift.

---

## Honest denominators

* `lowreg_loMass`: theorem **0%** (`ShortTime/LowRegAllOrderJet.lean:1052`,
  `sorry` at `:1064`); its dedicated route-correct machinery ≈ **41%**
  (unchanged from PLAN5 No. 145 — this recon added no Lean).
* J0 widening: **0%** stated (this document is the design, not the edit);
  its satisfiability homework: **done**.
* J5 `N`-indexed engine: **0%** stated; the generalization is verified feasible.
* Tame `C0` bottom: **100%** — `gridIntHigh` PROVED (PLAN5 No. 145e); no
  frontier left, `selfLow_jet_quad` and `c0_jet_tower_quad` unconditional.
* `(N) ricci_flow_unif_existence`: theorem **0%** — stated with `sorry` at
  `Evolution/ExtendViaUniqueness.lean:98`.
* Whole HCG compactness project: ≈ **3%**.

ShortTime `sorry` census at recon time: exactly two in `ShortTime/*.lean` —
`LowRegAllOrderJet.lean:1064` (`lowreg_loMass`) and
`WeylEigenvalueCountingBound.lean:115` (the citation-sorry, policy pending).
Route-error counter: **2/3** (unchanged; this recon opened no new route).
