# M2 — the `a = 1` mode-coordinate forcing for `lowregNfun`

Design recon for planner Nos. 146–147 (`UNIF_EXISTENCE_PLAN5.md`).  Read-only:
no Lean run, no `.lean` edit.  Consumer = the J4 rung-3 per-scale closure.

---

## 0. LEAD: EXHIBIT TWELVE — CONFIRMED.  The object already exists.

The M2 diagnosis says: *"at `a = 1` no mode-coordinate forcing function is
defined for `lowregNfun`; without it the rung-3 closure has no `Fseq` to be
stated about."*  **That is a false wall.**  The forcing is in the tree, with the
docstring naming its own role:

`Analysis/Spectral/Intrinsic/HeatSemigroup/GalerkinTameSol.lean:549`

```lean
/-- The Galerkin forcing coordinate: the `i`-th eigen-coefficient of the
nonlinearity at the retracted state of the coefficient family `c`, killed off
the truncation.  This is the tame analogue of `deTurckGalerkinForcingSymm`. -/
def galTameForce (g₀ : SmoothRiemannianMetric I M) (a : ℕ) {R : ℝ} (hR : 0 ≤ R)
    (Nfun : lowerState (I := I) (M := M) g₀ a R →
      tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ))
    (S : Finset (TensorEigenIdx (I := I) (M := M) g₀ 0 2))
    (c : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ)
    (i : TensorEigenIdx (I := I) (M := M) g₀ 0 2) : ℝ :=
  if i ∈ S then
    (Nfun ⟨galTameStateC (I := I) (M := M) g₀ a R S c,
      galTameStateC_mem (I := I) (M := M) g₀ a hR S c⟩).coeff i
  else 0
```

No gate.  Generic in `a`, `Nfun`, `S`.  Companions: `galTameForce_apply`
(`:615`, `@[simp]`, `rfl`) and `galTameForce_eq` (`:593` — on the state ball
the retraction is inert, so the forcing is the *true* truncated nonlinearity).

And it is **already instantiated at `a = 1` for `lowregNfun`**, N-indexed, on the
whole horizon: `lowregGalSol`, `ShortTime/LowRegGalerkinSol.lean` (file header:
*"The order-one `V_N` Galerkin system for `lowregNfun` … This file is the
**first**"* of the three producers `lowreg_loMass`'s docstring lists).

**Timing, so the exhibit is not arguable.**  `GalerkinTameSol.lean` mtime
`2026-08-04 11:32`; `LowRegGalerkinSol.lean` `11:39`.  The M2 claim was written
into `LowRegAllOrderJet.md` at `21:15` and `UNIF_EXISTENCE_PLAN5.md` at `22:23`
— roughly ten hours **after** the producer landed.  Both files are untracked
(`git status`: `??`), which is presumably why the census grep missed them: they
are in the tree but not in the index.

**Taxonomy.**  Same failure mode as the project's earlier false walls (A0′ L1,
the iterated-tangent-bundle wall, the №97 Palatini/Ksup census): a wall declared
from the *consumer's* vocabulary (`deTurckGalerkinForcing*`) without grepping for
the *object* under its own name.  Census lesson: grep the mathematical role
(`Galerkin forcing`, `Fseq`, `tame`), not only the high-gate declaration's name,
and include untracked files.

**Residual M2 after the exhibit: ONE lemma.**  See §3.

---

## 1. Anatomy of the high-gate original

### 1.1 The definition chain

`deTurckGalerkinForcingSymm` (`HeatSemigroup/GalerkinParabolicEnergyDeTurck.lean:58`)

```lean
def deTurckGalerkinForcingSymm (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (U : ℕ → ℝ → TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ) (N : ℕ) (t : ℝ)
    (i : TensorEigenIdx (I := I) (M := M) g₀ 0 2) : ℝ :=
  if i ∈ eigenIdxFinset (I := I) (M := M) g₀ N then
    (deTurckSobolevNHa2Symm (I := I) (M := M) g₀ g_bg a
      (finiteEigenComboHs (I := I) (M := M) g₀ (eigenIdxFinset (I := I) (M := M) g₀ N)
        (U N t) ((a : ℝ) + 2))).coeff i
  else 0
```

Shape is *identical* to `galTameForce`: `if i ∈ S then (𝒩 (combo of coords)).coeff i
else 0`.  The only structural difference is that `galTameForce` composes with the
retraction `galTameStateC` so that `𝒩`'s domain (`lowerState g₀ a R`) is met
unconditionally.

**Over-count correction (i).**  `deTurckSobolevNHa2Symm`
(`DeTurck/SobolevNonlinearityExistence.lean:2783`) binds **no gate** — it is a
`dite` whose `else` branch is `0`.  It therefore *exists* at `a = 1`; what fails
below the gate is that the branch is junk and no lemma is available.  "Only
EXISTS above the gate" is literally false, substantially right.

**Over-count correction (ii).**  Two different gates are in play, and the census
conflates them: the *forcing's* Lipschitz gate is `2 * finrank ℝ E + 10 ≤ a`
(`deTurckSobolevNHa2Symm_lipschitzWith`, `:2849`), but the *closure's* is
`4 * finrank ℝ E + 10 ≤ a` (`deTurckGalerkin_forcing_closure_perScaleSymm`,
`GalerkinParabolicEnergyDeTurck.lean:1486`, binder `ha_super`).

### 1.2 What the consumers actually take from the forcing

| consumer | what it uses | gate-dependent? |
|---|---|---|
| `galerkin_energy_l1_bound` (`GalerkinParabolicEnergy.lean:497`) | **only** `hderiv` and `hclosure` — `Fseq` appears nowhere else | generic (no gate; no continuity, measurability or integrability of `Fseq` is ever assumed) |
| `deTurckGalerkin_forcing_closure_perScaleSymm` (`:1484`) | the `_apply`/`rfl` unfolding, then the tame ladders on `𝒩` | `4·finrank+10 ≤ a` — **the ladders**, not the forcing |
| `galerkinPerMode_eq_perModeConvSymm` (`GalerkinLimitUniformMass.lean:70`, private) | `hUinit`, `hUcont`, `hUderiv`, **plus** `ContinuousOn (fun t => Fseq N t i)` | gate enters *only* through the continuity lemma |
| `continuousOn_galerkinForcingSymm` (`GalerkinLimitUniformMass.lean:33`, private) | `deTurckSobolevNHa2Symm_lipschitzWith` | `2·finrank+10 ≤ a` |

The decisive reading: **the energy engine consumes nothing from `Fseq` but the
ODE and the pairing bound.**  Verbatim, `galerkin_energy_l1_bound`:

```lean
    (hderiv : ∀ N, ∀ t ∈ Set.Ico (0 : ℝ) T, ∀ i ∈ sseq N,
      HasDerivWithinAt (fun r => U N r i)
        (-(TensorEigenIdx.lambda (I := I) (M := M) i) * U N t i + Fseq N t i)
        (Set.Ici t) t)
    (hclosure : ∀ (N : ℕ) (k : ℕ), ∀ t ∈ Set.Ico (0 : ℝ) T,
      2 * ∑ i ∈ sseq N, tensorSobolevWeight (I := I) (M := M) i (σ₀ + (k : ℝ)) *
          (U N t i * Fseq N t i) ≤ …)
```

`hcont` is about `U`; `hScont`/`hSderiv` are about the primitive `S`.  So the
whole gate story on the forcing side is an artefact of the *identification*
layer, not of the energy hierarchy.

---

## 2. The `a = 1` replacement: the `Fseq` shape

### 2.1 Recommendation: **no new `def`.**

`Fseq` is a partial application of an existing generic definition.  Adding a
public `lowregGalForce` would be a parallel API for a specialization — the thing
`CLAUDE.md`'s Mathlib-discipline section forbids ("one canonical API per
concept"; wrappers only for public endpoints/old import paths).  The intended
shape, as it will appear at the closure's call site:

```lean
-- sseq N  :=  eigenIdxFinset (I := I) (M := M) g₀ N
-- Fseq N t :=
galTameForce (I := I) (M := M) g₀ 1
  (lowregStateRad_pos hCtop hB1 hρ hP).le
  (lowregNfun (I := I) (M := M) g₀ g_bg hδ hCtop hB1 hρ hP hreal)
  (eigenIdxFinset (I := I) (M := M) g₀ N) (U N t)
```

If a closure statement becomes unreadable, use a `set`/`private abbrev` **local
to that file**, never a public def.

### 2.2 It already matches the engine, verbatim

`lowregGalSol`'s conclusion (`ShortTime/LowRegGalerkinSol.lean:91`, tail):

```lean
    ∃ U : ℕ → ℝ → TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ,
      (∀ N, ∀ i ∈ eigenIdxFinset (I := I) (M := M) g₀ N,
        ContinuousOn (fun t => U N t i) (Set.Icc (0 : ℝ) T)) ∧
      (∀ N, ∀ t ∈ Set.Ico (0 : ℝ) T, ∀ i ∈ eigenIdxFinset (I := I) (M := M) g₀ N,
        HasDerivWithinAt (fun r => U N r i)
          (-(TensorEigenIdx.lambda (I := I) (M := M) i) * U N t i +
            galTameForce (I := I) (M := M) g₀ 1 … (U N t) i)
          (Set.Ici t) t) ∧
      (∀ N, ∀ i, U N 0 i = 0) ∧
      (∀ N, ∀ t, ∀ i, i ∉ eigenIdxFinset (I := I) (M := M) g₀ N → U N t i = 0)
```

Against `galerkin_energy_l1_bound`: conjunct 1 **is** `hcont`; conjunct 2 **is**
`hderiv` (same binder order `∀ N, ∀ t ∈ Ico, ∀ i ∈ sseq N`); conjunct 3 gives
`hinit` with `B0 := fun _ => 0` by the `Finset.sum_eq_zero` step that
`deTurckGalerkin_forcing_closure_perScaleSymm` already runs on `hU0`.  **Three of
the engine's five `Fseq`-adjacent inputs are free today.**

### 2.3 Property list — free vs. new

| property | needed by | verdict |
|---|---|---|
| `Fseq` is well-typed / defined at `a = 1` | everything | **FREE** — `galTameForce` (exhibit twelve) |
| unfolding `Fseq N t i = (𝒩 …).coeff i` on `S`, `0` off `S` | the closure | **FREE** — `galTameForce_apply` (`@[simp]`, `rfl`) |
| the ODE `hderiv` | energy engine | **FREE** — `lowregGalSol` |
| `hcont` for `U`, zero seed for `hinit` | energy engine | **FREE** — `lowregGalSol` |
| the retracted state lies in the state ball (so the ladders apply with no a-priori bound) | the closure | **FREE** — `galTameStateC_mem`, `galTameRetr_ball`, `galTameRetr_top` |
| retraction inert on the ball (to exorcise it at the limit) | final identification | **FREE** — `galTameForce_eq`, `galTameStateC_eq` |
| Finset Bessel truncation | the closure | **FREE** — `tensorHs.weight_sum_le_normSq` (M1, landed) |
| `perModeConv` convergence of the projected forcing | Fatou | **FREE** — `lowreg_projMode_tendsto` (`ShortTime/LowRegGalerkinIdent.lean:165`) |
| **`ContinuousOn (fun t => Fseq N t i) (Icc 0 T)`** | the perMode identification | **NEW** — sub-brick M2a (§3.1) |
| **the `perModeConv` identification at `a = 1`** | Fatou's other half | **NEW** — sub-brick M2b (§3.2) |
| `hclosure` (the pairing bound at base order 1) | energy engine | **NEW, but this is J4/M3, not M2** |

One structural remark worth banking, because it settles a worry in the M3
census: the retraction makes the H² state-ball hypothesis **free at the closure
level** — `galTameStateC_mem` says the retracted state is in
`lowerState g₀ 1 (lowregStateRad …)` by construction, so the a₁/a₂ ladders apply
to it unconditionally.  What is *not* N-uniform is the top norm
(`galTameRetr_top` gives `√κ·R` with `κ = N+1`), which is exactly why the L²ₜH³
dependence has to ride in J5's `A N t` coefficient rather than in a constant.

---

## 3. Home + brick decomposition

> **STATUS 2026-08-04 — §3 IS DELIVERED, M2 CLOSED.**  `galTameForce_contOn`
> (`GalerkinTameSol.lean:674`, Route B as written below), `galTamePerMode`
> (`:886`, the port with `ha_super` deleted), plus one bridge this plan did not
> list, `galTameStateC_emb` (`:262`).  Focused check + targeted build green,
> `#print axioms` clean on all three.  No import churn; no file outside
> `GalerkinTameSol.lean` touched.  Executor report: `UNIF_EXISTENCE_PLAN5.md`
> No. 149-executor-M2.  **Next target is NOT in this document**: the `a = 1`
> instantiation and the Galerkin-vs-projected forcing seam flagged in that
> report both wait on the §6.4 re-pricing verdict for J4-rung-3.

Both sub-bricks belong in **`HeatSemigroup/GalerkinTameSol.lean`**, stated
generically in `a`/`Nfun`/`S` beside `galTameForce`.  Import check done: that
file imports `GalerkinParabolicEnergyDeTurck` → `MaximalRegularity/Plancherel` →
`MaximalRegularity/PerMode`, so `perModeConv`, `perModeConv_hasDerivAt`,
`perModeConv_zero_left` are all in cone.  **No import churn, no low-file edit,
no full-cone rebuild** (cf. the No. 146 lesson: a low ShortTime edit cost ~9 984
jobs).

### 3.1 Sub-brick M2a — `galTameForce_contOn` (FIRST; full handoff)

Statement to write (name ≤ 20 letters, conclusion-first):

```lean
theorem galTameForce_contOn (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    {R : ℝ} (hR : 0 ≤ R)
    (Nfun : lowerState (I := I) (M := M) g₀ a R →
      tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ))
    (S : Finset (TensorEigenIdx (I := I) (M := M) g₀ 0 2))
    {κ : ℝ} (hκ0 : 0 ≤ κ)
    (hκ : ∀ i ∈ S, 1 + TensorEigenIdx.lambda (I := I) (M := M) i ≤ κ)
    {K : ℝ≥0}
    (hK : LipschitzOnWith K Nfun (galTameBall (I := I) (M := M) g₀ a R κ))
    {T : ℝ} (c : ℝ → TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ)
    (hc : ∀ i ∈ S, ContinuousOn (fun t => c t i) (Set.Icc (0 : ℝ) T))
    (i : TensorEigenIdx (I := I) (M := M) g₀ 0 2) :
    ContinuousOn (fun t => galTameForce (I := I) (M := M) g₀ a hR Nfun S (c t) i)
      (Set.Icc (0 : ℝ) T)
```

The hypothesis bundle is **exactly** `galTameSolOne`'s (`:642`), so every call
site that has a solution already has the inputs.

Two routes; take B first.

* **Route B (short, ~15–25 lines).**  `galTameField_lip` (`:431`) already gives
  `LipschitzWith K' (galTameField … Nfun S)` from `hκ0`/`hκ`/`hK`.  Inside
  `galTameSolOne` the bridge `galTameForce = galTameField + diag` is already
  performed at one line — `rw [galTameField_apply, galTameForce_apply, if_pos hi,
  dif_pos hi, hsub]`.  So: coordinate vector `t ↦ w t` is continuous
  (`continuousOn_pi` + `EuclideanSpace.equiv … .symm.continuous`), compose with
  the Lipschitz field, project with `ContinuousLinearMap`/coordinate evaluation,
  and add back `λᵢ · c t i` via `hc`.  Off `S`, `if_neg` + `continuousOn_const`.
* **Route A (mirror of the original, ~40–60 lines).**  Follow
  `continuousOn_galerkinForcingSymm` (`GalerkinLimitUniformMass.lean:33`) line
  for line, replacing `deTurckSobolevNHa2Symm_lipschitzWith` by
  `hK` + `galTameState_lip` (`:330`), and using the in-file `galEmbedCombo`
  (`:84`) instead of `continuousOn_galerkinForcing_field` (which lives in the
  sibling `GalerkinForcingTimeL2Limit.lean:54`, out of cone).  Membership in
  `galTameBall` along the way is `galTameRetr_ball` (`:412`).

Difficulty: **routine local proof.**  No missing API identified — every lemma the
proof needs is in the same file.  Failure signal that should stop the executor:
if `galTameField_lip`'s `K'` cannot be turned into `ContinuousOn` of the
*coordinate* map without a new projection lemma, fall back to Route A rather than
adding a new CLM wrapper.

### 3.2 Sub-brick M2b — `galTamePerMode` (SECOND)

Generic mirror of the private `galerkinPerMode_eq_perModeConvSymm`
(`GalerkinLimitUniformMass.lean:70–142`), stated for `galTameForce` and with the
`ha_super` binder **deleted** — its only use in the original is to reach the
continuity lemma, which M2a now supplies gate-free.

Conclusion shape (unchanged from the original):

```lean
    c t i =
      perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i)
        (Set.IccExtend hT.le (fun p : ↑(Set.Icc (0 : ℝ) T) =>
          galTameForce (I := I) (M := M) g₀ a hR Nfun S (c p.1) i)) t
```

Proof skeleton, already in the original and fully in cone: `Set.IccExtend` +
`Continuous.Icc_extend'` (fed by M2a), `tensor_lambda_nonneg`,
`perModeConv_hasDerivAt`, `perModeConv_zero_left`, and Mathlib's
`ODE_solution_unique_of_mem_Icc_right`.  Difficulty: **mechanical port** —
the original is ~75 lines of ODE plumbing with no gate-specific step.

Then the `a = 1` instantiation for `lowregNfun` is a one-liner in
`ShortTime/LowRegGalerkinSol.lean`, feeding `lowregGalSol`'s own conjuncts.

### 3.3 Session pricing (calibrated: campaign estimates run ~2× optimistic)

* M2a: **0.3 session**.  Even doubled from a naive "one afternoon lemma", it is
  small — hypotheses pre-bundled, all lemmas local.
* M2b: **0.5–0.7 session**.  Port risk is `IccExtend`/`Subtype` friction, not
  mathematics.
* **M2 total: ~1 session**, against the ~1 that No. 147 implicitly reserved for
  "the a = 1 mode-coordinate forcing" as a *producer build*.  The exhibit does
  not shrink the calendar much; it changes the *kind* of work from "design and
  build a forcing" to "two adapter lemmas over an existing one", which lowers
  the variance and removes the design risk.

Sequencing: M2a/M2b are **independent of M3** and of the calibration.  They can
run in parallel with the sibling M3 executor (disjoint files:
`GalerkinTameSol.lean` + `LowRegGalerkinSol.lean` here vs. `LowRegLadderRung.lean`
+ `LowRegC01JetTower.lean` there).

---

## 4. Exhibit hunt — the rest of the sweep

* `GalerkinForcingTimeL2Limit.lean` — `continuousOn_galerkinForcing_field`
  (`:54`) is **gate-free and `a`-generic** (hypothesis: `hUcont` only), which
  confirms the field-continuity half is intrinsically gate-free;
  `galerkinPerMode_eq_perModeConv` (`:117`) is public but still carries
  `ha_super`.  Neither is reusable here — out of `GalerkinTameSol`'s cone and
  tied to `deTurckGalerkinForcing`.  (If a later brick wants one canonical copy,
  `:54`'s canonical home is `GalerkinParabolicEnergyDeTurck.lean`, where
  `finiteEigenComboHs` and `galerkinCoordEmbed` live — a low-file move costing a
  full-cone rebuild, so not now.)
* `GalerkinLimitUniformMass.lean` privates — `continuousOn_galerkinForcingSymm`
  (`:33`), `galerkinPerMode_eq_perModeConvSymm` (`:70`), `galerkinCoordFieldSymm`
  (`:144`).  All gate-carrying and `Symm`-specific: **templates** for §3, not
  reusable objects.  Its `:1163` call site is the model for wiring `Fseq := …`
  into `galerkin_energy_l1_bound`.
* The `_symm` family (`deTurckSobolevNHa2Symm_*`) is gated at `2·finrank+10`
  throughout; no gate-free sibling.  `galerkinCoordField`/`galerkinRestrict` and
  their tame counterparts (`galTameField`, `galerkinCoordRestrict`,
  `galerkinCoordDiag`, `galerkinCoordEmbed`) all exist and are gate-free.

No second exhibit found beyond §0.

---

## 5. Honest denominators

* `(N) ricci_flow_unif_existence`: theorem **0%** — stated at
  `Evolution/ExtendViaUniqueness.lean:80`, `sorry` at `:98`; untouched by this
  recon.
* `lowreg_loMass` (`ShortTime/LowRegAllOrderJet.lean`, still `sorry`): theorem
  **0%**.  Its dedicated machinery ≈ **51% → ≈ 55%** on the exhibit alone — of
  the three order-one producers its own docstring lists, #1 (the `V_N` system)
  is **done** (`lowregGalSol`), #2 (the perMode identification) is ~30% (its
  forcing exists; the two adapter lemmas remain), #3 (the per-scale closure) is
  **0%** and is the real frontier.
* M2 as scoped by No. 147: **~70% pre-existing**; residual = §3.1 + §3.2 —
  both now **delivered and census-clean** (2026-08-04), so **M2 = 100%**.
  Producer #2 (the perMode identification) thereby moves ~30% → ~75%, and
  `lowreg_loMass`'s dedicated machinery ≈ 57% → ≈ 60%.  Producer #3 (the
  per-scale closure) is unchanged at **0%** and is still the real frontier.
* J4-rung-3: **0% stated**.  Prerequisites: M1 100%, M2 ~70%, M3 0%.
* Whole HCG compactness project: ≈ **3%**.
* Post-tame remainder: 11–18, central 14 (unchanged; this recon does not move
  it — it re-labels ~1 session of M2 from "build" to "adapt").
* Route-error counter: **2/3** (unchanged — this is a census over-count found in
  read-only recon, the same taxonomy No. 147 already ruled on).

**§§0–5 were written as design recon only** — at the time of writing nothing
had been verified in Lean, no Lean process had been run and no `.lean` file had
been touched; every claim was grep/read evidence with a `file:line` handle.
**The §3 bricks were then executed on 2026-08-04** and verified in Lean (see the
STATUS block in §3); the recon's route survived unchanged.
