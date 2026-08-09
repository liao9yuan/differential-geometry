# UnifTraceLip.lean — G3 lane nodes 2 and 3

Status: **BOTH LANDED sorry-free** (2026-08-07).  Focused check green, targeted
module build green, axiom probes clean.  784 lines.

* node 2 = `trace24_h2_lip_unif` (entry 209)
* node 3 = `pairTrace_h2_lip_unif` (entry 214) — see the section near the end

## What this file provides

`trace24_h2_lip_unif` — the class-uniform sibling of the private metricwise
`trace24_h2_lip` (`DeTurckRemainderLowBaseC2Lip.lean:1358`, READ-ONLY).  One
`H²` radius `ρ` and one Lipschitz coefficient `C` are chosen from `(gBase, Λ)`
before the class metric varies; on the common ball the two moving cometric
double traces `pureTrace g gT p`, `p = 2, 4`, are Lipschitz in their first three
covariant `L²` jets in the `H²` distance of the perturbations.

Class hypothesis pair is exactly the ruled one:
`MetricUniformEquivalentOn univ gBase g Λ` plus
`∀ a ≤ 3, MetricCovDerivOrderBoundOn univ a g gBase Λ`.  No fourth jet.

The statement spells out `∑ j ∈ Finset.range 3, ‖iteratedCovGrad …‖ ^ 2`
because the monolith's `c2JetSq` abbreviation is private; the two conjuncts are
otherwise identical to `trace24_h2_lip`'s.

## Part-0 finding: the named "single missing lemma" was NOT missing

Entry 202 named as this brick's one gap a *class-uniform pointwise fibre bound
for* `cometricDoubleTraceField g p`, "the analogue of `rfns_idEndo_le`", and
predicted it would be the whole brick.  **It already exists, public and
sorry-free:**

    theorem cometricTrace_rfns_p (p : ℕ) (g : SmoothRiemannianMetric I M) (x : M) :
        riemannianFiberNormSq g (p + 2) p x
            ((cometricDoubleTraceField g p).toSection x) ≤
          (Module.finrank ℝ E : ℝ) ^ (p + 6)

`Analysis/Parabolic/RicciLinearization/CometricTraceSelfBound.lean:220`
(namespace `DifferentialGeometry.Analysis.Parabolic.TensorSpectral`; note the
argument order — `p` first, then `g`, then `x`).  It is rank-generic, single
metric, no `δ`, no existential, and its constant is a PURE DIMENSION constant —
so no `Λ`-expression and no metric-equivalence hypothesis are needed at all.
Its own route is a succ recursion `traceSucc_rfns` (private, same file, an
EQUALITY: each passenger slot multiplies the squared fibre norm by the
dimension) on top of `rfns_slotExtendFib_eq`.  The p = 2 special case with the
sharp exponent `n ^ 6` is `cometricTrace_rfns` (`:42`).

Consequence: part 1 of the brick collapsed to the ~25-line jet-window
corollary `dtJet` below, and the brick's real work was part 2.

Deliberately NOT used: `exists_bound_riemannianFiberNormSq_smoothCcTensor` (the
existential metric-dependent constant that `RemainderCoeffPerOrderJetEnvelopes`
still uses internally for the same field).  It cannot be uniformized; entry 202
had already rejected it for the identity coefficient, and the same rejection
applies here.

## Route

Metricwise `trace24_h2_lip` input → class-first sibling used here:

| metricwise input | class-first sibling |
| --- | --- |
| `invCoeff_h2_lip` | `invCoeff_h2_lip_unif` (`UnifInvCoeffLip.lean:351`, node 1) |
| `appRS_h2_h2_h2 g 4 4 2` | `appRS_h22_unif … 4 4 2` (`UnifAppH22.lean:70`) |
| `appRS_h2_h2_h2 g 6 6 4` | `appRS_h22_unif … 6 6 4` (same, valence-generic) |
| `J₂/J₄ = c2JetSq g (cometricDoubleTraceField g p)` | `dtJet` (here) + `volumeReal_cross` |
| `insert3_jet_c2` / `insert5_jet_c2` (private) | `ins3Jet` / `ins5Jet` (here) |

`appRS_h22_unif` is genuinely valence-generic and serves both instantiations
verbatim; the argument convention is `appRS_h22_unif hDim gBase hΛ p r c` with
`Φ : SmoothCcTensor g r c`, `W : SmoothCcTensor g p r`, output
`appCcRS g p r c Φ W`.

### `dtJet`: the parallel-field jet window

    ∑_{j<3} ‖∇ʲ (cometricDoubleTraceField g p)‖² ≤ n^(p+6) · vol(g)

Only the order-zero term survives: the field is parallel
(`cometricDoubleTraceField_covGrad_eq_zero`, rank-generic, public), and
`iteratedCovGrad_eq_zero_of_covGrad_eq_zero`
(`CovGrad/KoszulSectionParallelRaise.lean:44`, public) turns that into
`iteratedCovGrad g (p+2) p (m+1) Φ = 0` for every `m`.  The order-zero term is
`cometricTrace_rfns_p` fed through `norm_le_of_pointwise_fiberNormSq_bound_rs`.
This is the same three-step shape as entry 202's `idSlotJet`; the reusable
recipe also appears inline at `LieCorr0TraceRadiusFree.lean:255-275`.

The class step is `volumeReal_cross`, giving
`n^(p+6) · volCompareC Λ · vol_{gBase}(M)`.

### The slot-insertion jet tower

`D₂ = slotInsertEndoCc g 3 dEndo` and `D₄ = slotInsertEndoCc g 5 dEndo` must be
reduced to `slotInsertEndoCc g 1 dEndo`, which `hslot1` identifies with the
inverse-metric coefficient difference that node 1 bounds.  The monolith does
this with private `insertSucc_jet_c2` / `insert3_jet_c2` / `insert5_jet_c2`.
Re-derived here (№194) from three PUBLIC producers, generic in the slot index:

* `tsSlotInsertEndoCc_succ_eq_reindex_slotExtend`
  (`CovGrad/CurvatureCoefficientDifferenceJetTower/TsRungs.lean:1172`) — the
  public twin of the private `slotInsertEndoCc_succ_eq_reindex_slotExtend` in
  `MetricArmCoeffJetTower.lean:2725`.  Worth remembering: several `MetricArm…`
  private helpers have public `ts…` twins in `TsRungs.lean`.
* `rfns_iteratedCovGrad_rsDomDomCongr_both_eq` (`MetricArmCoeffJetTower.lean:2706`)
* `rfns_iteratedCovGrad_slotExtend_le` (`CovGrad/OperatorFieldFibreNormJet.lean:680`)

`insSuccPt` (pointwise) → `insSuccSq` (squared `L²`, via
`normSq_le_integral_of_pointwise_fiberNormSq_le_rs`) → `insSuccJet` (the `H²`
window) → `ins3Jet` (`n²`) and `ins5Jet` (`n⁴`).  These are generic in the slot
and will serve every later `_lip`/`_pair` node that carries a slot-inserted
endomorphism.

Note the public `rfns_iteratedCovGrad_slotInsertEndoCc_le_endo`
(`MetricArmCoeffJetTower.lean:2795`) bounds slot `s` by slot **0**, not by slot
1, so it is the wrong direction for this node — the succ step had to be rebuilt.
That is why `insSuccPt` exists instead of a one-line call.

### Closed constant

With `vol = volCompareC Λ · vol_{gBase}(M)`, `n = Module.finrank ℝ E`:

    A₂ = √(n^8 · vol),   A₄ = √(n^10 · vol)
    K₂ = C₂ · A₂ · (3 · Cinv),   K₄ = C₄ · A₄ · (9 · Cinv)
    C  = K₂ + K₄

`ρ` and `Cinv` are inherited verbatim from `invCoeff_h2_lip_unif`; `C₂`, `C₄`
are `appRS_h22_unif`'s constants at `(4,4,2)` and `(6,6,4)`.  The factors `3`
and `9` are `√(n²)` and `√(n⁴)` at `n = 3`, from `ins3Jet`/`ins5Jet`.

## What failed / what to avoid

* **Keep the dimension symbolic inside the constant.**  First attempt defined
  `A₂ := √(3^8 · vol)` and then tried `rw [hDim]; norm_num;
  exact mul_le_mul_of_nonneg_left hvolg (by norm_num)`.  `norm_num` reshaped the
  goal so that the multiplier of `mul_le_mul_of_nonneg_left` was still a
  metavariable when `by norm_num` ran, leaving two `⊢ 0 ≤ ?m` goals.  Fix:
  define `A₂ := √((Module.finrank ℝ E : ℝ)^8 · vol)` so no `hDim` rewrite is
  needed at all, and elaborate the nonnegativity side condition FIRST as a named
  `have hfr` before passing it.  Same pattern as node 1's `hCh`/`hCp`.
* `(finrank)^(2+6)` versus `(finrank)^8` unifies fine by `Nat` literal defeq —
  no `norm_num` needed on the exponent.
* The monolith's `simpa only [c2JetSq, K₂] using (show … by … ring ▸ h)` idiom
  for the output step is fragile; `refine (happ₂ …).trans (le_of_eq ?_)` then
  `dsimp only [K₂]; ring` is the readable equivalent and worked first try.

## Verification

Focused check GREEN (22 s, no warnings).  Targeted module build GREEN
(9929 jobs).  Axiom probe run through a temporary scratch module (`lake env
lean` suppresses `#print axioms`), deleted afterwards:
`trace24_h2_lip_unif`, `cometricTrace_rfns_p` and `invCoeff_h2_lip_unif` each
depend on `[propext, Classical.choice, Quot.sound]` only.

---

# G3 lane node 3 — `pairTrace_h2_lip_unif` (entry 214)

Status: **LANDED sorry-free** (2026-08-07), same file.  Entry 209's prediction
that this node would be MECHANICAL scored **TRUE**: it compiled green on the
first focused check, in 26 s, needing **no `set_option maxHeartbeats`** at all
(the metricwise `pairTrace_h2_lip` carries `1600000`).

## What it provides

The class-uniform sibling of the private metricwise `pairTrace_h2_lip`
(`…C2Lip.lean:1569`, READ-ONLY).  One `ρ` and one `C` from `(gBase, Λ)`; for
every class metric `g`, the pair contraction `lieCovPair g gm` of the two moving
double traces is Lipschitz, in `∑_{j<3} ‖∇ʲ ·‖²` at valence `(6, 2)`, in the
`H²` distance of the perturbations.  Class hypothesis pair is the ruled one, as
in node 2.

## Route

| metricwise input | class-first sibling |
| --- | --- |
| `trace24_h2_lip` | `trace24_h2_lip_unif` (node 2, this file) |
| `appRS_h2_h2_h2 g 6 4 2` | `appRS_h22_unif … 6 4 2` (verified: `Φ : g 4 2`, `W : g 6 4`, out `g 6 2`) |
| `J₂ = c2JetSq g (pureTrace g g 2)` | `ptDiag … 2` = `ptSelf` + `dtJet` + `volumeReal_cross` |
| `J₄ = c2JetSq g (pureTrace g g 4)` | `ptDiag … 4`, same |
| `jet3_add_c2` / `jet3_nonneg_c2` (private) | `jetAdd` / inline (here) |
| `LowBaseInternal.pairTrace_eq` | reused directly — it is PUBLIC (`…LowBaseAction.lean:9000`) |

**`ptSelf` is a bare `rfl`, not the predicted `SmoothCcTensor.ext`.**
`pureTrace g₀ g₁ p := pureDoubleTraceField g₀ g₁ p`
(`…JetTower/PairTrace.lean:1317`) and `cometricDoubleTraceField g₀ p`
(`CovGrad/CometricDoubleTraceField.lean:729`) are declared with *literally the
same three fields* once `g₁ := g₀` — same `toFun`, same `contMDiff_toFun`
producer, `hasCompactSupport := HasCompactSupport.of_compactSpace _`.  Structure
eta plus proof irrelevance makes `pureTrace g g p = cometricDoubleTraceField g p`
definitional.  The `ext` fallback (`SmoothCcTensor.ext` needs
`h : S.toSection = T.toSection`, then `DFunLike.ext`, cf.
`CometricTraceSelfBound.lean:322`) was never needed.

Private helpers added, all reusable by later `_pair`/`_bdd` nodes:

* `ptSelf`, `ptDiag` — the diagonal double-trace window, class-uniform;
* `jetAdd` — range-three subadditivity of the squared jet window;
* `jetAbs` — absolute window from (difference window + reference window),
  i.e. `A = (A - B) + B`, the step the monolith inlines as `hend₂`/`hend₄`;
* `pairSplit` — `lieCovPair g gT - lieCovPair g gU` as a sum of two
  one-difference `appCcRS` products;
* `zeroTie`, `zeroHs` — the zero-perturbation boilerplate needed to read the
  Lipschitz node at `(P, 0)` and get an ABSOLUTE bound out of it;
* `movWin` — *(added by node 4, entry 216)* the whole "read the class Lipschitz
  estimate at `(P, 0)`, add back the diagonal" block, extracted from node 3's
  in-proof `hmov`.  Node 3's public statement is byte-identical; only its proof
  body changed (`hzρ`, `hdiag₂`, `hdiag₄` and the `hcut`/`hmul` steps all moved
  inside `movWin`, and `hmov` is now four lines: `rw [hB₂sq, hB₄sq]`,
  `dsimp only [A₂, A₄, vol]`, one `movWin` call).

## Closed constant

`n = Module.finrank ℝ E`, `vol = volCompareC Λ · vol_{gBase}(M)`; `ρ`, `Ct` from
`trace24_h2_lip_unif`; `Ca` from `appRS_h22_unif … 6 4 2`:

    A₂ = n^8 · vol,             A₄ = n^10 · vol
    B₂ = √(2·((Ct·ρ)² + A₂)),   B₄ = √(2·((Ct·ρ)² + A₄))
    K₁ = Ca · Ct · B₄,          K₂ = Ca · B₂ · Ct
    C  = 2 · (K₁ + K₂)

Note `A₂`/`A₄` are the SQUARED windows here (node 2 kept them under a `√`),
because they are only ever consumed as `J ≤ A`; that removes two `Real.sq_sqrt`
round trips.  The dimension stays symbolic throughout — node 2's lesson.

## What failed / what to avoid

* Nothing failed mathematically; there was no second route attempt.
* Two mechanical linter fixes were needed after the first green:
  `omit [BoundarylessManifold I M] in` on `zeroTie` (unused section variable),
  and the final `show 2 * (…) ≤ (C * N)^2` had to become a named
  `have hend : … := …; exact hfin.trans hend` — the build (not the focused
  `lake env lean`) flags `show` used for a definitional (zeta) goal change.
  **Note the asymmetry: the focused check did NOT report the `show` warning;
  only the targeted build did.**  Do not treat a clean focused check as proof
  that a declaration is warning-free.
* `jetAdd` is now a THIRD copy of the same three-line fact (`jet3_add_c2`
  private in `…C2Lip.lean:1037`; `jetAdd` private in `UnifInvCoeffLip.lean:304`;
  and the public `lowJetSq` form `jetAdd` in
  `DeTurckRemainderLowBaseH2VB.lean:85`).  The public one was NOT reused on
  purpose: `H2VB` imports the 10.8k `DeTurckRemainderLowBaseLip` monolith, and
  the `Unif…` layer deliberately stops at `…C2Lip`.  Promoting one copy into a
  light shared module is a **dedup chip**, not this brick's job.

## Verification

Focused check GREEN (25.7 s, no warnings).  Targeted module build GREEN
(9930 jobs, incl. the probe module).  Axiom probe through a temporary scratch
module, deleted afterwards:

    'DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.pairTrace_h2_lip_unif'
      depends on axioms: [propext, Classical.choice, Quot.sound]

No `sorryAx` anywhere in the build output.

## New public declarations (census additions deferred)

`trace24_h2_lip_unif` (node 2), `pairTrace_h2_lip_unif` (node 3),
`pairTr_h2_bdd_unif` (node 4).  Everything else in the file is `private`.

---

# G3 lane node 4 — `pairTr_h2_bdd_unif` (entry 216)

Status: **LANDED sorry-free** (2026-08-07), same file (784 → 913 lines).  Entry
214's prediction that this node would be MECHANICAL *and shorter than the
metricwise route* scored **TRUE on both halves**: first focused check green in
24.9 s with **no `set_option maxHeartbeats`** (the metricwise `pairTrace_h2_bdd`
carries `1200000`), and the proof is a factor-by-factor bound with no
`(T, 0)`-reading and no diagonal `lieCovPair g g` window at all.

## What it provides

The class-uniform sibling of the private metricwise `pairTrace_h2_bdd`
(`…C2Lip.lean:1794`, READ-ONLY).  One `ρ` and one absolute size `B`, both
selected from `(gBase, Λ)` before the class metric varies; for every class
metric `g` and every `H²`-small perturbation `T` tying `gT` to `g`, the pair
contraction satisfies `∑_{j<3} ‖∇ʲ (lieCovPair g gT)‖² ≤ B²` at valence
`(6, 2)`.  The conclusion is ABSOLUTE — no `‖T‖` factor — exactly mirroring the
metricwise statement.  Class hypothesis pair is the ruled one (nodes 2 and 3).

## Route — the SHORT one, not the metricwise mirror

The metricwise proof reads its own Lipschitz theorem at `(T, 0)` and then adds
back the diagonal window `J = c2JetSq g (lieCovPair g g)` via `jet3_add_c2`.
The class-first route skips that entirely:

1. `LowBaseInternal.pairTrace_eq` (PUBLIC, `…LowBaseAction.lean:9000`) gives
   `lieCovPair g gT = appCcRS g 6 4 2 (pureTrace g gT 2) (pureTrace g gT 4)`;
2. `movWin` (extracted from node 3's `hmov`) bounds BOTH factors absolutely,
   by `B₂` and `B₄`;
3. one `appRS_h22_unif … 6 4 2` call multiplies them: `≤ (Ca · B₂ · B₄)²`.

So the diagonal `lieCovPair g g` never appears, and the `jetAdd` /
`jetAbs` splitting used by node 3's endgame is not needed here — the only jet
algebra is the one already inside `movWin`.

| metricwise input | class-first sibling |
| --- | --- |
| `pairTrace_h2_lip` read at `(T, 0)` | not used — replaced by `pairTrace_eq` + `movWin` |
| `J = c2JetSq g (lieCovPair g g)` (diagonal) | not needed |
| `jet3_add_c2` | not needed |
| — | `appRS_h22_unif … 6 4 2` (the multiplying step) |
| `trace24_h2_lip_unif` | consumed only through `movWin` |

## Closed constant

`n = Module.finrank ℝ E`, `vol = volCompareC Λ · vol_{gBase}(M)`; `ρ`, `Ct` from
`trace24_h2_lip_unif`; `Ca` from `appRS_h22_unif … 6 4 2`:

    A₂ = n^8 · vol,             A₄ = n^10 · vol
    B₂ = √(2·((Ct·ρ)² + A₂)),   B₄ = √(2·((Ct·ρ)² + A₄))
    B  = Ca · B₂ · B₄

`ρ` is node 2's radius, unchanged.  `B₂`/`B₄` are literally node 3's, so the two
nodes now share one constant recipe through `movWin`.  Dimension symbolic
throughout.

## What failed / what to avoid

* Nothing failed.  No second route was attempted; the first one closed.
* The one refactor 214 named — extracting `hmov` — was done exactly as
  specified.  Guard rail respected: node 3's docstring and signature
  (`UnifTraceLip.lean:688–721`) are byte-identical to the pre-edit text, and its
  axiom probe was re-run to confirm nothing moved.
* Two small `dsimp`/`rw` bridges are needed because the `A₂`, `A₄`, `vol`, `B`
  constants are `let`-bound: `rw [hB₂sq]; dsimp only [A₂, vol]; exact hraw₂` to
  turn `movWin`'s explicit-volume RHS into `B₂ ^ 2`, and `dsimp only [B]` before
  the final `happ` call.  Do NOT reach for `show` here — that is precisely the
  zeta-goal-change pattern the build linter flagged in node 3.
* `ptDiag`'s exponent is `p + 6`; `movWin`'s statement writes `8` and `10`.
  `exact` closes the gap by `Nat`-literal defeq, as node 3 already relied on.

## Verification

Focused check GREEN (24.9 s), first pass, no repair.  Targeted module build
GREEN (`Built …ShortTime.UnifTraceLip (22s)`, 9929 jobs).  **Build warnings were
read for this file specifically** — per node 3's lane-discipline finding, the
module was force-re-elaborated (deleting its `.trace` and `.olean.hash`; a bare
`touch` does NOT invalidate lake's content-hash trace) and the full log grepped:
**zero** warning lines mention `UnifTraceLip.lean`.  Axiom probes through a
temporary scratch module, deleted afterwards:

    'DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.pairTr_h2_bdd_unif'
      depends on axioms: [propext, Classical.choice, Quot.sound]
    'DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.pairTrace_h2_lip_unif'
      depends on axioms: [propext, Classical.choice, Quot.sound]

No `sorryAx` anywhere in the build output.

**Name compliance:** `pairTr_h2_bdd_unif` is 18 characters — inside the
project's 20-character budget, unlike node 3's tolerated 21-char
`pairTrace_h2_lip_unif`.

## Next node up the lane

`curvMono_h2_lip` (private, `…C2Lip.lean:1880`, `set_option maxHeartbeats
1800000`) — the second consumer of `pairTrace_h2_lip`, and it needs BOTH the
Lipschitz node and the bound node, which are now the two theorems above.  It is
**pre-flagged NOT mechanical**: it adds the curvature-refold monomial machinery,
which has no class-first sibling yet.  Per entry 215, a READ-ONLY scout goes
first — do not attempt it as a direct executor brick.

The third and last consumer of `pairTrace_h2_lip` is the public `lowJetSq`-form
export wrapper `LowBaseInternal.pairTrace_pair_h2` (`:4655`).
