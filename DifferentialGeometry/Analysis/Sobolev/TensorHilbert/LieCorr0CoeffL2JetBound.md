# LieCorr0CoeffL2JetBound

New leaf (RULING 1, planner acceptance №19): the `TensorHilbert/` home of the
`lieCorr0Field` realizedFam jet-L2 top-separated producer (2nd genuinely-missing
`C₀` constituent of `Ψ₀`).  Namespace `DifferentialGeometry.Integral.Connection`.

Endpoints (deferred until all four Kc atoms land, see below):
`lieCorr0Field_realizedFam_jetL2_{perOrder,summed}_topSeparated`, shapes verbatim
= the deTurckLie siblings `DeTurckLieCoeffL2JetBound.lean:739/799`, `Ktop`
R-free (from the DLb top piece), single summed `Kc`.

## State (2026-07-25): diamond RESOLVED; RE-RECON DONE; verdict POSITIVE (no LowJet).

The TensorRS TotalSpace topology-instance diamond that blocked `LieCorr0Split`
is FIXED (commit `55efbcbd7`): `LieCorr0Split` now BUILDS lake-green.
`LieCorr0LowJet` is an ABANDONED DEEP-WIP draft (~40 pre-existing errors: syntax
errors at :1381/:1520/:1598, undefined `lieCorr0IVPerm`, unimported
`ccTensorBilinSymm`/`gFibreOpBound`, embedded `sorry`s, genuine proof failures —
see `LieCorr0LowJet.md`).  It is a LIABILITY, quarantined, NOT an asset.  This
leaf must therefore be built WITHOUT LowJet.  (The full diamond saga is retired;
its blow-by-blow lived in this note's earlier revisions and is superseded.)

### BANKED GREEN (2026-07-25 build session): the TOP piece + assembly helper
- `endoArm_eq_dlb` : `deTurckLieEndoArmField g₀ g₁ g_bg = deTurckLieDLbCoeffField
  g₀ g₁ g_bg` (both `ofCLM(deTurckLieDLbFib g₁ g_bg)`, by `ext`).
- `lc0Insert_base_eq_neg_dlb` : `lc0Insert g₀ g₁ g₀ = −deTurckLieDLbCoeffField
  g₀ g₁ g₀`.
- `lc0InsertBase_realizedFam_perOrder_topSeparated` : the top piece's per-order
  top-separated bound, inherited verbatim from the committed DLb field producer
  at `g_bg := g₀`; `Ktop = Ktop_DLb` (R-free).
- `sq_le_five_add` : `t ≤ a+b+c+d+e` (all ≥0) ⟹ `t² ≤ 5(a²+…+e²)`.

## The 5-way split (field level)

`lc0_decomp` (`LieCorr0Split.lean:169`): `lieCorr0Field g₀ g₁ g_bg = ((lc0Insert
g₀ g₁ g_bg + lc0VB g₀ g₁) + lc0AMix g₀ g₁ g_bg) + lc0Riem g₀ g₁`.  Split the
insert piece `lc0Insert g_bg = lc0Insert g₀ + (lc0Insert g_bg − lc0Insert g₀)`
(the base insertion is the top; the difference is a Kc piece):

    lieCorr0Field = lc0Insert g₀    [TOP,  Ktop R-free via DLb]
                  + (lc0Insert g_bg − lc0Insert g₀)   [Kc]
                  + lc0VB            [Kc]
                  + lc0AMix          [Kc]
                  + lc0Riem          [Kc]

Ruling 2 discipline: the four Kc pieces are `∇²T`-free (each `∇ⁱ` reaches at most
`∇^{i+1}T`, well inside the `∑_{j<i+3}` window) and carry `R` in `Kc` only; the
top piece keeps the R-free `Ktop`.  `sq_le_five_add` fans the 5-way sum out to
`Ktop = 5·Ktop_DLb`, single summed `Kc`.

## RE-RECON VERDICT (2026-07-25) — POSITIVE.  All four Kc pieces build from committed generic engines; LowJet's refolds are NOT needed.

The old plan (acceptance №19) lifted the four Kc pieces via LowJet's
`vb_refold`/`amix_refold`/`riem_refold`/`insert_diff` refolds.  That premise is
DEAD (LowJet is broken WIP).  Fresh recon of the committed tree shows the
refolds are unnecessary: a fully generic "cometric-trace of a product of two
order-1 factors → jet-L2 ball-uniform" engine already exists and covers all four
pieces.  NO salvage-port from LowJet is required.

### The reusable generic engine (the linchpin)
- **Pointwise Leibniz product-grid**: `rfns_iteratedCovGrad_appCcRS_diagonalProductGrid_rankLeft_le`
  (`MetricArmCoeffJetTower.lean:2360`).  For the cometric contraction
  `appCcRS g p a b Φ W` (= `traceStep`-cometric ∘ `prodKappa(Φ)` ∘ `W`):
  `rfns(∇^j appCcRS Φ W) ≤ appCcGdiag j · ∑_{i<j+1} rfns(∇^i Φ) · ∑_{l<j+1-i} rfns(∇^l W)`.
  Proved by induction via `covGrad_appCcRS_eq` (Leibniz).  `appCcRS` is exactly
  `traceStep ∘ prodKappa`; `tensor0SProdKappaFib` (`DeTurckLieHigherOrderCoeffField.lean:389`)
  is the underlying `prodKappa`.
- **Integrator (ball-uniform, R in constant)**:
  `exists_integrated_iteratedCovGrad_diagonalProductGrid_twoArm_rs_le`
  (`RemainderCoeffPerOrderJetEnvelopes.lean:870`): for two fields S,T with
  order-0 sups `ΛS,ΛT`, `∫ ∑_i rfns(∇^i S)·∑_l rfns(∇^l T) ≤ C·(ΛT²·∑‖∇^i S‖² +
  ΛS²·∑‖∇^l T‖²)` (Moser split + Gagliardo–Nirenberg).  This is the ballUniform
  integrator (NOT `antidiagonalTupleGrid_integral_ballUniform_tameWindow`, which
  is used only in the topSeparated tower).
- **Committed end-to-end precedent** for the exact lc0VB shape:
  `deTurckLieArm1Coeff_realizedFam_jetL2_perOrder_ballUniform`
  (`DeTurckLieArm1CoeffL2JetBound.lean:4812`) — "g₁-cometric trace of
  connection-difference × interior-product(deTurckVF)"; its per-piece glue
  `lieArm1_appCc12_normSq_le` (:1853) and sub-producers
  `lieArm1Piece_connDiff_realizedFam_jetL2_perOrder_ballUniform` (:4209) /
  `lieArm1Piece_connDiffBg_…` (:4311) combine layers 1+2.
- **ballUniform → topSeparated (Ktop=0) reshape**: the traceHess/Moser pattern —
  `P i ≤ 0·(top) + P i·(1 + low)` by `nlinarith` (see `TraceHessJetL2Summed.md`).

### Atom availability (agent-verified)
- `connDiff` / `connDiffSection` / `connDiffLoweredCc` (Atom 3): RICHLY controlled
  pointwise — `rfns_iteratedCovGrad_connDiffSection_le`
  (`ConnectionDifferenceJetTower.lean:1638`) + order-0/order-1 fibre bounds +
  envelope packagers.
- `metricConnDiffLoweredFib g₁ g₁ g'` (Atom 1): NO direct jet bound under its own
  name.  Only route is its `_toModel` identity `= gm.inner(connDiff gA gB v₀ v₁)
  v₂` (`DeTurckLieHigherOrderCoeffField.lean:460`) → push through Atom 3.
  **Mismatch to watch**: it lowers by **g₁** (moving), whereas the committed
  connDiff bounds lower by **g₀** (background) — the reduction must absorb the
  g₁-vs-g₀ lowering (the Arm1 file already handles this via
  `lieArm1_deTurckVF_cometric_trace`, `DeTurckLieArm1CoeffL2JetBound.lean:2897`).
- raw `deTurckVF g₁ g'` (Atom 2): NO direct jet bound; its jet control lives on
  the `deTurckLieWEndoInsert` endomorphism (= ∇W + connDiff·W) and, for the raw
  contraction, on the DLb low atoms `wOmega`/`wXi`
  (`DeTurckVectorFieldL2JetBound.lean` `_lowOrder_jetL2_succ_generic`).

### Per-summand routing

| Kc piece | fibre structure (`LieCorr0Core.lean`) | committed route | effort |
|---|---|---|---|
| `lc0VB` | `2·traceStep(g₁,VBPerm) ∘ prodKappa(metricConnDiffLoweredFib g₁ g₁ g₀) ∘ interior_product(deTurckVF g₁ g₀)` (:144) | twoArm engine (Φ = metricConnDiffLowered→connDiff, W = deTurckVF interior-product); closest to `deTurckLieArm1Coeff` (same atoms, different contraction — NOT a reindex) | MEDIUM |
| `lc0AMix` | `2·(AMixHalf + swap·AMixHalf)`, `AMixHalf` = chain of traceSteps over prodKappa(metricConnDiffLoweredFib g₁ g₁ g_bg) and prodKappa(metricConnDiffLoweredFib g₁ g₁ g₀) (:162) | twoArm engine, both factors connection-difference (via Atom-3 push) | MEDIUM |
| `lc0Riem` | `−traceStep(g₁,RiemPerm2) ∘ traceStep(g₀,RiemPerm1) ∘ prodKappa(lieCorr0RiemLoweredFib g₀)` (:237); passenger = FIXED g₀-curvature `g₀.inner∘riemannOp(LC g₀)` | **DONE — see "lc0Riem: the route that worked" below.**  Neither of the two guessed routes was used: the winner was twoArm with the live arm *reduced to the committed rank-1 cometric envelope via `slotExtend` + a source 3-cycle reindex* | landed |
| `lc0Insert g_bg − lc0Insert g₀` | `slotInsert(NEndo g_bg − NEndo g₀)`; by `nEndo_diff` (`LieCorr0Split.lean:103`) = `slotInsert(connDiff g₁ g₀ (deTurckVF g₁ g₀ − deTurckVF g₁ g_bg))` | **STATED, ONE `sorry` — see "lc0Insert-diff: the missing engine" below.**  The recon guess ("twoArm engine, deTurckVF-diff via DLb wOmega/wXi") was WRONG in a fatal way: the product is an *interior-product contraction*, not the operator *composition* the appCcRS grid covers, and the deTurckVF machinery it needs is all `private` | **blocked (missing engine)** |

All four go to `Kc` (R allowed).  Only the top piece needs the R-free `Ktop`,
already delivered via DLb.

## lc0Riem: the route that worked (2026-07-25 build session)

`lieCorr0RiemFib = (−1)·(traceStep(g₁,2,Perm2) ∘ traceStep(g₀,4,Perm1) ∘ prodKappa(Riem g₀))`.
Only the OUTER `g₁`-cometric moves; everything to its right is `g₀`-only.  So push
the outer permutation `Perm2` into the passenger and read the piece as a two-arm
action:

    lc0Riem g₀ g₁ = − appCcRS g₀ 2 4 2 (live (4,2) arm) (fixed (2,4) passenger)

- **live arm** = the rank-`2` `g₁`-cometric double trace `cometricDoubleTraceFib g₁ 2`.
- **passenger** = `domDomCongrFibRank(Perm2) ∘ traceStep(g₀,4,Perm1) ∘ prodKappa(Riem g₀)`,
  built directly with `contMDiff_clm_section_of_pointwise` off the three committed
  `LieCorr0Core` smoothness lemmas (`lieCorr0_prod_section_contMDiff`,
  `lieCorr0TraceStep_section_contMDiff`, `lieCorr0_ddc_section_contMDiff`).

**The key move — do NOT re-derive the cometric envelope at `p = 2`.**  The committed
envelope `cometricDoubleTraceField_order0sup_jetL2_ballUniform_generic` is stated only
for `cometricCastG0` (`p = 1`, valence `(3,1)`); re-deriving its ~250-line proof at
`p = 2` was the obvious-but-wrong plan.  Instead:

    cometricDoubleTraceFib g₁ 2 = reindexCoeffGen(σ) (slotExtend (cometricCastG0 g₀ g₁))

with `σ : Equiv.Perm (Fin 4)` the source three-cycle `0↦1↦2↦0` (identity on slot 3).
Reason: `slotExtend` reads the new passenger slot as the LEADING SOURCE slot, whereas
the rank-`2` double trace contracts slots 0,1 and puts the passenger third — the two
tuples `(v₀, Lb^k, b_k, m)` and `(Lb^k, b_k, v₀, m)` differ by exactly that 3-cycle.
Both TARGET slot orders already agree, so no target permutation is needed.  Then
`rfns_iteratedCovGrad_reindexCoeffGen_eq` (source permutation is `rfns`-invariant) +
`rfns_iteratedCovGrad_slotExtend_le` (costs one factor `finrank ℝ E`) transport BOTH
the order-`0` sup and the jet-`L²` sums from `p = 1` to `p = 2` in six lines.

Rest of the pipeline is the standard layer idiom: pointwise product grid
`rfns_iteratedCovGrad_appCcRS_diagonalProductGrid_rankLeft_le`, then
`normSq_le_integral_of_pointwise_fiberNormSq_le_rs` against the integrator
`exists_integrated_iteratedCovGrad_diagonalProductGrid_twoArm_rs_le` (`choose`d over the
order `k`, since it is stated per-`k`), then the `realizedFam` threading copied from
`gInvDiffSlotCoeff_realizedFam_perOrder_l2_ballUniform`, then `Ktop = 0` and
`Kc i ≤ Kc i · (1 + low)` by `nlinarith`.

## SESSION STATE (2026-07-25, first build session — superseded by the insert-diff session below for the resumption point)

### What is verified-green now (vs the previous session, which banked NOTHING)
The previous session ran no build at all and left the leaf importing broken
`LieCorr0LowJet`.  That import is now DELETED and the leaf is **fully green,
sorry-free and warning-free**, verified by a real targeted module build (not only a
focused check — `lake env lean` success alone is untrustworthy in this repo).
Axiom-audited to exactly `[propext, Classical.choice, Quot.sound]`:

- `endoArm_eq_dlb`, `lc0Insert_base_eq_neg_dlb`,
  `lc0InsertBase_realizedFam_perOrder_topSeparated` (TOP piece), `sq_le_five_add`
  — the four previously-drafted theorems, which **survived contact with the compiler
  essentially unchanged**; no mathematical repair was needed.
- `lc0Riem_realizedFam_perOrder_topSep` — **the first Kc atom, NEW and green**,
  with its supporting layer `lc0RiemSrc`, `lc0RiemLive`, `lc0RiemLive_toSec`,
  `lc0RiemPassFib(+_contMDiff)`, `lc0RiemPass`, `lc0RiemFib_eq`, `lc0Riem_eq_app`,
  `lc0RiemLive_rfns_le`, `lc0RiemLive_l2_le`.

The four drafted theorems needed only *plumbing* repair, never mathematical repair:
a missing `LieCorr0Split.olean` (the leaf is outside the root import graph, so its
own imports had never been built — build the import first, or the focused check dies
on a missing olean), and two inherited unused-binder-name warnings, silenced with the
layer's own `set_option linter.unusedVariables false in` idiom.

### Lean lessons from this session
- **Namespaces bite hardest.**  Four separate `unknownIdentifier` rounds, all from the
  leaf's *restricted* `open ... (a b c)` lists.  `reindexCoeffGen`/`domDomCongrFibRank`/
  `tensor0SProdKappaFib` are `Analysis.Parabolic.TensorSpectral`;
  `convexPerturbation`/`convexPerturbation_gFibreOpBound`/`realizedFam_inner_of_mem`/
  `Icc_subset_realizedSmallSet` are `PDE.DeTurck.RicciLinearization` (same home as
  `realizedFam`); `cometricDoubleTraceFib` is `…IntrinsicSpectral.DeTurck`;
  `lieCorr0*` needs `open LieCorr0Core`; `tensor0S_curry_apply_eval` is
  `TensorMultilinear`.  Widen the restricted lists rather than doing a bare full
  `open` (the restriction is deliberate).
- `iteratedCovGrad_smul_real` has **no public home** — it exists as a copy-pasted
  `private theorem` in at least four files.  A fifth copy was added here; the real fix
  is one public lemma in the `iteratedCovGrad` module (flagged as a separate task).
- Two different instantiations of the same `@[simp]` lemma in one goal: `rw` picks one
  instantiation and the second `rw` then fails.  Use `simp only [lemma]` instead.
- `(-1 : ℝ) • A` is NOT `rfl`-equal to `-A` for CLMs — `neg_one_smul` first.  But
  `.comp` associativity IS defeq, so after that a bare `rfl` closes the fibre identity.
- `add_le_add_right` in this Mathlib adds on the LEFT of the displayed goal; prefer
  `linarith` from the `mul_le_mul_of_nonneg_left` step over guessing the orientation.
- A `Select-String | Select-Object -First N` pipeline over a `lake build` makes the
  build report exit 255 (broken pipe) even when it succeeded — redirect to a file, then
  filter.

## lc0Insert-diff: the missing engine (2026-07-25 second build session)

**Status: STATED with the correct full signature, ONE isolated `sorry`.**  The atom
`lc0InsertDiff_realizedFam_perOrder_topSep` (top-separated, `Ktop = 0`, signature verbatim
= `lc0Riem`/top-piece) is proved from a single `ballUniform` frontier lemma
`lc0InsertDiff_ballUniform` (the `sorry`) by the trivial reshape `K i ≤ K i·(1+low)`
(`nlinarith`).  The `sorry` is the ONLY gap; `#print axioms` confirms the atom carries
`sorryAx` and nothing else new, while the four banked theorems + `lc0Riem` stay exactly
`[propext, Classical.choice, Quot.sound]`.

### Why the recon route (and the "mirror lc0Riem" plan) FAILED — read before retrying
The endomorphism is `Endo = connDiff g₁ g₀ (deTurckVF g₁ g₀ − deTurckVF g₁ g_bg)`
(`nEndo_diff`): the moving connection difference `connDiff g₁ g₀` **contracted** with the
deTurckVF-difference `Vdiff`.  Three things make this NOT a recombination of the committed
`lc0Riem` machinery:

1. **The product is an interior-product contraction, not an operator composition.**  The
   committed product grid `rfns_iteratedCovGrad_appCcRS_diagonalProductGrid_rankLeft_le`
   (and `appCc_iteratedCovGrad_diagonalProductGrid_le`) are for `appCcRS`/`appCc` =
   composition of `(0,·)`-operators.  `connDiff·Vdiff` contracts a lower slot with a
   vector.  Grepped the whole tree: there is **no `clm_apply`/`endoApply`/interior-product
   Leibniz jet product grid**.  (`lc0Riem` worked precisely because its live factor was a
   cometric *double trace* = an `appCcRS` after `slotExtend`+reindex; no analogue here.)
2. **The `deTurckLieWEndo`-difference route is provably circular.**  `wEndo_eq_covDeriv_add_connDiff`
   gives `WEndo g₁ g_ref = ∇^{g₀}(dVF) + connDiff·dVF`, so
   `Endo = (WEndo g₁ g₀ − WEndo g₁ g_bg) − ∇^{g₀}(Vdiff)`.  But `∇^{g₀}(Vdiff) = (WEndo diff) − Endo`,
   so the identity collapses to `Endo = Endo`.  `WEndo`-difference producers
   (`deTurckLieWEndoInsert_realizedFam_jetL2_perOrder_ballUniform`) do NOT isolate `Endo`.
3. **The natural committed home is `private`.**  Inside `deTurckLieWEndoInsert_eq_cometricRaise`
   (`DeTurckVectorFieldL2JetBound.lean`) the connDiff·dVF part of `WEndo` is exactly
   `cometricRaise(wAlphaB)`, with `wAlphaB = appCc(wCA, wOmega)` — and `Endo` (the g₀↔g_bg
   difference) is `cometricRaise(appCc(wCA, wOmega(·,g₀) − wOmega(·,g_bg)))`, an `appCc`
   product that the committed `appCc` grid + `wOmega_L2_topsep` *could* control.  But
   `wAlphaB`, `wCA`, `wOmega`, `wXi` are **all `private`** in that file, and the identity
   `slotInsert(connDiff·dVF) = cometricRaise(wAlphaB)` is buried, not exposed.

### The precise missing engine (what the next agent must build first)
A public jet-`L²` `ballUniform` producer for the `(1,1)` endomorphism
`connDiff g₁ g₀ (deTurckVF g₁ g₀ − deTurckVF g₁ g_bg)` (equivalently the `(2,2)` insert-diff
after the DLb-style slotInsert-sum decomposition + `slotInsertEndoCc_le_endo` reduction —
that plumbing IS committed and cheap, mirroring `deTurckLieDLbCoeffField_eq_slotInsert_sum`
/ `rfns_iteratedCovGrad_dlbSlotZero_le`).  Cleanest realization: in
`DeTurckVectorFieldL2JetBound.lean`, **expose** `wCA`, `wOmega`, and the identity
`slotInsertEndoCc g₀ 0 (connDiff g₁ g₀ (dVF g₁ g_ref)) = cometricRaiseSlot0Field(wAlphaB g₀ g₁ g_ref)`
as public lemmas, then the insert-diff endomorphism = `cometricRaise(appCc(wCA, wOmega-diff))`
is controlled by `appCc_iteratedCovGrad_diagonalProductGrid_le` + `wOmega`'s committed
top-separated producer + the cometricRaise jet bound.  (Alternative: a general
interior-product Leibniz jet grid at the tensor layer — larger, more reusable.)
NB: touching `DeTurckVectorFieldL2JetBound.lean` is a *different file* — coordinate the claim.

### Resumption order for a successor
1. **Unblock the missing engine** (above) — expose the private `wCA`/`wOmega`/`wAlphaB`
   layer, or add the interior-product grid — then discharge `lc0InsertDiff_ballUniform`.
2. `lc0VB`, then `lc0AMix` (routing table).  Both are ALSO connDiff×deTurckVF interior
   products (`interior_product(deTurckVF)`), so the SAME missing engine unblocks all three
   remaining atoms — build it once, reuse three times.  `lc0Riem` was the only atom whose
   live factor was a pure cometric trace (hence the only clean-recombination atom).
3. Assemble the two endpoints ONLY once all four Kc atoms are green (`sq_le_five_add`).
   `Ktop = 5·Ktop_DLb` (R-free), single summed `Kc`.
4. The leaf is outside the root import graph — verify with a targeted module build, and
   build its imports first (a bare focused check dies on a missing `.olean`).

## Honest accounting
`(N) ricci_flow_unif_existence` still **0%**.  The constituent is NOT closed: the two
endpoints are **0% (still unstated)**.  Dedicated machinery = top piece (done) + four Kc
atoms (**1 of 4 GREEN: `lc0Riem`; 1 of 4 STATED-with-`sorry`: `lc0Insert`-diff; 2 unstarted:
`lc0VB`, `lc0AMix`**) + the 5-way assembly (helper `sq_le_five_add` done, wiring pending).
Counting only sorry-free content (top + `lc0Riem`) against a top+4-atoms+assembly
denominator: **~33%** — UNCHANGED from the previous session, because this session's atom is
not sorry-free.  What DID advance: the insert-diff is now correctly *stated* (was unstated),
and — the real deliverable — the frontier is *pinned*: a single missing engine
(interior-product/`wAlphaB` jet control) blocks THREE of the four Kc atoms, so building it
once is the highest-leverage next move.

## Verification
Focused check + trustworthy targeted module build both succeed with **exactly one `sorry`**
(`lc0InsertDiff_ballUniform`, line 504).  `#print axioms`: the four banked + `lc0Riem` are
`[propext, Classical.choice, Quot.sound]`; `lc0InsertDiff_realizedFam_perOrder_topSep` is
`[propext, sorryAx, Classical.choice, Quot.sound]` (honest — the atom is stated, not proved).
No commit made.
