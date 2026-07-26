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
- `iteratedCovGrad_smul_real` — RESOLVED 2026-07-25: the copy here was deleted; use the public
  `iteratedCovGrad_smul` from `Analysis/Spectral/Tensor/CovGrad/IteratedCovGradLinear.lean`
  (next to `iteratedCovGrad_add`; in scope via `open DifferentialGeometry.PDE.RicciFlow`).
  Same cleanup applied to the four other listed copies; six same-named copies remain elsewhere
  (LowRegRicciOne, LowRegCoeffJets, RicciArmResidualFieldGridWindow, RemainderCoeffL2JetMoser,
  DLaTopSeparated, DeTurckVectorFieldL2JetBound) plus ~10 alias-named ones — separate task.
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

### THE CANCELLATION (session-3 key result — frontier partially DISSOLVED for this atom)
The interior-product frontier does NOT actually survive for `lc0Insert`-diff.  The
`g₀↔g_bg` difference **cancels the moving factor**.  Chain (all in
`DeTurckVectorFieldL2JetBound.lean`, `wEndo_eq_covDeriv_add_connDiff` gives the wAlphaB↔connDiff·dVF
match):

    slotInsert(Endo) = cometricRaise(wAlphaB(g₀,g₁,g₀) − wAlphaB(g₀,g₁,g_bg))
                     = cometricRaise(appCc(wCA g₀ g₁, wOmega(g₀,g₁,g₀) − wOmega(g₀,g₁,g_bg)))

and the **wOmega-difference collapses** because `wCA`/`cometricCastG0` are the SAME at both
refs while the `wXi` connDiff-parts telescope:

    wOmega(g₀,g₁,g₀) − wOmega(g₀,g₁,g_bg) = appCc(cometricCastG0 g₀ g₁, wXi g₀ g_bg g₀)   [FIXED passenger]

This is **`wOmegaDiff_eq`**, now LANDED GREEN + axiom-clean (`[propext, Classical.choice,
Quot.sound]`) in `DeTurckVectorFieldL2JetBound.lean` (with helper `appCc_sub_right`).  So the
endomorphism is `cometricRaise(appCc(wCA, appCc(cometricCastG0, wXi g₀ g_bg g₀)))` — a
moving-cometric-on-**FIXED**-passenger `appCc` chain, the exact `lc0Riem` shape, NOT a generic
interior-product contraction.  The generic contraction-Leibniz engine question survives ONLY
for `lc0VB`/`lc0AMix` (whose deTurckVF is NOT a difference, so no cancellation) — re-assess there.

### Remaining assembly (all committed-generic — NO new frontier), layer order
1. **hoist** (highest single-reuse piece; SKIPPED session-3 for budget):
   `slotInsertEndoCc g₀ 0 (connDiffDVF g₀ g₁ g_ref) = cometricRaiseSlot0Field g₀ 0 (wAlphaB g₀ g₁ g_ref)`
   — extract from `deTurckLieWEndoInsert_eq_cometricRaise`'s proof body (the connDiff half; mirror
   `cotangentToDual_cometricRaise_wAlpha` for wAlphaB alone). ~40–60 lines cotangentToDual algebra.
2. **W1 producer** (`appCc(cometricCastG0 g₀ g₁, wXi g₀ g_bg g₀)`, moving cometric × FIXED):
   `appCc_iteratedCovGrad_diagonalProductGrid_le` + `cometricCastG0_order0sup_jetL2_succ_generic`
   (order-0 sup + jet sums, already generic-in-g₁ via htie) + `wXi g₀ g_bg g₀` fixed bounds.  This
   IS the `lc0Riem` recipe (moving-cometric-on-fixed).
3. **W2 producer** (`appCc(wCA g₀ g₁, W1)`, two moving arms): `appCc` grid + wCA jets (via
   `rfns_iCG_wCA_eq_connDiffSection` → `connDiffSection` producers) + W1 producer (layer 2).
4. **cometricRaise**: `cometricRaiseSlot0Field` jet bound → the `(1,1)` endomorphism producer.
5. **(2,2)→(1,1) reduction IN THE LEAF**: mirror `deTurckLieDLbCoeffField_eq_slotInsert_sum`
   (slotInsert-sum decomposition) + `rfns_iteratedCovGrad_dlbSlotZero_le`/`dlbSlotOne_le`
   (`slotInsertEndoCc_le_endo` + `rsDomDomCongr_both_eq`) + `sq_le_two_add`; then discharge
   `lc0InsertDiff_ballUniform`.  The leaf's own `nEndo_diff` gives `Endo = NEndo g_bg − NEndo g₀`.
6. Thread `realizedFam` (all producers are generic-in-g₁ via the `htie`/P interface).

### Resumption order for a successor
1. Do the **hoist** (layer 1) — public named lemma in `DeTurckVectorFieldL2JetBound.lean`.
2. Build layers 2→4 (the endomorphism `(1,1)` producer), then discharge `lc0InsertDiff_ballUniform`
   via layer 5.  `lc0Riem` + `wOmegaDiff_eq` are the working templates; NO new frontier remains
   for THIS atom.
3. `lc0VB`, then `lc0AMix` — these do NOT get the cancellation (deTurckVF not a difference); the
   generic interior-product/contraction-Leibniz engine question is LIVE there, re-assess then.
4. Assemble the two endpoints ONLY once all four Kc atoms are green (`sq_le_five_add`).
5. The leaf is outside the root import graph — verify with a targeted module build, and build its
   imports first (a bare focused check dies on a missing `.olean`).

## Honest accounting
`(N) ricci_flow_unif_existence` still **0%**.  The constituent is NOT closed: the two
endpoints are **0% (still unstated)**.  Dedicated machinery = top piece (done) + four Kc
atoms (**1 of 4 GREEN: `lc0Riem`; 1 of 4 STATED-with-`sorry`: `lc0Insert`-diff; 2 unstarted:
`lc0VB`, `lc0AMix`**) + the 5-way assembly (helper `sq_le_five_add` done, wiring pending) +
the shared engine infrastructure (`wOmegaDiff_eq` keystone landed, engine assembly pending).
Sorry-free-content fraction: **~33%** (top + `lc0Riem`), still — the `lc0Insert`-diff atom
remains sorried.  What session-3 advanced: (a) the **cancellation** — `lc0Insert`-diff is NOT
a generic-interior-product frontier, it reduces to the `lc0Riem` moving-cometric-on-fixed
shape; (b) the `wOmegaDiff_eq` keystone verified green.  Honest sessions-to-atom-2-green with
the cancellation in hand: **~1–2** (the hoist + 4 producer layers + leaf reduction are all
committed-generic, but intricate in a 4165-line file with slow checks).

## Verification (session 3)
Leaf UNCHANGED (still one honest `sorry` at `lc0InsertDiff_ballUniform`, line 504; atom stated,
carries `sorryAx`).  Producer file `DeTurckVectorFieldL2JetBound.lean`: two keystone lemmas
added — `appCc_sub_right`, `wOmegaDiff_eq` — verified via targeted module build (green, `Built …
DeTurckVectorFieldL2JetBound (98s)`); both axiom-audited `[propext, Classical.choice, Quot.sound]`.
Hoist SKIPPED (budget).  No commit made.

## SESSION 4 — the SIMPLER route: ballUniform needs NO cancellation (`wOmegaDiff_eq` unused here)

**Key realization.**  The atom `lc0InsertDiff_ballUniform` needs only a *ballUniform* per-order
bound `‖∇^i(lc0Insert g_bg − lc0Insert g₀)‖² ≤ K i` (no top term).  The `wOmegaDiff_eq`
cancellation + W1/W2 appCc-chain plan from session 3 was aimed at a SHARP top-separated bound and
is **not needed** for ballUniform.  Instead, crudely triangle the wAlphaB-difference and reuse the
committed per-order wAlphaB bound.  This collapses "layers 2–4" into two small steps.

### The route (all committed-generic; the cancellation is bypassed)
1. **`lieCorr0NEndo` = derivation-insert, linear in the endo.**  `lieCorr0InsertFib`
   (`LieCorr0Core:88`) = `slotInsertEndoFib 2 0 (NEndo) + slotInsertEndoFib 2 1 (NEndo)` (slot0+slot1
   update, LINEAR in `lieCorr0NEndo`).  So `lc0Insert(g_bg) − lc0Insert(g₀)` is the derivation-insert
   of `NEndo(g_bg) − NEndo(g₀)`, and `nEndo_diff` (`LieCorr0Split:103`) gives that endo-difference
   `= connDiff g₁ g₀ (dVF g₀) − connDiff g₁ g₀ (dVF g_bg)`.
2. **Producer `connDiffDVFSection g₀ g₁ g_ref`** (public): the smooth (1,1)-endo section
   `x ↦ connDiff g₁ g₀ x (deTurckVF g₁ g_ref x)` (smooth via `connDiffOp_homSection_contMDiff.clm_bundle_apply
   deTurckVF.contMDiff`, exactly the `hBV`/`hBW` of `lieCorr0NEndo_homSection_contMDiff`).
3. **HOIST** (producer) `slotInsertEndoCc g₀ 0 (connDiffDVFSection g₀ g₁ g_ref) =
   cometricRaiseSlot0Field g₀ 0 (wAlphaB g₀ g₁ g_ref)` — `deTurckLieWEndoInsert_eq_cometricRaise`
   with the wAlphaA (covDeriv) half DELETED; uses `wAlphaB_unitModel_apply` (:418,
   `= g₀.inner x (connDiff g₁ g₀ x (wVF g₁ g_ref x) w) u`) + `cotangentToDual_slotInsertEndoFib'` +
   a generic `cotangentToDual_cometricRaise_gen` (the existing `cotangentToDual_cometricRaise_wAlpha`
   generalized to any `(0,2)` `A`).
4. **cometricRaise is a JET ISOMETRY**: `rfns_iteratedCovGrad_cometricRaiseSlot0Field_eq`
   (`RecoveryEndomorphismJetBound:275`) ⟹ `‖∇^i cometricRaise A‖ = ‖∇^i A‖` (mirror
   `norm_iCG_wEndoInsert_eq_wAlpha`).  So NO cometricRaise-jet reasoning is needed.
5. **Per-order wAlphaB bound** (producer): extract the `hBsum` block of `wAlpha_order0_jetL2_generic`
   (:2836–2884) as a standalone `wAlphaB_jetL2_perOrder_generic`: `‖∇^i wAlphaB(g₀ g₁ g_bg)‖² ≤ F i`
   (per-order, ballUniform, generic-in-g₁ via htie).  Apply at `g_bg := g₀` and `g_bg := g_bg`.
6. **(1,1) endo-diff producer** (producer, PUBLIC): via `slotInsertEndoCc_sub` + hoist ×2 +
   isometry ×2 + triangle: `‖∇^i slotInsertEndoCc g₀ 0 (connDiffDVF(g₀) − connDiffDVF(g_bg))‖² ≤
   2 F₀ i + 2 F_bg i` at `g₁ = realizedFam` (clone lc0Riem htie/hδP/hPball plumbing).
7. **Leaf**: (a) `lc0InsertDiff_eq_slotInsert_sum` — mirror `deTurckLieDLbCoeffField_eq_slotInsert_sum`
   (:47) but for the `lc0Insert`-difference, giving the connDiffDVF-difference endo (fold in
   `nEndo_diff`); (b) mirror `normSq_iCG_dlbField_le` (:358) → `‖∇^i LC‖² ≤ 4·finrank·‖∇^i(1,1)‖²`
   via `rfns_iteratedCovGrad_slotInsertEndoCc_le_endo` (generic, MetricArmCoeffJetTower:2863) +
   `sq_le_two_add`; (c) combine with (6) ⟹ `K i = 4·finrank·(2F₀ i + 2F_bg i)`, discharge the sorry.

The two riskiest pieces are the HOIST fibre proof (step 3) and the leaf field identity (step 7a);
both have exact committed templates.

## SESSION 4 RESULT (2026-07-26) — ATOM 2 GREEN, sorry discharged, axiom-clean

`lc0InsertDiff_ballUniform` no longer has a `sorry`; `lc0InsertDiff_realizedFam_perOrder_topSep`
is GREEN and axiom-audited `[propext, Classical.choice, Quot.sound]` (0 `sorryAx` in the file).
The whole route is committed-generic; **the `wOmegaDiff_eq` cancellation was NOT used** (crude
triangle `wAlphaB(g₀) − wAlphaB(g_bg)` suffices for a `ballUniform` bound).

### What landed
**Producer `DeTurckVectorFieldL2JetBound.lean`** (all `[propext, Classical.choice, Quot.sound]`):
- `cotangentToDual_cometricRaiseSlot0_gen` — generalized the existing `_wAlpha` lemma to any
  `(0,2)` field (old lemma kept as a 1-line wrapper; no duplication).
- `connDiffDVFSection g₀ g₁ g_ref` (public def) — the connDiff-part endo section
  `x ↦ connDiff g₁ g₀ x (deTurckVF g₁ g_ref x)`.
- `slotInsertEndoCc_sub` (private) — slot insertion is subtractive in the endo section.
- `connDiffDVFInsert_eq_cometricRaise` (public, the **HOIST**) —
  `slotInsertEndoCc g₀ 0 (connDiffDVFSection g₀ g₁ g_ref) = cometricRaiseSlot0Field g₀ 0 (wAlphaB g₀ g₁ g_ref)`.
- `norm_iCG_cometricRaiseSlot0Field_eq` (private) — the cometricRaise jet ISOMETRY at the norm level.
- `wAlphaB_jetL2_perOrder_generic` (private) — extracted the `hBsum` arm of `wAlpha_order0_jetL2_generic`.
- `connDiffDVFInsertDiff_realizedFam_jetL2_perOrder_ballUniform` (public, the `(1,1)` producer).

**Leaf `LieCorr0CoeffL2JetBound.lean`**:
- `sq_le_two_add`, `normSq_iCG_le_scaled` — copies of the (private) `DeTurckLieCoeffL2JetBound` helpers.
- `endoDiffSection` + `endoDiffSection_apply` (= `lieCorr0NEndo g_bg − g₀` via `nEndo_diff`).
- `lc0InsertDiff_eq_slotInsert_sum` — the `(2,2)` field identity, transcribed from
  `deTurckLieDLbCoeffField_eq_slotInsert_sum` with the LHS being the `lieCorr0InsertFib` DIFFERENCE
  (reconciled to the endo-difference via `nEndo_diff` + `ContinuousMultilinearMap.map_update_sub`).
- `normSq_iCG_lc0InsertDiff_le` — the `×4·finrank` `(2,2)→(1,1)` reduction (mirror `normSq_iCG_dlbField_le`).
- `lc0InsertDiff_ballUniform` — discharged: `normSq_iCG_lc0InsertDiff_le` + the producer bound, `K i = 4·finrank·Kprod i`.

### Lean lessons (session 4)
- `slotInsertEndoCc_sub` at the fibre: after `slotInsertEndoFib_sub_left`, the LHS is `(A − B) D`,
  needing `ContinuousLinearMap.sub_apply` (NOT `Tensor0SSpace.toModel_sub`) to match `A D − B D`.
- The HOIST closes with a terminal `rfl` (the `connDiffDVFSection` coercion is defeq to the `wVF`
  form but not syntactically equal after the `g₀.symm` rewrite).
- Leaf `open` gap: `reindexCoeffFibGen` (bare, not just `_apply`) had to be added to the restricted
  `TensorSpectral` open list (namespaces bite; the DLb file opens the bare name).
- `cometricRaiseSlot0Field g₀ 0` with `s := 0` prints indices as `0+1`/`0+2`; state `have`s with
  literal `1 1`/`0 2` and prove by the lemma (defeq accepted by `exact`) so downstream `rw` matches.
- Final chain: `4·finrank·‖..‖² ≤ 4·finrank·K i` is `mul_le_mul_of_nonneg_left hprod hfr_nn` DIRECTLY;
  a stray `rw [mul_assoc]` re-associates the LHS and breaks the match.

### lc0VB / lc0AMix honest read (does the HOIST help? NO)
The HOIST is specifically `slotInsert(connDiff·deTurckVF) = cometricRaise(wAlphaB)` — the DeTurck
endomorphism's connDiff half.  `lc0VB` / `lc0AMix` are NOT slot insertions of that endo: `lc0VB`
(`LieCorr0Core:144`) is `2·traceStep(g₁,VBPerm) ∘ prodKappa(metricConnDiffLoweredFib g₁ g₁ g₀) ∘
interior_product(deTurckVF g₁ g₀)` — an **interior-product contraction** of deTurckVF into a slot,
NOT a composition.  Their deTurckVF is NOT a `g₀↔g_bg` difference, so there is no cancellation and
no `wAlphaB`.  **The generic interior-product / contraction-Leibniz engine question STANDS for them.**
Reusable from this session: `slotInsertEndoCc_sub`, `norm_iCG_cometricRaiseSlot0Field_eq`, the
`(2,2)→(1,1)` reduction pattern, and the twoArm `wAlphaB`-style integrator recipe — but NOT the HOIST.
Committed precedent to follow instead: `deTurckLieArm1Coeff_realizedFam_jetL2_perOrder_ballUniform`
(`DeTurckLieArm1CoeffL2JetBound.lean:4812`), "g₁-cometric trace of connection-difference ×
interior-product(deTurckVF)" — the SAME shape as `lc0VB`.

### Resumption point (atom 3 = `lc0VB`)
Start from `deTurckLieArm1Coeff_realizedFam_jetL2_perOrder_ballUniform` as the template; the live
frontier is the interior-product(deTurckVF) contraction jet control (Arm1 handles it via
`lieArm1_deTurckVF_cometric_trace` / `lieArm1_appCc12_normSq_le`).  `lc0AMix` after `lc0VB`.  Assemble
the two endpoints (`sq_le_five_add`) only once all four Kc atoms are green.

## Honest accounting (updated 2026-07-26)
`(N) ricci_flow_unif_existence` still **0%** (endpoints unstated).  Dedicated machinery = top piece
(done) + four Kc atoms (**2 of 4 GREEN: `lc0Riem`, `lc0Insert`-diff**; 2 unstarted: `lc0VB`,
`lc0AMix`) + 5-way assembly (helper done, wiring pending) + shared engine.  Sorry-free-content
fraction of the leaf's four-atom machinery: **~50%** (was ~33%).  The `lc0Insert`-diff atom is the
first to fully exercise the producer HOIST + `wAlphaB` + `(2,2)→(1,1)` chain end-to-end.

## SESSION 5 (2026-07-25) — ATOM 3 = `lc0VB`: RECON VERDICT **route 3** (real engine gap); STATED with ONE `sorry`

**Decision.**  `lc0VB_realizedFam_perOrder_topSep` is stated verbatim in the `lc0Riem`/`lc0Insert`-diff
shape (`Ktop = 0`, `∇²T`-free) and derived green by the trivial reshape from the single frontier
`lc0VB_ballUniform` (the ONE `sorry`).  Verified by a targeted module build (79s, green): the two new
theorems carry exactly `[propext, sorryAx, Classical.choice, Quot.sound]`; every prior atom (4 banked
+ `lc0Riem` + both `lc0Insert`-diff) stays `[propext, Classical.choice, Quot.sound]`.  No commit made.

### RECON VERDICT — the Arm1 template's *kernel* transfers, its *end-to-end fold* does NOT
`lc0VB` (`LieCorr0Core:144`) = `2 · traceStep(g₁, VBPerm) ∘ prodKappa(metricConnDiffLoweredFib g₁ g₁ g₀)
∘ interior_product(1, deTurckVF g₁ g₀)`.  **Two moving arms** (metricConnDiffLowered g₁ AND deTurckVF g₁);
neither the `lc0Riem` fixed-passenger trick nor the `lc0Insert`-diff `wAlphaB` hoist applies (confirmed:
`lc0VB` is not a slot insertion of the DeTurck endo).  Named checks against Arm1
(`DeTurckLieArm1CoeffL2JetBound.lean`):

- ✓ **Transfers (generic kernel).**  `lieArm1_deTurckVF_cometric_trace` (`:2897`) —
  `deTurckVF g₁ gB = ∑ₖ connDiff g₁ gB (cometricLmodel(dualₖ)) (basisₖ)`, generic in `gB` ⟹ applies at
  `gB := g₀`.  With `interior_product`'s linearity (`interior_product_toModel_eval` `:2250`) this rewrites
  `ip(deTurckVF)` as a g₁-cometric sum of `ip(connDiff)`.  The committed product grid
  `rfns_iteratedCovGrad_appCcRS_diagonalProductGrid_rankLeft_le` (`MetricArmCoeffJetTower:2360`) +
  integrator `exists_integrated_iteratedCovGrad_diagonalProductGrid_twoArm_rs_le`
  (`RemainderCoeffPerOrderJetEnvelopes:862`) bound any resulting `appCcRS` — both already used by `lc0Riem`.
- ✗ **Does NOT transfer (Arm1-specific).**  (1) `deTurckLieArm1Coeff_eq_lieArm1Piece_sum` (`:4133`) is a
  ~2000-line hand-rolled 13-term identity whose live arm is `deTurckLieTraceCoeff` (**traceHessian**), not
  `metricConnDiffLowered`; `lc0VB`'s two arms are both connDiff-family (no traceHessian) — a different
  contraction, not a reindex.  (2) `lieArm1_slot2_vf_trace` (`:2967`) is slot-2-of-rank-3 specific
  (`lc0VB` inserts at slot-0 of rank-2 via `interior_product 1`).  (3) `metricConnDiffLoweredFib g₁ g₁ g₀`
  has **no reusable jet producer** — the tree-wide grep finds it only in the Arm1 file and this note; Arm1's
  `lieArm1LoweredBgKappa` + `lieArm1_kappa_feed`/`lieArm1_psiB_feed` are `private` and field-specific.
- **No committed generic interior-product-fold engine exists** (grepped: Arm1 / Kernel / VectorField each
  hand-roll their own `interior_product` fold; there is no `clm_apply`/`endoApply`/interior-product Leibniz
  jet product grid).

### The missing engine — exact required shape (what `lc0VB_ballUniform` needs)
1. **Fibre identity** `lieCorr0VBFib g₀ g₁ = reindexCoeffGen(σ)(appCcRS g₀ p a b Φ W)` (or a small sum
   thereof), folding `traceStep(g₁, VBPerm) ∘ prodKappa(metricConnDiffLowered g₁ g₁ g₀) ∘ ip(deTurckVF g₁ g₀)`
   into a bounded `appCcRS` of two connDiff-family arms.  Route: `lieArm1_deTurckVF_cometric_trace`
   (needs a thin PUBLIC wrapper — currently `private` in the Arm1 file; the claim on that file protects such a
   wrapper) + `interior_product` linearity + `appCcRS_toSection` slot bookkeeping for `VBPerm`.  This is the
   `lc0VB` analogue of `deTurckLieArm1Coeff_eq_lieArm1Piece_sum`, but single-term (≈200–400 lines, not 2000).
2. **Arm producers (per-order, ballUniform, generic-in-g₁ via `htie`/P):**
   - Φ = `metricConnDiffLowered g₁ g₁ g₀` — g₁-lowered ⟹ reduce to g₀-family + P-perturbation
     (the `lc0VB` analogue of `lieArm1LoweredBgKappa`/`lieArm1_kappa_feed`, using `connDiffLoweredCc`
     + `lieArm1PbLow`-style P terms).  This producer is the shared linchpin (see `lc0AMix` read).
   - W = `deTurckVF g₁ g₀` — via its cometric-trace-of-`connDiff` form ⟹ `connDiffSection g₁ g₀`
     (`connDiffSection_lowOrder_jetL2_succ_generic`, `DeTurckVectorFieldL2JetBound:1999`).
3. Then the `lc0Riem` tail idiom: product grid + integrator (`choose`d over `k`) + `realizedFam`
   `htie`/`hδP`/`hPball` threading + `Ktop = 0` reshape.

Effort: comparable to atom 2's full arc (3 sessions).  No cancellation shortcut (deTurckVF is a single
field, not a g₀↔g_bg difference), so `wOmegaDiff_eq` does NOT help.  Genuine build, not a one-lemma reuse.

### `lc0AMix` (atom 4) honest read — shares the METRICCONNDIFFLOWERED producer, NOT the interior product
`lc0AMix` (`LieCorr0Core:162`) = `2·(AMixHalf + swap∘AMixHalf)`, `AMixHalf` = a **chain of traceSteps** over
`prodKappa(metricConnDiffLowered g₁ g₁ g_bg)` and `prodKappa(metricConnDiffLowered g₁ g₁ g₀)` — **two
metricConnDiffLowered arms, NO `interior_product`, NO `deTurckVF`.**  So:
- It does **not** share `lc0VB`'s interior-product-fold frontier (no deTurckVF cometric-trace needed).
- It **does** share the `metricConnDiffLowered` per-order producer (item 2·Φ above) — both arms are exactly
  that object, at `g_bg` and at `g₀`.  Once that producer lands (for `lc0VB` green), `lc0AMix` reuses it and
  needs only the traceStep-chain fibre identity (pure `prodKappa`+`traceStep`, closest to the `lc0Riem`
  moving-arm recipe) — plausibly **easier than `lc0VB`**.  Recommended order: build the `metricConnDiffLowered`
  producer once, discharge `lc0VB_ballUniform`, then `lc0AMix` largely follows.

### Resumption order for atom 3 (to turn route 3 → green)
1. Public wrapper over `lieArm1_deTurckVF_cometric_trace` in `DeTurckLieArm1CoeffL2JetBound.lean` (claimed).
2. `metricConnDiffLowered g₁ g₁ g₀` per-order ballUniform producer (the shared linchpin; new lemma, best home
   near the Arm1 connDiff-feed layer or a fresh producer file).
3. `lieCorr0VBFib = reindexCoeffGen(appCcRS …)` fibre identity in the leaf (or a producer file).
4. Discharge `lc0VB_ballUniform` via product grid + integrator + `realizedFam` threading (clone `lc0Riem`).

## Honest accounting (updated 2026-07-25, session 5)
`(N) ricci_flow_unif_existence` still **0%** (both endpoints `lieCorr0Field_realizedFam_jetL2_{perOrder,summed}_topSeparated`
STILL UNSTATED = 0%).  Dedicated machinery = top piece (done) + four Kc atoms (**2 of 4 GREEN: `lc0Riem`,
`lc0Insert`-diff; 1 of 4 STATED-with-`sorry`: `lc0VB` (this session); 1 unstarted: `lc0AMix`**) + 5-way
assembly (helper `sq_le_five_add` done, wiring pending) + the shared `metricConnDiffLowered` producer (0%).
Sorry-free-content fraction of the leaf's four-atom machinery: still **~50%** (atom 3 STATED locks the
interface and pins the frontier, but its mathematical content — `lc0VB_ballUniform` — is sorried).  What
session 5 advanced: the recon verdict (route 3, engine gap named + shaped) and the atom interface, green
except the single documented `sorry`.

## SESSION 6 (2026-07-25) — LINCHPIN LANDED: the `metricConnDiffLowered` producer is GREEN; BOTH lc0VB arms now have committed producers

The shared engine both `lc0VB` and `lc0AMix` need — the per-order jet-`L²` producer for the moving arm
`metricConnDiffLoweredFib g₁ g₁ g₀` — is **LANDED GREEN, axiom-clean** in the Arm1 producer file
`DeTurckLieArm1CoeffL2JetBound.lean` (namespace `DifferentialGeometry.Integral.Connection`, same as the leaf,
so directly consumable).  Verified by a targeted module build (green, 97s); all three new declarations audit
to exactly `[propext, Classical.choice, Quot.sound]`.

### The decisive identity (why this was a short reuse, not a rebuild)
`metricConnDiffLoweredFib gm gA gB x = gm.inner (connDiff gA gB v₀ v₁) v₂`
(`DeTurckLieHigherOrderCoeffField.lean:453/460`).  Arm1's `lieArm1LoweredBgKappa g₀ g₁ g_bg`
(`:260`) is **defined as** `connDiffLoweredCc g₁ g_bg`, whose unitModel is
`g₁.inner (connDiff g_bg g₁ · ·) ·` (`lieArm1_kappa_unitModel_apply :1297`).  Since
`connDiff g_bg g₁ = -connDiff g₁ g_bg` (antisymmetry), **`metricConnDiffLowered g₁ g₁ g_bg =
-lieArm1LoweredBgKappa g₀ g₁ g_bg`** (sections over g₀).  Fibre-norm and jet-norm are sign-invariant, so
Arm1's committed private `lieArm1_kappa_feed` (the g₁-lowered → g₀ P-perturbation reduction) delivers the
bound directly.

### What landed (all `[propext, Classical.choice, Quot.sound]`)
- `metricConnDiffLoweredCc g₀ g₁ g_bg : SmoothCcTensor g₀ 0 3` (public def) — the section wrapper for
  `metricConnDiffLoweredFib g₁ g₁ g_bg` over g₀ (mirrors `lieArm1LowFix`/`MixedSection.fromMultilinearSection`).
- `metricConnDiffLoweredCc_eq_neg_kappa` (public) — the sign identity `= -lieArm1LoweredBgKappa`
  (`smoothCcTensor_ext_of_unitModel` + `lieArm1_kappa_unitModel_apply` + `lieArm1_connDiff_antisymm`).
- `metricConnDiffLoweredCc_jetL2_ballUniform_generic` (public, THE PRODUCER) — g₁-generic sup `Λ` + per-order
  jet-`L²` sums `F i`, uniform over the perturbation ball; a thin transport of `lieArm1_kappa_feed` via the
  sign identity (norms sign-invariant).  Same shape as `cometricDoubleTraceField_order0sup_jetL2_ballUniform_generic`
  (which `lc0Riem` consumed) — the consumer threads `realizedFam` for `g₁`.
- (private helpers: `metricConnDiffLoweredField`, `metricConnDiffLoweredCc_unitModel_apply`.)

### Task 2 (deTurckVF arm) — ALREADY COMMITTED, no new code
After the interior-product fold `lieArm1_deTurckVF_cometric_trace`, the deTurckVF arm of `lc0VB` becomes the
**pure** connection difference `connDiffSection g₁ g₀` (the cometric trace turns deTurckVF into `connDiff`,
NOT into `connDiff·deTurckVF`).  Its g₁-generic sup+`L²` producer is the committed PUBLIC
`lieArm1_connDiff_feed` (`:698`) — verbatim the sup+`L²` pair for `connDiffSection g₁ g₀`.  So the coordinator's
`connDiffDVFSection` guess (atom 2's `connDiff·deTurckVF` endo) is NOT the arm; `connDiffSection` +
`lieArm1_connDiff_feed` is, and it is done.  **Both of `lc0VB`'s fibre-identity arms now have committed
g₁-generic producers.**

### REVISED resumption order for the `lc0VB` fibre-identity brick (the next brick)
The two producers are ready; the remaining work is the fibre identity + assembly (do NOT reduce to new
frontiers):
1. **Public wrapper over `lieArm1_deTurckVF_cometric_trace`** (currently `private` in the Arm1 file) — the
   `deTurckVF g₁ g₀ = ∑ₖ connDiff g₁ g₀ (cometric dualₖ)(basisₖ)` vector identity; the claim on that file
   protects a thin public wrapper.
2. **Fibre identity** `lieCorr0VBFib g₀ g₁ = reindexCoeffGen(σ)(appCcRS g₀ p a b Φ W)` with
   Φ = `metricConnDiffLoweredCc g₀ g₁ g₀` (via item 1: fold `ip(deTurckVF)` → cometric trace of `connDiff`;
   then match `traceStep(VBPerm)` + `prodKappa` to `appCcRS`), W = `connDiffSection g₁ g₀`.  Single-term
   (≈200–400 lines), the `lc0VB` analogue of `deTurckLieArm1Coeff_eq_lieArm1Piece_sum` (but not 2000 lines).
3. **Discharge `lc0VB_ballUniform`** in the leaf: product grid `rfns_iteratedCovGrad_appCcRS_diagonalProductGrid_rankLeft_le`
   + integrator `exists_integrated_..._twoArm_rs_le` + `realizedFam` threading (clone `lc0Riem`), feeding the two
   producers (`metricConnDiffLoweredCc_jetL2_ballUniform_generic`, `lieArm1_connDiff_feed`).

### `lc0AMix` (atom 4) — reuses THIS producer twice; still no deTurckVF
`lc0AMix` = chain of traceSteps over `prodKappa(metricConnDiffLowered g₁ g₁ g_bg)` and
`prodKappa(metricConnDiffLowered g₁ g₁ g₀)` — two `metricConnDiffLoweredCc` arms (at `g_bg` and at `g₀`), NO
interior product.  Both are covered by `metricConnDiffLoweredCc_jetL2_ballUniform_generic` (this session).  So
`lc0AMix` needs only its own traceStep-chain fibre identity (no deTurckVF fold) — closest to the `lc0Riem`
moving-arm recipe, plausibly the easiest of the four Kc atoms once the producer (now landed) is in hand.

## Honest accounting (updated 2026-07-25, session 6)
`(N) ricci_flow_unif_existence` still **0%** (both endpoints STILL UNSTATED = 0%).  Dedicated machinery = top
piece (done) + four Kc atoms (**2 of 4 GREEN: `lc0Riem`, `lc0Insert`-diff; 1 of 4 STATED-with-`sorry`: `lc0VB`;
1 unstarted: `lc0AMix`**) + 5-way assembly (helper done, wiring pending) + the shared `metricConnDiffLowered`
producer (**NOW DONE, green + axiom-clean**) + the deTurckVF arm (**already committed via
`lieArm1_connDiff_feed`**).  Leaf four-atom sorry-free-content fraction still **~50%** (the `lc0VB` atom is
still sorried at `lc0VB_ballUniform`), BUT the two producers that discharge that sorry are now both in hand, so
the remaining `lc0VB` work is the fibre identity + assembly (no missing engine).  Honest sessions-to-`lc0VB`-green:
**~1–2** (fibre identity ≈200–400 lines + leaf discharge, both committed-generic).  Honest
sessions-to-`lc0AMix`-green after `lc0VB`: **~1** (reuses this producer twice; simpler traceStep-chain fibre
identity, no deTurckVF).

## SESSION 7 (2026-07-25) — lc0VB FIBRE IDENTITY + ASSEMBLY LANDED GREEN; sorry isolated to the VBPass jet bound

The `lc0VB` outer decomposition + leaf discharge are **GREEN** (targeted leaf build, 90s, zero errors).  The
fibre identity came out **cleaner than the recorded `reindexCoeffGen(appCcRS …)` guess**: `lc0VB` reuses
`lc0Riem`'s live arm *verbatim*.

### The fibre identity (what it actually looked like)
`appCcRS g a b c Φ W = Φ.comp W` (generic fibrewise composition; the "cometric trace" lives *inside* Φ/W).
So — since `lieCorr0TraceStep g₁ 2 VBPerm = cometricDoubleTraceFib g₁ 2 ∘ domDomCongr(VBPerm)` and
`lc0RiemLive.toSection = cometricDoubleTraceFib g₁ 2` — the split is simply

    lc0VB = 2 · appCcRS g₀ 2 4 2 (lc0RiemLive g₀ g₁) (lc0VBPass g₀ g₁)          -- `lc0VB_eq_app`, GREEN

with **`lc0RiemLive` REUSED unchanged** (the live `(4,2)` `g₁`-cometric double trace) and the *only* new object
`lc0VBPass g₀ g₁ : SmoothCcTensor g₀ 2 4 = domDomCongr(VBPerm) ∘ prodKappa(metricConnDiffLoweredFib g₁ g₁ g₀)
∘ ip(deTurckVF g₁ g₀)` (the moving passenger).  Proof of the fibre identity: `rw [lieCorr0VBFib,
lc0RiemLive_toSec]; rfl` (`.comp` associativity is defeq — 2 lines).  `lc0VBPassFib_contMDiff` clones
`lc0RiemPassFib_contMDiff` with the `ip`/`prodKappa`/`domDomCongr` blocks from `lieCorr0VBFib_contMDiff`.

### The leaf discharge (GREEN) — `lc0VB_ballUniform` now proved from ONE frontier
`lc0VB_ballUniform` and `lc0VB_realizedFam_perOrder_topSep` are **GREEN**, cloning the `lc0Riem` two-arm
assembly: the live arm bound is `lc0Riem`'s own (`cometricDoubleTraceField_order0sup_jetL2_ballUniform_generic`
+ `lc0RiemLive_l2_le`/`_rfns_le`), the product grid `rfns_iteratedCovGrad_appCcRS_diagonalProductGrid_rankLeft_le`
+ integrator `exists_integrated_..._twoArm_rs_le g₀ 4 2 2 4` combine, and the `2·` gives a factor 4
(`iteratedCovGrad_smul` + `norm_smul`).  The moving passenger's bound is the **single remaining `sorry`**:

    vbPass_jetL2  -- g₁-generic sup + per-order jet-L² for lc0VBPass (2,4); ONE sorry

### The isolated frontier `vbPass_jetL2` — exact remaining shape
`lc0VBPass = domDomCongr(VBPerm) ∘ prodKappa(mcd) ∘ ip(deTurckVF)` is a `(2,4)` operator field.  It is the
nested two-arm product `lc0VBPass ≐ appCcRS g₀ 2 1 4 (prodKappa mcd) (ip dvf)`, so its jet bound follows from a
SECOND product-grid application over `prodKappa(mcd)` and `ip(deTurckVF)`, feeding the two armed producers:
- Φ' = `prodKappa(metricConnDiffLoweredFib g₁ g₁ g₀)` `(1,4)` ← `metricConnDiffLoweredCc_jetL2_ballUniform_generic`
  (session 6) via a `prodKappa` jet lemma (NOT yet committed).
- W' = `ip(deTurckVF g₁ g₀)` `(2,1)` ← `lieArm1_connDiff_feed` (`connDiffSection`) via the
  `lieArm1_deTurckVF_cometric_trace` fold + an `interior_product` jet lemma (NOT yet committed).

The **genuinely missing pieces** are exactly two Leibniz jet lemmas: `rfns(∇^i prodKappa(Φ))` in terms of
`rfns(∇ Φ)`, and `rfns(∇^l ip(V))` in terms of the (folded) `connDiff` jets.  Tree-wide grep found neither
(`slotExtend` only tensors a *unit* slot, not a general `Φ`).  These are the resumption target.

### Verified-green this session (axiom-clean where not sorry-dependent)
`lc0VB_eq_app`, `lc0VBPass`, `lc0VBPassFib(+_contMDiff)`, `lc0VBFib_eq` — no sorry.  `lc0VB_ballUniform`,
`lc0VB_realizedFam_perOrder_topSep` — carry only the `vbPass_jetL2` `sorryAx`.  `vbPass_jetL2` — the one
flagged `sorry`.  All prior atoms (top, `lc0Riem`, `lc0Insert`-diff) stay `[propext, Classical.choice,
Quot.sound]`.

### Resumption order (turn `vbPass_jetL2` → green)
1. **`prodKappa` jet lemma** — `rfns_iteratedCovGrad` of `tensor0SProdKappaFib(Φ)(D)` ≤ (grid) · `rfns(∇ Φ)` ·
   `rfns(∇ D)`, the Leibniz product grid for `prodKappa`.  Best home: the `OperatorFieldFibreNormJet` /
   `MetricArmCoeffJetTower` layer next to `rfns_iteratedCovGrad_slotExtend_le`.
2. **`interior_product` jet lemma** — `rfns(∇^l ip(V))` via `lieArm1_deTurckVF_cometric_trace` (needs a thin
   PUBLIC wrapper over that private Arm1 lemma) reducing `ip(deTurckVF)` to a cometric trace of
   `connDiffSection`, then `lieArm1_connDiff_feed`.
3. Discharge `vbPass_jetL2` = second grid application (`appCcRS g₀ 2 1 4`) + the two producers + `realizedFam`.
4. Then `lc0AMix` (atom 4): two `metricConnDiffLoweredCc` arms, NO ip — reuses the `prodKappa` jet lemma (item 1)
   twice; no `interior_product` lemma needed.  Likely the easiest atom.

## Honest accounting (updated 2026-07-25, session 7)
`(N) ricci_flow_unif_existence` still **0%** (both endpoints STILL UNSTATED = 0%).  Dedicated machinery = top
piece (done) + four Kc atoms (**2 of 4 GREEN: `lc0Riem`, `lc0Insert`-diff; `lc0VB` now
STRUCTURALLY GREEN with ONE isolated `sorry` at `vbPass_jetL2` — the fibre identity + full assembly proved;
1 unstarted: `lc0AMix`**) + the shared producers (`metricConnDiffLowered` DONE, deTurckVF arm committed) +
5-way assembly (helper done, wiring pending).  What session 7 advanced: `lc0VB`'s fibre identity + leaf
discharge landed green, so the remaining `lc0VB` gap collapsed from "the whole ballUniform" to **two committed
Leibniz jet lemmas** (`prodKappa` + `interior_product`).  Honest sessions-to-`lc0VB`-green: **~1** (build the two
jet lemmas + discharge `vbPass_jetL2`).  Sessions-to-`lc0AMix`-green after: **~1** (reuses the `prodKappa` lemma;
no `ip`).
