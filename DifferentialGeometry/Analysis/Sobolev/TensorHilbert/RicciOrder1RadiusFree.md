# `RicciOrder1RadiusFree.lean` — grid currency for the order-one Ricci kernel

Created 2026-08-03 during brick A1-CUR-1 (`low1Ker_jet`).

## Mathematical content

The order-one arm of the linearized Ricci operator is **linear** in the
connection difference.  `kernelField_eq_neg_arm_combination` exhibits
`linearizedRicciConnDiffOrder1KernelField g₀ g₁` as the negated sum of five
slot-permuted / reindexed copies of the single insertion field
`connDiffContrInsertionField g₀ g₁`, and that field is a reindexed double slot
extension of `connDiffSection g₁ g₀`.  Since slot permutations and contravariant
reindexings are pointwise fibre isometries at every jet order, and slot
extension costs one dimension factor, the kernel inherits the connection
difference's radius-free `atgw` window at offset `+2` — **one** derivative of
the state.  This is exactly what separates the order-one arm from the
order-zero arm, where the `A·A` term is quadratic and no radius-free bound
exists (see `A1CUR_PLAN.md` §5.2).

## What it provides

* `permAppEqRs` — public re-derivation of `appCcRS (slotPermCc σ) S =
  rsDomDomCongrSection σ S`.  Needed because `permApp_eq_rs` is `private` in the
  read-only `DeTurckRemainderLowBaseAction.lean`.
* `ricci1Split` — the public `rsDomDomCongrSection`-form split (the A1-CUR plan
  step-1 "public re-derivation of `ricci1_split`"), obtained from the promoted
  `kernelField_eq_neg_arm_combination` by `simp only [permAppEqRs]`.
* `insertAtgw` — radius-free pointwise `atgw` window at `+2` for
  `connDiffContrInsertionField`, constant `finrank² · Ccd l`.
* `ricciKerAtgw` — the same for `linearizedRicciConnDiffOrder1KernelField`,
  constant `46 · Cins l` (four binary applications of `2`-subadditivity, the
  same `46` as the fixed-order private `ricciKer_h2_rf`).

## Promotions performed elsewhere

* `DeTurckVFJetRadiusFree.lean`: `rfns_iCG_connDiffSection_atgw_rf` made public
  (was `private`); docstring added.
* `RicciConnDiffOrder1TameEnvelope.lean`: `slotPermCc`,
  `kernelField_eq_neg_arm_combination` and the seven `kOutPerm*` / `kInPerm*`
  permutations made public with docstrings.  **This is the copy that is actually
  in the `LowRegC01JetTower` import chain** — the plan's instruction to promote
  the `LieFieldJetL2Summed.lean:136` copy would have required a new import; that
  copy was left untouched and no duplicate was created.

## Lessons

* Namespace trap: `ccTensorBilinSymm` and `gFibreOpBound` live under
  `…IntrinsicSpectral.MetricRealization`.  Omitting that `open` produces the
  confusing error `Invalid argument name 'I' for function` (the name resolves to
  a different declaration), not an "unknown identifier".
* `riemannianFiberNormSq_add_le` gives `≤ 2*a + 2*b`.
* `gridBase g₀ P x` and its expanded lambda are definitionally equal but not
  syntactically; `rw` with a `rfl`-proved equation before any `ring` step.

## Verification

Focused check passed, sorry-free, no warnings.

## Follow-on: `LieFieldJetL2Summed.lean` deduplicated (required, not optional)

**Lesson (cost: one ~40 min chain build).**  A `private` declaration does **not**
protect against a same-named public declaration arriving by import: promoting
`slotPermCc` / `kernelField_eq_neg_arm_combination` / the seven permutations in
`RicciConnDiffOrder1TameEnvelope.lean` made
`LieFieldJetL2Summed.lean` fail with nine

```
a non-private declaration `…TensorSpectral.slotPermCc` has already been declared
```

errors, because that file transitively imports the envelope and carried its own
`private` copies of exactly those names in the same namespace.  Privacy hides a
name from *importers*; it does not give it a distinct fully-qualified name for
collision purposes.

Fix (and it is the dedup the A1-CUR plan asked for, applied on the other side):
the nine local copies — the seven perms, `slotPermCcFib_contMDiff` and
`slotPermCc`, and `kernelField_eq_neg_arm_combination` — were **deleted** from
`LieFieldJetL2Summed.lean`; the rest of that file now uses the imported public
originals unchanged.  Both file docstrings were corrected (they claimed the
declarations were "copied verbatim … hence not importable").  Its five remaining
copied helpers (`armOuter_rfns_eq`, `armFull_rfns_eq`, `armOuter_norm_eq`,
`armFull_norm_eq`, `c3_norm_five_le`) are still `private` on both sides and do
not clash.

A tree-wide scan for further `private` copies of the promoted names found none
(`slotPermCc0` in `RicciConnDiffOrder0KernelJetGrid.lean` is a different name).

## Final verification

`lake build +LieFieldJetL2Summed +ScratchC01Census`: **9599 jobs, completed
successfully, 0 errors**.  Axiom census: `atgwFold`, `atgwToJet`, `permAppEqRs`,
`ricci1Split`, `insertAtgw`, `ricciKerAtgw`,
`rfns_iCG_connDiffSection_atgw_rf`, `kernelField_eq_neg_arm_combination` all
`[propext, Classical.choice, Quot.sound]`.
