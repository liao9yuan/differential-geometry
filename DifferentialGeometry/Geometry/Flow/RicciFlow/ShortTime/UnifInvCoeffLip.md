# UnifInvCoeffLip.lean — G3 lane entry node

Status: **LANDED, sorry-free, axiom-clean** (2026-08-07).  Ledger entry 202 in
`UNIF_EXISTENCE_PLAN6.md`.

## What this file provides

`invCoeff_h2_lip_unif` — the class-uniform sibling of the metricwise
`invCoeff_h2_lip` (`Analysis/Spectral/Intrinsic/DeTurck/DeTurckRemainderLowBaseC2Lip.lean:1147`).
One `H²` radius `ρ` and one Lipschitz coefficient `C` are selected from
`(gBase, Λ)` before the class metric varies, under exactly the pair

- `MetricUniformEquivalentOn univ gBase g Λ`
- `∀ a ≤ 3, MetricCovDerivOrderBoundOn univ a g gBase Λ`

(no fourth jet).  Conclusion: on the common ball, the pointwise fibre norm and
the first three covariant `L²` jets of
`gInvDiffSlotCoeff g gT - gInvDiffSlotCoeff g gU` are bounded by
`(C · ‖T − U‖_{H²})²`.

## Part-0 finding (recorded because it corrects the dispatch's premise)

The metricwise node the three radius chains thread is **not** a Lipschitz clause
inside `inv_coeff_h2`.  `inv_coeff_h2` (`DeTurck/PrincipalCoeffH2.lean:202`) has
exactly two clauses — a pointwise order-zero bound and an `L²` jet bound — and
`inv_coeff_h2_unif` (`ShortTime/UnifInvCoeffH2.lean:60`) uniformizes **both** of
them.  Nothing was dropped there.  The Lipschitz/pair layer is a **separate,
strictly larger theorem**, `invCoeff_h2_lip`, whose two-endpoint statement has no
counterpart in `inv_coeff_h2` at all.  So "the dropped clause" framing was wrong;
the gap is a whole theorem, and this file supplies it.

## Route

The proof mirrors the metricwise one, replacing each metric-dependent input by
its class-first sibling.  The translation table (this is the reusable part):

| metricwise input (`invCoeff_h2_lip`) | class-first sibling used here |
| --- | --- |
| `inv_coeff_h2 hDim g` | `inv_coeff_h2_unif` (`UnifInvCoeffH2.lean:60`) |
| `appRS_h2_h2_h2 hDim g 2 2 2` | `appRS_h22_unif` (`UnifAppH22.lean:70`) |
| `jet3_fiber_c2 hDim g 2 2` (private) | `morreyRS_unif` (`HCGCompactness/UnifMorreyRS.lean`, mixed valence) |
| `hs2_low2 g 2` (inside `perturbSlot2_jet`) | `covsum_hs_two` at `IsCurvAction0 g 2 Kcurv.rankTwo` (`SobolevScale/UnifBochnerGap.lean:490`) |
| `J0 = c2JetSq g (fullSlot2 g g)` | **no sibling existed** — supplied here as `idSlotJet` |

`morreyRS_unif` was the single most valuable discovery: it is the class-uniform
mixed-valence Morrey estimate, i.e. the `_unif` sibling of the private
`jet3_fiber_c2`, and it already existed.  Consumers of the `_lip` layer should
reach for it rather than re-deriving a pointwise-from-jets bound.

### The genuinely new ingredient: the identity rank-two coefficient

`fullSlot2 g g = slotInsertEndoCc g 1 (fullRaisedEndoField g g)` is the identity
`(2,2)` coefficient.  Its `H²` window is bounded **uniformly** because

- it is parallel — `iteratedCovGrad_slotInsert_fullRaised_id_succ_eq_zero`
  (public, `CovGrad/CurvatureCoefficientDifferenceJetTower/Lowered.lean:445`)
  kills every positive order after the slot transfer;
- its pointwise fibre norm is a pure dimension constant — `rfns_idEndo_le`
  (public, `CovGrad/RecoveryEndomorphismJetBound.lean:454`) via
  `sharpFlatEndoCc_eq_slotInsert_fullRaised` (public, `Lowered.lean:313`).

So only the order-zero term survives and it costs `27 · vol(g)`, which the class
volume comparison `volumeReal_cross` turns into
`27 · volCompareC Λ · vol(gBase)`.  This is `idSlotJet` in the file.

### Closed constant

With `Kcurv` from `exists_curv_actions gBase hΛ`, `Ch = h2CovsumC Kcurv.rankTwo`,
`vol = volCompareC Λ · vol_{gBase}(M)`, and `(ρ, Cinv)` / `Cmul` / `Cpt` from
`inv_coeff_h2_unif` / `appRS_h22_unif` / `morreyRS_unif`:

    Cp = 3 · Ch
    Z  = 2 · ((Cinv · ρ)² + 27 · vol)
    A  = √Z
    C0 = Cmul² · Cp · A²
    C  = (Cpt + 1) · C0

`ρ` is inherited verbatim from `inv_coeff_h2_unif`, i.e. `min 1 (4·Cop)⁻¹` with
`Cop = hs2OpActionC (morreyTwoC gBase Λ) Kcurv.rankTwo`.  Every factor is chosen
before `g` varies; the three `∃`-provided factors (`Cinv`, `Cmul`, `Cpt`) are
class-first in exactly the sense the rest of the `_unif` corpus already uses.

## №194 re-derivations (never re-elaborate the monolith)

Four private helpers of `DeTurckRemainderLowBaseC2Lip` were re-derived here from
their public producers rather than exported from the monolith:

- `permICG` — jet-norm invariance under `domDomCongrSection`, from
  `riemannianFiberNormSq_iteratedCovGrad_domDomCongrSection` (public) plus the
  `tensorL2Norm`/integral bridge.  Stated generically in the rank `s`, unlike the
  private rank-2 original.
- `symmICG` — from `iteratedCovGrad_symmS_eq` (public) plus `permICG`.
- `insOneICG` — slot-1 to slot-0 jet transfer, from
  `rfns_iteratedCovGrad_slotInsertEndoCc_le_endo` (public,
  `TensorHilbert/MetricArmCoeffJetTower.lean:2795`) and
  `normSq_le_integral_of_pointwise_fiberNormSq_le_rs` (public).
- `perturbICG` — from `insOneICG`, `insert_symmRaise_eq` (public,
  `CovGrad/SymmRaiseEndoField.lean:277`) and `norm_iCG_cometricRaiseSlot0Field_eq`.

`invSlot_sub_factor` (`C2Lip.lean:745`) is already **public** and is used
directly; only its olean is read, the monolith is never re-elaborated.

## What failed / what to avoid

- Do **not** try to compute `riemannianFiberNormSq` of the identity coefficient
  from the definition.  `riemannianFiberNormSq_eq_sum_witness` (public) does not
  export orthonormality of its frame, and the frame witness that does
  (`RiemannianFiberNormSqTensorInnerBridge.lean:472`) is private.  The public
  route is the slot transfer + `rfns_idEndo_le`, which never touches the frame.
- Do **not** reach for `exists_bound_riemannianFiberNormSq_smoothCcTensor` for the
  identity term: it produces a non-explicit, metric-dependent constant and is
  useless for a class-uniform bound.  (The private `bdSharpFlat_tgrid` route in
  `RiemannCoefficientPalatiniRefold.lean` does exactly this and cannot be
  uniformized.)
- Three cheap first-pass errors, all fixed: a `↑3` Nat-cast blocking `linarith`
  (fix: `push_cast at h`), and two `simpa using congrArg (· ^ 2)` steps that
  simp-normalized `0 ^ 2` away (fix: state the two vanishing jets at the literal
  indices `1` and `2` and `rw` them into the expanded sum).

## Verification

Focused check GREEN (24 s, no warnings).  Targeted module build GREEN
(9928 jobs).  Axiom probe of `invCoeff_h2_lip_unif`: `propext`,
`Classical.choice`, `Quot.sound` only — sorry-free.  Probe run from a temporary
scratch module which was deleted afterwards (`lake env lean` suppresses
`#print axioms`, so the probe must go through `lake build`).

## New public declarations (census additions deferred)

`invCoeff_h2_lip_unif`.  Everything else in the file is `private`.

## Next node up the lane — DONE (2026-08-07), see `UnifTraceLip.md`

`trace24_h2_lip` (private, `DeTurckRemainderLowBaseC2Lip.lean:1358`) — the first
consumer of `invCoeff_h2_lip`.  Its inputs are `invCoeff_h2_lip` (now available
class-uniformly), `appRS_h2_h2_h2` at `(4,4,2)` and `(6,6,4)` (covered by
`appRS_h22_unif`, which is generic in the valence), and the jet windows
`c2JetSq g (cometricDoubleTraceField g 2)` / `(… g 4)`.

**Landed as `trace24_h2_lip_unif` in `UnifTraceLip.lean`.**

**CORRECTION to this section's prediction.**  The paragraph above named the
"single missing lemma" as a class-uniform pointwise fibre bound for
`cometricDoubleTraceField g p`, the analogue of `rfns_idEndo_le`.  That lemma
was **not missing** — it already existed, public and sorry-free, as

    cometricTrace_rfns_p (p) (g) (x) :
      rfns g (p+2) p x ((cometricDoubleTraceField g p).toSection x)
        ≤ (Module.finrank ℝ E : ℝ) ^ (p + 6)

`Analysis/Parabolic/RicciLinearization/CometricTraceSelfBound.lean:220`,
rank-generic, single-metric, with a PURE DIMENSION constant, so it needs no `Λ`
and no metric-equivalence hypothesis at all.  Its own route (`traceSucc_rfns`,
private, same file) is a slot-succ EQUALITY on `rfns_slotExtendFib_eq` — not a
component computation.  Grep-verify a named gap against the whole tree before
pricing it as a brick; this is the recurring over-count pattern.

The real work of node 2 turned out to be the slot-insertion jet tower
(`insert3_jet_c2` / `insert5_jet_c2` re-derivation), which this section did not
mention at all.  Details in `UnifTraceLip.md`.
