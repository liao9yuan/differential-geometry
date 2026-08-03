# UnifCurvaturePack.lean — the curvature packaging brick

Dispatch: `ShortTime/UNIF_EXISTENCE_PLAN2.md` No. 78, dispatch (i).

## What the file is for

`UnifJetTowerMatch.lean` (No. 73) bridged the two jet towers in the
**section → field** direction:

* `ccUnitField g s W` — the metric-free `(0,s)` field carried by a
  `SmoothCcTensor g 0 s`;
* `iterCovGrad_unit_eq` — `unit(∇^j W) = iterCov g s (ccUnitField g s W) j`,
  every order, no arity cast;
* `rfns0_unit_eq`, `rfns_iterCovGrad_eq` — the same at the level of the
  pointwise fibre norm.

What was missing was the **field → section** direction.  Every `Λ`-class and
fixed-metric curvature estimate in the tree (`UnifCurvatureJetsLow.lean`,
`UnifCurvatureJet1Diff.lean`, the whole `covStep`/`diffStep` layer) is stated on
the *field* `metricRm04 g` in `iterCov`/`normSq0S` currency, while E3's
consumers (`hcurv` at `Analysis/Spectral/Tensor/SobolevScale/UnifBochnerGap.lean`,
`hsup` at `ShortTime/UnifNZeroBound.lean`) speak
`SmoothCcTensor`/`iteratedCovGrad`/`riemannianFiberNormSq`.  Producing a section
whose unit field *is* `metricRm04 g` closes that direction and makes
`rfns_iterCovGrad_eq` a one-rewrite transport.

## Contents

Generic packaging layer (rank-generic, curvature-free):

* `ccOfField g s A : SmoothCcTensor g 0 s` — a smooth `(0,s)` field packaged as a
  section.  Underlying section = `MixedSection.fromMultilinearSection ∞ A`;
  compact support = `HasCompactSupport.of_compactSpace` (no extra hypothesis:
  the HCG layer already carries `[CompactSpace M]`).
* `ccOfField_unit` (`@[simp]`) — `ccUnitField g s (ccOfField g s A) = A`.  Proof
  is exactly `MixedSection.toMultilinearSection_fromMultilinearSection`.
* `rfns_ccOfField_eq` — the transport equation at every order `j`:
  `riemannianFiberNormSq g 0 (s+j) x ((iteratedCovGrad g 0 s j (ccOfField g s A)).toSection x)
   = normSq0S g x (s+j) (iterCov g s A j x)`.

Curvature instance:

* `rmSection g : SmoothCcTensor g 0 4` — `ccOfField g 4 (metricRm04 g)`.
* `rmSection_unit` (`@[simp]`) — `ccUnitField g 4 (rmSection g) = metricRm04 g`.
* `rfns_rmSection_eq` — the curvature transport equation.

Transported bounds:

* `exists_rmJetSup g a` — fixed-metric, order `a`:
  `riemannianFiberNormSq g 0 (4+a) x ((iteratedCovGrad g 0 4 a (rmSection g)).toSection x) ≤ K²`.
  From `exists_curvJet_sup` (`UnifCurvatureJet1Diff.lean`).
* `exists_rmJetSups g a` — one constant for the whole window `j ≤ a` (the shape
  `hsup`-style consumers ask for), by running maximum.
* `unifRmSecSup gBase g₀ hΛ hΛ2 hcomp hjet1 hjet2` — the `Λ`-class **order-0**
  bound `riemannianFiberNormSq g₀ 0 4 x ((rmSection g₀).toSection x) ≤ C²`, `C`
  closed in `(Λ, gBase)`.  From `unifRm04Sup`.

## Honest scope — which consumer slots this does and does not fill

* **`hsup`-shaped slots (fibre sup on `iteratedCovGrad … .toSection x`)**: for
  the *curvature* section these are now directly fillable at **all orders for a
  fixed metric** (`exists_rmJetSups`) and at **order 0 class-uniformly**
  (`unifRmSecSup`).  Note that `UnifNZeroBound.staticN_h1_le`'s own `hsup` is
  about `deTurckRHSSection` (rank 2), not `rmSection`; `ccOfField` /
  `rfns_ccOfField_eq` are stated rank-generically precisely so that the same
  transport applies there once a `deTurckRHSField` `iterCov` bound exists.
* **`hcurv` (`UnifBochnerGap.bochner_step_unif`) is NOT fillable from this file,
  and no `unifFc` is defined.**  `hcurv` bounds
  `‖∇^p (pointwiseTensorCurv g₀ r S)‖_{L²}` for an *arbitrary* section `S`; that
  needs (a) a Leibniz/Kato product estimate for the curvature *action*
  `pointwiseTensorCurv` — a separate missing lemma — and (b) a **class-uniform
  all-order** sup of `∇^a Rm`, which is still open for every `a ≥ 1` behind the
  Palatini difference brick (`UnifCurvatureJet1Diff.md`, PLAN2 No. 77/78
  dispatch (ii)).  Defining a `unifFc` name here would have promised
  class-uniform all-order content that does not exist.

## Placement note

`ccOfField` / `ccOfField_unit` / `rfns_ccOfField_eq` are curvature-free and
belong next to `ccUnitField` in `UnifJetTowerMatch.lean`; they live here only
because that file was held by another agent during this session.  Move them when
`UnifJetTowerMatch.lean` is next touched, keeping this file as the curvature
instance.

## Lean lessons

* The `Tensor0SField` anonymous-constructor `NormedSpace` synthesis failure
  recorded in `UnifJetTowerMatch.md` does **not** bite in the
  `fromMultilinearSection` direction: we *consume* an existing field
  (`metricRm04 g`) and *produce* a `MixedSection`, so no `Tensor0SField` is built
  by `⟨_, _⟩`.  The `deTurckRHSSection` precedent (`(0,2)`) transfers verbatim to
  `(0,4)`.
* `rw` with `rfns_rmSection_eq g 0 x` fails against a goal written with the
  literal `4`: the lemma's statement has `4 + 0`, `iteratedCovGrad … 0 …` and
  `iterCov … 0`, all of which are *definitionally* but not *syntactically* the
  reduced forms.  Fix used in `unifRmSecSup`: introduce the order-`0` instance
  with an explicit reduced type ascription
  (`have hkey : … 4 … := rfns_rmSection_eq g 0 x`) and rewrite with `hkey`.
  Elaboration accepts it (all three reductions are `rfl`).
* `set R := <big expr> with hR` followed by `have hs : Real.sqrt R ≤ K := by rw [hR]; …`
  does **not** work here: the `have`'s goal comes back zeta-expanded, so `rw [hR]`
  reports "did not find an occurrence of the pattern `R`".  Abbreviating a long
  fibre-norm expression this way costs a debugging cycle for nothing — factor the
  arithmetic step into a small `private` lemma (`sqLeOfSqrtLe : 0 ≤ a → √a ≤ K →
  a ≤ K²`) and `refine` it instead, so the big expression is never named.

## Verification

Real `lake build` of the module: green, zero `sorry`, no warnings from this file.
`#print axioms` on all nine public declarations (probes run under `lake build`,
since `lake env lean` suppresses them): `[propext, Classical.choice, Quot.sound]`.


## 2026-08-02 addition — the object-level tower identity

### What was added (3 public, 2 private; all axiom-clean)

* `cc_ext_unit g W1 W2 (h : forall x, ccUnitField g s W1 x = ccUnitField g s W2 x) : W1 = W2`
  — the converse of `ccUnitField`: a `(0, s)`-rank section is *determined* by its
  unit field.  This is the missing extensionality principle of the whole
  `ccUnitField`/`ccOfField` layer.
* `iterCovGrad_ccOfField g s j A :
  iteratedCovGrad g 0 s j (ccOfField g s A) = ccOfField g (s + j) (iterCov g s A j)`
  — the tower bridge as an identity of *objects*, not of norms.  Both sides are
  `(0, s + j)`-sections; no arity cast, no combinatorial factor, constant `1`.
* `iterCovGrad_rmSection g a :
  iteratedCovGrad g 0 4 a (rmSection g) = ccOfField g (4 + a) (iterCov g 4 (metricRm04 g) a)`
  — the curvature instance.
* private `zeroS_eq_unit` (a `(0,0)`-tensor is its scalar readout times the unit)
  and `rs0_apply_eq_smul` (a `(0,s)`-rank fibre element on an arbitrary input is
  its unit value rescaled).

### Why this and not another norm transport

`ccOfField_unit` and `rfns_ccOfField_eq` were already here: they transport the
*unit value* and the *fibre norm*.  What was missing is that the two towers agree
as objects, from which every other functional of the jet (linearity, `toL2`,
`toHs`, later Sobolev/Bochner functionals) transports through the same packaging
by rewriting once, instead of needing a new per-functional transport lemma.  The
proof is short because rank-zero fibres are one dimensional: agreement on the
unit is agreement outright (`cc_ext_unit`), and the unit values agree by
`iterCovGrad_unit_eq` composed with `ccOfField_unit`.

### Recon finding — the No. 77 "unbridged towers" gap is fully closed

The dispatch that produced this addition was aimed at No. 77's final paragraph
("`iteratedCovGrad g 0 s j (toRS0 A) = toRS0 (iterCov g s A j)` is missing").
That gap was already closed twice over: No. 73 (`UnifJetTowerMatch.lean`) in the
section -> field direction and No. 81 (this file) in the field -> section
direction.  A fresh sibling `HCGCompactness/IterCovLiftBridge.lean` was written
and verified green during this run, then **deleted** before landing: its
`ccUnit_ccLift` / `rfns_ccLift` / `curvJetSup_rs` were verbatim duplicates of
`ccOfField_unit` / `rfns_ccOfField_eq` / `exists_rmJetSup`.  Only the genuinely
new object-level content survives, and it lives here, next to `ccOfField`.

Duplicate worth knowing about (NOT resolved here): `ccOfField` has a twin,
`ccLift0S` (`Evolution/ForwardUniqueIBP.lean:72`), built from
`unitScalarRSLiftCs` instead of `MixedSection.fromMultilinearSection`, with its
own `ccLift0S_unit`.  Two definitions of the same map now exist in the tree.
When the placement note above is executed (moving `ccOfField` next to
`ccUnitField` in `UnifJetTowerMatch.lean`), collapse `ccLift0S` onto it.

### Lean lessons

* `apply ContMDiffSection.ext` (and anything that unifies against
  `Cs^inf(I; TensorRSModel .., ..)`) fails with
  `failed to synthesize FiberBundle (TensorRSModel 0 s R E) fun x => TensorRSSpace 0 s I x`
  unless the declaration is elaborated under
  `set_option backward.isDefEq.respectTransparency false`.  The knob is
  transparency, **not** `synthInstance.maxHeartbeats` — this file already sets
  the heartbeat budget to 1600000 and still failed.  Every file in the tree that
  uses `SmoothCcTensor.ext; ContMDiffSection.ext` (`CovGrad/Defs.lean`,
  `L2Operator/L2PMap.lean`, `RawConnLapLinear.lean`) sets the transparency
  option; this file did not, so the new lemma carries it as a scoped
  `set_option ... in`.
* Modifier order: `omit [..] in`, `set_option .. in`, **then** the docstring,
  then the declaration.  Putting `omit .. in` between the docstring and the
  declaration is a parse error (`unexpected token 'omit'; expected 'lemma'`), and
  a focused `lake env lean` run made *before* the edit will not catch it.
* Contrary to the "Verification" note below, `#print axioms` output **did**
  appear under `scripts/lake-locked.ps1 check` (`lake env lean`) in this run.

### Verification of the addition

Focused check: green, no warnings from this file.  Real targeted `lake build` of
`+...HCGCompactness.UnifCurvatureJetOne` (which imports this module): green,
`Build completed successfully`, zero errors.  `#print axioms` on the three new
public declarations: `[propext, Classical.choice, Quot.sound]`.
