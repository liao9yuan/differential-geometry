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
