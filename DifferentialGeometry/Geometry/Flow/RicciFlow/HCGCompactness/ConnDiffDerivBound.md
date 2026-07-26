# ConnDiffDerivBound — B2 P1 (ungated fibre→vector reduction)

Companion note for `ConnDiffDerivBound.lean`.  Full mission route: `UNIF_ITEM6_RECON.md`.

## What is landed (verified, sorry-free, axioms = [propext, Classical.choice, Quot.sound])

- `covDerivConnDiff_fibreNorm_le` (public): the **ungated** B2 P1 brick.
  ```
  √(g₂(covDerivConnDiff g₂ g₁ (ext v)(ext w)(ext u) x, ·))
      ≤ ‖(covGrad g₂ 1 2 (connDiffSection g₁ g₂)).toSection x‖ · √(g₂ v v)·√(g₂ w w)·√(g₂ u u)
  ```
  `ext · = smoothExtensionTangent x ·`; norm is the `g₂`-fibre norm via `tensorRS_riemannianBundle g₂ 1 3`.
- `covGrad_connDiffSection_flat_eval_eq_inner` (private helper): the flat/eval bridge, re-derived from the
  PUBLIC `connDiffSection_covGrad_eq_covDerivConnDiff` (the parent file's copy is `private`).
- `covDerivConnDiff_gJet_le` (public): **the B2 endpoint** (session 7).  Under
  `MetricUniformEquivalentOn K g₂ g₁ Λ` + `MetricCovDerivOrderBoundOn K 1/2 g₁ g₂ Λ'/Λ''` and
  `x ∈ K`,
  ```
  √(g₂(covDerivConnDiff g₂ g₁ (ext v)(ext w)(ext u) x, ·))
      ≤ (3/2)·Λ⁴·(Λ'' + Λ·Λ'²) · √(g₂ v v)·√(g₂ w w)·√(g₂ u u)
  ```
  This is verbatim the `hA1` binder of `covStepDiff_norm_le` (`UnifCovSumCross.lean`).
- `covDerivConnDiff_g1_le`, `lcDiff_covOne_le`, `field_eq_mcd1`, `nabla3_eq_mcd2`,
  `sqrt_normSq0S_comp` (private): the dual-core and currency/comparability layer beneath it.

## Why this is the right brick

(Historical framing from session 1; superseded by the dual route below — B2 is now closed and the
"remaining frontier" language here no longer applies.)

B2 (the full ungated output-vector bound in `Λ,Λ',Λ''`) was planned as **P1 ∘ P2**:
- P1 = this file (ungated Cauchy–Schwarz reduction to the fibre norm) — DONE.
- P2 = `‖covGrad g₂ 1 2 (connDiffSection g₁ g₂)‖_{fibre} ≤ CA(Λ,Λ',Λ'')` — the a=1 analogue of
  `lcDiff_norm_le`.  See `UNIF_ITEM6_RECON.md` §4 for its brick sequence.  **This factorisation was
  NOT the route taken**: the dual/eval route reaches the B2 endpoint directly and never needs the
  fibre-norm intermediate, so P1 ended up unused by the endpoint.

Compose: any P2 supply `hNW : ‖covGrad connDiffSection‖ ≤ CA` gives, in one `le_trans` +
`mul_le_mul_of_nonneg_right`, the full B2 bound `≤ CA·√(g₂ v v)·√(g₂ w w)·√(g₂ u u)` that both consumers
(T-B `mixedComm_norm_le`/`hA1`, 2a-tel (b)) need.

## Lean lessons (what to reuse / what bit)

- **Extraction is faithful, not novel math**: the proof is the ungated half (lines ~177–349) of the
  δ<1-gated `exists_covDerivConnDiff_gQuadratic_le_of_jetEnvelope`
  (`Curvature/CovDerivConnDiffQuadraticBound.lean`).  The gate is used ONLY for the fibre bound `hWnorm`,
  never for P1 — confirmed by copying the second half verbatim with the fibre bound removed.
- **Environment must match the parent file**: importing `CovDerivConnDiffQuadraticBound` is not enough;
  `covGrad` lives in `DifferentialGeometry.Analysis.Parabolic.TensorSpectral` and must be `open`ed.
  The full open set copied from the parent: `Integral.L2`, `Integral.Connection`, `PDE.RicciFlow`,
  `PDE.RicciFlow.IntrinsicSpectral.MetricRealization`, `Analysis.Parabolic.TensorSpectral`,
  `Analysis.Laplacian`, `Analysis.Sobolev.TensorHilbert` (+ `Bundle Manifold Set Filter Tensor0SBundle`).
  Symptom of a missing open: `covGrad` auto-bound as an implicit `x✝ : Sort _`, then `Invalid argument
  name I for function`.
- **`set_option backward.isDefEq.respectTransparency false`** is needed on the flat/eval bridge (copied
  from the parent) for the `hA_bridge : covDerivConnDiff g₂ g₁ Xsec Zsec Ysec x = A` `rfl` (the
  `ContMDiffSection.mk` ↔ `smoothExtensionTangent` coercion defeq) — arg SWAP `Xsec Zsec Ysec = ext v,
  ext w, ext u`.
- **`attribute [-instance] tensorRSSpace_normedAddCommGroup tensorRSSpace_normedSpace in`** on the P1
  theorem so `‖W‖` resolves to the `RiemannianBundle` fibre norm (via the in-statement `letI`), not the
  auto `TensorRSSpace` norm.
- `lake env lean` gives a fast error read but false-green success (v4.29 checkout); the green above is an
  authoritative `lake build` + `#print axioms` (stripped after audit).

## Home debt

Pure fibre-currency Curvature-layer content; canonical home is next to
`abs_tensor13_flat_eval_le_fibreNorm_mul_sqrt` in `Geometry/Curvature/CovDerivConnDiffFibreExtraction.lean`.
Placed in this HCG leaf only because the leaf is the ratified B2 home / editable set.  Promote upstream
once B2 assembles (and de-privatise the parent's `covGrad_connDiffSection_flat_eval_eq_inner` so this
file's private copy can be dropped).

## B2 P2 — ROUTE DECISION (dual/eval, NOT the component engine) + session 6 landed

**Deviation from the planner's P2.b/c/d, sanctioned by recon §4.**  After full recon I chose the
**dual/eval route** over the "(1,3)-component→l² engine + compose-P1" route the mission prescribes.
Rationale (shortest correct, one genuine frontier already discharged):

- P2.a (`connDiff_koszul_deriv`, `ChristoffelDiffKoszulDeriv.lean`) is the LOWERED-eval identity
  `2·g₁(covDerivConnDiff g₂ g₁ W X Y x, Z x) = [three ∇₂²g₁ combos] − 2·(∇₂_W g₁)(A(X,Y), Z x)`.
- The dual route pairs it against the output vector itself (set `Z x = B := covDerivConnDiff …`), so
  `2·g₁(B,B) = Σ± nabla0SFun 3 W field x ![·,·,B] − 2·nabla0SFun 2 W (mtf g₁) x ![A(u,w), B]`, bounds
  each RHS term by the multilinear Cauchy–Schwarz **`abs_apply_le_sqrt_normSq0S`** (already exists,
  `Tensor/RSTensor/Tensor0SRiemannian/Comparison.lean:739`) in the `metricCovDeriv 2 / metricCovDeriv 1`
  currency, re-expands `|A(u,w)|` by the a=0 atoms **`connDiffVec_norm_le`** + **`lcDiff_norm_le`**,
  divides by `|B|` (as in `connDiffVec_norm_le` step 7), then converts `g₁↔g₂` by comparability.
- This **produces B3's `hA1` (the eval form) DIRECTLY** — it does NOT need the fibre-norm intermediate
  `‖covGrad …‖ ≤ CA` (P2.d) nor a compose-with-P1 step, and it avoids building a new (1,3)-component
  →l² bridge and a new quadratic-l² inequality.  P1 (`covDerivConnDiff_fibreNorm_le`) therefore
  becomes an UNUSED alternative for this consumer (keep it — it is the honest fibre reduction and other
  consumers may want it).  The component route remains valid if the fibre-norm endpoint is ever wanted.

**Predicted final constant: `CA = (3/2)·Λ⁴·(Λ'' + Λ·Λ'²)`** (= `(3/2)Λ⁴Λ'' + (3/2)Λ⁵Λ'²`).  Matches
recon §0 shape `poly(Λ)·(Λ''+Λ'²)` with the √Λ power one higher than a=0 (order-4 vs order-3
comparability).  Derivation (all g₁-norms unless noted; `n`-free):
`2|B|²_{g₁} ≤ (3·M2_{g₁} + 2·M1_{g₁}·NA_{g₁})·|v||w||u|·|B|_{g₁}` ⟹
`|B|_{g₁} ≤ (3/2·M2_{g₁} + M1_{g₁}·NA_{g₁})·|v||w||u|_{g₁}`, then
`M2_{g₁} ≤ √(Λ⁴)·metricCovDerivNorm 2 g₁ g₂ ≤ Λ²Λ''`, `M1_{g₁} ≤ √(Λ³)Λ'`,
`NA_{g₁} ≤ (3/2)√(Λ³)Λ'`, `|B|_{g₂} ≤ √Λ|B|_{g₁}`, `|v|_{g₁} ≤ √Λ|v|_{g₂}` (×3).

### VERIFIED-GREEN this session (session 6, 2026-07-25) — whole-file `lake build` EXIT=0 (9451 jobs)

Three private foundational helpers landed in `ConnDiffDerivBound.lean` (after P1, before `end Curvature`):

- `field_eq_mcd1` — currency bridge: `totalNabla0S 2 (LC g₂)(metricTensorField g₁)(metricField_totalReg …)`
  (= `field` in `connDiff_koszul_deriv`) `= metricCovDeriv g₁ g₂ 1`.  Proof: `DFunLike.ext` + `intro x` +
  `totalNabla0S_apply` + `exact (metricCovDerivStep_apply g₂ 0 (metricTensorField g₁) x).symm`
  (default-transparency defeq closes `metricCovDeriv 1 ≡ metricCovDerivStep 0 (mtf g₁)`, `0+2≡2`,
  `LeviCivita≡leviCivitaConnectionOfMetric`).
- `nabla3_eq_mcd2` — currency bridge (order 2): `nabla0SFun 3 (LC g₂) W field x slots
  = metricCovDeriv g₁ g₂ 2 x (Fin.cons (W x) slots)`.  Proof: `rw [field_eq_mcd1, show mcd2 = step 1 (mcd1),
  metricCovDerivStep_apply]` then `exact (totalNabla0SFun_apply_section 3 …).symm`.  Needs
  `[VectorBundle]`+`[ContMDiffVectorBundle 1]` binders (for `metricField_totalReg`).
- `sqrt_normSq0S_comp` — general-`s` `(0,s)` comparability under `MetricUniformEquivalentOn K g₂ g₁ Λ`:
  `√normSq0S(g₁,s,A) ≤ √(Λ^s)·√normSq0S(g₂,s,A)`.  = `exists_diagInv_of_metricUniformEquivalentOn` +
  `Tensor0SBundle.normSq0S_diag_le` (general-s, `Comparison.lean:358`) + `Real.sqrt_mul`.  Subsumes the
  order-3 and order-4 conversions the assembly needs — **NO order-4 sibling needed in AllTimesBounds**.

Imports ADDED to `ConnDiffDerivBound.lean`: `…HCGCompactness.MetricLapDiff`,
`…HCGCompactness.MetricCovDerivLinear` (for `metricCovDerivStep_apply`),
`…Connection.LeviCivita.ChristoffelDiffKoszulDeriv` (for `connDiff_koszul_deriv`/`metricField_totalReg`).
Open ADDED: `DifferentialGeometry.HCGCompactness` (metric-jet currency; `metricCovDeriv` resolves to the
HCG 2-arg one, no clash since `Integral.Connection` is NOT opened).  `LeviCivita`/`metricField_totalReg`/
`connDiff_koszul_deriv` referenced fully-qualified as `DifferentialGeometry.Integral.Connection.…`.

Axiom audit: NOT separately run this session (stand-down); the three helpers compose only standard
mathlib (`DFunLike.ext`, `Real.sqrt_*`) + already-axiom-clean project lemmas, so clean is expected.

### VERIFIED-GREEN session 7 (2026-07-25) — B2 CLOSED in this file

The two remaining lemmas landed, both sorry-free, whole-module `lake build` green, no new imports and
no change to the variable block (`[NormedSpace ℝ E]`-only discipline respected; nothing was added to
`AllTimesBounds.lean`).

- `lcDiff_covOne_le` (private, NEW — not in the session-6 plan).  `lcDiff_norm_le` restated in the
  `metricCovDerivNorm` currency.  The plan called for re-deriving the private `covOne_eq_deriv`
  (which needs the private `covSelfOneAt`, ~35 lines); instead this reads the bound straight off the
  **public** `diff_le_covOne_basis_ref_lc` (`AllTimesBounds.lean:3287`), which is already stated in
  `metricCovDerivNorm` — `lcDiff_norm_le`'s own proof only converts it to `metricDerivNorm` at the
  very last step.  Four lines, and `metricDerivNorm` never enters the file.
- `covDerivConnDiff_g1_le` (private) — the dual core, exactly the planned route.  Conclusion:
  `√(g₁ B B) ≤ (3/2·√normSq0S(g₁,4,mcd2) + √normSq0S(g₁,3,mcd1)·√normSqRS(g₁,1,2)(connDiff))
   · √(g₁vv)·√(g₁ww)·√(g₁uu)`.
- `covDerivConnDiff_gJet_le` (public) — the endpoint.  **Constant proved = the predicted
  `CA = (3/2)·Λ⁴·(Λ'' + Λ·Λ'²)`**, no weakening of the statement.
  Axioms: `[propext, Classical.choice, Quot.sound]`.

`hA1` dischargeability was **verified, not assumed**: a temporary scratch module importing both
`ConnDiffDerivBound` and `UnifCovSumCross` was built green with
`covStepDiff_norm_le g₁ g₂ s S x hCA (fun v w u => covDerivConnDiff_gJet_le hEq hJet1 hJet2 hx v w u)`
as a bare term proof, then deleted.  So B3 can consume this endpoint with `CA` instantiated to
`3 / 2 * Λ ^ 4 * (Λ'' + Λ * Λ' ^ 2)` and no adapter.  (Note the import direction: `UnifCovSumCross`
does NOT import this file, so the consumer side must add the import when it wires B2 in.)

### Route as executed (kept for reference)

Two lemmas, using ONLY already-present ingredients:

1. **The dual core (`covDerivConnDiff_g1_le`, private).**  For `x`, `v w u : TangentSpace I x`, set
   `Wsec/Xsec/Ysec := ContMDiffSection.mk (smoothExtensionTangent x v/w/u) (…_contMDiff …)` (as in P1's
   `covGrad_connDiffSection_flat_eval_eq_inner`), `B := covDerivConnDiff g₂ g₁ (ext v)(ext w)(ext u) x`,
   `Zsec := ContMDiffSection.mk (smoothExtensionTangent x B) (…)`.  Instantiate
   `connDiff_koszul_deriv g₁ g₂ Wsec Xsec Ysec Zsec x`; LHS `= 2·g₁(B, Zsec x) = 2·g₁(B,B)` via
   `smoothExtensionTangent_eq` (`Zsec x = B`) and coe-of-mk = rfl (`↑Wsec = smoothExtensionTangent x v`,
   so `covDerivConnDiff … ↑Wsec ↑Xsec ↑Ysec x = B` defeq).  RHS: rewrite the three `nabla0SFun 3 W field`
   terms by `nabla3_eq_mcd2` into `metricCovDeriv g₁ g₂ 2 x (Fin.cons v ![·,·,·])`, and the last
   `nabla0SFun 2 W (mtf g₁)` term by `(metricCovDeriv_one_apply_section g₁ g₂ Wsec x ![A(u,w),B]).symm`
   into `metricCovDeriv g₁ g₂ 1 x (Fin.cons v ![A(u,w),B])`.  Then:
   - build an internal g₁-ON basis at x (copy the `let D := (tangentMetricData_gen g₁ x).metric; …;
     ob := stdOrthonormalBasis; basis := ob.toBasis; hON` block verbatim from `connDiffVec_norm_le`
     steps (3), or from `covStepDiff_norm_le`'s `hON` block — but with `g₁` as the fibre metric);
   - `abs_apply_le_sqrt_normSq0S g₁ x 4 basis hON (metricCovDeriv g₁ g₂ 2 x) (Fin.cons v ![w,u,B])` etc.
     bounds each combo by `√normSq0S(g₁,4,mcd2)·√(g₁vv)·√(g₁ww)·√(g₁uu)·√(g₁BB)` (`∏_{Fin 4}` = product
     of the four √g₁ via `Fin.prod_univ_…`; the third combo has slot order `![B,w,u]` — same product,
     CS is slot-symmetric);
   - `abs_apply_le_sqrt_normSq0S g₁ x 3 basis hON (metricCovDeriv g₁ g₂ 1 x) (Fin.cons v ![A(u,w),B])`
     bounds the last term by `√normSq0S(g₁,3,mcd1)·√(g₁vv)·√(g₁ A(u,w))·√(g₁BB)`;
   - `connDiffVec_norm_le g₁ (LC g₁)(LC g₂) w u : √(g₁ A(u,w)) ≤ √normSqRS(g₁,1,2)(connDiffTensor
     (LC g₁)(LC g₂) x)·√(g₁ww)·√(g₁uu)` (note `difference cov cov' x Y X` with `Y=u,X=w` gives `A(u,w)`);
   - triangle-inequality the identity `2·g₁(B,B) = Σ± … ≤ Σ|…|`, collect the common `|v||w||u||B|_{g₁}`,
     divide by `√(g₁BB)` (rcases `eq_or_lt` of `Real.sqrt_nonneg`, then `le_of_mul_le_mul_right`, exactly
     as `connDiffVec_norm_le` step (7)).  Result:
     `√(g₁BB) ≤ (3/2·√normSq0S(g₁,4,mcd2) + √normSq0S(g₁,3,mcd1)·√normSqRS(g₁,1,2)(connDiff))·√(g₁vv)√(g₁ww)√(g₁uu)`.
2. **The endpoint (`covDerivConnDiff_gJet_le`, public — MATCHES B3's `hA1`).**  Signature: hypotheses
   `(hEq : MetricUniformEquivalentOn K g₂ g₁ Λ) (hJet1 : MetricCovDerivOrderBoundOn K 1 g₁ g₂ Λ')
   (hJet2 : MetricCovDerivOrderBoundOn K 2 g₁ g₂ Λ'') (hx : x ∈ K) (v w u)`, conclusion the `hA1` body
   `√(g₂.inner x B B) ≤ CA·√(g₂vv)·√(g₂ww)·√(g₂uu)` with `CA = (3/2)·Λ⁴·(Λ'' + Λ·Λ'²)`.  Proof: apply the
   dual core; convert every g₁ factor to g₂ by `sqrt_normSq0S_comp` (at s=4 for mcd2, s=3 for mcd1) +
   the comparability sandwich `(hEq.2 x hx ·).1/.2` for the `√(g₁··) ≤ √Λ·√(g₂··)` vector factors and
   `√(g₂BB) ≤ √Λ√(g₁BB)`; fold `metricCovDerivNorm 2 g₁ g₂ x = √normSq0S(g₂,4,mcd2) ≤ Λ''` (hJet2),
   `metricCovDerivNorm 1 g₁ g₂ x = √normSq0S(g₂,3,mcd1) ≤ Λ'` (hJet1); and `NA_{g₂}`-form of `lcDiff_norm_le`
   — but note `lcDiff_norm_le`/`connDiffVec_norm_le` here run in the **g₁** fibre, so keep `NA_{g₁} =
   √normSqRS(g₁,1,2)(connDiff (LC g₁)(LC g₂) x)` and bound it by `(3/2)√(Λ³)·metricDerivNorm 1 g₁ g₂ g₂ x`
   via `lcDiff_norm_le g₂ g₁ hEq hx` (fibre = g₁ = its `h`; check the swap: `lcDiff_norm_le g h (hEq:
   MetricUniformEquivalentOn K g h C) : √normSqRS(h,1,2)(connDiff (LC h)(LC g) x) ≤ (3/2)√(C³)·
   metricDerivNorm 1 h g g x`, so `g := g₂, h := g₁`), then `metricDerivNorm 1 g₁ g₂ g₂ x =
   metricCovDerivNorm 1 g₁ g₂ x` (re-derive `covOne_eq_deriv` locally — it is private in MetricLapDiff;
   it is short: `metricCovDeriv g₂ g₂ 1 = 0` + `sub_zero`) `≤ Λ'` (hJet1).  Arithmetic: `√(Λ^s)` powers
   combine as `√(Λ⁴)=Λ²`, `√(Λ³)·√(Λ³)=Λ³`, `√Λ·(√Λ)³=Λ²`; close with `nlinarith`/explicit `calc`.

### Ingredients — all confirmed present (file:line)
`connDiff_koszul_deriv` (ChristoffelDiffKoszulDeriv.lean:227) · `abs_apply_le_sqrt_normSq0S`
(Comparison.lean:739) · `connDiffVec_norm_le` (ConnectionDifferenceNorm.lean:60) · `lcDiff_norm_le`
(MetricLapDiff.lean:164) · `metricCovDeriv_one_apply_section` (PointedConvergence.lean:105) ·
`metricCovDerivStep_apply` (MetricCovDerivLinear.lean:101) · `smoothExtensionTangent_eq`
(Curvature/CurvatureOperator/Defs.lean:803) · `metricCovDerivNorm`/`MetricCovDerivOrderBoundOn`/
`metricDerivNorm`/`exists_diagInv_of_metricUniformEquivalentOn` (AllTimesBounds.lean / PointedConvergence.lean,
namespace `DifferentialGeometry.HCGCompactness`).  B3 target `hA1`: `UnifCovSumCross.lean:709-725`.

### Lean lessons (session 7)

- **The whole Koszul→metric-jet rewriting chain worked first try.**  `rw [hAbr, hXx, hYx, hZx] at
  hkos` then the three `nabla3_eq_mcd2` rewrites then `hWx`; the only real friction was instance
  setup and one elaboration issue (below).  The session-6 currency helpers were the right bricks.
- **`haveI : IsManifold I (1 + 1) M` is required**, not just `IsManifold I 1 M`, before
  `TangentBundle.contMDiffVectorBundle (n := 1)` will synthesize.  Symptom is a bare
  `failed to synthesize IsManifold I (1 + 1) M` pointing at the `haveI` line itself.  Copy both
  `haveI`s from `covStepDiff_norm_le`.
- **Term-4 bridge must be `exact`, not `rw`.**  `connDiff_koszul_deriv`'s quadratic term is
  `nabla0SFun 2 (LeviCivita g₂) W (metricTensorField g₁)`, while
  `metricCovDeriv_one_apply_section` says `nabla0SFun 2 (leviCivitaConnectionOfMetric g₂) W
  (metricCovDeriv g₁ g₂ 0)`.  Both differences are pure delta (`LeviCivita ≡
  leviCivitaConnectionOfMetric`, `metricCovDeriv _ _ 0 ≡ metricTensorField _`).  State the `have` in
  the **koszul** syntactic form and close it with `exact h`; then `rw [h4] at hkos` matches.  Same
  trick for `hJ2 : metricCovDerivNorm 2 g₁ g₂ x ≤ Λ''` used as a bound on
  `√normSq0S(g₂, 4, mcd2)` (`2 + 2 ≡ 4` plus the `metricCovDerivNorm` delta).
- **`Fin.cons a ![b,c,d] i` will not elaborate inside a standalone `∏`-statement**: the motive
  `α : Fin (n+1) → Sort _` stays a metavariable and you get `argument has type ?m i but is expected
  to have type TangentSpace I x`.  Do NOT state a separate `hprod4` helper.  Instead take the
  Cauchy–Schwarz result first (where `Tensor0SSpace`'s domain has already pinned the motive), then
  `refine le_trans h (le_of_eq ?_); congr 1; change (∏ i : Fin 4, … (![a,b,c,d] i) …) = _; simp
  [Fin.prod_univ_four]`.  The `change` from `Fin.cons` to `![…]` is `rfl` (`Matrix.vecCons` is
  `Fin.cons`) and is what lets the `Matrix.cons_val_*` simp set fire.  Use `change`, not `show` —
  `linter.style.show` flags a `show` that alters the goal.
- **`linarith`/`nlinarith` do the product bookkeeping for free.**  Do not hand-normalise the
  Cauchy–Schwarz right-hand sides (`M2·(Sv·Su·Sw·SB)` vs `M2·(Sv·Sw·Su·SB)`); their ring
  normalisation identifies the monomials.  The `|T| ≤ …` collection, the `SB·(2·SB) ≤ SB·(…)`
  restatement before `le_of_mul_le_mul_left`, and the final halving were all one-liners.
- **`√Λ` bookkeeping is `linear_combination` work, not `nlinarith` work.**  For the two places where
  `(√Λ)² = Λ` has to be used inside an equality — `(Λ√ΛΛ')·(3/2·Λ√ΛΛ') = 3/2·Λ³Λ'²` and the final
  `√Λ·(Cb·(√Λ·)³) = 3/2Λ⁴(…)` — use `linear_combination (coeff) * hs2` with
  `hs2 : Real.sqrt Λ ^ 2 = Λ`.  For the outer one the coefficient carries the extra factor
  `(√Λ² + Λ)` because the identity needs `s⁴ − Λ² = (s²−Λ)(s²+Λ)`.
- **`positivity` cannot see through `set`.**  Declare every `0 ≤ …` fact BEFORE the `set` that
  abstracts the term, so `set` rewrites the hypothesis too; afterwards the variable is opaque.  In
  the endpoint the polynomial-in-`Λ` nonnegativity (`0 ≤ Λ'' + Λ·Λ'²`) also needs explicit
  `add_nonneg`/`mul_nonneg` — `positivity` has no access to `hEq.1` or the jet hypotheses.
  `Λ' , Λ'' ≥ 0` come free from `Real.sqrt_nonneg` through the jet bounds; no extra hypotheses.
- The stale-`.olean` shape bit once at the start: `object file '…ChristoffelDiffKoszulDeriv.olean'
  does not exist` from a dead build.  One targeted `build -NoLakeLock +Module.Name` fixed it.

### Lean lessons (session 6)
- The `field` in `connDiff_koszul_deriv`'s RHS = `metricCovDeriv g₁ g₂ 1` — prove by `DFunLike.ext`
  (`Tensor0SField` is a `ContMDiffSection` abbrev) + `totalNabla0S_apply` + `metricCovDerivStep_apply.symm`
  (default-transparency `exact` bridges `0+2≡2` and `LeviCivita≡leviCivitaConnectionOfMetric`; `rw`'s
  reducible auto-rfl does NOT close these — use `exact _.symm`).
- `metricCovDerivStep_apply` lives in `MetricCovDerivLinear.lean` (NOT pulled in by `MetricLapDiff`);
  import it explicitly.
- Opening `DifferentialGeometry.HCGCompactness` (not `Integral.Connection`) avoids the `metricCovDeriv`
  1-arg/2-arg name clash; qualify the few `Integral.Connection` names.
- `normSq0S_diag_le` (Comparison.lean:358) is general-`s`, so ONE `sqrt_normSq0S_comp` covers s=3 and s=4;
  the recon's "add an order-4 sibling in AllTimesBounds" is unnecessary — AllTimesBounds is UNTOUCHED.

## Status / next

- 2026-07-25 (session 8 — the `hA1` discharge is WIRED): `covStepDiff_of_jets` landed in
  `UnifCovSumCross.lean` (public, axioms `[propext, Classical.choice, Quot.sound]`, whole-module
  build green, zero warnings on the file).  It is the fully-discharged, `D_N`-facing jet variant of
  `covStepDiff_jet_le`: it drops `hCA`/`hA1` and takes the metric-jet inputs, discharging `hA1` via
  `covDerivConnDiff_gJet_le` with `CA = (3/2)·Λ⁴·(Λ'' + Λ·Λ'²)`.  `UnifCovSumCross.lean` now
  `import`s this file (verified acyclic).  **This closes the "consumer side has to add that import"
  item** for the T-B chain.  Design ruling (from the coordinator): there were no live call sites —
  the "three T-B consumers" are the not-yet-written `D_N` recursion — so the metric-jet hypotheses
  went into the NEW variant's SIGNATURE (honest-input-bundle style), not threaded through existing
  signatures.  KEY subtlety recorded there: `covStepDiff_jet_le`'s own NA-fold measures
  `∇g₂ w.r.t. g₁` while this endpoint discharges `hA1` via `∇g₁ w.r.t. g₂`, so the comparability is
  shared through `metricUniformEquivalentOn_symm` (one `hEq`, same `Λ`) but the two first-order jets
  are genuinely distinct facts — `covStepDiff_of_jets` carries BOTH `hJet1` (∇g₁/g₂) and `hJet1'`
  (∇g₂/g₁), sharing the constant `Λ'`.  The **norm** variant (of `covStepDiff_norm_le`, NA explicit)
  was NOT added: its statement alone exceeds the coordinator's ≤10-line budget and the jet variant is
  the `D_N` API; norm stays abstract and can be added trivially (same one-line composition) if wanted.
- 2026-07-25 (session 7): **B2 CLOSED inside this file.**  `covDerivConnDiff_gJet_le` proved
  sorry-free with the predicted constant `CA = (3/2)·Λ⁴·(Λ'' + Λ·Λ'²)`; axiom-clean; whole-module
  build green with zero warnings.  `hA1` of `covStepDiff_norm_le` verified dischargeable by an
  actual (throwaway) build, not by inspection.  Nothing in this file is a frontier any more —
  every declaration is proved.
  **Remaining wiring (OUTSIDE this file):**
  1. DONE (session 8, above): `UnifCovSumCross.lean` imports this file and exposes
     `covStepDiff_of_jets`, the discharged T-B jet step.
  2. The 2a-tel composition-(b) consumer (same `covDerivConnDiff` sub-frontier) can now discharge
     `hA1` the same way once that consumer is written.
  3. Home debt (unchanged): promote `covDerivConnDiff_fibreNorm_le` (and possibly the dual core) to
     `Geometry/Curvature/CovDerivConnDiffFibreExtraction.lean`, and de-privatise the parent's
     `covGrad_connDiffSection_flat_eval_eq_inner` so this file's private copy can be dropped.
  Note `covDerivConnDiff_fibreNorm_le` (P1) is now confirmed UNUSED by the dual route.  Keep it: it
  is the honest fibre reduction and is the entry point if a fibre-norm endpoint is ever wanted.
- 2026-07-25 (session 6): STAND-DOWN pause.  File GREEN.  P1 + 3 P2 currency/comparability helpers
  landed (verified, whole-file `lake build` EXIT=0).  Dual-route chosen (see above).  Resume at the two
  numbered "EXACT NEXT STEPS" (dual core + endpoint) — all ingredients present, no new frontier.
- 2026-07-25 (session 1): P1 LANDED (verified, axiom-clean).  Recon COMPLETE (`UNIF_ITEM6_RECON.md`).
