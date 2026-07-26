# InteriorProductJetBound — the ip-vector Leibniz jet engine

Built 2026-07-26 (ip-engine session) to discharge the frozen `lc0VB` atom's `vbPass_jetL2`
(see `LieCorr0CoeffL2JetBound.md`, sessions 5–9) and to serve brick 4's radius-free
re-derivation (`LieCorr0CoeffDiffRadiusFree.md`).

## What it provides

- `ipTracePerm : Equiv.Perm (Fin 3) = swap 1 2` — the slot arrangement for the trace.
- `ipLowCc g ω : SmoothCcTensor g 2 1` — the interior product with `♯ω` on `(0,2)`-tensors,
  DEFINED as a composition of committed operator-field constructions:
  `appCcRS g 2 3 1 (reindexCoeffGen (cometricDoubleTraceField g 1) ipTracePerm)
  (slotExtend (slotExtend ω))` — fixed `g`-cometric double trace ∘ input-slot swap ∘ `A ↦ A ⊗ ω`.
- `ipLowCc_toSec_ip` — the fibre identification: with `hflat : unitModel g 1 ω x (·z) = g.inner x V z`,
  `(ipLowCc g ω).toSection x = Tensor0SBundle.interior_product 1 x V`.
- `rfns_icg_ipLow_le` — pointwise jets: `∃ c, ∀ ω l x, |∇ˡ(ipLowCc g ω)|²(x) ≤ c l · ∑_{m≤l} |∇ᵐω|²(x)`.
- `norm_icg_ipLow_le` — the jet-`L²` form.  Both are **radius-agnostic** (constants depend on
  `g, l, dim E` only), so ballUniform and R-free consumers use them identically.

## Why no new Leibniz induction (the design point)

The session-8 spec asked for an `interior_product` sibling of
`rfns_iteratedCovGrad_slotExtend_le`.  Instead of a new `∇ⁱ`-commutation induction (the
slotExtend route costs ~700 lines), `ipLowCc` is *defined* through committed pieces so the jet
bound is a product-grid corollary:

- the grid `rfns_iteratedCovGrad_appCcRS_diagonalProductGrid_rankLeft_le` bounds the composition;
- the trace arm is `∇`-parallel (`cometricDoubleTraceField_covGrad_eq_zero`, rank-generic), so
  only its order-`0` term survives (`Finset.sum_eq_single 0`); its sup comes from
  `exists_bound_riemannianFiberNormSq_smoothCcTensor` (compactness — this is why `c` is
  existential and `g`-dependent);
- the input-slot reindex is jet-invariant (`rfns_iteratedCovGrad_reindexCoeffGen_eq`);
- each `slotExtend` costs one `dim` factor (`rfns_iteratedCovGrad_slotExtend_le`, twice).

Placement: beside the grid (Sobolev/TensorHilbert), NOT beside `slotExtendFib`'s jet lemma in
`OperatorFieldFibreNormJet` — the proof consumes the grid, which lives above that layer.

## Proof-route notes (for cloners)

- The eval proof clones the `RicciArmResidualFieldGridWindow` private templates:
  `orthoFrame_basis/expansion_at_center` (orthonormal expansion at the frame center),
  `cometricDoubleTraceFib_toModel_center` (orthoframe-diag trace read),
  `tensor0S_rank0_eq_smul_unit` (rank-0 curry), `toModel_cons_sum_smul` (slot-0 multilinearity).
- `ipTracePerm = swap 1 2` is self-inverse, so the `domDomCongr` direction ambiguity vanishes.
- Landmines hit and fixed: `ω` as a binder clashes with the ContDiff `ω` scoped notation (use
  `om`); PowerShell `Set-Content -Encoding utf8` writes a BOM that Lean rejects (write via .NET
  `UTF8Encoding($false)`); a `Fin.cons`-tuple applied at `(σ i)` needs a `: Fin 3 → E` type
  ascription or the dependent motive leaks; two `tensor0S_curry_apply_eval` rewrites in the
  rank-0 step over-close the goal (defeq) — one suffices.
- `iteratedCovGrad` of the zero tensor vanishes by induction on `iteratedCovGrad_succ` +
  `covGrad_zero` (no committed lemma existed; local `ipjb_icg_zero`).

## Status

Verification passed (focused check + targeted module build, in-graph).  All three public
declarations axiom-clean.  Consumers so far: `LieCorr0CoeffL2JetBound.lean` (`vbSplit`,
`vbPass_jetL2`).
