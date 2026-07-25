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

## Why this is the right brick

B2 (the full ungated output-vector bound in `Λ,Λ',Λ''`) factors as **P1 ∘ P2**:
- P1 = this file (ungated Cauchy–Schwarz reduction to the fibre norm) — DONE.
- P2 = `‖covGrad g₂ 1 2 (connDiffSection g₁ g₂)‖_{fibre} ≤ CA(Λ,Λ',Λ'')` — the SINGLE remaining frontier,
  the a=1 analogue of `lcDiff_norm_le`.  See `UNIF_ITEM6_RECON.md` §4 for its brick sequence.

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

## Status / next

- 2026-07-25: P1 LANDED (verified, axiom-clean).  Recon COMPLETE (`UNIF_ITEM6_RECON.md`).
- NEXT (P2, the frontier): `‖covGrad g₂ 1 2 (connDiffSection g₁ g₂)‖_{fibre} ≤ CA(Λ,Λ',Λ'')` under
  `MetricUniformEquivalentOn K g₂ g₁ Λ` + `MetricCovDerivOrderBoundOn K {1,2} g₁ g₂ {Λ',Λ''}`.  Crux =
  the differentiated Koszul identity (`UNIF_ITEM6_RECON.md` §4 P2.a).  Genuine multi-brick / multi-session.
