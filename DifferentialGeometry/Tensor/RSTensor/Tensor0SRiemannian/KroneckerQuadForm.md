# KroneckerQuadForm.lean — brick 2 of `ric_bound` (the non-diagonal norm bound)

Pure linear algebra feeding `coordInner0S` (Comparison.lean) → `aN_intrinsic_point`
(RicBoundAssembly) → `ric_bound`.  Goal: convert an intrinsic `gRef`-norm into the
raw frame-component `ℓ²` when the frame Gram's inverse-eigenvalues are bounded below.

## Verified (2026-06-10, sorry-free, focus-checked)

- **`sum_posSemidef_mul_posSemidef_nonneg`** — PSD-pairing: `0 ≤ ∑ i j, M i j * G i j`
  for real PSD `M, G`.  Proof: spectral decomposition of `M`
  (`M i j = ∑ k λ_k U_ik U_jk`), reorder the triple sum, each term
  `λ_k · (U_·kᵀ G U_·k) ≥ 0`.  Imports: `Mathlib.Analysis.Matrix.Spectrum/.PosDef`
  (the `LinearAlgebra.Matrix.Spectrum` olean is NOT built in this checkout — use the
  `Analysis.Matrix.*` ones, as MaximumPrinciple.lean does).
- (sibling, in Comparison.lean) **`coordInner0S_identity_le_pow_diagonal`** — the
  diagonal case `coordInner0S Id ≤ (1/m)^s coordInner0S (diagInv μ)` for `μ ≥ m`.

## REMAINING capstone — `quadForm_id_le_pow` (the induction)

`(1/C)^s · ∑_I c_I² ≤ ∑_{I,J} (∏_a Q(I_a,J_a)) c_I c_J` for symmetric `Q ≥ (1/C)Id`,
any `c : (Fin s→Idx)→ℝ`.  Induction on `s`:
- base `s=0`: `Fin 0→Idx` is `Unique`; `∏` over `Fin 0` = 1; both sides = `c(∅)²`.
- step: peel index 0 via `Fin (s+1)→Idx ≃ Idx × (Fin s→Idx)` (`Fin.cons`/`Fin.tail`);
  `∏_{Fin(s+1)} = Q(k,l)·∏_{Fin s}` (`Fin.prod_univ_succ`).  Set `v_k := c(cons k ·)`,
  `B_s(u,w) := ∑ (∏Q) u w` (the `s`-form).  Then RHS = `∑_{k,l} Q(k,l) B_s(v_k,v_l)`.
  - `M := Q - (1/C)Id` is PSD (from the quadratic-form lower bound + `hQsymm`).
  - `Gmat k l := B_s(v_k,v_l)` is PSD: `∑_{k,l} a_k a_l B_s(v_k,v_l) = B_s(Σ a v, Σ a v)
    ≥ 0` by IH (bilinearity of `B_s` + IH gives `B_s(w,w) ≥ (1/C)^s Σw² ≥ 0`).
  - `sum_posSemidef_mul_posSemidef_nonneg M Gmat`: `∑ M_kl Gmat_kl ≥ 0`
    ⟹ `∑ Q_kl B_s(v_k,v_l) ≥ (1/C) ∑_k B_s(v_k,v_k) ≥ (1/C)·(1/C)^s ∑ c² = (1/C)^{s+1}∑c²`.

Then apply to `coordInner0S` (Comparison.lean): `coordInner0S` unfolds to exactly the
`∑_{I,J}(∏Q) c c` form with `c = tensor0SComponent`, giving the non-diagonal
`coordInner0S_identity_le_pow` that brick 2 consumes.

ASSESSMENT: ~100 lines, fiddly `Fin.cons` reindex + the Gram-PSD-from-IH bilinearity
expansion + the `M`-PSD bridge.  Self-contained pure linear algebra → ideal Pro-consult
candidate (full design above), or a multi-iteration solo grind (Comparison/this-file
checks are ~30–50s each).
