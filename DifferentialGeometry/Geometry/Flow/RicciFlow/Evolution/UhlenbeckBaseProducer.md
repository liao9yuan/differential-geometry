# Uhlenbeck base `∂ₜRm04` discharge — plan (Lemma 6.1)

**Target.** Prove `Riemann04BTensorWithRicciDriftEvolutionInFrameOn Rm04 roughLapRm04 B ricciOneUp`
(`Uhlenbeck.lean:727`) for a Ricci-flow solution in the coordinate frame:
`∂ₜR_{ijkl} = ΔR_{ijkl} + 2(B_{ijkl} − B_{ijlk} + B_{ikjl} − B_{iljk}) − drift_{ijkl}`,
with `drift = riemann04RicciDriftInFrame ricciOneUp Rm04` (the four `R_·^p R_{p···}` contractions).
This is Hamilton's curvature evolution — the **un-traced** analogue of the built Ricci
Lichnerowicz evolution.

## Mathematical route (Morgan–Tian / Hamilton), mirroring the proven Ricci case

The Ricci case (`Evolution/Ricci/{Bianchi,Commutator}.lean`) factors as
`ricciVariationExpandedRHS` (the ∇²Ric form of `∂ₜRic`) **=** evolution RHS
(`ΔRic + Rm∗Ric`), the second equality via the *differentiated contracted Bianchi*
+ *Ricci commutators*. The (0,4) discharge factors the same way:

**Lemma A — variation/lowering (the `∇²Ric` form of `∂ₜRm04`).**
1. `∂ₜΓ^k_{ij} = −g^{kl}(∇_iR_{jl}+∇_jR_{il}−∇_lR_{ij})`  [`christoffelEvolution_of_solution` — DONE]
2. `∂ₜR^l_{ijk} = ∇_i(∂ₜΓ^l_{jk}) − ∇_j(∂ₜΓ^l_{ik})`  [`rm13Deriv_of_solution` — DONE]
3. Lower: `∂ₜR_{mijk} = g_{ml}∂ₜR^l_{ijk} + (∂ₜg_{ml})R^l_{ijk}`,
   with `∂ₜg = −2Ric` ⇒ the `−2R_{ml}R^l_{ijk}` drift contribution.
4. Substitute (1) into `g_{ml}∂ₜR^l_{ijk}` using `∇g = 0`:
   `= −∇_i∇_jR_{km} − ∇_i∇_kR_{jm} + ∇_i∇_mR_{jk} + ∇_j∇_iR_{km} + ∇_j∇_kR_{im} − ∇_j∇_mR_{ik}`.
   Call this `rm04VariationExpandedRHS` (a `∇²Ric` combination), analogous to
   `ricciVariationExpandedRHSInFrame`.

**Lemma B — Bianchi+commutator (the `∇²Ric` form = `ΔRm + 2B − drift`).**
5. `(∇_j∇_i − ∇_i∇_j)R_{km}` etc. = curvature commutators (Ricci identity) ⇒ `Rm∗Ric` terms
   [banked: `curvComm`, `second_bianchi`, the `tensor0S_ricciIdentity` used in the Ricci case].
6. The remaining `∇∇Ric` terms convert to `Δ R_{ijkl}` via the *differentiated second
   (contracted) Bianchi* `∇_pR^p_{ijk} = ∇_jR_{ik} − ∇_kR_{ij}` and `Δ = ∇^p∇_p`
   [banked general identities in `Geometry/Curvature/Bianchi.lean`: `second_bianchi`,
   `contracted_bianchi`, `contractOfSecond`; to be specialized to the moving solution].
7. Collect ⇒ `ΔRm04 + 2(B…) − drift`.

## Banked pieces to reuse
- `rm13Deriv_of_solution` (`∂ₜRm13`) — built this session.
- `christoffelEvolution_of_solution` (`∂ₜΓ`) — built this session.
- `solution_rm04LowersRm13At`, `rm13_apply_eq_rm04_raise` (`RmRaisingBridge.lean`) — lowering realization.
- `Geometry/Curvature/Bianchi.lean`: `second_bianchi`, `contracted_bianchi`, `curvComm`,
  `contractOfSecond` — the abstract (0,4) Bianchi identities.
- The Ricci-case templates `ricciVariationExpandedRHSInFrame`,
  `RicciContractedCommutatorsInFrame_of_tensor0S_ricciIdentity_lc`,
  `differentiatedContractedBianchiInFrameOnLocal_of_regular` — structure to mirror un-traced.

## Decomposition into Lean lemmas (effort: multi-session)
- A1: `rm04VariationExpandedRHS` def (the ∇²Ric combination) + sign bookkeeping.
- A2: `∂ₜRm04 = rm04VariationExpandedRHS` (lower `rm13Deriv` + `∂ₜg=−2Ric` product rule).
  Needs a time-derivative raise/lower bridge (`∂ₜ(g·rm13) = (∂ₜg)·rm13 + g·∂ₜrm13`) at the
  component level — the first genuinely new sub-theorem.
- B1: differentiated second-Bianchi for the moving solution (un-traced).
- B2: (0,4) curvature commutators (Ricci identity at rank (0,4)).
- B3: `rm04VariationExpandedRHS = ΔRm04 + 2B − drift` (assemble B1+B2).
- C: package `Riemann04BTensorWithRicciDriftEvolutionInFrameOn` from A2+B3, then feed the
  banked `uhlenbeckCurvatureEvolution_of_solution_components` → pulled heat form.

## STATUS — A-half of Lemma 6.1 DONE (2026-06-08, GREEN build 3716, axiom-clean target)
- ✅ **Brick 1:** `metricCompInFrame_timeDeriv` — `∂ₜ metricCompInFrame = −2·ricciCompInFrame`
  from `hS.equation`.
- ✅ **Brick 2 (the gateway realization, was the "missing API"):**
  `realizedRmBase_eq_curvCoeff_lower` — `Rm04_{m₀m₁m₂m₃} = Σ_p curvCoeff^p_{m₀m₁m₂}·g_{m₃p}`,
  by chaining `solution_rm04LowersRm13At` + `rm13_eval_eq_christoffelCurvCoord` + the metric
  flat (`dualToCotangent_apply_gen`/`tangentFlatLinear_apply_gen`, both `rfl`).
- ✅ **A2:** `realizedRmBase_timeDeriv` — `∂ₜRm04` in the expanded `∇²Ric` form, by the
  product rule `HasDerivWithinAt.sum`/`.mul` on Brick 2, with `∂ₜcurvCoeff = rm13Deriv_of_solution`
  and `∂ₜg = metricCompInFrame_timeDeriv`. (Lean: `HasDerivWithinAt.sum`'s `f'` is a
  higher-order metavar — give per-summand derivs explicitly via a `hterm` hyp; `.congr` needs
  `Finset.sum_apply` to match the sum-of-functions form.)

  **So `∂ₜRm04` is now ESTABLISHED** (the whole variation/lowering half). The RHS is the
  expanded `Σ_p (∂ₜΓ-covderiv difference)·g + curvCoeff·(−2Ric)` form.

## B — PRIMARY ROUTE (3D algebraic, via Weyl=0) — `ham3_main` only needs dim 3

**Why this route.** In `dim 3` the Weyl tensor vanishes, so `Rm04` is an explicit *algebraic*
function of `(Ric, S, g)` (Kulkarni–Nomizu). The `∂ₜRm04` evolution then follows by
*differentiating that algebraic identity* using the already-built `∂ₜRic`, `∂ₜS`, `∂ₜg` — **no
second-Bianchi / curvature-commutator re-derivation at all** (that work is already inside
`∂ₜRic`/`∂ₜS`). `ham3_main` only needs the dim-3 instance, so this is the shortest path.
*Tool is the 3D decomposition, NOT contracted Bianchi (which goes ∇Ric→∇Rm and cannot invert
the trace; only Weyl=0 makes the trace invertible).*

**Banked pieces (confirmed present):**
- 3D decomposition `Rm04 = KN(Ric,S,g)`: `Geometry/Curvature/DimensionThree/RiemannFromRicci.lean`
  — `rm04Comp_displayedRiemannFromRicci3D_at` (orthonormal `Fin 3` basis):
  `R_{ijlk} = R_{il}δ_{jk} − R_{jl}δ_{ik} − R_{ik}δ_{jl} + R_{jk}δ_{il} − (S/2)(δ_{il}δ_{jk}−δ_{jl}δ_{ik})`,
  given `RiemannFromRicci3DTraceDataAt g Ric scalar Rm04 basis`. Also `RicciControlsRm.lean`,
  `CurvatureAlgebra.lean`.
- `∂ₜRic = ΔRic + reaction` ✅ (`evol_ricci_lichnerowicz_...`).
- `∂ₜS = ΔS + 2|Ric|²` ✅ (scalarEvolution, tasks #8–10).
- `∂ₜg = −2Ric` ✅; `∇g = 0` ✅ (Levi-Civita) ⇒ **`Δ` passes through the KN `⊙g`**, so
  `ΔRm04 = KN(ΔRic, ΔS, g)` (diffusion term for free).

**Route (each step bounded, NO Bianchi):**
- ✅ **B3a DONE** (`rm04_kn_gform`, `Geometry/Curvature/DimensionThree/RiemannFromRicci.lean`,
  GREEN build 3586, axiom-clean): the **basis-free metric-form KN identity** in dim 3,
  `Rm04(X,Y,Z,W) = Ric(X,Z)g(Y,W) − Ric(Y,Z)g(X,W) − Ric(X,W)g(Y,Z) + Ric(Y,W)g(X,Z)
  − (S/2)(g(X,Z)g(Y,W) − g(Y,Z)g(X,W))` for ALL vectors, from `RiemannFromRicci3DTraceDataAt`.
  Proof: lift the banked δ-form via `tensor0S_apply_eq_sum`+`sum_fin_four_fun`+`inner_eq_sum_repr3`
  + `Ric`/`g` expansions, brute-forced on `Fin 3` (`simp [Fin.sum_univ_three,…]; ring`).
  **FRAME WORRY RESOLVED:** the conclusion is *basis-free* — the orthonormal basis is internal to
  the proof, so at each `t` (with its own orthonormal basis) the identity holds for FIXED vectors
  (e.g. coordinate-frame `e_a` at `x₀`, `t`-independent). So differentiation in a fixed frame is
  direct; no moving-frame reconciliation needed.
- **NEXT — B3a′ (trace-data discharge):** for the solution at each regular `t`, build
  `RiemannFromRicci3DTraceDataAt (g t) (Ric t) (S t) (Rm04 t) (orthonormal basis at t)`. Banked:
  `algebraicCurvatureSymmetries3_standardRmCompAt_of_leviCivita_realizes` (symmetries),
  the Ricci/scalar trace relations (3D), an orthonormal basis at each `t` (Gram–Schmidt). Sign
  convention: displayed `Ric`/`scalar` vs geometric — use the `−Ric`/`−scalar` bridge as in
  `rm04_firstTrace_einstein3_at`.
- **THEN B3b:** apply `rm04_kn_gform` at fixed coordinate-frame `e_a,e_b,e_c,e_d` ⇒
  `Rm04(t)(e_a,e_b,e_c,e_d) = KN(Ric(t),S(t),g(t))` (scalar identity in `t`); differentiate by the
  product rule.
- B3b: differentiate (product rule on the multilinear KN): `∂ₜRm04 = KN(∂ₜRic,∂ₜS,g) + KN(Ric,S,∂ₜg)`.
- B3c: substitute the three built evolutions + `Δ`-through-`g`:
  `∂ₜRm04 = ΔRm04 + [KN(Ric-reaction, scalar-reaction, g) + KN(Ric, S, −2Ric)]`.
- B3d: the bracket `= 2(B…) − ricciDrift` — a **finite dim-3 algebraic identity** (all `B`,
  `Ric`-contractions reduce to `Ric` via the same KN decomposition). `fin_cases` + `ring`-style.
- B3e: package `Riemann04BTensorWithRicciDriftEvolutionInFrameOn` (dim 3) via `HasDerivWithinAt.congr_deriv`.

A2 (`realizedRmBase_timeDeriv`, the `∇²Ric` form) stays as a verified alternative establishment
of `∂ₜRm04` but is NOT on this route — the 3D route differentiates the KN identity instead.

- Downstream already built: pullback (`uhlenbeckCurvatureEvolution_of_solution_components`) +
  `∂ₜ∇ᵏRm` assembly (`nablaKRm_timeDeriv_of_solution`).

## TODO (deferred) — B GENERAL-DIMENSION route (un-traced second Bianchi)

Only needed if the project later wants the Uhlenbeck base in `dim ≠ 3`. **Not required for
`ham3_main`.** This is the un-traced (rank-4, 4 free indices) analogue of the entire
~1250-line `Ricci/Commutator.lean` + the differentiated second Bianchi:
- final reduction = short `rw`+`ring` delegating to an `Rm04ContractedCommutators` package
  (mirror `ricciVariationExpandedRHS_eq_evolutionRHS_of_commutators`, `Commutator.lean:1093`);
- package proven from (i) un-traced *differentiated second Bianchi* (build; cf.
  `DifferentiatedContractedBianchiInFrameOnLocal`) and (ii) rank-4 `tensor0S_ricciIdentity_of_torsionFree`
  (`Tensor/RicciIdentity/Tensor0S/Formula.lean:975`, rank-general — usable directly).
- Starts from A2's `∇²Ric` expanded RHS (`realizedRmBase_timeDeriv`).
- Hardest single theorem in the pillar; warrants GPT Pro route consultation on the index
  bookkeeping. **Deferred.**
