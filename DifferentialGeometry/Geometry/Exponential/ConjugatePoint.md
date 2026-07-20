# ConjugatePoint.lean

## 2026-07-19 created (option-1 lane, brick N-a + N-b; interface RULED by user)

The conjugate-point interface, in the form the user ruled ("differential def
+ bridge"): definition = differential-singularity of the intrinsic
exponential; Jacobi phrasing = bridge theorem.  All green, build-verified,
no `sorry`:

- `IsConjVec g hEnorm p x` — the vector-slot differential of
  `expMapIntrinsic g hEnorm p` at `x` is not injective.
- `isConjVec_iff` — ⟺ a nonzero kernel vector.  (Manual injectivity/kernel
  equivalence; `map_sub` as a `rw` pattern FAILS here — the goal's `a - b`
  and `map_sub`'s elaborate through different-but-defeq `Sub` instance paths
  (`TangentSpace 𝓘(ℝ,E) x` vs `E`); term-mode `calc … := map_sub f a b`
  unifies fine.  Also: `push_neg` is deprecated in this pin — use
  `push Not`.)
- `isConjVec_iff_jacobi` — ⟺ some variation Jacobi field with `w ≠ 0`
  vanishes at `t = 1` (bridge through `intrinsic_jacobi_one`; the `rw` needs
  a trailing explicit `rfl`).
- `jacobiVar_zero` — the variation field vanishes at `t = 0`
  (`intrinsicGeodesic_zero` + `mfderiv_const`), giving the classical
  "nontrivial Jacobi field vanishing at both ends" phrasing.

No smallness/injectivity-radius hypothesis anywhere — meaningful at every
scale via `intrinsicExp_smooth`.

## Remaining N frontier (next planning pass)

- N-c: the endpoint covariant-derivative identity `D_t J_w(0) = w` (check
  first whether the intrinsic lane's endpoint identities already provide it —
  `intrinsicGeodesic_mfderiv_zero` is the t-velocity version; the s-field
  version needs the `∂ₛ∂ₜ` commutation at `0`).
- N-d: the index-form argument (minimizing ⟹ no INTERIOR conjugate vector)
  — the genuinely hard brick: broken-variation second-variation comparison
  from a Jacobi field vanishing at an interior time.  Assets:
  `Variation/SecondVariation{,Minimiser}.lean`, `jacobi_unique`,
  `exists_intrFrame`, Wronskian layer.  Reference route:
  frenzymath `IndexForm*` + `NoConjugateOfMinimizing` +
  `MinimalGeodesicNoConjugate` (five files — plan before implementing).
