# CGTPaths

## State — 2026-07-27

The quantitative fixed-endpoint homotopy layer and the short-path selector are
implemented, focused-green, and exact-current.

`pathLen` measures a `Path` through its canonical real-line extension.
`IsFlatC1Path` records a global `C¹` extension with constant endpoint collars.
The checked flat-path calculus consists of `refl`, `symm`, and `trans`, with
the exact length identities `pathLen_refl`, `pathLen_symm`, and
`pathLen_trans`.

`ShortHomotopy L p q` stores an ordinary `Path.Homotopy p q` together with the
strict bound `pathLen (hom.eval t) < L` for every homotopy time.  Its checked
operations are `mono`, `refl`, `symm`, `trans`, and `appendRight`.

`exists_flat_path` packages Mathlib's Riemannian-distance path theorem as a
globally `C¹` path with constant endpoint collars and the same strict length
bound.  No path quotient or parallel smoothing hierarchy is introduced.

The next consumer is the actual inverse-fiber injection in
`CGTEvenCover.lean`.

Honest accounting:

- bounded homotopy and flat-path relation layer: theorem/API 100%;
- short exponential-lift producer: theorem 100%, dedicated machinery 100%;
- paper Lemma 4.4 endpoint cancellation: theorem 100%;
- paper Lemma 4.5 even cover: theorem 0%, dedicated machinery about 60%;
- `intrLoop_ge_cgt`: theorem 0%;
- dedicated pointwise CGT machinery: about 45–50%;
- sequence-level `InjRadiusDecayInput` producer: theorem 0%;
- unconditional metric compactness theorem: 0%;
- whole HCG supporting machinery: about 61%.
