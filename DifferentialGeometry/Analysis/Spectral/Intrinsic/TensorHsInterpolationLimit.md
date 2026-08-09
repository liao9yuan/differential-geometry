# Tensor Hs interpolation and spectral exhaustion

## Role

This module contains rank-generic spectral compactness bricks for
`tensorHs`.  In addition to the existing interpolation theorems, it now owns
the canonical finite spectral exhaustion for arbitrary tensor rank `(r,s)`.

## Generic exhaustion

`eigenFinset` is defined directly from
`tensorEigenIdx_one_add_lambda_lt_finite`.  The companion lemmas identify
membership, prove monotonicity, show that every eigen-index eventually occurs,
and package convergence to the top finset filter.  This is the low-level API
needed by scalar `(0,0)` Galerkin compactness; the older `(0,2)`-specific
`eigenIdxFinset` remains a compatibility API and is not imported backwards.

No convergence hypothesis, chart selector, or geometric assumption was added.

## Coordinate convergence

`tendsto_of_coeff` is now the canonical rank-generic coefficient-to-Sobolev
compactness bridge: coordinatewise convergence plus a uniform higher-order
bound gives norm convergence after a strict Sobolev downshift.  The former
private duplicate in the `(0,2)` forcing-limit file was removed, and its sole
consumer now uses this lower-layer theorem directly.  The pre-existing
low-norm interpolation theorem is retained as a short compatibility entrypoint
derived from `tendsto_of_coeff`.

`cont_of_coeff` is the corresponding parameterized continuity bridge.  It
applies `tendsto_of_coeff` to every convergent sequence in a first-countable
domain, using the uniform higher-order bound on the original family.  This is
the reusable producer needed to turn the all-order Galerkin coefficient limit
into a continuous path after one strict Sobolev downshift.

## Verification

The generic exhaustion, coefficient-convergence, and coefficient-continuity
sources are implemented without `sorry`, and focused verification passed.
These APIs and their dedicated machinery are 100% complete.  The downstream
`scalar_gal_subseq` theorem is also verified elsewhere; the current frontier is
the separate `scalar_gal_limit` strong-solution identification theorem.  The
Perelman noncollapsing endpoint theorem remains theorem-level 0% and is not
claimed by this API addition.

## M1 (2026-08-04): `weight_sum_le_normSq` — Finset Bessel truncation

Added beside `weight_mul_coeff_sq_le_normSq`, whose single-mode statement it
generalizes to any finite index set:
`∑_{i∈S} (1+λᵢ)^σ (T.coeff i)² ≤ ‖T‖²`.

Why here: this is the step a spectrally truncated (Galerkin) energy estimate needs
in order to read a FULL-`Hˢ` bound on a function that is not in the truncation
subspace — the projected pairing term is a finite sum over `S`, while the DeTurck
jet ladder that bounds it speaks about `‖·‖_{Hˢ}`.  It is prerequisite (M1) of the
rung-3 tower-direct closure (see `ShortTime/LowRegAllOrderJet.md` and
`ShortTime/UNIF_EXISTENCE_PLAN5.md` No. 146-executor).

Lean lesson: the Mathlib name is `Summable.sum_le_tsum`, NOT `Finset.sum_le_tsum`
(which does not exist outside the `ENNReal` namespace).  Its argument order is
`(s : Finset ι) (hs : ∀ i ∉ s, 0 ≤ f i) (hf : Summable f)` — Finset FIRST,
Summable LAST — which is the opposite of the neighbouring `Summable.le_tsum`
(Summable first).  First attempt used the wrong name; focused check green after
the one-token fix.
