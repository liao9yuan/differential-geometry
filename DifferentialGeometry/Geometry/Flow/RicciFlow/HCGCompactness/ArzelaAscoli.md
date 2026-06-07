# ArzelaAscoli

## Source

This file records the sequential Arzela-Ascoli wrapper used as MSM135 Lemma
3.14.  The proof uses Mathlib's compact-open Arzela-Ascoli theorem, metrizability
of `C(X, R)` for locally compact sigma-compact domains, and the compact-open
to uniform-on-compacts convergence equivalence.

## Definitions and theorems

- `arzelaAscoli_subseq_tendsto` extracts a subsequence converging in the bundled
  compact-open topology on `C(X, R)`.
- `arzelaAscoli_subseq_tendstoUniformlyOnCompacts` translates that convergence
  to `TendstoUniformlyOn` on every compact subset.

## Frontier

No new analytic frontier is introduced here.  The deep compactness statement is
provided by Mathlib's Arzela-Ascoli theorem; this file only repackages it in the
sequential form needed by HCG compactness.

## Verification

Verification passed for the targeted Arzela-Ascoli module.  The local audit
found no proof placeholders in the Lean file.
