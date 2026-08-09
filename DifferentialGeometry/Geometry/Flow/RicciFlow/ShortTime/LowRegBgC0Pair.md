# LowRegBgC0Pair

## Role

This module owns the two-state `H¹` estimates for the order-zero correction
created by replacing the frozen DeTurck background with an arbitrary fixed
smooth background. All dangerous second state derivatives are refolded at the
action level before taking the `H¹` jet.

## Current state

All three cancellation-preserving pieces are complete:

- `dlaBg_pair_h1` uses the exact Palatini factorization and proves the two-arm
  modulus `B0(R,A) * D2 + B1(A) * ||T-U||_H2`;
- `dlbIns_pair_h1` estimates `DLb + Insert` only after their base-background
  heads cancel, so its modulus uses the spectral `H2` difference alone;
- `amixBg_pair_h1` refolds both AMix permutations before applying the finite
  five-factor telescope, again using only spectral `H2` state data.

The public capstone `lie0_bg_pair_h1` combines these pieces through the exact
`deTurckLieCoeffField + lieCorr0Field` decomposition. It is the complete
order-zero fixed-background correction at a moving metric, has no `D3` or
`D4` difference input, and uses no high-state smallness.

The persistent Lean LSP accepted the capstone with zero diagnostics. Typical
saved-file iterations took about 8--13 seconds, while the largest incremental
re-elaboration took about 73 seconds; the subsequent identical query reused
the completed info tree in 0.012 seconds. The independent focused check passed
in 211.9 seconds. The same server remained in use throughout.

## Remaining frontier

The next layer is path integration, not more zero-order algebra. A sibling
should evaluate `lie0_bg_pair_h1` on the two realized radial paths, integrate
the resulting `H1` modulus, combine it with the same-background `C0` pair and
the arbitrary-background `C1` pair, and then apply the existing `a1Lo_diff`
operator interface. The fixed curvature coefficient cancels in the two-state
`C0` difference.

`ricci_flow_unif_existence` itself remains unproved (0%). Its dedicated
low-base machinery is approximately 82% complete after this C0 brick; the
whole HCG compactness project remains in the low single digits.

## Verification

The Lean source is placeholder-free and its focused check passed. The public
capstone is ready for a targeted module refresh before a downstream sibling
imports it.

## 2026-08-02 restoration (read before ever editing this file again)

The mechanical C0Core split accidentally overwrote this file; the first
recovery (33-patch replay from the `rollout-2026-08-01T00-35-49` Codex
session) restored only an intermediate 1605-line snapshot ending at
`dlaBg_pair_h1` — that rollout's patch list was a mirrored copy of the first
33 of 109 patches, all authored in the `rollout-2026-07-29T06-05-04` session.
The remaining 43 patches (07:55–09:11 UTC on 2026-08-01), containing
`dlbIns_pair_h1`, `amixBg_pair_h1`, the capstone `lie0_bg_pair_h1`, and its
proof-body completion, were replayed on 2026-08-02 with strict
context-validated unified-diff application on top of the certified 1605-line
seed.  The result matched the terminal state byte-for-byte.

Current certified state: 3401 lines, zero sorry, all four public theorems
present.  SHA256:
`36C615CB2442A7E22806EF9291F3A326763F8C534F56B7AFDC06C1C9126699F5`
(the old guard `F614...80FD` now identifies only the pre-capstone backup at
`.codex-scratch/c0core-split/LowRegBgC0Pair.dlaBg-1605-preCapstone.lean`).
Focused check and targeted `.olean` build are GREEN (build 121 s) against the
split C0Core chain, and `LowRegBgA1Pair` compiles again on top of it
(build 27 s).  Do not overwrite or rename this file; extend it only through
reviewed edits.
