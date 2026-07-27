# ShiCutoff.lean

## 2026-07-24 — Route B-prime producer scaffold

The public solution-facing producer `shiBarrierCutoff_of_sol` is stated in its
canonical evolution-layer file.  Its quantifier order ends in `∀ O`, matching
the checked `complete_of_barrier` consumer.

The current body fixes the canonical data:

- `Λ = d² √K`;
- `R n = n + 1`;
- the normalized ENNReal distance
  `z = ofReal (exp (Λ s) / R n) * d_s(O,y)`;
- the cutoff `evalue z`;
- the compact time-zero support ball of radius `2 R n`.

The field-by-field construction of `ShiBarrierCutoffData` is now written
without a source placeholder.  Its verification still waits for three direct
local producer APIs to be landed in their canonical files:

1. the ENNReal-valued cutoff profile and its monotonicity/constant-zone facts;
2. pointwise differentiability of the gradient of a scalar composition;
3. the neighborhood-form parabolic scalar chain rule.

The complete ENNReal profile package has already passed an isolated focused
scratch check using `ENNReal.truncateToReal 2`; it is waiting only for the
current shared writer to exit before being moved into `CutoffProfile.lean`.
The two local chain-rule proof bodies have likewise passed earlier isolated
focused checks.

While that writer remains active, the disjoint producer source has advanced
through the whole constants-first record: the curvature-to-Ricci
quadratic bound, `a n = (R n)⁻¹`, the common error constant and vanishing error
sequence, compact support, anchor-distance comparison, support vanishing,
range, center exhaustion, and the joint-continuity composition are now
written.  The center branch, evolving-distance finiteness at a positive
contact, local finite-distance shrink, Calabi support pullback, and all
lower-support regularity fields are also written.  The final noncentral
estimate now splits between the constant cutoff zone and active annulus and
closes the singular radial term from `1 < a exp(Λt) r`.  Its pure
real-algebra helper passed an isolated focused scratch check.  The complete
producer has not yet had a focused check, so this remains source progress
rather than a checked theorem.

No further geometric or analytic input is currently known to be missing.
The theorem is therefore still theorem-level **0%**; its dedicated Route
B-prime machinery is about **85%**.  Whole HCG supporting machinery remains
about **60%**, and unconditional `compactnessSol` remains theorem-level **0%**.

## 2026-07-27 — concrete barrier-cutoff producer closed

`shiBarrierCutoff_of_sol` is now focused-green and exact-green (`3997/3997`)
with no `sorry`, `admit`, new axiom, or local heartbeat override.  It produces
the quantifier-correct family

```text
∀ O, Nonempty (ShiBarrierCutoffData (flowG S) T O)
```

directly from one complete initial slice and the order-zero curvature bound.
The earlier profile, scalar-chain-rule, compact-support, and evolving-distance
items are all discharged in the checked proof.

The theorem-scoped removal of the two tangent-space norm instances is retained
only to avoid the known background-norm instance diamond; it is local and does
not leak into the public API.  The private `metric_smul_self` avoids the same
elaboration seam and is intentionally not promoted into a parallel public
metric API.

Honest accounting: `shiBarrierCutoff_of_sol` is theorem-level **100%**, and its
dedicated Route B-prime cutoff machinery is **100%**.  This does not by itself
prove `compactnessSol`; that endpoint remains theorem-level **0%**.
