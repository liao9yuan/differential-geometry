# CutoffData

## 2026-08-28: one fixed finite-error cutoff

`ShiFixedCutoff` packages exactly the data used by a compact finite-error
maximum-principle argument: one cutoff, one error, a compact spatial support,
vanishing off that support, range in `[0,1]`, joint continuity on the compact
slab, and a lower parabolic support at every positive cutoff point. It is a
data record, not a class or a second cutoff hierarchy; the existing exhaustion
records remain unchanged.

`ShiFixedCutoff.slab_compact` and `mem_of_pos` record the two immediate
projections used by the finite Bernstein consumer. The file is warning-free
focused GREEN.

The record is 100% complete. The generic raw `m = 1` consumer remains to be
implemented in a separate file because `Complete.lean` is already near the
3000-line limit. The P2 constructor remains blocked specifically on
ball-local moving-distance anchor/continuity; `shiRm1_ball` and `smooth_nlc`
remain 0% theorem endpoints.
