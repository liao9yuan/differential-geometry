# GoodCoveringSeq

## 2026-07-01 NetLimitData Refinement

- Added `NetLimitData.subseq` so the diagonal net-limit package can be refined
  along a further strict master subsequence without rebuilding the radius-limit
  data.
- Added simp projections for the refined master subsequence and unchanged
  limit radii, plus `NetLimitData.stable_subseq` to carry pairwise `B`-ball
  intersection stability through a later refinement.
- Verification passed for the focused file check. The first attempt timed out
  after the external command boundary and left a stale Lake lock under the same
  token; the process was gone, the stale Lake lock was released, and the retry
  passed.
- The targeted module refresh also passed. Warnings were replayed from existing
  upstream modules, not from the new `NetLimitData` helpers.
