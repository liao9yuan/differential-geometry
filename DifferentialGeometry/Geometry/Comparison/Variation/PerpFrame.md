# PerpFrame notes

## 2026-07-08

- Added `exists_time_clip`, a reusable smooth bounded time reparametrization
  equal to the identity on `Icc 0 L`.  It is the low-layer smooth-extension
  brick needed when a downstream curve is only controlled on a compact time
  interval but an existing frame API asks for a globally smooth time parameter.
- Verification passed for the focused file check and the targeted module
  refresh.  The remaining volume-comparison frontier is downstream: use this
  time clip to build either a global smooth radial extension that stays inside
  the exponential smoothness radius, or localize the parallel-frame API to
  `Icc 0 b`.

- Added `exists_time_window_clip`, the same cutoff-times-identity idea but for
  any closed window strictly inside `(-lam, lam)`.  This is the stronger brick
  needed for endpoint-safe transport: downstream curves can agree on a
  neighborhood of `Icc 0 b`, not merely on the closed interval itself.
  Verification passed.  The downstream volume bridge consumed it through
  `RadialGronwall.exists_rclip_nbhd`.

## 2026-07-18 positive-speed perpendicular frame

- Added `exists_perp_pos`, producing the required perpendicular orthonormal
  family along a positive-speed curve while retaining the existing local-frame
  conventions.
- Focused verification and the exported module refresh passed.
- The result is consumed by the assembled radial comparison producer; it does
  not resolve the global cut-locus transfer.

## 2026-07-27 positive-speed global frame

- `exists_perp_par_pos` now owns the global construction: a positive-speed
  geodesic receives a globally smooth family that is orthonormal,
  velocity-perpendicular, and parallel on the controlled interval.
- The former unit-speed theorem `exists_parallel_perp_frame` is retained as a
  compatibility wrapper.  The proof no longer derives or carries an unused
  unit-speed propagation fact.
- Focused verification passed.  No targeted refresh was run, so the exported
  artifact is not claimed current in this handoff.  The two declarations retain
  the file's pre-existing unused-section-variable warning.
- No connectedness assumption was introduced.  Any later global geometric
  capstone that still needs connectedness will use the component-restriction
  route rather than strengthen this local frame API.
- The geometric endpoint theorem `jacobi_pair_pos` remains unstated (theorem
  level 0%); its dedicated frame/index-form machinery is about 80%.  The
  textbook comparison lemma remains theorem-level 0% with about 75% of its
  dedicated machinery available.  Whole HCG compactness supporting machinery
  remains about 61%; the unconditional compactness theorem remains 0%.
