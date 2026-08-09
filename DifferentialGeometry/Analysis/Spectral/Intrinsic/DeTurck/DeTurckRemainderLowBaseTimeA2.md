# DeTurckRemainderLowBaseTimeA2

## 2026-08-05 — radius-flexible second-order pair

`radialA2_pairR` exposes the same coefficient and admissible upper cutoff as
`radialA2_pair`, but quantifies over every smaller realized radius.  Its two
operator bounds scale as `C * r`, and the high/low inclusion square is retained.
This lets a downstream solver choose `r` after seeing `C` rather than merely
reporting a potentially large product at the initially selected cutoff.

Focused verification passed warning-free, and the direct module refresh passed.
The result is per metric; class-uniform control of its coefficient is a separate
producer for `(N)`.
