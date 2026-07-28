# Basic

## State — 2026-07-27

`SmoothRiemannianMetric.ext_inner` is now the canonical low-level
extensionality theorem: equality of the fiberwise inner products determines a
smooth Riemannian metric.  This promotes the formerly sphere-local helper to
the metric base layer without changing any existing public declaration.

The source is focused-green and the targeted artifact is exact-current.  The
theorem is routine API infrastructure; it does not advance a geometric
endpoint by itself.
