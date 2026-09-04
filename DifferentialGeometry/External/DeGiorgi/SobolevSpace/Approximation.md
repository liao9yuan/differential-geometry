# Approximation

## Smooth cutoff API

- The existing compact-in-open-domain cutoff construction is now public as
  `exists_smooth_cutoff`; no proof body or hypotheses changed.
- This is the canonical low-level cutoff used to turn signed compactly
  supported tests into differences of nonnegative tests.
- Focused verification and the required named refresh passed without warnings.
