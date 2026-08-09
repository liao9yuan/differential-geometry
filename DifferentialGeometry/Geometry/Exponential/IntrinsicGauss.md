# IntrinsicGauss

## 2026-07-23 complete intrinsic Gauss pairing

The new canonical theorem `intrinsic_gauss` proves Gauss's lemma for the
time-one complete intrinsic exponential:

```text
g_exp(u)(terminalVelocity(u), d(exp)_u(w)) = g_p(u,w).
```

The proof uses the global affine launch variation
`F(s,t) = intrinsicGeodesic p (u + s • w) t`.  Constant geodesic speed and the
moving-foot speed derivative identify the transverse derivative of the
longitudinal velocity; mixed covariant derivatives commute; metric
compatibility then makes the terminal pairing affine in time.  The endpoint
variation is identified with the exponential differential by
`intrinsic_jacobi_one`.

The statement has no `ConnectedSpace`, chart source, raw exponential-domain,
or radius hypothesis.  It is therefore the lower intrinsic producer required
by the fixed-first selected inverse branch, not a wrapper around the
chart-fixed Gauss theorem.

The completed proof and its local linter cleanup passed focused verification
with no diagnostics.  Its exact artifact is current, and the file contains no
placeholders.

`intrinsic_gauss` itself is complete (100%).  The downstream fixed-first Layer
A now consumes it and is also complete (100%).  These are producer results;
the radial-Laplacian endpoint and unconditional `compactnessSol` theorem remain
separately accounted.

## 2026-07-27 intrinsic CGT radial fence

Two intrinsic-framed consequences are now focused-green with no diagnostics:

- `intrFrame_radial_le` bounds the Euclidean radial pairing by the
  Riemannian speed measured by `intrFrameMetric`;
- `intrLift_norm_le` integrates that pointwise estimate for a `C¹` lift
  starting at the model origin:
  `ofReal ‖η b‖ ≤ pathELength (intrinsicFramedExp ∘ η) a b`.

The proof is the intrinsic, no-radius analogue of the checked raw Gauss length
fence.  It uses the time-one intrinsic Jacobi formula, `intrinsic_gauss`, the
exact normal-frame norm identity, and the existing one-sided slope/integral
lemma.  It introduces no raw exponential-domain bound, injectivity-radius
assumption, or new HCG input.

The zero-start statement is intentional: it is exactly the continuation seam
for the CGT short exponential lift starting from the constant path, and avoids
adding a stronger general-start derivative API before it is needed.

Theorem accounting: both radial-fence theorems are 100% focused-verified, and
the exact module artifact is current (`3806/3806`).
The compact continuation theorem producing the full short lift is still 0%;
its dedicated machinery is now about 30%.  The CGT loop estimate
`intrLoop_ge_cgt`, the sequence `InjRadiusDecayInput` producer, and the
unconditional metric/flow compactness endpoints remain 0%.
