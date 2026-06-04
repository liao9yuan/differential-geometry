# Differential Geometry in Lean 4

An ongoing geometry library project, currently working on geometric analysis on Riemannian manifolds and heading toward Ricci flow.

## Formalized theorems

Each is `sorry`-free (axioms: `propext, Classical.choice, Quot.sound`).

- [Bonnet–Myers diameter bound](DifferentialGeometry/Geometry/Comparison/BonnetMyers/Headlines.lean#L114) — a positive Ricci lower bound forces a bounded diameter.
- [Bochner formula](DifferentialGeometry/Analysis/Elliptic/Regularity/Bochner/Polarised.lean#L341) — the polarised, pointwise form.
- [Weitzenböck identity](DifferentialGeometry/Analysis/Elliptic/ConnectionLaplacian/GreenIdentityAndIBP/IntegratedOrder2Weitzenbock.lean#L196) — the integrated $L^2$ form.
- [Lichnerowicz inequality](DifferentialGeometry/Analysis/Elliptic/Lichnerowicz.lean#L134).
- [Reilly identity](DifferentialGeometry/Analysis/Elliptic/WithBoundary/Neumann/Reilly.lean#L164) — an integral identity on a manifold with boundary.
- [Voss–Weyl divergence formula](DifferentialGeometry/Analysis/Integration/DivergenceTheorem/ChartInvariance.lean#L616) — the chart-invariant divergence.
- [Scalar-curvature evolution under Ricci flow](DifferentialGeometry/Geometry/Flow/RicciFlow/Evolution/Scalar/Basic.lean#L96).
- [Perelman's $\mathcal{W}$-entropy invariances](DifferentialGeometry/Geometry/Flow/RicciFlow/Entropy/Defs.lean#L110) — scale and diffeomorphism invariance.
- [Perelman's $\mathcal{F}$-functional first variation](DifferentialGeometry/Geometry/Flow/RicciFlow/Entropy/F/Producer.lean#L411) — Perelman's formula 5.10.

## Work in progress

- [Ricci flow short-time existence](DifferentialGeometry/Geometry/Flow/RicciFlow/ShortTimeExistence.lean#L68) — the DeTurck reduction and the conjugating-flow / variational machinery are complete and `sorry`-free; the headline statement currently rests on one deferred parabolic-regularity input.

## AI Disclaimer

Generative AI (Claude, Gemini, Aristotle) was used in the development of this codebase. The high-level architecture is human-designed; AI agents assisted with formalizing individual proofs and writing boilerplate. All definitions and core theorem statements were human-verified for correctness. Since all proofs are verified by Lean's type checker, AI-generated and human-written code are held to the same standard of correctness. The authors are generally confident about the correctness of the code, but make no guarantees.
