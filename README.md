# Differential Geometry in Lean 4

An ongoing geometry library project: geometric analysis on Riemannian manifolds, now past short-time existence for the Ricci flow and heading toward Hamilton's 1982 theorem on three-manifolds with positive Ricci curvature.

## Formalized theorems

Each is `sorry`-free (axioms: `propext, Classical.choice, Quot.sound`).

> These three are the standard axioms of Lean's core library — propositional extensionality, the axiom of choice, and quotient soundness — on which all of classical mathematics in Mathlib rests. `#print axioms` lists everything a theorem transitively assumes: a `sorry` would surface as `sorryAx`, and any ad-hoc axiom would be named. An output of exactly these three therefore certifies that the proof is fully kernel-checked, with no `sorry` and no assumptions beyond the classical foundations.

- [Ricci flow short-time existence](DifferentialGeometry/Geometry/Flow/RicciFlow/ShortTimeExistence.lean#L34) — on every closed Riemannian manifold $(M, g_0)$ the Ricci flow $\partial_t g = -2\operatorname{Ric}_{g(t)}$ has a solution on some $[0, T)$ with $g(0) = g_0$, jointly smooth in $(t, x)$ up to and including the initial time. Proved via the DeTurck reduction and a conjugating flow of the DeTurck vector field; a `#print axioms` audit is embedded at the declaration site.
- [Bonnet–Myers diameter bound](DifferentialGeometry/Geometry/Comparison/BonnetMyers/Headlines.lean#L114) — a positive Ricci lower bound forces a bounded diameter.
- [Bochner formula](DifferentialGeometry/Analysis/Elliptic/Regularity/Bochner/Polarised.lean#L341) — the polarised, pointwise form.
- [Weitzenböck identity](DifferentialGeometry/Analysis/Elliptic/ConnectionLaplacian/GreenIdentityAndIBP/IntegratedOrder2Weitzenbock.lean#L196) — the integrated $L^2$ form.
- [Lichnerowicz inequality](DifferentialGeometry/Analysis/Elliptic/Lichnerowicz.lean#L134).
- [Reilly identity](DifferentialGeometry/Analysis/Elliptic/WithBoundary/Neumann/Reilly.lean#L164) — an integral identity on a manifold with boundary.
- [Voss–Weyl divergence formula](DifferentialGeometry/Analysis/Integration/DivergenceTheorem/ChartInvariance.lean#L616) — the chart-invariant divergence.
- [Scalar-curvature evolution under Ricci flow](DifferentialGeometry/Geometry/Flow/RicciFlow/Evolution/Scalar/Basic.lean#L96).
- [Perelman's $\mathcal{W}$-entropy invariances](DifferentialGeometry/Geometry/Flow/RicciFlow/Entropy/Defs.lean#L110) — scale and diffeomorphism invariance.
- [Perelman's $\mathcal{F}$-functional first variation](DifferentialGeometry/Geometry/Flow/RicciFlow/Entropy/F/Producer.lean#L411) — Perelman's formula 5.10.

## PDE infrastructure

Underlying these results is a substantial geometric-analysis backbone — the [`Analysis/`](DifferentialGeometry/Analysis) pillar, roughly 680,000 lines of Lean:

- [**Integration & the divergence theorem**](DifferentialGeometry/Analysis/Integration) — Riemannian measures, integration by parts and surface measures, with and without boundary.
- [**Elliptic regularity**](DifferentialGeometry/Analysis/Elliptic) — the connection (rough) Laplacian, Green identities, Gårding / Caccioppoli estimates, and interior bootstrap.
- [**Spectral theory**](DifferentialGeometry/Analysis/Spectral) — the scalar theory on closed manifolds (discrete Laplacian spectrum, compact resolvent, eigenbasis); an iterated covariant-gradient jet calculus for tensor fields with fibre-norm towers and Sobolev-scale spectral estimates; and the intrinsic heat-semigroup / Galerkin machinery driving the DeTurck flow.
- [**Sobolev spaces**](DifferentialGeometry/Analysis/Sobolev) — chart-based and intrinsic $H^k$ / $W^{k,p}$ spaces with completeness, embedding and compactness results; tensor-valued Hilbert–Sobolev towers; Moser-type tame product estimates; and Gagliardo–Nirenberg interpolation down to fibre-norm level.
- [**Parabolic & heat equations**](DifferentialGeometry/Analysis/Parabolic) — heat semigroups, Duhamel mild solutions, Lions–Magenes time-Sobolev theory, strict parabolicity and principal symbols, and the complete quasilinear existence engine behind the DeTurck–Ricci reduction: maximal-regularity Galerkin solutions with all-order Sobolev-scale jet control, tame estimates for the DeTurck nonlinearity, and joint $(t,x)$-smoothness of the solution down to the initial time. A parabolic [maximum principle and heat smoothing](DifferentialGeometry/Analysis/Heat) sit alongside.
- [**ODE flows**](DifferentialGeometry/Analysis/ODE) — $C^\infty$ dependence of flows on their initial data, and time-dependent flows on closed manifolds jointly smooth up to the initial time (via Seeley-type time extension of the vector field).

The classical De Giorgi–Nash–Moser regularity machinery is vendored under [`External/`](DifferentialGeometry/External).

## Work in progress

- **Hamilton's theorem** (R. S. Hamilton, *Three-manifolds with positive Ricci curvature*, J. Differential Geom. **17** (1982), 255–306): every closed 3-manifold carrying a metric of positive Ricci curvature admits a metric of constant positive sectional curvature — it is a spherical space form, and in the simply-connected case diffeomorphic to $S^3$. This is the surgery-free ancestor of Perelman's proof of the Poincaré conjecture: the normalized Ricci flow converges directly to the round metric. Building on the [Ricci flow machinery](DifferentialGeometry/Geometry/Flow/RicciFlow) above; upcoming milestones include uniqueness of the flow, curvature evolution equations beyond the scalar case, tensor maximum principles, and the pinching estimates that drive convergence of the normalized flow.

## AI Disclaimer

Generative AI (ChatGPT, Claude, Deepseek, Gemini, GLM, etc.) was used in the development of this codebase. The high-level architecture is human-designed; AI agents assisted with formalizing individual proofs and writing boilerplate. All definitions and core theorem statements were human-verified for correctness. Since all proofs are verified by Lean's type checker, AI-generated and human-written code are held to the same standard of correctness.
