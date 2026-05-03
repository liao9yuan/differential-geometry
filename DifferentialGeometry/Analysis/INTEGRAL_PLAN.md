## Goal

Build the "integral aspects" of differential geometry directly on top of Mathlib + the existing Synthetic/Realization layers, with the engineering endpoint of **short-time existence of the Ricci flow** — which closes the last remaining Synthetic axiom and makes the entire Ricci-flow calculus unconditional. Further phases reach Perelman's entropy monotonicity, κ-non-collapsing, and ultimately the proof of the Poincaré conjecture.

## Design Philosophy (vs. Synthetic Differential)

The Synthetic layer was abstract `(k, R, V, Time)` because Mathlib's tensor / vector-field API was thin, and parallelizability kept intruding. Measure theory is the opposite situation — Mathlib's Bochner / Lp / Radon / spectral machinery is battle-tested. We therefore **do not replicate the Abstract / Realization split for integration**. Everything in this layer is concrete on `(M, I, g)`, imports Mathlib directly, and uses the Synthetic layer only through its already-proven tensor identities.

### Non-Axioms

- **No new `axiom`**, **no new `class`** (with two carefully scoped exceptions: `HasSmoothBoundary E H I` and `HasOrientableBoundary M`, the with-boundary typeclasses, see "With-boundary parallel" below), **no `sorry` hiding an axiomatic assumption**. Every fact either comes from Mathlib or is proved here.
- **No cohomological-orientation assumption** (density-first). Volume forms are an optional enrichment on oriented submanifolds, not a foundation.
- **No "wait for Mathlib / friends to upstream"**. Everything we need, we write. The one external import we take is the **DeGiorgi repo** (Armstrong–Kempe 2026) for Sobolev spaces on bounded Euclidean domains and De Giorgi–Nash–Moser elliptic regularity — a standalone sorry-free Lean 4 project.
- **No joint smoothness on time × space product**. Any statement about a $t$-parameterised object (metric family, integrand, flow) uses the weakest regularity sufficient for its calculus claim: pointwise `HasDerivAt` in $t$, plus continuity / domination in $(t, x)$ on neighborhoods of compact sets. Joint $C^\infty$ / joint smoothness on $\mathbb{R} \times M$ is not permitted as a hypothesis in the Integral, Analysis, or PDE layer. The eventual Ricci-flow solution *is* jointly smooth, but that is packaged at the Synthetic / Realization / bridge layer at the point of use — never wired into the integration engine's public API. This keeps the engine reusable for non-smooth-solution applications (heat equations with rough coefficients, weak evolution PDE, etc.).

### With-boundary parallel (mandatory)

Manifolds with boundary are **first-class citizens** in this plan. Every Phase 3+ Task that admits a boundary case delivers TWO parallel versions:

- **Boundaryless track** (default, the M8 / Poincaré endpoint route): theorem signatures carry `[I.Boundaryless]` (or implicit closed-manifold prose). Files in the natural locations.
- **With-boundary track** (parallel, mandatory wherever feasible): theorem signatures replace `[I.Boundaryless]` with `[HasSmoothBoundary E H I]` (the project-internal typeclass abstracting "smooth (n-1)-dim boundary"; defined in `Integral/DivergenceTheorem/WithBoundary/ModelBoundary.lean`). Where chart-invariance of geometric objects (e.g., outward unit normal) enters the statement, signatures additionally carry `[HasOrientableBoundary M]` (defined in `Integral/DivergenceTheorem/WithBoundary/Orientation.lean`). Files in `WithBoundary/` sub-directories.

**Boundary integrals** appear in two equivalent forms:
1. **Chart-by-chart formulation** via `boundaryFaceSum g X` (a finite POU sum of chart-local boundary face integrals). Always available.
2. **Intrinsic formulation** $\int_{\partial M} g(X, \nu) \, dS$ via `outwardNormal g` and `surfaceMeasure g`. Available under the additional `[HasOrientableBoundary M]` hypothesis.

**Phase 3 with-boundary infrastructure already shipped** (~16,000 lines, 22 files in `Integral/DivergenceTheorem/WithBoundary/`):
- `PartialDerivWithin.lean`, `LocalFormula.lean`, `Ibp.lean`, `ChartInvariance.lean`, `Global.lean`, `POUReduction.lean` — chart-local divergence + chart-invariance + global divergence + Leibniz / POU sum.
- `InteriorCompactSupport.lean`, `IntegrationByParts.lean`, `Gradient.lean`, `Laplacian.lean`, `Green.lean` — interior-supported divergence theorem, IBP, gradient, Laplacian, Green's identities.
- `ModelBoundary.lean`, `BoundaryManifold.lean`, `InducedMetric.lean`, `SurfaceMeasure.lean`, `EuclideanHalfSpaceInstance.lean` — `HasSmoothBoundary` typeclass, boundary as a manifold, induced metric, surface measure, canonical instance.
- `Orientation.lean`, `OutwardNormal.lean`, `BoundaryGramMatrix.lean` — `HasOrientableBoundary` typeclass, outward unit normal (`Continuous` + `ContMDiff`), boundary Gram-matrix infrastructure.
- `Stokes.lean`, `GreenWithBoundary.lean`, `Family.lean` — Stokes' theorem with boundary integral, Green's identities with boundary terms, time-parameterised wrappers.

**Boundary conditions for Phase 5+ Laplacian / heat / parabolic**: on a manifold-with-boundary, the Laplacian splits into **Dirichlet** and **Neumann** versions, defined by the choice of variational domain ($H^1_0$ vs $H^1$). Each ships its own resolvent / spectrum / heat semigroup / parabolic existence parallel. See per-phase notes below.

**Corners are out of scope** for the with-boundary track. The `HasSmoothBoundary` typeclass deliberately excludes corner models (`EuclideanQuadrant`, etc.). Whitney–Stokes for stratified spaces is a future extension, not part of M8 or its prerequisites.

### Coupling with Synthetic

The Synthetic/Realization layer provides two things we consume:

1. **Abstract operators specialised to `(C^∞(M,ℝ), Γ(TM))`** — ∇, trace, metric duality, time derivative, gradient, divergence, Laplacian, Hessian. We use these at their concrete endpoints.

2. **Pointwise identities**, already complete at the Synthetic `(k, R, V, Time)` level:
   - `Synthetic/Operator/Bochner.lean:bochner_pointwise` — the full Weitzenböck/Bochner identity `Δ|∇f|² = 2|∇²f|² + 2Rc(∇f,∇f) + 2⟨∇f, ∇Δf⟩` (pointwise, Hessian-level).
   - `Synthetic/Flow/RicciFlow/Evolution/scalar_curvature_evolution` — `∂_t R = 2|Rc|² + tr_g(∂_t Rc)`.
   - `Synthetic/Flow/RicciFlow/Evolution/laplacian_evolution` — `∂_t(Δu) = 2⟨Rc, Hess u⟩ + tr_g(∂_t Hess u)`.
   - `Synthetic/Flow/RicciFlow/Evolution/RiemannEvolution` (1476 lines) — `∂_t Rm`.

The integral layer's job is to **take `∫_M` of these pointwise identities, using the volume-variation formula `d/dt dV_{g(t)} = ½ tr_g(∂_t g) dV_{g(t)}` (Phase 1.5) to handle the time derivative of the measure**. The resulting integrated identities (e.g. `d/dt ∫ R² dV_{g(t)} = ...`) are stated and proved concretely on `(M, I, g, μ_g)`.

For the **with-boundary track**, the same Synthetic pointwise identities apply on the manifold interior. The integration over the manifold-with-boundary $M$ then carries an additional **boundary integral correction** (via Stokes from Phase 3 with-boundary), e.g.,
```
d/dt ∫_M R dV_g = -∫_M R² + 2 ∫_M |Rc|² + ∫_{∂M} (boundary flux from chart-by-chart Stokes)
```
The boundary correction is expressed via `boundaryFaceSum` (chart-by-chart) or, under `[HasOrientableBoundary M]`, via `∫_{∂M} ⟨...,ν⟩ dS`.

**Integration is not abstracted.** Unlike the differential-side Synthetic layer, we do not parameterise integration over an abstract ring; the Mathlib `Measure` / Bochner machinery is consumed directly. The same integration engine serves both the boundaryless and the with-boundary tracks; only the boundary integral terms differ.

## External Dependencies

| Dependency | Role | Status |
|-----------|------|--------|
| Mathlib (current) | Bochner integration, Lp, `Measure`, partition of unity, covariant derivatives, compact self-adjoint spectral theory (`IsCompactOperator` + `orthogonalComplement_iSup_eigenspaces_eq_bot` + `finite_dimensional_eigenspace`), Picard–Lindelöf, bump functions, convolution | already in `lakefile.toml` |
| `Analysis/InnerProductSpace/Laplacian.lean` (Kebekus 2025) | Euclidean Δ on finite-dim inner product spaces | wrap as chart-local Δ in Phase 5.1 / 5.6 |
| DeGiorgi repo (Armstrong–Kempe) | Sobolev spaces on bounded Euclidean domains; De Giorgi–Nash–Moser elliptic regularity | vendor / add as lake dep in Phase 4 |
| Existing Synthetic/Realization | ∇, trace, Levi-Civita, time derivative, all tensor identities | complete (15,664 lines, 0 sorry, 3 admit) |
| Existing `Synthetic/Operator/` | `divergence`, `laplacian`, `grad`, `Hessian`; `Bochner.lean` = full pointwise Weitzenböck | complete |
| Existing `Synthetic/Flow/RicciFlow/Evolution/` | all pointwise RF evolution identities | complete; **foundation for Phase 9, 10, 12, 13** |
| Existing `Tensor/`, `VectorBundle/`, `DifferentialForm/` | Tensor bundle machinery; read-only | 4 sorrys in `DifferentialForm`, 2 in `RSTensor/Metric.lean` — **we do not depend on these** |

### Note on `to02Tensor`

`Tensor/RSTensor/Metric.lean` has 2 sorrys in the smoothness proof of `RiemannianMetric.to02Tensor`. **We do not need this packaging.** For Phase 1 we work directly with `Bundle.ContMDiffRiemannianMetric.inner` (already smooth by definition) and extract local matrix components via the chart trivialization.

### Note on Hausdorff measure shortcut (considered and rejected)

We considered defining `μ_g := c_n · μH[n]` on `(M, d_g)` (n-dim Hausdorff measure on the Riemannian metric space). Mathlib has `μH[d]`, and `(M, d_g)` is already a metric space via `IsRiemannianManifold` + `PathELength`. But identifying `μH[n]` with the classical `√det g · Lebesgue` formula requires Riemannian normal coordinates, the exponential map, and Gauss's lemma — **none of which are in Mathlib** and none of which are in our current Synthetic layer. Building exp + Gauss would itself be a multi-thousand-line project. We therefore stick with the direct chart-formula approach.

## Dependency Topology

```
Mathlib
  ↓
Tensor/, VectorBundle/, DifferentialForm/   (friend-maintained, read-only)
  ↓
Synthetic/                                   (existing, untouched)
  ↓
Synthetic/Realization/                       (existing, complete)
  ↓
Integral/
  Measure/   Integration/   Evolution/   BakryEmery/
  DivergenceTheorem/                                    ← shipped
    + DivergenceTheorem/WithBoundary/                   ← shipped
  ↓
Analysis/
  Sobolev/         + Sobolev/WithBoundary/             [imports DeGiorgi repo]
  Laplacian/       + Laplacian/WithBoundary/{Dirichlet,Neumann}/
  HeatEquation/    + HeatEquation/WithBoundary/
  Parabolic/       + Parabolic/WithBoundary/
  HarmonicAnalysis/+ HarmonicAnalysis/WithBoundary/
  ↓
PDE/
  DeTurck/   RicciShortTime.lean             closes last Synthetic axiom
  TensorMaximumPrinciple/                    ← Hamilton path H1
  (PDE/WithBoundary/ deferred — research-grade)
  ↓
  ├─ Hamilton Path ──────────────────────────────────────────┐
  │  Synthetic/Flow/RicciFlow/                               │
  │    Pinching/                                             │
  │      RicciEvolution.lean, TraceFreeEvolution.lean        │
  │      EigenvalueEstimates.lean, PinchingInequality.lean   │
  │      FiniteTimeBlowup.lean                               │
  │    Normalized/                                           │
  │      Definition.lean, Evolution.lean                     │
  │      ShiEstimates.lean, LongTimeExistence.lean           │
  │      Convergence.lean, ConstantCurvature.lean            │
  │  ↓                                                       │
  │  Geometry/                                               │
  │    Geodesic.lean, ExponentialMap.lean                    │
  │    ConstCurvatureJacobi.lean, ConjugatePoint.lean        │
  │    SphereRecognition.lean                                │
  │  ↓                                                       │
  │  Hamilton/PositiveRicci.lean  ← final theorem            │
  └──────────────────────────────────────────────────────────┘
  ↓
Perelman/
  F, W, reduced length, κ-non-collapsing
  + Perelman/WithBoundary/{F.lean, W.lean}   (static definitions only; dynamic deferred)
  ↓
Poincare/   Surgery/   Geometrization/        (far future)
```

## File Tree (target)

```
DifferentialGeometry/
  Synthetic/, Tensor/, VectorBundle/, DifferentialForm/   (existing)

  Integral/                              NEW
    Measure/
      ChartDensity.lean                  # √det g · Lebesgue in one chart
      Glue.lean                          # μ_g via POU + Measure.sum
      Invariance.lean                    # chart independence
      Properties.lean                    # Radon, IsOpenPosMeasure, σ-finite
      Family.lean                        # t ↦ μ_{g(t)} for smooth g_fam
    Integration/
      Basic.lean                         # ∫_M f dμ_g wrappers (Bochner)
      TensorL2.lean                      # L²(Γ(T^{r,s}M)) — concrete
      CompactSupport.lean                # C^∞_c(M, ℝ), Γ_c(TM)
      VolumeFormula.lean                 # dV_{g(t)}/dt = ½ tr(g⁻¹ ∂_t g) dV_g
    DivergenceTheorem/
      LocalFormula.lean                  # chart: div(X)√det g = ∂_i(X^i √det g)
      POUReduction.lean                  # ∑ φ_α X, bilinear glue
      Closed.lean                        # M compact, ∫ div X dμ_g = 0
      Proper.lean                        # HasCompactSupport X ⇒ same
      IBP.lean                           # ∫ X(f)·g + ∫ f·X(g) = -∫ fg div X
      Family.lean                        # time-dependent IBP
      WithBoundary/                      # with-boundary parallel API (SHIPPED)
        ModelBoundary.lean               # HasSmoothBoundary I typeclass
        BoundaryManifold.lean            # ∂M as a (n-1)-dim manifold
        InducedMetric.lean               # induced Riemannian metric on ∂M
        SurfaceMeasure.lean              # μ_{g|∂M} on ∂M
        EuclideanHalfSpaceInstance.lean  # canonical 𝓡∂ n instance
        PartialDerivWithin.lean          # fderivWithin chart-target API
        LocalFormula.lean                # chart-local div via partialDerivWithin
        Ibp.lean                         # chart-local IBP
        ChartInvariance.lean             # localDivergence chart-invariant
        POUReduction.lean                # Leibniz + POU sum
        Global.lean                      # divergence_g_with_boundary
        InteriorCompactSupport.lean      # ∫div = 0 for tsupport ⊆ I.interior M
        IntegrationByParts.lean          # IBP (interior-supported)
        Gradient.lean                    # grad_g_with_boundary
        Laplacian.lean                   # Δ_g_with_boundary (interior)
        Green.lean                       # Green's I + II (interior)
        Orientation.lean                 # HasOrientableBoundary M typeclass
        OutwardNormal.lean               # ν : Continuous + ContMDiff
        BoundaryGramMatrix.lean          # Gram matrix on boundary submanifold
        Stokes.lean                      # ∫div = boundary integral (chart-by-chart)
        GreenWithBoundary.lean           # Green's I + II with boundary terms
        Family.lean                      # time-dependent wrappers
    Evolution/                           # integrated pointwise ∂_t identities
      ScalarCurvature.lean               # d/dt ∫ R dV, d/dt ∫ R² dV
      RiemannNorm.lean                   # d/dt ∫ |Rm|² dV
    BakryEmery/                          # static + dynamic Γ-calculus
      Gamma.lean                         # Γ(f,g) := ⟨∇f, ∇g⟩
      Gamma2.lean                        # Γ_2(f,g); Γ_2(f,f) = Weitzenböck RHS
      CurvatureDim.lean                  # CD(K, N) condition
      Spacetime.lean                     # time-dependent version for Perelman
      WithBoundary/                      # Γ-calculus with boundary conditions
        Gamma.lean                       # Γ via Δ_g^N or Δ_g^D
        Gamma2.lean                      # Γ_2 with boundary terms
        CurvatureDim.lean                # CD(K,N) on cpt-w-bdry
        Spacetime.lean                   # spacetime version w/ boundary
    Orientation/                         # OPTIONAL
      VolumeForm.lean                    # |dV_g| = ω_g on orientable M

  Analysis/                              NEW
    Sobolev/
      Local.lean                         # wrapper around DeGiorgi's W^{k,p}
      Manifold.lean                      # intrinsic W^{k,p}(M) via ∇
      Chart.lean                         # chart-based W^{k,p}(M)
      Equivalence.lean                   # two defs coincide on compact M
      Embedding.lean                     # Sobolev embedding on compact M
      Rellich.lean                       # Rellich–Kondrachov
      WithBoundary/                      # with-boundary Sobolev parallel
        Chart.lean                       # chart-based W^{k,p} on half-space charts
        Manifold.lean                    # intrinsic W^{k,p} via partialDerivWithin
        Equivalence.lean                 # two defs coincide on closed-mfd-w-bdry
        Rellich.lean                     # Rellich on cpt-w-bdry
        Embedding.lean                   # Sobolev embedding (boundary case)
        Trace.lean                       # boundary trace operator W^{1,p}(M) → L^p(∂M)
    Laplacian/
      Def.lean                           # Δ_g = -div∘grad on C^∞_c(M, ℝ)
                                         #   wraps Kebekus Laplacian chart-locally
      SelfAdjoint.lean                   # Δ = Δ* on L² via IBP
      Domain.lean                        # dom(Δ) = H²(M); closed operator
      Resolvent.lean                     # (Δ+1)⁻¹ : L² → H² compact
      Spectrum.lean                      # discrete spectrum, eigen-basis
                                         #   assembled from Mathlib compact-s.a. theorem
      EllipticRegularity.lean            # Δu ∈ H^k ⇒ u ∈ H^{k+2}
                                         #   via DGNM + POU chart reduction
      Lichnerowicz.lean                  # λ_1 ≥ n/(n-1) · inf(Rc/g) via Weitzenböck
      WithBoundary/                      # with-boundary Laplacian (Dirichlet + Neumann)
        Dirichlet/
          Def.lean                       # Δ_g^D via Friedrichs on H^1_0
          Resolvent.lean                 # compact resolvent on Dirichlet space
          Spectrum.lean                  # discrete eigenvalues, smooth eigenfunctions
          EllipticRegularity.lean        # H^1_0 → H^2 ∩ H^1_0
          Lichnerowicz.lean              # Lichnerowicz with Dirichlet
        Neumann/
          Def.lean                       # Δ_g^N via Friedrichs on H^1
          Resolvent.lean                 # compact resolvent on Neumann space
          Spectrum.lean                  # discrete eigenvalues
          EllipticRegularity.lean        # H^1 → H^2 with Neumann b.c.
          Reilly.lean                    # Reilly formula (boundary Lichnerowicz)
    HeatEquation/
      Semigroup.lean                     # e^{tΔ} via spectral calculus
      Smoothing.lean                     # u₀ ∈ L² ⇒ u(t) ∈ C^∞ for t > 0
      Duhamel.lean                       # u = e^{tΔ}u₀ + ∫ e^{(t-s)Δ} f(s) ds
      MaximumPrinciple.lean              # parabolic weak max principle
      WithBoundary/                      # heat semigroup w/ boundary conditions
        DirichletSemigroup.lean          # e^{tΔ_g^D}
        NeumannSemigroup.lean            # e^{tΔ_g^N}
        Smoothing.lean                   # adapted smoothing
        Duhamel.lean                     # Duhamel w/ boundary conditions
        MaximumPrinciple.lean            # max principle (Hopf lemma form on bdry)
    Parabolic/
      ScalarLinear.lean                  # ∂_t u = Δu + V(x,t)u + f
      TensorLinear.lean                  # ∂_t T = Δ T + (lower-order)
      QuasiLinear.lean                   # Banach fixed point scheme
      EnergyEstimates.lean               # H^k-norm Grönwall; Weitzenböck reuse
      WithBoundary/                      # parabolic w/ Dirichlet + Neumann
        DirichletLinear.lean
        NeumannLinear.lean
        DirichletQuasiLinear.lean
        NeumannQuasiLinear.lean
        EnergyEstimates.lean             # H^k Grönwall + boundary correction
    HarmonicAnalysis/
      EuclideanLogSobolev.lean           # Gross's log-Sob on ℝⁿ
      ManifoldLogSobolev.lean            # M-version from CD(K, ∞) (via BakryEmery)
      LiYau.lean                         # OPTIONAL: Li–Yau gradient est. via Synthetic
      Riesz.lean                         # OPTIONAL: R_j := ∇_j (-Δ)^{-1/2}
      WithBoundary/                      # log-Sob, Li–Yau on cpt-w-bdry
        ManifoldLogSobolev.lean          # CD(K,∞) on Neumann Δ_g^N
        LiYau.lean                       # OPTIONAL: Li–Yau on Neumann heat flow

  PDE/                                   NEW
    DeTurck/
      VectorField.lean                   # W = W(g, ḡ) from background metric
      Transformation.lean                # ∂_t g = -2 Rc + L_W g is strictly parabolic
      Symbol.lean                        # principal symbol computation
      ODEGauge.lean                      # φ_t via ODE (NOT harmonic map heat flow)
    RicciShortTime.lean                  # FINAL theorem, closes Synthetic axiom
    RicciSyntheticClosure.lean           # hooks theorem into
                                         # Synthetic/Realization/RicciFlow.lean
    TensorMaximumPrinciple/              # NEW — Hamilton path H1
      ConvexCone.lean                    # closed convex cones, tangent cones
      Basic.lean                         # parabolic PDE cone preservation
      PositiveDefinite.lean              # Ric > 0 preserved under RF

  Synthetic/Flow/RicciFlow/
    Pinching/                            # NEW — Hamilton path H2
      RicciEvolution.lean                # ∂_t Rc from ∂_t Rm
      TraceFreeEvolution.lean            # ∂_t |Ric₀|²
      EigenvalueEstimates.lean           # eigenvalue ODE analysis
      PinchingInequality.lean            # |Ric₀|²/R² non-increasing
      FiniteTimeBlowup.lean              # R_max → ∞ in finite time
    Normalized/                          # NEW — Hamilton path H3
      Definition.lean                    # normalized flow, volume preserved
      Evolution.lean                     # normalized ∂_t Rm, ∂_t Rc, ∂_t R
      ShiEstimates.lean                  # Shi's derivative estimates
      LongTimeExistence.lean             # long-time existence
      Convergence.lean                   # exponential convergence to Einstein
      ConstantCurvature.lean             # 3D: Rc=c·g ⇒ const sectional curvature

  Geometry/                              # NEW — Hamilton path H4
    Geodesic.lean                        # geodesic spray, local existence
    ExponentialMap.lean                  # exp_p, smoothness, d(exp_p)_0=id
    ConstCurvatureJacobi.lean            # Jacobi fields for constant K only
    ConjugatePoint.lean                  # conjugate points at π/√K
    SphereRecognition.lean               # M ≅ S^n for constant K>0

  Hamilton/                              # NEW — Hamilton path H5
    PositiveRicci.lean                   # final theorem: Ric>0 ∧ π₁=0 ⇒ S³

  Perelman/                              NEW
    F.lean                               # F(g, f) = ∫ (R + |∇f|²) e^{-f} dV
    FMonotone.lean                       # dF/dt ≥ 0; Γ_2 / BakryEmery repack
    W.lean                               # W(g, f, τ) entropy
    WMonotone.lean                       # dW/dτ ≥ 0
    ReducedLength.lean                   # L-function, reduced length ℓ
    NoLocalCollapse.lean                 # κ-non-collapsing

  Poincare/                              far future
    Surgery/
    Geometrization/
```

---

## Phase 1 — Riemannian Volume Measure

> **Phase 1 with-boundary note**: the Riemannian volume measure construction (chart density × Lebesgue × POU) is **boundary-agnostic** — chart targets can be half-spaces and the construction goes through unchanged. Phase 1 ships ONE version that serves both tracks. The `[I.Boundaryless]` hypothesis is NOT needed in Phase 1's exported signatures (verified: Phase 1's `Integral/Measure/{ChartDensity,Glue,Invariance,Properties,Family}.lean` carry zero `[I.Boundaryless]` references).

### 1.1 Chart density (`Integral/Measure/ChartDensity.lean`)

For `g : RiemannianMetric I ∞ M` and a chart `(U, φ) = extChartAt I x₀`, define

```lean
noncomputable def chartDensity (g : RiemannianMetric I ∞ M) (x₀ : M) : M → ℝ :=
  fun x => Real.sqrt (Matrix.det (gramMatrixInChart g x₀ x))
```

where `gramMatrixInChart` reads `g_ij(x) = g(x)(∂/∂x^i, ∂/∂x^j)` by applying `Bundle.ContMDiffRiemannianMetric.inner g x` to the chart's coordinate frame vectors. Prove:

1. `chartDensity_pos`: density is `> 0` on the chart source.
2. `chartDensity_smooth`: `C^∞`. Components `g_ij` are smooth (by definition of `ContMDiffRiemannianMetric.inner`); `Matrix.det` polynomial; `Real.sqrt` smooth on `ℝ_{>0}`.
3. Local measure: push Lebesgue via `φ.symm`, `withDensity`-weight by `chartDensity`, restrict to chart source.

### 1.2 Global glue (`Integral/Measure/Glue.lean`)

Given a smooth POU `{φ_α}` subordinate to an atlas `{U_α}`,

```lean
noncomputable def riemannianMeasure (g : RiemannianMetric I ∞ M) : Measure M :=
  ∑' α, (localMeasure_α g).withDensity (fun x => φ_α x)
```

Each summand locally finite Radon; POU locally finite ⇒ sum well-defined; `∫ f dμ_g = ∑_α ∫ f · φ_α dμ_g` for compactly supported smooth `f`.

### 1.3 Chart invariance (`Integral/Measure/Invariance.lean`)

For two charts `φ, ψ` with the same source: `|det(D(ψ ∘ φ⁻¹))|` times the transformation law `det g_ψ = det g_φ · |det(D(φ ∘ ψ⁻¹))|²` gives the equality.

### 1.4 Properties (`Integral/Measure/Properties.lean`)

`IsLocallyFiniteMeasure`, `IsOpenPosMeasure`, σ-finite, Radon.

### 1.5 Time-parameterised family (`Integral/Measure/Family.lean`)

Time-differentiability of `t ↦ ∫ f(t, x) dμ_{g(t)}(x)`; volume variation `d/dt dV_{g(t)} = ½ tr_g(∂_t g) dV_{g(t)}`. **Hypotheses follow principle (D′)**: pointwise `HasDerivAt` in `t` of the metric's chart-Gram entries and of `f`, plus continuity / domination in `(t, x)` on neighborhoods of compact sets — **never** joint `C^∞` on $\mathbb{R} \times M$. The Ricci-flow solution's actual joint smoothness is packaged on the Synthetic / Realization side at the point of use, not inside the Integral-layer API.

### 1.6 Mathematical risks

POU + `tsum` subtleties, `ContMDiff.matrix_det` may need bootstrapping, chart-invariance is the "densest calculation of the phase" — isolate as stand-alone Euclidean lemma about `withDensity` under diffeomorphic change-of-variables.

---

## Phase 2 — Integration Mechanics

> **Phase 2 with-boundary note**: integration mechanics (Bochner integral wrappers, compact-support API, $L^2$ tensor inner product) are **boundary-agnostic**. Phase 2 ships ONE version that serves both tracks. No `[I.Boundaryless]` references needed.

### 2.1 Basic API (`Integral/Integration/Basic.lean`)

`∫_M f := ∫ f dμ_g`; `integral_add`, `integral_smul`, measurability.

### 2.2 Compact support (`Integral/Integration/CompactSupport.lean`)

`C_c^∞(M, ℝ)`, `Γ_c(TM)` as `ℝ`-submodules. Closed under `·`, `X(f)`, `∇`. Dense in `L^p`.

### 2.3 L² on tensor fields (`Integral/Integration/TensorL2.lean`)

`⟨S, T⟩_{L²} := ∫_M ⟨S(x), T(x)⟩_g dμ_g` using Synthetic's `TensorInnerProduct.lean`. Concrete via Lp completion.

---

## Phase 3 — Divergence Theorem & IBP

**This is the analytic core.** Δ self-adjointness, energy estimates, Perelman monotonicity all chain off this.

> **Phase 3 status**: BOTH the boundaryless and the with-boundary tracks have shipped (~17,000 lines in `Integral/DivergenceTheorem/`). The boundaryless track lives at the directory's top level; the with-boundary track lives in `WithBoundary/` with 22 sub-files. See "With-boundary parallel" in the Non-Axioms section above for the full file inventory. Downstream Phases 4+ may consume both tracks directly. The mathematical descriptions below remain for reference.

### 3.1 Local formula (`DivergenceTheorem/LocalFormula.lean`)

```
div_g(X) · √det g = ∂_i (X^i · √det g)
```

### 3.2 POU reduction (`DivergenceTheorem/POUReduction.lean`)

`X = ∑_α φ_α X`. Using Synthetic's `divergence_smul` and `∑ φ_α ≡ 1`: `∑ div_g(φ_α X) = ∑ φ_α div_g(X)`.

### 3.3 Closed manifold (`DivergenceTheorem/Closed.lean`)

`[CompactSpace M] → ∀ X, ∫_M div_g(X) dμ_g = 0`. Each chart-local integral is `0` by compact support + Fubini; POU glue.

### 3.4 Proper support (`DivergenceTheorem/Proper.lean`)

Same for `HasCompactSupport X` on general σ-compact `M`.

### 3.5 IBP (`DivergenceTheorem/IBP.lean`)

- `∫ X(f) dμ_g = -∫ f · div_g(X) dμ_g`.
- `∫ ⟨∇f, ∇g⟩_g dμ_g = -∫ f · Δ_g g dμ_g = -∫ Δ_g f · g dμ_g` (f or g compactly supported).

### 3.6 Time-dependent IBP (`DivergenceTheorem/Family.lean`)

Pointwise-in-t IBP + `SpatialTemporalComm` + volume variation.

---

## Phase 4 — Sobolev Spaces on M

> **Phase 4 with-boundary mandate**: every Sobolev / Rellich / embedding theorem ships boundaryless + with-boundary parallel. See per-task notes below. New Task 4.8 (boundary trace operator) is added for the with-boundary track.

### 4.1 Import DeGiorgi (`Analysis/Sobolev/Local.lean`)

Add `github.com/scottnarmstrong/DeGiorgi` as lake dep; wrap `W^{k,p}(Ω)` for `Ω ⊆ ℝⁿ` open bounded. Provides weak derivatives, completeness, Euclidean Sobolev embedding, DGNM interior regularity.

### 4.2 Intrinsic Sobolev (`Analysis/Sobolev/Manifold.lean`)

```lean
intrinsicSobolev k p := { u : Lp ℝ p μ_g | ∀ j ≤ k, ∇^j u ∈ Lp ℝ p μ_g }
```

Distributional `∇^j`; completeness; `C^∞(M)` dense in `H^k(M)` via mollification (Mathlib `BumpFunction.Convolution`).

### 4.3 Chart-based (`Analysis/Sobolev/Chart.lean`)

`u ∈ W^{k,p}_chart(M)` iff every `(φ_α u · ρ_α) ∈ W^{k,p}(ℝⁿ)` via DeGiorgi.

### 4.4 Equivalence (`Analysis/Sobolev/Equivalence.lean`)

Intrinsic vs. chart on compact M: `‖∇u‖² ≈ ‖∂u‖² ± lower-order` with constants from bounded Christoffel symbols.

### 4.5 Rellich–Kondrachov (`Analysis/Sobolev/Rellich.lean`)

`H^{k+1}(M) ↪ H^k(M)` compact on compact M. Chart-reduce to DeGiorgi.

### 4.6 Sobolev embedding (`Analysis/Sobolev/Embedding.lean`)

`k > n/p ⇒ W^{k,p}(M) ↪ C^0(M)`.

### 4.7 Risks

DeGiorgi toolchain alignment (pin commit); distributional ∇^j subtlety; constant bookkeeping on compact M.

### 4.8 Boundary trace operator (with-boundary track) (`Analysis/Sobolev/WithBoundary/Trace.lean`)

For $u \in W^{1,p}(M)$ on a compact manifold-with-boundary $(M, g)$, the **boundary trace** $u|_{\partial M}$ is well-defined as an element of $L^p(\partial M, \mathrm{surfaceMeasure}\,g)$, and the trace operator $\mathrm{tr}_{\partial M}: W^{1,p}(M) \to L^p(\partial M)$ is bounded linear. Build chart-locally via DeGiorgi's trace operator on $\Omega \cap \{x_0 = 0\}$ in a half-space chart + POU glue. Density of $C^\infty(M) \cap W^{1,p}$ → trace identity $\mathrm{tr}_{\partial M}(u) = u|_{\partial M}$ for smooth $u$.

This is the bridge between Phase 4 (Sobolev) and the boundary-condition variants of the Laplacian (Phase 5 with-boundary track).

---

## Phase 5 — Laplacian and Spectrum

> **Phase 5 with-boundary mandate**: on a manifold-with-boundary, the Laplacian splits into **Dirichlet** (`Δ_g^D` via Friedrichs on $H^1_0$) and **Neumann** (`Δ_g^N` via Friedrichs on $H^1$) versions. Each has its own resolvent / spectrum / elliptic regularity / Lichnerowicz parallel. The orchestrator delivers the boundaryless track first, then the Dirichlet track, then the Neumann track. Files in `Analysis/Laplacian/WithBoundary/{Dirichlet,Neumann}/`.

### 5.1 Definition (`Analysis/Laplacian/Def.lean`)

```lean
noncomputable def laplacian : C^∞(M, ℝ) →ₗ[ℝ] C^∞(M, ℝ) :=
  fun f => divergence_g (gradient_g f)
```

Chart-locally wraps Kebekus's `Analysis/InnerProductSpace/Laplacian.lean:laplacianWithin`.

### 5.2 Self-adjointness on `C^∞_c` (`Analysis/Laplacian/SelfAdjoint.lean`)

Direct from Phase 3 IBP twice.

### 5.3 Closed extension, domain H² (`Analysis/Laplacian/Domain.lean`)

Extend Δ to H² → L². **Potential Mathlib gap**: unbounded `IsSelfAdjoint` is not developed in Mathlib. Pragmatic path: **work exclusively with the bounded resolvent `(Δ + 1)⁻¹`** (below). Essential self-adjointness can be recorded as a corollary later if needed.

### 5.4 Compact resolvent (`Analysis/Laplacian/Resolvent.lean`)

**Theorem**: `(Δ + 1)⁻¹ : L²(M) → L²(M)` is a compact bounded self-adjoint operator.

**Proof**: maps into H² (elliptic regularity 5.6); H² ↪ L² compact by Rellich (4.5); composition compact. Self-adjointness from IBP. Order internally: 5.6 → 5.4 → 5.5.

### 5.5 Discrete spectrum (`Analysis/Laplacian/Spectrum.lean`)

**Theorem**: `Δ` has pure-point spectrum `0 = λ_0 < λ_1 ≤ λ_2 ≤ ... → +∞` with `C^∞` eigenfunctions `{e_n}` forming an orthonormal basis of `L²(M)`.

**Proof**: Assemble from Mathlib's **infinite-dimensional compact self-adjoint spectral theorem**:
- `ContinuousLinearMap.orthogonalComplement_iSup_eigenspaces_eq_bot` (`InnerProductSpace/Spectrum.lean:394`) — eigenvectors' span is total.
- `ContinuousLinearMap.finite_dimensional_eigenspace` (`:421`) — each nonzero eigenspace is finite-dim.

These two don't package as a single "sorted orthonormal basis" theorem (unlike the finite-dim `IsSymmetric.eigenvectorBasis` which is finrank-bound). We assemble:
1. Enumerate eigenvalues of `(Δ+1)⁻¹` descending: `μ_0 ≥ μ_1 ≥ ... → 0`; convert to `λ_n = 1/μ_n − 1` ascending.
2. Within each finite-dim eigenspace pick an orthonormal basis; concatenate.
3. Totality from the iSup/orthogonal-complement lemma.
4. Smoothness of `e_n` by iterated elliptic regularity (5.6).

This assembly is ~500 more lines than the finite-dim shortcut would give.

### 5.6 Elliptic regularity (`Analysis/Laplacian/EllipticRegularity.lean`)

`Δu ∈ H^k(M) ⇒ u ∈ H^{k+2}(M)`. Chart-localize; apply DGNM interior regularity from DeGiorgi; POU-glue.

### 5.7 Lichnerowicz (`Analysis/Laplacian/Lichnerowicz.lean`)

**Theorem**: On closed M with `Rc ≥ (n-1) K g` (K > 0), `λ_1(Δ) ≥ n K`.

**Proof**: For Δ-eigenfunction `f` with `Δf = -λ_1 f`, apply Synthetic's `Bochner.lean:bochner_pointwise` to get
```
Δ|∇f|² = 2|∇²f|² + 2 Rc(∇f, ∇f) + 2⟨∇f, ∇Δf⟩.
```
Integrate: `0 = 2 ∫|∇²f|² + 2 ∫Rc(∇f,∇f) - 2λ_1 ∫|∇f|²`. Cauchy–Schwarz `|∇²f|² ≥ (Δf)²/n = λ_1² f²/n`; combine with the Ricci bound and `∫|∇f|² = λ_1 ∫f²`. A few lines of algebra gives `λ_1 ≥ n K`.

Cheap: Weitzenböck is in Synthetic, IBP in Phase 3, spectrum in 5.5. Pure assembly.

### 5.8 With-boundary Dirichlet/Neumann variants (`Analysis/Laplacian/WithBoundary/{Dirichlet,Neumann}/...`)

Mandatory parallel of 5.1–5.7 on a manifold-with-boundary $[\mathrm{HasSmoothBoundary}\,E\,H\,I]\,[\mathrm{CompactSpace}\,M]$. Two boundary-condition variants:

**Dirichlet** ($\mathrm{dom}(Q^D) := H^1_0(M)$):
- `Def.lean`: $\Delta_g^D$ via Friedrichs on $H^1_0$.
- `Resolvent.lean`: $(1-\Delta_g^D)^{-1}$ compact self-adjoint on $L^2$. Compactness from Rellich (Phase 4 with-boundary version).
- `Spectrum.lean`: $\Delta_g^D$ has discrete pure-point spectrum $0 < \lambda_1^D \le \lambda_2^D \le \ldots \to \infty$. Note: $\lambda_0^D > 0$ (Poincaré) — different from boundaryless / Neumann case.
- `EllipticRegularity.lean`: Nirenberg difference quotient method adapted, with chart-localised half-space variant and boundary trace control.
- `Lichnerowicz.lean`: Dirichlet Lichnerowicz lower bound (Reilly / boundary integral correction terms).

**Neumann** ($\mathrm{dom}(Q^N) := H^1(M)$, no trace constraint):
- `Def.lean`: $\Delta_g^N$ via Friedrichs on $H^1$.
- `Resolvent.lean`: $(1-\Delta_g^N)^{-1}$ compact self-adjoint.
- `Spectrum.lean`: discrete spectrum $0 = \lambda_0^N < \lambda_1^N \le \ldots \to \infty$. Constant function is the eigenfunction for $\lambda_0^N = 0$ (matches boundaryless case).
- `EllipticRegularity.lean`: Nirenberg with Neumann b.c.
- `Reilly.lean`: Reilly identity $\int_M (\Delta f)^2 - |\mathrm{Hess}\,f|^2 = \int_M \mathrm{Rc}(\nabla f, \nabla f) + \int_{\partial M} \langle \mathrm{II}(\nabla^\partial f), \nabla^\partial f \rangle - 2 \int_{\partial M} \partial_\nu f \cdot \Delta^\partial f$ (the boundary analog of Bochner integral identity). New, no Synthetic counterpart.

The orchestrator splits the eight files (Dirichlet × 5 + Neumann × 5, minus overlap) into substeps autonomously.

---

## Phase 6 — Heat Equation / Semigroup

> **Phase 6 with-boundary mandate**: heat semigroup on a manifold-with-boundary requires a boundary condition. The orchestrator delivers the boundaryless track (closed M, no boundary terms), then the Dirichlet track $e^{t\Delta_g^D}$, then the Neumann track $e^{t\Delta_g^N}$. Each provides the spectral construction, smoothing, Duhamel formula, and parabolic max principle (with the Hopf lemma form on the boundary). Files in `Analysis/HeatEquation/WithBoundary/{DirichletSemigroup,NeumannSemigroup,Smoothing,Duhamel,MaximumPrinciple}.lean`.

### 6.1 Spectral semigroup (`HeatEquation/Semigroup.lean`)

```lean
heatSemigroup t u := ∑' n, Real.exp (-λ_n · t) • ⟨u, e_n⟩ • e_n
```

Semigroup law, strong continuity, generator `-Δ`. Mathlib has no `StronglyContinuousSemigroup`; we build a thin wrapper as needed.

### 6.2 Smoothing (`HeatEquation/Smoothing.lean`)

`t > 0 ⇒ u(t) ∈ C^∞(M)`. Decay `e^{-λ_n t}` against any Sobolev norm + Weyl-type asymptotics (non-sharp sufficient).

### 6.3 Duhamel (`HeatEquation/Duhamel.lean`, `Parabolic/ScalarLinear.lean`)

`u(t) = e^{tΔ} u_0 + ∫_0^t e^{(t-s)Δ} f(s) ds`.

### 6.4 Max principle (`HeatEquation/MaximumPrinciple.lean`)

Weak parabolic max principle via `u_ε := u − εt`.

### 6.5 With-boundary semigroups (`HeatEquation/WithBoundary/...`)

Mandatory. On compact manifold-with-boundary, both Dirichlet and Neumann semigroups: $e^{t\Delta_g^D} u := \sum_n e^{-\lambda_n^D t} \langle u, e_n^D \rangle e_n^D$ and analogously for Neumann (using the Phase 5 with-boundary spectra). Smoothing ($t > 0 \Rightarrow u(t) \in C^\infty$ on the closed manifold-with-boundary, INCLUDING boundary regularity in the trace sense) requires the Phase 5 elliptic regularity for the corresponding boundary condition. Hopf lemma (strict positivity of normal derivative at boundary maxima for non-constant solutions) for Dirichlet case.

---

## Phase 7 — Parabolic Existence

> **Phase 7 with-boundary mandate**: parabolic existence on a manifold-with-boundary requires Dirichlet or Neumann boundary conditions. The orchestrator delivers boundaryless first, then the four with-boundary variants (linear-Dirichlet, linear-Neumann, quasi-linear-Dirichlet, quasi-linear-Neumann). Files in `Analysis/Parabolic/WithBoundary/`. Energy estimates carry boundary correction terms (boundary integrals via Stokes from Phase 3 with-boundary).

### 7.1 Tensor-valued linear (`Parabolic/TensorLinear.lean`)

`∂_t T = Δ T + (lower-order)`; Synthetic's Weitzenböck handles the commutators.

### 7.2 Quasi-linear (`Parabolic/QuasiLinear.lean`)

Banach fixed point on `u ↦ e^{tΔ}u_0 + ∫ e^{(t-s)Δ} N(u(s)) ds` in `C([0,T]; H^k)`. Uses `Mathlib.Topology.MetricSpace.Contracting`.

### 7.3 Energy estimates (`Parabolic/EnergyEstimates.lean`)

H^k Grönwall. **Crucial reuse**: curvature corrections from commuting `Δ` with `∇^j` are given by Synthetic's `Bochner.lean:bochner_pointwise` and the Ricci-identity lemmas (`hessian_commute_ricci`). **We do not re-derive Weitzenböck here**.

### 7.4 Risks

Compositional Lipschitz (Sobolev algebra `H^k · H^k ⊆ H^k` for k > n/2); tensor-valued heat flow bookkeeping.

### 7.5 With-boundary parabolic (`Parabolic/WithBoundary/...`)

Mandatory. Linear and quasi-linear parabolic problems on compact manifold-with-boundary, with both Dirichlet and Neumann boundary conditions. Built on Phase 5 (with-boundary Δ$_g^D$ / Δ$_g^N$) + Phase 6 (with-boundary semigroups). Energy estimates (Grönwall in $H^k$) carry an additional **boundary correction term** $\int_{\partial M} (\text{boundary trace stuff})$ for Neumann; vanishes for Dirichlet by the trace-zero condition. Files split in the obvious way (linear-Dirichlet, linear-Neumann, quasi-linear-Dirichlet, quasi-linear-Neumann, energy-estimates with boundary corrections).

---

## Phase 8 — DeTurck & Ricci Short-Time Existence

> **Phase 8 with-boundary scope**: Ricci flow on a closed manifold (the M8 endpoint) lives in the boundaryless track. Ricci flow on a manifold-with-boundary is a **separate research-grade problem** (Shi's prescribed-boundary-data short-time existence, Hamilton's clamped-boundary, etc.) that requires careful choice of boundary conditions on the metric flow itself. **The with-boundary version of Phase 8 is OUT OF SCOPE for M8.** The boundary-condition prerequisites built in Phase 5–7 (with-boundary track) provide the analytic foundation; a future phase `PDE/WithBoundary/` could pick up Ricci-flow-with-boundary cleanly without disturbing the boundaryless M8 endpoint.

### 8.1 DeTurck vector field (`PDE/DeTurck/VectorField.lean`)

`W^i(g, ḡ) := g^{jk}(Γ^i_{jk}(g) − Γ̄^i_{jk}(ḡ))`; genuinely a tensor (Christoffel differences are tensorial).

### 8.2 Strict parabolicity (`PDE/DeTurck/Transformation.lean`)

`∂_t g = −2 Rc(g) + L_W g` has principal symbol `|ξ|²_g · id_{Sym²}`. We build a thin `principalSymbol` abstraction.

### 8.3 DeTurck short-time (`PDE/DeTurck/ShortTime.lean`)

Apply Phase 7.

### 8.4 ODE gauge transformation (`PDE/DeTurck/ODEGauge.lean`)

**Simplification**: the classical DeTurck gauge uses the ODE

```
d/dt φ_t(x) = -W(g̃(t), g₀)(φ_t(x)),   φ₀ = id_M
```

where `W` is the DeTurck vector field (a smooth time-dependent vector field). This is an ODE on `M`, **not** a PDE (harmonic map heat flow). The time-dependent ODE reduces to a time-independent integral curve on `M × ℝ` via the extended vector field `V(x, t) = (-W(t)(x), ∂_t)`. Mathlib's `Geometry/Manifold/IntegralCurve/ExistUnique.lean` provides existence and uniqueness for integral curves of smooth vector fields on manifolds (via chart-local Picard–Lindelöf). On a compact manifold, the flow exists for the same time interval as the DeTurck–Ricci flow. `φ_t` is a family of diffeomorphisms (standard flow properties).

Then `g(t) := φ_t^* g̃(t)` solves the true Ricci flow `∂_t g = -2 Rc(g)`.

This is ~400 lines (ODE wrapper + pullback verification), down from the original harmonic-map-heat-flow estimate of ~2000 lines.

### 8.5 Ricci short-time (`PDE/RicciShortTime.lean`)

```lean
theorem ricci_flow_shortTime_exists
    (g_0 : RiemannianMetric I ∞ M) [CompactSpace M] :
    ∃ T > 0, ∃ g_fam : Ico 0 T → RiemannianMetric I ∞ M,
      SmoothInTime g_fam ∧ g_fam 0 = g_0 ∧ ∀ t, ∂_t g_fam t = -2 • Ric (g_fam t)
```

### 8.6 Synthetic closure (`PDE/RicciSyntheticClosure.lean`)

Ricci-flow axiom in `Synthetic/Realization/RicciFlow.lean` becomes a theorem. **Synthetic is unconditional.**

---

## Hamilton Positive Ricci Path — Phases H1–H5

> **Goal**: Formalize Hamilton's 1982 theorem: *A closed simply connected 3-manifold admitting a Riemannian metric with strictly positive Ricci curvature is diffeomorphic to $S^3$.* This is the positive-Ricci-curvature case of the Poincaré conjecture, and historically the first major application of Ricci flow to topology.

> **Scope note**: All phases H1–H5 assume **closed** $M$ (`[CompactSpace M] [I.Boundaryless]`) and **dimension 3** (`FiniteDimensional.finrank ℝ (TangentSpace I : M → Type _) = 3`). The with-boundary versions are out of scope for the Hamilton path (Ricci-flow-with-boundary is a separate research-grade problem — see Phase 8 note). The dimension-3 specialization is essential: in 3D the Weyl tensor vanishes identically, so the Riemann curvature is algebraically determined by the Ricci tensor, which drastically simplifies all estimates.

> **Prerequisites**: Phase 8 (Ricci flow short-time existence, i.e. M8 milestone). The Hamilton path is an **alternative** to the Perelman path (Phase 9–15). While the Perelman path aims at the full Geometrization conjecture via entropy monotonicity and κ-non-collapsing, the Hamilton path is a shorter route targeting only the positive-Ricci-curvature case, using eigenvalue pinching estimates instead of entropy.

> **Existing Synthetic infrastructure consumed**: All pointwise Ricci-flow evolution identities from `Synthetic/Flow/RicciFlow/Evolution/`:
> - `RiemannEvolution.lean` (1476 lines) — the master theorem `riemann_tensor_evolution_hamilton`: $\partial_t Rm = \Delta Rm + Q_{\text{rm}}$ where $Q_{\text{rm}}$ is a purely algebraic expression (no time derivatives). This is the single most important identity for the Hamilton path.
> - `ScalarCurvature.lean` (315 lines) — $\partial_t R = \Delta R + 2|Rc|^2$ under Ricci flow.
> - `Connection.lean`, `Gradient.lean`, `Laplacian.lean` — $\partial_t\nabla$, $\partial_t(\nabla f)$, $\partial_t(\Delta u)$.
> - `RiemannLaplacian.lean` — $\Delta Rm$ (rough Laplacian on the $(1,3)$-Riemann tensor).
> - `RiemannVariation.lean` (641 lines) — connection variation formulas, reusable for DeTurck linearization.

> **Mathlib ODE infrastructure available**: Mathlib provides a full ODE stack that the Hamilton path leverages:
> - `Analysis/ODE/PicardLindelof.lean` (867 lines) — Picard–Lindelöf existence/uniqueness in Banach spaces; $C^n$ smoothness of solutions in time; continuous/Lipschitz dependence on initial conditions.
> - `Analysis/ODE/Gronwall.lean` (408 lines) — Grönwall inequality + ODE solution uniqueness.
> - `Geometry/Manifold/IntegralCurve/ExistUnique.lean` (283 lines) — existence and uniqueness of integral curves of $C^1$ vector fields on smooth manifolds (via chart-local reduction to Picard–Lindelöf). Boundaryless version: `exists_isMIntegralCurveAt_of_contMDiffAt_boundaryless`.
> - `Geometry/Manifold/IntegralCurve/UniformTime.lean` (215 lines) — Lee Lemma 9.15: uniform-time existence on compact manifolds.
> - `Dynamics/Flow.lean` (292 lines) — abstract flow definition (not ODE-constructed; a wrapper is needed).
>
> **What Mathlib ODE does NOT provide (we build ourselves)**:
> - Time-dependent vector fields on manifolds (reducible to time-independent on $M \times \mathbb{R}$)
> - Construction of a global flow from local integral curves on a compact manifold (~300 line wrapper)

### Dependency Graph (Hamilton Path)

```
Phase 8 (M8: Ricci flow short-time existence)
  │
  ├──────────────────────────────────────────────────┐
  │                                                  │
  ▼                                                  ▼
Phase H1: Tensor Maximum Principle          Phase H4: Sphere Recognition
  │  ├── ConvexCone.lean                      ├── Geodesic.lean
  │  ├── Basic.lean (parabolic cone)          ├── ExponentialMap.lean
  │  └── PositiveDefinite.lean                ├── ConstCurvatureJacobi.lean
  │     ★ Ric > 0 preserved                   ├── ConjugatePoint.lean
  │                                           └── SphereRecognition.lean
  ▼                                              ★ M ≅ S³
Phase H2: Pinching Estimates
  ├── RicciEvolution.lean (∂_t Rc from ∂_t Rm)
  ├── TraceFreeEvolution.lean (∂_t |Ric₀|²)
  ├── EigenvalueEstimates.lean
  ├── PinchingInequality.lean
  └── FiniteTimeBlowup.lean
     ★ R_max → ∞ in finite time
  │
  ▼
Phase H3: Normalized Ricci Flow
  ├── Definition.lean
  ├── Evolution.lean
  ├── ShiEstimates.lean
  ├── LongTimeExistence.lean
  ├── Convergence.lean
  └── ConstantCurvature.lean
     ★ converges to Einstein metric Rc = c·g, c > 0
     ★ 3D ⇒ constant sectional curvature > 0
  │
  ▼
Phase H5: Final Assembly
  └── PositiveRicci.lean
     ★ Theorem: closed simply connected 3-manifold with Ric > 0 is S³
```

### Phase H1 — Tensor Maximum Principle

**Prerequisites**: Phase 8 (Ricci flow short-time existence), Phase 6.4 (scalar parabolic max principle — for bootstrapping).

**Outputs**:
- `PDE/TensorMaximumPrinciple/ConvexCone.lean` — closed convex cones in finite-dimensional real vector spaces, tangent cones, ODE preservation condition.
- `PDE/TensorMaximumPrinciple/Basic.lean` — the core theorem: parabolic PDE on vector bundles preserves closed convex cones.
- `PDE/TensorMaximumPrinciple/PositiveDefinite.lean` — application: the cone of positive-definite symmetric $(0,2)$-tensors is preserved under Ricci flow, hence **$Ric > 0$ is preserved**.

**Mathematical content**: Hamilton's tensor maximum principle generalizes the scalar maximum principle (Phase 6.4) to sections of vector bundles. The statement:

> Let $E \to M$ be a smooth Riemannian vector bundle with a metric connection, and let $T(t) \in \Gamma(E)$ solve $\partial_t T = \Delta T + Q(T)$ on $[0, \tau)$, where $Q$ is a smooth fiber-preserving map. Let $K \subseteq E$ be a closed fiberwise convex subset (i.e., each fiber $K_x \subseteq E_x$ is a closed convex cone) that is **invariant under the ODE** $dT/dt = Q(T)$ (meaning: if $T \in K$ then the ODE solution starting at $T$ stays in $K$ for all small positive time). Then $T(t) \in K$ for all $t \in [0, \tau)$.

**Proof sketch**:
1. **Reduction to the scalar case**: For any supporting linear functional $\ell$ to the cone $K$ (an element of the dual cone), the scalar function $u(t, x) := \ell(T(t, x))$ is nonnegative initially and satisfies a parabolic inequality $\partial_t u \ge \Delta u + \text{(lower-order terms involving } T\text{)}$.
2. **Scalar parabolic maximum principle** (Phase 6.4): $u \ge 0$ initially $\Rightarrow$ $u \ge 0$ for all time.
3. **Convex geometry**: if all supporting linear functionals stay nonnegative, then the section stays in the cone.

**Application to Ricci flow**: Take $E = \mathrm{Sym}^2(T^*M)$ (symmetric $(0,2)$-tensors) and $K =$ the cone of positive-definite symmetric bilinear forms. The ODE $d/dt\, Rc = -2 Rc^2 + \dots$ (obtained from the $\Delta$-free part of the full PDE) preserves $K$: for any eigenvector $v$ of $Rc$ with eigenvalue $\lambda$, the ODE for $\lambda$ satisfies $d\lambda/dt \ge -2\lambda^2$, so if $\lambda > 0$ initially, it stays positive. Hence $Ric > 0$ is preserved under Ricci flow.

**Key theorem**:
```lean
theorem ricci_positive_preserved_under_rf
    [CompactSpace M] [I.Boundaryless]
    (g_fam : ℝ → RiemannianMetric I ∞ M) [h_rf : IsRicciFlow g_fam]
    (h_pos : ∀ x, posDef (Ric (g_fam 0) x)) :
    ∀ t ≥ 0, ∀ x, posDef (Ric (g_fam t) x) := ...
```

**Line estimate**: ~2000 lines (convex cone theory ~600, core tensor max principle ~800, application to Ricci positivity ~600).

### Phase H2 — Pinching Estimates

**Prerequisites**: Phase H1, Synthetic `RiemannEvolution.lean` ($\partial_t Rm = \Delta Rm + Q$).

**Outputs**:
- `Synthetic/Flow/RicciFlow/Pinching/RicciEvolution.lean` — derive the explicit formula for $\partial_t Rc$ from the Synthetic master theorem $\partial_t Rm = \Delta Rm + Q_{\text{rm}}$ by contracting the first two indices. In 3D this yields the classical Hamilton formula $\partial_t Rc_{ij} = \Delta Rc_{ij} + 3R Rc_{ij} - 6 Rc_{ik} Rc^k_j + (2|Rc|^2 - R^2) g_{ij}$ (or an equivalent form).
- `Synthetic/Flow/RicciFlow/Pinching/TraceFreeEvolution.lean` — evolution of the trace-free Ricci tensor $Ric_0 := Rc - \frac{R}{3}g$ and its squared norm $|Ric_0|^2 = |Rc|^2 - R^2/3$.
- `Synthetic/Flow/RicciFlow/Pinching/EigenvalueEstimates.lean` — evolution of the eigenvalues $\lambda \le \mu \le \nu$ of $Rc$ under the Ricci flow, via the maximum principle applied to carefully chosen test functions of the eigenvalues.
- `Synthetic/Flow/RicciFlow/Pinching/PinchingInequality.lean` — the key estimate: $|Ric_0|^2 / R^2$ is non-increasing (or bounded by a decaying function) under Ricci flow when $Ric > 0$. In 3D, this implies the ratio $\nu/\lambda$ of largest to smallest eigenvalue of $Rc$ is bounded uniformly in time.
- `Synthetic/Flow/RicciFlow/Pinching/FiniteTimeBlowup.lean` — **Theorem**: if $Ric > 0$ everywhere on a closed 3-manifold, then the un-normalized Ricci flow develops a singularity in finite time: $\max_{x\in M} R(x,t) \to \infty$ as $t \nearrow T_{\max} < \infty$.

**Mathematical content**: This is the heart of Hamilton's 1982 paper. The key idea:

1. **From $\partial_t Rm$ to $\partial_t Rc$**: The Synthetic master theorem `riemann_tensor_evolution_hamilton` gives $\partial_t Rm = \Delta Rm + Q_{\text{rm}}$ with $Q_{\text{rm}}$ expressed purely algebraically in $Rm$, $Rc$, $g$, and $\nabla \nabla Rc$ (no time derivatives). Contracting the first and second indices ($g^{ik} (\partial_t Rm_{ijkl}) = \partial_t Rc_{jl}$) yields the explicit formula for $\partial_t Rc$. Since $g^{ik} \Delta Rm_{ijkl} = \Delta Rc_{jl}$ (the rough Laplacian commutes with metric contraction — proved as a lemma), the main work is computing the contraction of $Q_{\text{rm}}$.

2. **3D simplification**: In dimension 3, the full Riemann tensor is determined by the Ricci tensor:
   $$Rm_{ijkl} = R_{ik}g_{jl} - R_{il}g_{jk} - R_{jk}g_{il} + R_{jl}g_{ik} - \frac{R}{2}(g_{ik}g_{jl} - g_{il}g_{jk})$$
   This identity (pure linear algebra, ~300 lines) is used to eliminate $Rm$ from all evolution equations, reducing everything to $Rc$ and $R$.

3. **Evolution of $|Ric_0|^2$**: Compute $\partial_t|Ric_0|^2$ from the $\partial_t Rc$ formula. The result has the structure $\partial_t|Ric_0|^2 = \Delta|Ric_0|^2 - 2|\nabla Ric_0|^2 + (\text{cubic in } Ric_0, R)$. Using the 3D identity to express everything in terms of eigenvalues, one obtains a differential inequality that forces $|Ric_0|^2 / R^{2-\varepsilon} \to 0$ as $R \to \infty$.

4. **Eigenvalue pinching**: Let $\lambda(x,t) \le \mu(x,t) \le \nu(x,t)$ be the eigenvalues of $Rc$. The pinching estimate shows that $\frac{\nu}{\lambda} \le C$ uniformly in space and time, and $\frac{\nu - \lambda}{R} \to 0$ as $R \to \infty$. This means the metric becomes "rounder" (eigenvalues approach equality) as the curvature grows.

5. **Finite-time singularity**: The evolution $\partial_t R = \Delta R + 2|Rc|^2$ implies $\partial_t R_{\max} \ge \frac{2}{3} R_{\max}^2$ (since $|Rc|^2 \ge R^2/3$ by Cauchy–Schwarz on eigenvalues). The ODE $dy/dt = \frac{2}{3}y^2$ blows up in finite time, so $R_{\max} \to \infty$ at some $T_{\max} < \infty$.

**Key theorem**:
```lean
theorem ricci_positive_finite_time_singularity
    [CompactSpace M] [I.Boundaryless]
    (h_dim : finrank ℝ (TangentSpace I : M → Type _) = 3)
    (g_fam : ℝ → RiemannianMetric I ∞ M) [h_rf : IsRicciFlow g_fam]
    (h_pos : ∀ x, posDef (Ric (g_fam 0) x)) :
    ∃ T < ∞, (∀ t < T, ∀ x, posDef (Ric (g_fam t) x)) ∧
      Filter.Tendsto (λ t => maxScalarCurvature (g_fam t)) (𝓝[<] T) atTop := ...
```

**Line estimate**: ~3500 lines (Ricci evolution from Rm ~600, trace-free evolution ~700, eigenvalue estimates ~800, pinching inequality ~900, finite-time blowup ~500).

### Phase H3 — Normalized Ricci Flow

**Prerequisites**: Phase H2, Phase 8 (Ricci flow short-time existence), Synthetic evolution identities.

**Outputs**:
- `Synthetic/Flow/RicciFlow/Normalized/Definition.lean` — the normalized Ricci flow: $\partial_t \tilde{g} = -2 Rc(\tilde{g}) + \frac{2}{n} r \tilde{g}$ where $r = \frac{\int_M R\, d\mu}{\int_M d\mu}$ is the average scalar curvature. Volume $\int d\mu_{\tilde{g}}$ is constant. The normalized flow is obtained from the un-normalized flow by a time reparameterization $d\tilde{t}/dt = \text{vol}(t)^{-2/n}$ and a homothetic scaling.
- `Synthetic/Flow/RicciFlow/Normalized/Evolution.lean` — recompute $\partial_{\tilde{t}} Rm$, $\partial_{\tilde{t}} Rc$, $\partial_{\tilde{t}} R$ under the normalized flow. The normalization adds lower-order correction terms proportional to $r \cdot Rm$, $r \cdot Rc$, $r \cdot R$ to the un-normalized evolution equations.
- `Synthetic/Flow/RicciFlow/Normalized/ShiEstimates.lean` — **Shi's local derivative estimates**: if $|Rm|$ is bounded on $M \times [0, T)$, then for every $k \ge 1$, $|\nabla^k Rm|$ is also bounded, with estimates depending only on $k$, $\sup|Rm|$, $T$, and the initial metric. The proof differentiates the evolution equation $k$ times, commutes $\Delta$ with $\nabla$ (producing $Rm * \nabla^k Rm$ terms via Synthetic's commutator identities), and applies a parabolic maximum principle inductively.
- `Synthetic/Flow/RicciFlow/Normalized/LongTimeExistence.lean` — **Theorem**: the normalized Ricci flow on a closed 3-manifold with $Ric > 0$ exists for all time $t \in [0, \infty)$. The proof uses the pinching estimate (Phase H2) to bound $|Rm|$ uniformly in time, then Shi's estimates to bound all derivatives, preventing finite-time singularity formation.
- `Synthetic/Flow/RicciFlow/Normalized/Convergence.lean` — **Theorem**: under the normalized Ricci flow with $Ric > 0$, $|Ric_0| \to 0$ and $R \to \text{const} > 0$ exponentially as $t \to \infty$. Hence $g(t)$ converges smoothly to a limit metric $g_\infty$ satisfying $Rc(g_\infty) = c \cdot g_\infty$ with $c > 0$ (a positive Einstein metric).
- `Synthetic/Flow/RicciFlow/Normalized/ConstantCurvature.lean` — **3D algebraic fact**: on a 3-manifold, $Rc = c \cdot g$ implies the metric has constant sectional curvature $K = c/2$. This follows from the 3D decomposition of $Rm$ in terms of $Rc$ (the same identity used in Phase H2).

**Mathematical content for Shi's estimates** (the most technically demanding part of Phase H3):

The evolution of $\nabla^k Rm$ is obtained by differentiating $\partial_t Rm = \Delta Rm + Rm * Rm$:
$$\partial_t (\nabla^k Rm) = \Delta(\nabla^k Rm) + \sum_{i+j = k} \nabla^i Rm * \nabla^j Rm$$
where $*$ denotes some algebraic bilinear pairing. The commutation $[\Delta, \nabla^k]$ produces curvature terms that are absorbed into the sum. Define $S_k := |\nabla^k Rm|^2$. Using the evolution equation and the Bochner identity:
$$\partial_t S_k = \Delta S_k - 2|\nabla^{k+1} Rm|^2 + \sum_{i+j=k} \nabla^i Rm * \nabla^j Rm * \nabla^k Rm$$
Let $K := \sup |Rm|$ and assume inductively that $S_j \le C_j$ for $j < k$. The worst term is $\nabla^k Rm * Rm * \nabla^k Rm \le K \cdot S_k$ and lower-order products bounded by induction. A maximum principle argument then bounds $S_k$.

**Key theorem**:
```lean
theorem normalized_rf_convergence_einstein
    [CompactSpace M] [I.Boundaryless]
    (h_dim : finrank ℝ (TangentSpace I : M → Type _) = 3)
    (g_fam : ℝ → RiemannianMetric I ∞ M) [h_rf : IsNormalizedRicciFlow g_fam]
    (h_pos : ∀ x, posDef (Ric (g_fam 0) x)) :
    ∃ (c : ℝ) (h_c : c > 0) (g_∞ : RiemannianMetric I ∞ M),
      Tendsto g_fam atTop (𝓝 g_∞) ∧
      ∀ x, Ric g_∞ x = c • g_∞ x := ...
```

**Line estimate**: ~3500 lines (definition + reparameterization ~400, normalized evolutions ~600, Shi estimates ~1000, long-time existence ~600, convergence ~500, constant curvature ~400).

### Phase H4 — Sphere Recognition (Constant Positive Curvature)

**Prerequisites**: Phase H3 (limit metric $g_\infty$ has constant positive sectional curvature), Mathlib `Geometry/Manifold/IntegralCurve/` (ODE on manifolds), Mathlib covering space theory (`Mathlib/Topology/Covering/Basic.lean`), Mathlib fundamental group (`Mathlib/AlgebraicTopology/FundamentalGroupoid/`).

**Outputs**:
- `Geometry/Geodesic.lean` — geodesic spray, local existence and uniqueness of geodesics.
- `Geometry/ExponentialMap.lean` — the exponential map $\exp_p : T_p M \to M$, smooth dependence on initial data, $d(\exp_p)_0 = \mathrm{id}$.
- `Geometry/ConstCurvatureJacobi.lean` — Jacobi fields specialized to **constant curvature $K > 0$ only**. The Jacobi equation degenerates to the scalar ODE $J''(t) + K J(t) = 0$ with solution $J(t) = A \sin(\sqrt{K} t) + B \cos(\sqrt{K} t)$.
- `Geometry/ConjugatePoint.lean` — conjugate points along radial geodesics occur precisely at $t = \pi/\sqrt{K}, 2\pi/\sqrt{K}, \dots$. Hence $\exp_p$ is a local diffeomorphism on $B_{\pi/\sqrt{K}}(0) \subset T_p M$.
- `Geometry/SphereRecognition.lean` — **Theorem**: A closed simply connected $n$-manifold with a Riemannian metric of constant positive sectional curvature is diffeomorphic to $S^n$.

**What Mathlib provides**: Mathlib has **no** exponential map, geodesics, Jacobi fields, conjugate points, or Hopf-Rinow. However, Mathlib has:
- A complete **covering space** theory: `IsCoveringMap`, `IsEvenlyCovered`, fiber bundle covering maps, quotient covering maps (free properly discontinuous actions).
- A complete **fundamental group** theory: `FundamentalGroupoid`, `FundamentalGroup`, `SimplyConnectedSpace`, homotopy invariance, product formulas, path-connected basepoint independence.
- **ODE on manifolds**: `exists_isMIntegralCurveAt_of_contMDiffAt_boundaryless` provides local existence of integral curves of vector fields on smooth manifolds.

**What we must build from scratch**:

**H4.1 Geodesic spray and geodesics** (`Geometry/Geodesic.lean`):

The geodesic spray $S : TM \to TTM$ is a smooth vector field on the tangent bundle. In local coordinates $(x^i, v^i)$ on $TM$ induced by a chart on $M$:
$$S(x, v) = v^i \frac{\partial}{\partial x^i} - \Gamma^i_{jk}(x) v^j v^k \frac{\partial}{\partial v^i}$$
where $\Gamma^i_{jk}$ are the Christoffel symbols of the Levi-Civita connection. Chart-invariance of this expression is verified using the Christoffel symbol transformation law (available from Mathlib's `CovariantDerivative` API or our Synthetic Realization). The geodesic through $p$ with initial velocity $v$ is the projection to $M$ of the integral curve of $S$ starting at $(p, v) \in TM$.

Since $TM$ is a smooth manifold (Mathlib: `TangentBundle` is a `SmoothManifoldWithCorners`), Mathlib's `exists_isMIntegralCurveAt_of_contMDiffAt_boundaryless` provides local existence and uniqueness of geodesics. On a compact manifold, the uniform-time lemma (`UniformTime.lean`) gives a uniform $\varepsilon > 0$ such that geodesics exist for time $(-\varepsilon, \varepsilon)$ from every point and every unit direction.

**H4.2 Exponential map** (`Geometry/ExponentialMap.lean`):
$$\exp_p(v) := \gamma_v(1), \qquad \gamma_v \text{ the geodesic with } \gamma_v(0) = p, \dot{\gamma}_v(0) = v$$
$\exp_p$ is defined on a star-shaped neighborhood of $0 \in T_p M$ and is smooth (by smooth dependence of ODE solutions on parameters). $d(\exp_p)_0 = \mathrm{id}_{T_p M}$ follows from $\gamma_{tv}(s) = \gamma_v(ts)$ (homogeneity of geodesics) and the definition of the tangent map.

**H4.3 Jacobi fields for constant curvature** (`Geometry/ConstCurvatureJacobi.lean`):

For a 1-parameter family of geodesics $\gamma_s(t) = \exp_p(t(v + s w))$, the variation vector field $J(t) = \frac{\partial}{\partial s}\big|_{s=0} \gamma_s(t)$ satisfies the Jacobi equation $D^2 J/dt^2 + R(J, \dot{\gamma})\dot{\gamma} = 0$. For **constant sectional curvature** $K$, $R(J, \dot{\gamma})\dot{\gamma} = K \cdot (| \dot{\gamma}|^2 J - \langle J, \dot{\gamma}\rangle \dot{\gamma})$. Decomposing $J = J^\perp \oplus J^\parallel$ (orthogonal/parallel to $\dot{\gamma}$):
- $J^\parallel(t) = (a + b t) \dot{\gamma}(t)$ (linear, trivial solution).
- $J^\perp(t)$ in a parallel orthonormal frame along $\dot{\gamma}$ satisfies the **scalar ODE**: $f''(t) + K |\dot{\gamma}|^2 f(t) = 0$. For a unit-speed geodesic ($|\dot{\gamma}| = 1$) and $K = 1$ (after rescaling): $f(t) = A \sin(t) + B \cos(t)$.

A Jacobi field with $J(0) = 0$ (vanishing at $p$) has the form $J(t) = \sin(t) \cdot E(t)$ where $E(t)$ is a parallel vector field along $\dot{\gamma}$.

**H4.4 Conjugate points** (`Geometry/ConjugatePoint.lean`):

$d(\exp_p)_v(w) = J_w(1)$ where $J_w$ is the Jacobi field along the radial geodesic with $J(0) = 0$, $DJ/dt(0) = w$. From H4.3, $J_w(t) = \sin(t) \cdot E_w(t)$ for $K = 1$, where $E_w(0) = w$. Hence $d(\exp_p)_v$ is singular iff $\sin(|v|) = 0$, i.e., $|v| = k\pi$ for $k = 1, 2, \dots$

Thus $\exp_p$ is a local diffeomorphism on the open ball $B_\pi(0) \subset T_p M$ (the first conjugate radius is $\pi$). For initial velocities with $|v| < \pi$, the exponential map is a diffeomorphism onto its image.

**H4.5 Sphere recognition** (`Geometry/SphereRecognition.lean`):

On a closed manifold $M$ with constant positive sectional curvature $K = 1$ (after rescaling), pick $p \in M$.

1. **Surjectivity**: $\exp_p(B_\pi(0)) = M$. For any $q \in M$, let $\gamma$ be a length-minimizing geodesic from $p$ to $q$ (exists by compactness of $M$ — the Riemannian distance function attains its minimum). Since $M$ has constant curvature $=1$, $\gamma$ has no conjugate points before $\pi$, so $\gamma$ is minimizing. The length of $\gamma$ is at most the diameter of $M$. The diameter is at most $\pi$ (by a standard argument: if $\mathrm{diam}(M) > \pi$, then some geodesic of length $> \pi$ would contain a conjugate point, contradicting minimality). Hence $q = \exp_p(v)$ for some $v \in \overline{B_\pi(0)}$.

2. **$\exp_p$ is a covering map**: Restrict $\exp_p$ to the open ball $B_\pi(0)$. $\exp_p|_{B_\pi(0)}$ is a local diffeomorphism (H4.4). Since $M$ is compact, $\exp_p$ is a proper map when restricted to any closed subset of $T_p M$. A proper local homeomorphism between connected manifolds is a covering map (this is a standard topological lemma — Mathlib may have this; otherwise ~200 lines to prove). Composing with the diffeomorphism $B_\pi(0) \cong \mathbb{R}^n$, we obtain a covering map $\mathbb{R}^n \to M$.

3. **Simply connected $\Rightarrow$ diffeomorphism**: Since $M$ is simply connected and $\exp_p|_{B_\pi(0)}$ is a covering map, it is a diffeomorphism. The open ball $B_\pi(0) \subset \mathbb{R}^n$ is diffeomorphic to $\mathbb{R}^n$, and $\mathbb{R}^n$ with one point compactified is $S^n$. The constant curvature condition ensures the metric extends smoothly to the added point, giving a diffeomorphism $M \cong S^n$.

**Alternative simpler endpoint** (no covering space argument needed): Since we already know from Phase H3 that the normalized Ricci flow converges to a metric with constant positive curvature, and the flow is a smooth 1-parameter family of metrics on the **same** manifold $M$, the topology of $M$ doesn't change. What we need is to identify the limit manifold $(M, g_\infty)$ with $S^3$. A standard theorem in Riemannian geometry states that a complete simply connected manifold of constant positive curvature is isometric to the round sphere — this is the **Killing-Hopf theorem** (or more precisely, the special case for positive curvature, also known as the classification of spherical space forms). Rather than proving the full Killing-Hopf theorem in generality, we scope H4 to exactly what is needed:

> If $(M, g)$ is a closed simply connected Riemannian manifold with constant sectional curvature $K > 0$, then $M$ is diffeomorphic to $S^n$.

This can be proved without the full Hopf-Rinow theorem: by compactness, $M$ is complete as a metric space; the exponential map $\exp_p : T_p M \to M$ is defined everywhere (geodesics extend indefinitely since $M$ is compact and geodesics cannot escape a compact manifold without boundary). The conjugate point analysis (H4.3–H4.4) shows $\exp_p$ is a local diffeomorphism on $B_{\pi/\sqrt{K}}(0)$. Using the constant curvature structure, one shows $\exp_p(B_{\pi/\sqrt{K}}(0)) = M$ and the map is injective (by a monodromy argument using simply connectedness). Hence $M$ is diffeomorphic to the open ball with its boundary identified to a point, which is $S^n$.

**Line estimate**: ~2800 lines (geodesic spray + geodesics ~800, exponential map ~600, const-curvature Jacobi fields ~400, conjugate points ~500, sphere recognition ~500).

### Phase H5 — Final Assembly

**Prerequisites**: Phase H1–H4, Phase 8 (M8: Ricci flow short-time existence).

**Output**: `Hamilton/PositiveRicci.lean` — the final theorem.

**Mathematical content**: Assemble the chain:

1. Start with a closed simply connected 3-manifold $(M, g_0)$ with $Ric(g_0) > 0$.
2. Phase 8: Ricci flow $g(t)$ exists for $t \in [0, T_{\max})$.
3. Phase H1: $Ric(g(t)) > 0$ for all $t \in [0, T_{\max})$.
4. Phase H2: $R_{\max}(t) \to \infty$ as $t \nearrow T_{\max} < \infty$ (finite-time singularity).
5. Phase H3: The normalized flow $\tilde{g}(\tilde{t})$ exists for all $\tilde{t} \in [0, \infty)$.
6. Phase H3: $\tilde{g}(\tilde{t}) \to g_\infty$ smoothly, with $Rc(g_\infty) = c \cdot g_\infty$, $c > 0$.
7. Phase H3 (ConstantCurvature): In 3D, this implies $g_\infty$ has constant positive sectional curvature.
8. Phase H4: A closed simply connected manifold with constant positive curvature is diffeomorphic to $S^3$.
9. Since $M$ carries the metric $g_\infty$, $M$ is diffeomorphic to $S^3$.

```lean
theorem hamilton_positive_ricci_three_sphere
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H)
    (M : Type*) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [CompactSpace M] [I.Boundaryless] [SimplyConnectedSpace M]
    (h_dim : FiniteDimensional.finrank ℝ (TangentSpace I : M → Type _) = 3)
    (g_0 : RiemannianMetric I ∞ M)
    (h_ric_pos : ∀ x, posDef (RicciCurvature g_0 x)) :
    ∃ (φ : M ≃ₜ^∞⟮I, 𝓡 3; 𝓡 3, 𝓡 3⟯ Sphere (Fin 4)), True := ...
```

where `posDef` means the symmetric bilinear form `Ric(x)` is positive-definite at every point, and `≃ₜ^∞` denotes a smooth diffeomorphism.

**Line estimate**: ~400 lines (orchestrating the assembly of theorems from H1–H4 and Phase 8).

---

## Phase 9 — Integrated Evolution Identities

Synthetic gives pointwise `∂_t R`, `∂_t(Δu)`, `∂_t Rm`. This phase integrates.

> **Phase 9 with-boundary mandate**: integrated evolution identities on closed manifolds use Phase 3's `∫div = 0`. On manifolds-with-boundary, the analogous identities carry a **boundary integral correction** (via Stokes from Phase 3 with-boundary). Specifically:
> - `d/dt ∫_M R dV_g = -∫_M R² + 2 ∫_M |Rc|² + (boundary correction term)`.
> - The boundary correction depends on the choice of metric-flow boundary condition (a Phase 8 with-boundary issue, deferred). For the *generic* with-boundary integrated identity (no specific b.c. on $g_{\mathrm{fam}}$), the boundary correction is expressed via `boundaryFaceSum` of the relevant flux vector. Files in `Integral/Evolution/WithBoundary/`.

### 9.1 Integrated scalar curvature (`Integral/Evolution/ScalarCurvature.lean`)

From `scalar_curvature_evolution` + volume variation (1.5) + Phase 3 IBP (contracted second Bianchi): `d/dt ∫ R dV = -∫ R² dV + 2 ∫ |Rc|² dV` and friends.

### 9.2 Integrated Riemann-norm (`Integral/Evolution/RiemannNorm.lean`)

`d/dt ∫ |Rm|² dV = ...` (boundary terms vanish on closed M).

### 9.3 Note

Building blocks of Perelman-era arguments. Nothing genuinely new — just integrated forms of Synthetic pointwise identities.

---

## Phase 10 — Bakry–Émery Γ-Calculus

Abstract the structure Synthetic's Weitzenböck already provides pointwise, so Perelman F/W drop out as integrated Γ_2 inequalities.

> **Phase 10 with-boundary mandate**: Γ-calculus on manifolds-with-boundary uses the Neumann Laplacian $\Delta_g^N$ as the natural choice (the Dirichlet version has subtleties around the Reilly identity). The orchestrator delivers boundaryless first, then Neumann with-boundary. Spacetime version (10.3) carries boundary terms that propagate to Phase 12–13 Perelman F/W with-boundary. Files in `Integral/BakryEmery/WithBoundary/`.

### 10.1 Γ, Γ_2 (`Integral/BakryEmery/Gamma.lean`, `Gamma2.lean`)

```
Γ(f, g)   := ½(Δ(fg) - f Δg - g Δf)       -- = ⟨∇f, ∇g⟩ identically (theorem)
Γ_2(f, g) := ½(Δ Γ(f,g) - Γ(f, Δg) - Γ(Δf, g))
```

Key identity (**from Synthetic's `bochner_pointwise`, not a new proof**):
```
Γ_2(f, f) = |∇²f|² + Rc(∇f, ∇f).
```

### 10.2 Curvature-dimension (`Integral/BakryEmery/CurvatureDim.lean`)

```lean
def IsCD (K : ℝ) (N : ℝ≥0∞) : Prop :=
  ∀ f ∈ C^∞(M, ℝ), Γ_2 f f ≥ K • Γ f f + (Δ f)^2 / N
```

Theorems on closed M:
- `Rc ≥ K · g ∧ dim M ≤ N ⇒ IsCD K N` (from 10.1 + algebraic Cauchy-Schwarz on `|∇²f|² ≥ (Δf)²/dim`).
- Under RF, `K = K(t)` tracks with `inf Rc(t)/g(t)`.

### 10.3 Spacetime version (`Integral/BakryEmery/Spacetime.lean`)

Time-dependent Γ_2 for `(g(t), f(t))` with Bakry–Émery Ricci `Rc_f := Rc + Hess f`. This is the direct input to Perelman F/W monotonicity.

### 10.4 Risks

Static framework is algebra + Synthetic identity — low risk. Spacetime version's mixed `∂_t`-and-`Δ` terms need careful bookkeeping but reuse Synthetic's `TimeJointSmoothness` + `TimeNabla`.

---

## Phase 11 — Log-Sobolev

> **Phase 11 with-boundary mandate**: log-Sobolev inequality on a manifold-with-boundary holds for the Neumann Laplacian under CD(K, ∞). The orchestrator delivers boundaryless first, then with-boundary via Phase 10 Neumann CD condition. Files in `Analysis/HarmonicAnalysis/WithBoundary/`.

### 11.1 Euclidean (`Analysis/HarmonicAnalysis/EuclideanLogSobolev.lean`)

Gross's log-Sobolev inequality on `ℝⁿ`:
```
∫ |f|² log(|f|²/‖f‖²) ≤ (2/π) ∫ |∇f|²     (up to normalisation)
```
Route: Fourier + heat semigroup hypercontractivity, or direct entropy-dissipation. Independent of the rest of this plan.

### 11.2 Manifold (`Analysis/HarmonicAnalysis/ManifoldLogSobolev.lean`)

**Corollary of Phase 10**: `IsCD K ∞` on closed M with `K > 0` ⇒ log-Sobolev with constant `1/K`. This is the Bakry–Émery consequence; nearly free once Phase 10 is in hand.

For `K = 0` or negative we use the Euclidean version on small geodesic balls + compactness.

---

## Phase 12 — Perelman F Functional

Now thin because of Phase 10.

> **Phase 12 with-boundary status**: Perelman F functional and its monotonicity are TIED TO Ricci flow. Since Ricci-flow-with-boundary is out of scope (Phase 8 note), Perelman F-with-boundary is also out of scope as an immediate Task. However, the **F functional itself** (definition, gradient flow interpretation, $\Gamma_2$ identity) extends naturally to manifold-with-boundary using the Phase 10 Neumann Γ-calculus + Phase 9 with-boundary integrated identities. The orchestrator should deliver the **STATIC** definitions and properties (no flow) in `Perelman/WithBoundary/F.lean`, but skip dynamic monotonicity (waits for Ricci-flow-with-boundary).

### 12.1 Definition (`Perelman/F.lean`)

```lean
noncomputable def perelmanF (g : RiemannianMetric I ∞ M) (f : C^∞(M, ℝ)) : ℝ :=
  ∫ x, (scalarCurvature g x + ‖grad g f x‖²_g) * Real.exp (-f x) ∂(μ_g)
```

### 12.2 Monotonicity (`Perelman/FMonotone.lean`)

Under coupled flow `∂_t g = -2(Rc + Hess f)`, `∂_t f = -Δf - R`:

**Theorem**: `dF/dt = 2 ∫ |Rc + Hess f|² e^{-f} dV_g ≥ 0`, with equality iff gradient Ricci soliton.

**Proof**: Direct from Phase 10.3 Γ_2-spacetime identity + `bochner_pointwise` + Phase 3 IBP + Phase 9.1 integrated `∂_t R`. This is where the Bakry-Émery abstraction pays off: the integrand is manifestly `Γ_2^{Rc_f}(f, f)`.

### 12.3 Diffeomorphism invariance

Via Synthetic Lie-derivative identities + Mathlib `MeasurePreserving` for diffeomorphism pullback.

---

## Phase 13 — Perelman W Entropy

> **Phase 13 with-boundary status**: same as Phase 12 — static definitions of W in `Perelman/WithBoundary/W.lean` (no dynamic monotonicity until Ricci-flow-with-boundary is in scope).

### 13.1 Definition (`Perelman/W.lean`)

```
W(g, f, τ) = ∫_M [τ(R + |∇f|²) + f - n] · (4πτ)^{-n/2} e^{-f} dV_g
```
with constraint `∫ (4πτ)^{-n/2} e^{-f} dV = 1`.

### 13.2 Monotonicity (`Perelman/WMonotone.lean`)

Under coupled flow, `dW/dτ = 2 ∫ τ |Rc + Hess f - (1/2τ) g|² · (4πτ)^{-n/2} e^{-f} dV ≥ 0`. Same Γ_2-spacetime machine as 12.2 with explicit τ scale.

### 13.3 μ-invariant

`μ(g, τ) := inf W(g, ·, τ)`. Finite and non-decreasing in t under Ricci flow.

---

## Phase 14 — Reduced Length & Volume

Perelman's ℒ-length and reduced length ℓ. ODE / calculus of variations on path spaces. Rellich-type compactness for minimisers.

---

## Phase 15 — κ-Non-Collapsing

**Theorem** (Perelman): Any solution of Ricci flow on a closed manifold is κ-non-collapsed on all scales for some κ > 0.

**Proof input**: W-monotonicity (Phase 13) + reduced-length asymptotics (Phase 14).

---

## Phase 16 and Beyond — Singularity Analysis, Surgery, Geometrization

| Phase | Content | Difficulty |
|-------|---------|-----------|
| 16 | Type-I singularity models via κ-non-collapsing + Hamilton compactness | very hard |
| 17 | Canonical neighbourhoods theorem | very hard |
| 18 | Standard solutions, ε-necks, horn decomposition | very hard |
| 19 | Ricci flow with surgery | mountain |
| 20 | Geometrization + Poincaré | mountain-peak |

Out of scope as detailed planning.

---

## Optional / Stretch

- **Riesz transforms** `R_j := ∇_j (-Δ)^{-1/2}` and their `L^p` boundedness. Independent of the main line; needs Calderón–Zygmund theory on `M` which Mathlib lacks. Significant harmonic-analysis value but no Poincaré dependency. `Analysis/HarmonicAnalysis/Riesz.lean`.
- **Li–Yau gradient estimate** `|∇u|²/u² - (∂_t u)/u ≤ n/(2t)` on `(M, g)` with `Rc ≥ 0`. Derivable from Synthetic's pointwise Bochner + max principle + heat smoothing. Independent side-theorem. `Analysis/HarmonicAnalysis/LiYau.lean`.
- **Gaussian heat-kernel estimates**. Follow from Bakry–Émery CD(K,∞) + Li–Yau. Phase 10+C composition.

---

## Milestones

The boundaryless track milestones (M1–M15) are the route to the Poincaré endpoint. The with-boundary parallel tracks each Phase 3+ milestone with a corresponding `M*-WB` milestone, delivered alongside.

| Milestone | Phase | Boundaryless | With-boundary parallel |
|---|---|---|---|
| M1: `μ_g : Measure M` built + invariant | 1 | ✅ shipped | (boundary-agnostic; same file) |
| M2: ∫ div X = 0 on closed M | 3 | ✅ shipped | ✅ M2-WB shipped (`integral_divergence_with_boundary_eq_zero_*`, `stokes_compact_via_pou`) |
| M3: Sobolev `W^{k,p}(M)` with DeGiorgi import | 4 | ✅ shipped | M3-WB shipped (with-boundary Sobolev + boundary trace) |
| M4: Δ spectral decomposition complete | 5 | pending | M4-WB pending (Dirichlet + Neumann Laplacians) |
| M5: Lichnerowicz `λ_1 ≥ nK` | 5.7 | pending | M5-WB pending (Reilly identity, Dirichlet/Neumann variants) |
| M6: Heat semigroup `e^{tΔ}` built | 6 | pending | M6-WB pending (Dirichlet + Neumann semigroups) |
| M7: Linear & quasi-linear parabolic existence | 7 | pending | M7-WB pending (Dirichlet + Neumann variants) |
| **M8: Ricci flow short-time exists ⇒ Synthetic axiom-free** | 8 | pending | M8-WB DEFERRED (Ricci-flow-with-boundary is research-grade; out of M8 scope) |
| **MH1: Tensor max principle ⇒ Ric > 0 preserved under RF** | H1 | pending | (boundaryless only; Hamilton path) |
| **MH2: Pinching estimates ⇒ finite-time singularity for Ric > 0** | H2 | pending | (boundaryless only; dimension 3 specialized) |
| **MH3: Normalized RF long-time + convergence to Einstein** | H3 | pending | (boundaryless only; requires Shi estimates) |
| **MH4: Sphere recognition ⇒ constant K>0 ∧ π₁=0 ⇒ S³** | H4 | pending | (boundaryless only; requires exponential map + Jacobi fields) |
| **MH5: Hamilton's theorem: Ric>0 closed 3-manifold with π₁=0 ⇒ S³** | H5 | pending | (boundaryless only; assembles M8 + MH1–MH4) |
| M9: integrated Ricci flow evolution identities | 9 | pending | M9-WB partial (boundary correction terms via Stokes) |
| M10: Bakry–Émery Γ-calculus + CD(K, N) | 10 | pending | M10-WB pending (Neumann Γ-calculus) |
| M11: Log-Sobolev (Euclidean + manifold via CD) | 11 | pending | M11-WB pending (via Neumann CD) |
| M12: Perelman F monotonicity | 12 | pending | M12-WB partial (static definitions only; dynamic awaits Ricci-flow-with-boundary) |
| M13: Perelman W entropy monotonicity | 13 | pending | M13-WB partial (same as M12-WB) |
| M14: reduced length infrastructure | 14 | pending | (out of scope as immediate Task) |
| M15: κ-non-collapsing theorem | 15 | pending | (out of scope) |
| M16+: singularity analysis → surgery → Poincaré | 16–20 | far future | (out of scope) |

---

## Risk Register

| Risk | Probability | Impact | Mitigation |
|------|-------------|--------|------------|
| DeGiorgi repo Lean-version drift | medium | high | pin to specific commit; fork if needed |
| POU glue measure: chart-invariance calculus error | high | high | isolate to standalone Euclidean lemma |
| `IsSelfAdjoint` unbounded missing in Mathlib | medium | medium | work with `(Δ+1)⁻¹` resolvent throughout |
| Infinite-dim compact-s.a. orthonormal basis needs assembly | certain | medium | Phase 5.5 explicit assembly plan |
| `StronglyContinuousSemigroup` missing | high | medium | thin wrapper |
| Tensor-valued parabolic Lipschitz constants | medium | high | compactness + Synthetic commutators |
| Principal symbol computation for Ricci+DeTurck | low | high | patient direct calculation |
| ODE gauge (Phase 8.4) time-dependent vector field on manifold | low | medium | reduce to time-independent on M×ℝ; Mathlib integral curves already exist |
| Euclidean log-Sobolev proof route | low | medium | Gross's classical proof is standard |
| --- | --- | --- | --- |
| **Hamilton Path specific** | | | |
| Tensor max principle: convex cone preservation on vector bundles | medium | high | reduce to scalar max principle via supporting linear functionals |
| Pinching estimate: 3D algebraic identity for Rm via Rc | medium | high | isolate as standalone algebraic lemma; test on standard 3D examples |
| Pinching estimate: eigenvalue crossing singularities | medium | medium | avoid differentiating eigenvalues directly; work with |Ric₀|² instead |
| Shi estimates: ∇Δ commutator induction for k-th derivative | high | high | Synthetic RiemannLaplacian + Bochner provide commutator identities; careful induction bookkeeping |
| Geodesic spray: chart-invariance of Christoffel symbol expression | high | high | Mathlib CovariantDerivative API provides Christoffel transformation; isolate chart-invariance lemma |
| Jacobi fields: from general R(H,γ̇)γ̇ to scalar ODE for K=const | medium | medium | constant curvature specialization is much simpler; J''+KJ=0 solved by sin/cos |
| exp_p covering map: proper local homeomorphism argument | medium | medium | Mathlib has covering space theory; may need "proper local homeo ⇒ covering map" lemma |
| Killing-Hopf vs sphere recognition scope | medium | medium | restrict to what Hamilton needs: constant K>0 + simply connected ⇒ S^n |

---

## Immediate Next Actions

Phases 1–3 (boundaryless and with-boundary tracks) are SHIPPED. Phase 4 (Sobolev) is largely complete (~36K lines, 0 sorrys). The next actions for the M8 endpoint:

1. **Phase 5 (Laplacian)** — boundaryless variational construction, then Dirichlet and Neumann with-boundary parallels. The orchestrator splits the with-boundary work autonomously into Dirichlet + Neumann × {Def, Resolvent, Spectrum, EllipticRegularity, Lichnerowicz/Reilly} substeps.
2. **Phase 6 (Heat semigroup)** — spectral construction from Phase 5 spectrum.
3. **Phase 7 (Parabolic)** — linear + quasi-linear existence.
4. **Phase 8 (DeTurck + Ricci short-time)** — M8 MILESTONE, closes the last Synthetic axiom.

After M8, the **Hamilton Positive Ricci path** (Phases H1–H5) becomes available as a shorter alternative to the full Perelman path. The orchestrator may begin H1 (Tensor Maximum Principle) immediately after M8, reusing the scalar parabolic max principle (Phase 6.4) and the Synthetic Ricci evolution identities.

The **Perelman path** (Phases 9–15) remains available as the long-term route to the full Geometrization conjecture.
