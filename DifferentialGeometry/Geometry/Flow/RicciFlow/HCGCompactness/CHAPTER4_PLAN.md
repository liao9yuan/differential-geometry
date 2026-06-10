# MSM135 Chapter 4 (Theorem 3.9 / `metricCompactness`) — book-faithful backlog

**Rule:** one Lean declaration per book result, in book order. Honest-input fields
ONLY where the book itself cites an external theorem (so far: `lbl384`, the Rauch
comparison inside `lbl387`, the Hessian comparison `lbl413`). Everything the book
proves, we prove. Each task is sized for one short codex iteration: it must build via
`& .\scripts\lake-locked.ps1 build +<Module>` (run from `E:\differential-geometry`),
contain no Lean proof holes, admissions, or axiomatic constants, and (for real
theorems) be `#print axioms`-clean.

**Splitting discipline:** if a task would need a NEW infrastructure/calculus layer or
more than ~3–4 sub-lemmas / 2 nesting levels, STOP and report for re-scoping rather
than recursing. (The earlier F3 micro-split to `F3e1b10` is the anti-pattern.)

Legend: `[x]` done & verified · `[~]` honest-input field (book-external) · `[ ]` todo.
Each line: `ID — book label/title → Lean deliverable ⟸ deps`.

---

## §1 Foundations (abstract; no geometry black-boxes; all parallelizable)

- [x] F1-def — Def *Approximate isometry* book-facing data
      → `PullbackMetricTensorData`, `PreApproxIsometryData`, `BookApproxIsometryData`
      (ApproximateIsometry.lean)
- [x] F1-metric — same-domain supplied-pullback metric comparison support
      → `IsApproxIsometryOn`, `IsTwoSidedApproxIsometryOn`,
      `normSq0S_compare_of_approxIsometry`, `normSqRS_compare_of_approxIsometry`
      (ApproximateIsometry.lean / Comparison.lean)
- [x] F1-c0 — Prop *Approximate isometries and norms* (vector metric comparison):
      from `PreApproxIsometryData` prove the `C^0` tangent/quadratic-form bound
      and package it as same-domain `MetricUniformEquivalentOn` when the
      pullback tensor is supplied as a Riemannian metric
      → `preApprox_quad_error_abs_le`, `preApprox_quad_upper`,
      `bookApprox_quad_twoSided`, `bookApprox_uniformEquiv_of_pullback`
      (ApproximateIsometry.lean).
- [x] F1 — Cor *Norms of tensors* in book-facing map form:
      derive tensor norm comparison for `Phi^* h` from F1-c0 and F1-metric
      → `bookNormRS_compare` (ApproximateIsometry.lean).
- [x] F2 — Prop *Distances*, path-speed form → derive the path-length comparison from
      a target-path producer with pointwise Riemannian speed comparison
      → `pathComp_tangent`, `dist_le_tangent`, `image_ball_tangent`
      (Distances.lean) ⟸ F1-c0,F2c
- [ ] F2-book — Prop *Distances*, book-facing pre-approximate-isometry form:
      from `PreApproxIsometryData` plus the supplied pullback-metric and
      typeclass-Riemannian norm compatibility, produce the path-speed hypothesis
      consumed by `image_ball_tangent`; do not invent a pullback metric
      constructor (Distances.lean / ApproximateIsometry.lean) ⟸ F1-c0,F2
- [x] F2c — Prop *Distances* length-infimum bridge from Riemannian path-length
      comparison to pointwise distance and ball inclusion → `edist_le_of_path_comp`,
      `dist_le_of_path_comp`, `image_ball_subset_of_path_comp` (Distances.lean) ⟸ F2b
- [x] F2b — Prop *Distances* package pointwise distance estimate as Lipschitz
      → `lipschitz_sqrt_of_dist_le` (Distances.lean) ⟸ F1-metric
- [x] F2a — Prop *Distances* final ball-inclusion step from the Lipschitz estimate
      → `image_ball_subset_of_lipschitz_sqrt` (Distances.lean) ⟸ F1-metric

### F3 / F4 — Lemma *Norms of covariant derivatives of tensors, I* + Cor II

**Audit status (2026-06-02):** the old finite-product/DC3 route was removed from
`ApproximateIsometry.lean` and from this active backlog.  Checked facts stay here
only when they prove a reusable tensor/coordinate theorem or a book-facing F3
endpoint.  Conditional scaffolding of the form "if a future Christoffel product
expansion exists, then packaging works" is not counted as progress.

- [x] F3-norm — RS norm + comparison: `innerRS`/`normSqRS`, `normRS`/`fieldNormRS`,
      `normSqRS_le_of_metric_equiv`, and the HCG wrappers
      `IsApproxIsometryOn.normSqRS_compare` / `normSqRS_compare_of_approxIsometry`
      (TensorRSRiemannian.lean; ApproximateIsometry.lean) ⟸ F1-metric
- [x] F3-conn — `lbl369` connection-difference base estimate and action formulas:
      `connDiff_le_approx`, `connDiff_book_le_approx`, `connDiff_book_le_eps_g`,
      `covDerivRS_sub_apply`, `localCovDeriv0S_sub`, `nablaRSFun_sub_raw`,
      `connActComp`, and `connAct_le_approx`
      (Model/TensorRS.lean; Regularity/Derivation.lean;
      ConnectionDifferenceAction.lean; ApproximateIsometry.lean) ⟸ F1-metric,F3-norm
- [x] F3-p1 — checked order-one tensor-derivative comparison support:
      `nablaRS_component_le_approx`, `nablaRS_norm_le_approx_comps`,
      `metricSubRS`, `nablaRSOneError_of_comps`, `nablaRS_one_le_approx_comps`
      and the component equality wrapper
      `nabla_component_eq_base_plus_connAct_components_trivFrame`
      (ApproximateIsometry.lean) ⟸ F3-norm,F3-conn
- [x] F3-r1 — book-facing first-order case of *Norms of covariant derivatives
      of tensors, I*: the estimate for `|nabla_g T|_g` in terms of
      `|nabla_h T|_g` and the zero-order `|Gamma_g - Gamma_h|_g <= C eps`
      bound.  This is the `r = 1` case and does not use
      `nabla_h (Gamma_g - Gamma_h)`.
      → `hcg_first_order_nabla_norm_estimate` (ApproximateIsometry.lean)
      ⟸ F3-p1,F3-hi-zero
- [x] F3-hi-shape — book-facing higher connection-difference target vocabulary:
      `metricCovDerivNormWith`, `IsTwoSidedApproxIsometryOn`,
      `ConnDiffFieldRealizes`, `connDiffDerivNorm`, `ConnDiffDerivRealizes`,
      `ConnDiffDerivBoundOn`, `ConnDiffEpsBoundOn`, `ConnDiffEpsBoundsBelow`
      (ApproximateIsometry.lean) ⟸ F3-p1
- [x] F3-hi-zero — checked `k = 0` book-facing bound:
      `connDiffDerivBound_zero`, `connDiffEpsBound_zero`
      (ApproximateIsometry.lean) ⟸ F3-hi-shape,F3-conn
- [x] DC1 — reusable coordinate theorem, not an F3 milestone by itself:
      Christoffel-difference component equation
      `lcDiffBasis_symm`, `lcDiff_symm`, `covMetric_lcDiff`, `lcDiff_combo`,
      `lcDiffComp_eq`, plus `lcDiffCompInFrame` / `lcDiffCompInFrame_eq_component`
      (Coordinates/ChristoffelTensor.lean)
- [x] DC2 — reusable coordinate theorem, not an F3 milestone by itself:
      inverse-metric covariant derivative support
      `metricCovDerivForMetricCompInFrame`, `metricCovDeriv2ForMetricCompInFrame`,
      `invDeriv_solve`, `invMetricCovDeriv_eq`
      (Coordinates/MetricCompatibility/Covariant.lean)
- [x] DC1-deriv - reusable coordinate producer for the first derivative of the
      Christoffel-difference equation:
      `lcDiffCovDerivCompInFrame`, `lcDiffSymMetricCovComp`,
      `lcDiffCovDerivRHS`, `lcDiffCompInFrame_extDeriv_eq`,
      `lcDiffSymMetricCovComp_extDeriv_eq`,
      `lcDiffCovDerivCompInFrame_eq`
      (Coordinates/ChristoffelTensor.lean) after DC1,DC2
- [x] DC1-deriv-quad - substituted first-derivative Christoffel-difference
      producer with only `nabla_h^2 g` and quadratic `(nabla_h g)^2` terms:
      `lcDiffQuadRHS`, `lcDiffRHS_eq_quad`, `lcDiffDeriv_eq_quad`
      (Coordinates/ChristoffelTensor.lean) after DC1-deriv,DC2
- [x] F3-realize-move - realization-level moving-slot component bridge:
      `TotalNablaRSRealizes.eval_moving_slots`,
      `TotalNablaRSRealizes.component_moving_slots`
      (Tensor/RSTensor/NablaOnTensors/HigherOrder.lean).  This is support for
      reading a realized total mixed covariant derivative in local-frame
      components; it does not by itself prove the connection-difference
      epsilon estimate.
- [x] F3-coframe0 - static local coframe basis bridge:
      `coframe_eq_basis0S`
      (Coordinates/Tensor.lean).  This identifies the local-frame coframe
      covector with the one-slot tensor basis at a point; the derivative of
      this coframe field remains the active missing producer.
- [x] F3-coframe1 - local coframe derivative/contraction producer:
      `nabla0SFun_one_eval_of_pair_eventually_const`,
      `nabla0SFun_one_eval_localFrame_dual`,
      `localCovariantDerivTensor0SAt_one_eval_of_pair_eventually_const`,
      `localCovariantDerivTensor0SAt_one_eval_localFrame_dual`
      (Coordinates/NablaComponents/OneForm/Smoothness.lean).  This proves the
      checked local-frame formula `(nabla_X theta^i)(e_j) = -Gamma^i_j(X)` in
      both bundled and unbundled forms; the remaining task is to feed it into
      the mixed moving-slot bridge, not to add another coframe assumption.
- [x] F3-coframe1-expansion - full coframe derivative basis expansion:
      `localCovariantDerivTensor0SAt_one_localFrame_dual_eq`
      (Coordinates/NablaComponents/OneForm/Smoothness.lean).  This packages
      `(nabla_X theta^i) = -sum_p Gamma^i_p(X) theta^p` as a one-form equality.
- [x] F3-lcDiff-corrections - local-frame moving-slot correction terms:
      `lcDiffUpperCorr`, `lcDiffLowerCorr0`, `lcDiffLowerCorr1`
      (Coordinates/ChristoffelTensor.lean).  These are the three correction
      terms needed by `TotalNablaRSRealizes.component_moving_slots` before the
      local-frame component bridge can be assembled.

The abandoned HCG-side finite-product and differentiated-Christoffel route
scaffolding was removed from the active plan and from `ApproximateIsometry.lean`.
Some low-level tensor algebra used while exploring that route remains in the
tensor layer because it is independently meaningful, but it is no longer
advertised as F3 progress.

**Close-F3 route (2026-06-02, after `Tensor0SSpace.rs0Equiv`):**

Use natural equivalences for zero-upper-slot tensors.  In particular, covariant
special cases must pass through `Tensor0SModel.rs0Equiv` /
`Tensor0SSpace.rs0Equiv`, with `toRS0` retained only as the forward
compatibility/application map.  Do not introduce fresh ad hoc wrappers for
`TensorRSSpace 0 s`.

The book proof of *Norms of covariant derivatives of tensors, I* has two
genuinely separate pieces:

1. **Connection-difference epsilon producers.**  For a full approximate
   isometry on the same supplied pullback domain, prove
   `ConnDiffEpsBoundsBelow K eps g h (p+1) C`, i.e.
   `|nabla_h^k (Gamma_g - Gamma_h)|_g <= C_k * eps` for `k <= p`.
   The checked `k = 0` producer is `connDiffEpsBound_zero`.  For `k = 1`,
   use DC1/DC2 to prove the differentiated Christoffel-difference bound
   schematically
   `|nabla_h D| <= C (|nabla_h^2 g| + |nabla_h g|^2)`, then use
   `IsTwoSidedApproxIsometryOn`, norm comparison, and `eps < 1` to convert it
   to `C * eps`.  For `k >= 2`, first introduce a reusable tensor/finite-sum
   polynomial-control lemma: every monomial in the differentiated Christoffel
   formula contains at least one positive derivative of `g`, so the approximate
   isometry derivative bounds make the monomial `O(eps)`.

2. **Book induction for *Norms of covariant derivatives of tensors, I*.**
   Once the connection-difference epsilon producers are available, prove the
   actual F3 induction separately.  The checked `r = 1` / one-total-derivative
   case is `hcg_first_order_nabla_norm_estimate` (wrapping
   `nablaRS_one_le_approx_total`); it consumes only `T`, supplied
   realizations of `nabla_h T` and `nabla_g T`, and the zero-order
   connection-difference epsilon bound.  Do not reintroduce the abandoned
   auxiliary `S = (Gamma_g-Gamma_h) * T` wrapper as a public route.  Higher
   steps should use the book recurrence plus `ConnDiffEpsBoundsBelow`, not a
   new consumer-side realization package.

This is the replacement for the old DC3/product-control route: DC1/DC2 are
allowed only as producers for the connection-difference epsilon estimates, not
as public F3 milestones.  The public F3 endpoint remains the book inequality
from *Norms of covariant derivatives of tensors, I*.

- [x] F3-hi-k1-assembly — assembled the checked coframe and lower-slot
      correction terms with `TotalNablaRSRealizes.component_moving_slots` to
      identify a realized first `h`-covariant derivative of
      `Gamma_g - Gamma_h` with the local-frame component formula
      → `totalNabla_lcDiff_localFrame` (ChristoffelTensor.lean),
        `connDiffOne_localFrame` (ApproximateIsometry.lean).
- [x] F3-hi-k1-norm — first positive-order connection-difference support:
      closed the public `ConnDiffEpsBoundOn K eps g h 1 C` endpoint and the
      below-two package, with no frame data exposed to callers
      → `connDiffEpsBound_one`, `connDiffEpsBound_zero_std`,
        `connDiffEpsConst_two`, `connDiffEpsBounds_two`
        (ApproximateIsometry.lean).
- [x] F3-p1-total-support — checked one-total-derivative estimate for supplied
      `TotalNablaRSRealizes` data, using the zero-order connection-difference
      bound and the tensor-layer connection-action identity
      → `nablaRS_one_le_approx_total` (ApproximateIsometry.lean).
- [x] F3-action-anti0 — antidiagonal `k = 0` component and norm-bound alignment
      for the connection-action identity
      → `totalNablaSub_anti0`, `totalNablaAnti0`
      (ConnectionDifferenceActionIdentity.lean).
- [x] F3-components-reconstruct — reusable mixed-tensor reconstruction from
      full `componentRS` coordinate tables, avoiding the failed Hom-basis
      transport route
      → `ofComponentsRS`, `componentRS_ofComponentsRS` (Components.lean).
- [x] F3-action-tensors — actual mixed tensors for the connection-action
      component formula and its antidiagonal Leibniz-sum component formula
      → `connActTensorAt`, `connActTensorAt_comp`,
        `connActAntiTensorAt`, `connActAntiTensorAt_comp`
      (ConnectionDifferenceAction.lean).
- [x] F3-action-jets — higher-jet connection-action target tensor and norm
      algebra, with genuine increasing-valence inputs
      `A a : TensorRSSpace 1 (a+2)` and `T b : TensorRSSpace r (b+s)`
      → `connActJetComp`, `connActJetAt`, `connActJetAt_comp`,
        `connActJetNormConst`, `abs_connActJet_le`,
        `norm_connActJet_le`, `norm_connActJetAt_le`
      (ConnectionDifferenceAction.lean).
- [x] F3-action-tensor-eq — tensor-level form of the supplied total derivative
      connection-change identity
      → `totalNablaSub_eq_connActTensor`
      (ConnectionDifferenceActionIdentity.lean).
- [x] F3-action-cleanup — removed the abandoned `S` wrapper route from the
      active backlog and deleted `ConnectionDifferenceActionDerivative.lean`.
      The generally useful base action identity remains in
      `ConnectionDifferenceActionIdentity.lean`.
- [x] F3-hi-kge2-realization — realized order-two connection-difference
      component bridge:
      identify a realized `nabla_h^2 (Gamma_g - Gamma_h)` with the
      trivialization-frame component expression
      → `lcDiff2Comp`, `lcDiffOneComp_eventually`,
        `totalNabla_lcDiff2_trivFrame` (ChristoffelTensor.lean),
        `metricCov3_comp_le`, `ConnDiffDerivRealizes.two`,
        `connDiffTwo_trivFrame` (ApproximateIsometry.lean).
- [x] F3-hi-kge2-base — first higher-order connection-difference producer:
      proved the `k = 2` local norm estimate, schematically bounded by
      `|nabla_h^3 g|`, `|nabla_h^2 g| |nabla_h g|`, and `|nabla_h g|^3`,
      and packaged the public order-two epsilon endpoint plus below-three
      controls
      → `connDiffTwo_trivON`, `connDiffEpsBound_two`,
        `connDiffTwoConst`, `connDiffEpsConst_three`,
        `connDiffEpsBounds_three` (ApproximateIsometry.lean).
- [ ] F3-hi-kge2 — higher connection-difference derivative controls for
      `ConnDiffEpsBoundOn ... k C` with `2 <= k`, after the `k = 2` producer
      route is checked and generalized.
- [~] F3 — final inequality from *Norms of covariant derivatives of tensors, I*:
      `|∇_g^r T|_g <= |∇_h^r T|_g + eps*C*Σ_{k<r}|∇_h^k T|_g`.
      **Norm-level induction COMPLETE (2026-06-09): `lemma45ScalarBdd` + `lemma45Double`**
      (Lemma45CovariantAbstract.lean) — the book's double induction with `hLift`
      DISCHARGED (strong induction over the doubly-indexed family
      `W i k = |∇_h^k ∇_g^i T|`).  Remaining = the one-step interface `hOne`
      (`|∇_h^k ∇_g X| ≤ |∇_h^{k+1} X| + ε·oneStepConst·Σ`), i.e. Phases 4–6
      (action identity + iterated Leibniz) = the component contraction-Leibniz
      ENGINE — same engine as ric_bound Claim 1 (parallel track); per user decision
      (2026-06-09) F3 interfaces at `hOne` and waits for/adapts that engine, plus the
      Phase 9 `hA` input (`connDiffEpsBound_{zero,one,two}` are its k≤2 instances).
- [ ] F4 — Corollary *Norms of covariant derivatives of tensors, II*
      → covariant (`q₁=0`) per-order constants used downstream ⟸ F3
- [x] F5-const — constants for *Composition of approximate isometries, I*
      → `compApproxConst`, `compApproxConst_pos`, `compApproxConst_nonneg`
      (Lemma45Constants.lean) ⟸ F4 constants
- [~] F5 — Prop *Composition of approximate isometries, I*:
      **`C⁰` part DONE (2026-06-09)**: `metricInner_nonneg`, `metricEquiv_mono`,
      `metricEquiv_trans` (product constants), `metricEquiv_comp_eps` (the book's
      additive form, `(1+ε₀)(1+ε₁) ≤ 1+3(ε₀+ε₁)`) — ApproxIsometryComp.lean,
      sorry-free, axiom-clean.  Derivative (`C^p`) part = the Lemma 4.5 consumer
      (book applies `lbl370` to `T := Φ₁*g₂−g₁`) — gated on the `hOne` engine
      interface of `lemma45Double`, like F3/F4.
- [~] F6 — Cor *Composition of approximate isometries, II*:
      **scalar accumulation core DONE**: `compEpsAccum` (`e n ≤ C·Σ δᵢ` from
      per-step costs; ApproxIsometryComp.lean).  Full version ⟸ F5-full.
- **⚠ STATE (2026-06-09): `ApproximateIsometry.lean` is currently STALE-BROKEN**
  against the in-flight tensor-layer relocation (`Tensor0SBundle.normRS`,
  `abs_quad02_le_norm`, `normSqRS_le_of_metric_equiv`, `abs_component0S_le_sqrt_normSq0S`
  unknown — the parallel `ric_bound` track is moving these, cf. `RSLoweringNorm.lean`
  in its working set).  `ApproxIsometryComp.lean` deliberately imports
  `AllTimesBounds` (healthy) instead.  F4 (Cor `lbl370`) is BLOCKED on both this
  breakage (its inputs `bookNormRS_compare`/`normSqRS_compare` live there) and the
  F3 interface; revisit after the tensor relocation settles.
- [ ] F7 — Def *Cᵖ-convergence of maps* + Def *C^∞-conv. uniformly on compacts*
      → 2 defs (reconcile with existing `PointedConvergence` names) ⟸ —
- [x] F8tool — abstract sequential Arzelà–Ascoli (Lemma 3.14) → `arzelaAscoli_subseq_…` (ArzelaAscoli.lean)
- [ ] F8 — Cor *Compactness of sequence of isometries* (L537) → apply F8tool ⟸ F7, F8tool
- [x] F9 — Def *Direct limit* (L628) + Lemma *Iₗ injective* (L660) → `SeqSystem`, `Lim`,
      `incl`, `incl_comp`, `incl_injective`, `exists_incl_eq`
      (Geometry/Topology/DirectLimit.lean, 2026-06-09, sorry-free)
- [x] F10 — Lemma *open cover for the direct limit* (L679) → `incl_isOpenMap`,
      `incl_isOpenEmb`, `range_incl_mono`, `iUnion_range_incl` (DirectLimit.lean)
- [x] F11 — Cor `lbl379` *compact sets in the direct limit* → `isCompact_exists` (DirectLimit.lean)
- [x] F12 — Cor `lbl380` σ-compact direct limits → `sigmaCompact` (DirectLimit.lean;
      second-countability glue deferred to the manifold layer)
- [x] F13 — Lemma `lbl381` *direct limit of Hausdorff is Hausdorff* → `t2Space`
      (DirectLimit.lean; also the universal property `lift`/`continuous_lift`)

## §5 Supporting: distance / exp⁻¹ derivatives (needed by A-convexity and Step B)

**PARKED (2026-05-31): not now-doable.** S1 spike confirmed §5 is blocked on deep
GlobalGeometry `sorry`s — minimal geodesics (`HopfRinow.lean:119`, "not in Mathlib") and
the Gauss lemma (`GaussLemma.lean:687` / `SmoothRadialExp.lean:715`) — plus cut locus;
Mathlib has no cut-locus / Riemannian-gradient / exp API. Decision: leave §5 as-is and
merge external global-geometry code later (likely already has these), then revisit. The
A-convexity (`lbl417`) and Step C center-of-mass that depend on §5 wait on that merge
(or become honest-input then).

- [ ] S1 — Lemma `lbl411` *gradient of d²* → BLOCKED: Gauss lemma + minimal geodesics
      both `sorry`; the gradient itself exists (`gradientFun`) ⟸ §5 PARKED
- [ ] S2 — Lemma `lbl412` *Hessian of d²* ⟸ S1
- [~] S3 — Lemma `lbl413` *Hessian comparison* ⟸ S2  〔book-external comparison geom → honest-input〕
- [ ] S4 — Cor *local convexity of d²* ⟸ S3
- [ ] S5 — Cor `lbl417` *convexity of small enough balls* ⟸ S4
- [~] S6 — Prop `lbl418` *derivatives of exp⁻¹* → currently `ExpInverseDerivBoundInput` (3.4 honest-input);
      OPTIONAL later: prove from S1–S5 ⟸ S1–S5

## §2 Step A: good coverings (L783–1369)

- [~] A0 — Prop `lbl384` *Inj-radius decay* → `InjRadiusDecayInput` (GeometricInputs.lean)  〔external CGT/CLY〕
- [~] A0' — Rauch comparison / volume multiplicity → `VolumeComparisonInput` (GeometricInputs.lean)  〔external Cheeger–Ebin〕
- [ ] A1 — eq `lbl386` λ[r] → `lambdaRadius` + positive/antitone ⟸ A0
- [ ] A2 — net construction (L882–955) → greedy λ-separated net + pairwise `B(x^α,λ[r^α])` disjoint ⟸ A1
- [ ] A3 — Lemma `lbl387` *cover with ball-number bound* → doubled balls cover `B(O,r)`; PROVE net-maximality cover, A(r) bound from A0' ⟸ A1,A2,A0'
- [ ] A4 — Prop `lbl388` *good cover of a Riemannian manifold* ⟸ A3
- [ ] A5 — Prop `lbl389` *center-distance bounds* (`r_k^α ≤ 2αλ[0]`) ⟸ A2
- [ ] A6 — Cor *center-distance convergence* (subsequence) ⟸ A5
- [ ] A7 — Cor `lbl390` `K'(r)` ⟸ A3
- [ ] A8 — Def `lbl391` *various size balls* (B̃⊂B̂⊂B⊂B̄⊂B⃗) ⟸ A1
- [ ] A9 — Prop *disjointness of smaller & covering of larger* (L1170) ⟸ A8,A3
- [ ] A10 — Prop *index bound `I(α,n)`* (L1187, multiplicity) ⟸ A8,A0'
- [ ] A11 — Prop *stability of intersections* (L1216, subsequence) ⟸ A8–A10
- [ ] A12 — Def `K(r)` (L1251) ⟸ A7,A11
- [ ] A13 — Prop *nesting on intersection* (L1268, triangle ineq.) ⟸ A8,A12
- [ ] A14 — Lemma `lbl383` *Existence of good coverings* (ASSEMBLY of A1–A13) ⟸ A1–A13

## §3 Step B: local metrics & transition maps (L1370–1882)

- [ ] B0 — Prop (L1413) *|∇ᵉRm|≤Cₑ ⟹ |∂ᵐg|≤C̃ₘ in normal coords*.
      **AUDIT CORRECTION (2026-06-09): does NOT exist** — the old "[x] = Lemma 3.11
      (`MetricAllTimesConclusion`)" conflated it with the TIME-window AllTimesBounds
      machinery.  Spatial B0 is genuine remaining work (B1's main missing producer).
      Staged route + status: `B0NormalCoordBounds.md`.  Stage 1 (2nd-order Grönwall
      engine) DONE; stage 2 core DONE 2026-06-10: **`exists_radial_jacobi_radius`**
      (`Exponential/JacobiVariation.lean`, green) — the radial `expMap` variation
      field is Jacobi on `(0,1)`; used the de-privatized `commute_ds_dt_curvature`
      (the W=∂_t commutation EXISTED, was private/unused) + smooth clamps
      (`Analysis/Calculus/SmoothClamp.lean`).  Stage-2 tail (J(0)=0, D_tJ(0)=w,
      endpoint J(1)=d(exp)ₓw, g_{ij}=⟨J_i,J_j⟩(1)) + stages 3–5 remain.
- [x] B0' — smooth exponential local diffeo → native `Geometry.Riemannian.
      NormalCoordinates.expMapDiffeo`/`normalChartAt` (0-sorry).  NOTE: its source is
      *some* nhd of 0; widening to the λ-ball scale (`injRadius` gives only injectivity
      on the eball) = the `lbl383` item-3 frontier.
- S6 input rebuilt natively (2026-06-09): `StepBInputs.lean` (`normalTransition`,
  `NormalTransitionDerivBound`, `ExpInverseDerivBoundInput`); `GeometricInputs.lean`
  healed into a pure umbrella import (the dangling `NormalChartData` section removed).
- [ ] B1 — Prop `lbl397` *approx isometry on a large ball* ⟸ A14, S6/A0', B0', F1
- [ ] B2 — Prop `lbl399` *local maps → id* ⟸ B1
- [ ] B3 — Prop `lbl402` *F_{kℓ;r} → id* ⟸ B1,B2
- [ ] B4 — Cor `lbl403` *F_{kℓ;r} local diffeo* ⟸ B3
- [ ] B5 — Lemma `lbl404` *limit of almost-identity pullbacks* ⟸ F1–F6
- [ ] B6 — Lemma `lbl405` *F_{kℓ,r} is (ε,p)-pre-approx-isometry* ⟸ B1–B5, F1–F6

## §6 Step C: nonlinear averages (L2638–end)

- [ ] C1 — Lemma `lbl429` *existence of center of mass* ⟸ S5
- [ ] C2 — Prop `lbl430` *cm dependence on weights/points* ⟸ C1
- [ ] C3 — Prop `lbl434` *averaging maps* ⟸ C1,C2
- [ ] C4 — Prop `lbl436` *average of →id maps →id* ⟸ C3,B6

## §4 Step D: directed system, limit, assembly (L1883–2102)

- [ ] D1 — Prop `lbl406` *metrics almost isometric on large balls* ⟸ B6,C4
- [ ] D2 — Prop `lbl407` *almost-isometric limiting metrics* ⟸ D1, F8
- [ ] D3 — Prop *convergence to a limit* (builds `M_∞`) ⟸ D2, F9–F13
- [ ] D4 — Prop *the limit is complete* ⟸ D3
- [ ] D5 — ASSEMBLY: discharge `metricCompactness` (MetricCompactness.lean) → build
      `MetricCompactnessConclusion` from D1–D4 + maps + convergence ⟸ all above

---

## Critical path & parallel tracks

- **Track α (now, no geometry):** F2-book→F3→F4→F5→F6 ; F7→F8 ; F9→{F10,F11,F12,F13}.
- **Track β — PARKED (was "now"; over-optimistic):** §5 `S1→S5` blocked on GlobalGeometry `sorry`s, awaiting external merge. Still now-doable here: `A1→A2 ; A8` (no convexity needed).
- **Then A:** A3,A5,A9,A10,A11,A12,A13 → A14.
- **Then B:** B1→B2→B3→B4 ; B5 ; → B6.
- **Then C:** C1→C2→C3→C4.
- **Then D:** D1→D2→D3→D4→D5.
- Honest-input boundary (total): A0 `lbl384`, A0' Rauch/volume, S3 `lbl413`, (temp) S6 `lbl418`.
  Everything else is proved.

Immediate next task: **F3-hi-kge2** - generalize the checked order-two
connection-difference producer to all higher orders needed by the book
induction, using the already checked `k = 0,1,2` endpoints as the base range.
