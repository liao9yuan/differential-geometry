# PRO RULING 2: (N) architecture design review (received 2026-08-03)

Second Pro consult on the (N) campaign.  First ruling (2026-07-22, the R1τ
route ruling that shaped the current architecture) = `UNIF_N_PRO_RULING.md`;
this ruling REVIEWS the architecture built since then.  Consult prompt =
`CONSULT_UNIF_N_REVIEW.md` (R-1…R-6 design rulings + G-1…G-3 architecture
questions); submitted user-side.  Integration ledger entry:
`UNIF_EXISTENCE_PLAN3.md` No. 115.  Recorded as a faithful structured digest
(the verbatim text lives in the conversation; one paste artifact in R-5's δ*
display was cleaned).

HEADLINE: architecture VIABLE, not yet closed.  No item UNSOUND.
R-1 (floor deletion) SOUND.  G-1 (DeTurck→Ricci conversion) SOUND.
R-2/R-3/R-4/R-5/R-6/G-2 SOUND-WITH-CAVEAT, each with a named smallest
repair.  Dominant risk: Galerkin bottom-scale bootstrap + identification of
the Galerkin limit with the A1 low-regularity fixed point (R-2 + R-4).
Mandated next check (item (i)): the stopped projected bottom-scale energy
proposition, ON PAPER, before further Galerkin Lean work.

## Classification summary (Pro's table)

| Item | Ruling | Decisive qualification |
| --- | --- | --- |
| R-1 | SOUND | State smallness is the genuine geometric input; time-derivative smallness was only one way to obtain it. |
| R-2 | SOUND-WITH-CAVEAT | First exit is standard only after an N-uniform stopped energy estimate gives a strict improvement on the full prescribed horizon. |
| R-3 | SOUND-WITH-CAVEAT | The counterexample and H³-capped repair are correct; explicitly certify that the total C0 quadratic symbol does not cancel. |
| R-4 | SOUND-WITH-CAVEAT | The current theorem correctly controls the Duhamel STATE's spectral mass, not an arbitrary pointwise representative of the L²ₜ forcing.  Limit identification is the weak link. |
| R-5 | SOUND-WITH-CAVEAT | The same-horizon inference is correct, but δ ≤ 1/3 alone does not establish absorption from the currently proved `a2_ladder` (κ has no proved upper bound). |
| R-6 | SOUND-WITH-CAVEAT | Three initial metric derivatives suffice for the uniform lifespan, provided every low-order spectral/elliptic constant is exposed without importing a high-order g₀ norm. |
| G-1 | SOUND | Joint smoothness to t = 0 gives a jointly smooth DeTurck vector field and diffeomorphism flow on the same half-open horizon. |
| G-2 | SOUND-WITH-CAVEAT | Needs explicit rebasing, Galerkin identification, finite-chart transfer, and interval bookkeeping; no measurable selection or class compactness needed. |

## R-1 — floor deletion: SOUND

The joint-smoothness argument needs `sup_{t≤T} ‖u(t)‖_{H²} ≤ 1/(2C)` — it
turns the spectral estimate into a pointwise fibre-operator estimate and
keeps `g₀ + u(t)` a metric.  `√T‖u_t‖` was merely one route to it.  The
implementation (`hstate` slot; `state_le_of_sqrt_floor` keeping the old
route; `norm_le_of_ae_le` upgrading the a.e. ball) reflects the exact
distinction.

No hidden derivative-smallness requirement: `u_t ∈ L²ₜH²` is needed as part
of the solution space (PDE, traces, time regularity) but its NORM need not
be small for: pointwise metric definition, smooth Nemytskii maps,
ellipticity, spatial tame estimates, joint-smoothness reconstruction.  A
hidden need would surface as a `u_t`-dependent coefficient in the spatial
operator or a contraction in the reconstruction — neither is present in
the endpoint signature.

Capping P is noncircular; ordering: P = min(geometric caps, contraction
caps, state cap) → R ≤ P/4 → choose T with `√T·D_static ≲ P`.  Everything
on the right is fixed before T.

## R-2 — fixed ball order and Galerkin first exit: SOUND-WITH-CAVEAT

Galerkin level is the correct location (continuous energies; the limit
lacks C_tH⁵).  BUT "finite-dimensional and continuous" is not enough — the
proof must deliver a UNIFORM-IN-N STRICT BOOTSTRAP IMPROVEMENT:

1. Projection bounds: spectral projector norm ≤ 1 on every scale used,
   commuting with the background Laplacian/resolvents; NO inverse
   inequality `‖U_N‖_{H^{m+1}} ≤ C_N ‖U_N‖_{H^m}` anywhere.
2. Stopped nonlinear estimates with constants from stopped radii +
   background data only, never the highest retained eigenvalue.
3. Projected source bounds `‖Π_N F‖_{H^m} ≤ ‖F‖_{H^m}`; per-datum high
   source norms may enter high-order CONSTANTS, never the class lifespan.
4. STRICT improvement `sup_{t≤τ_N} E_bot ≤ R₀²/2` (contradicting exit),
   not mere finiteness.
5. Full-horizon closure: the improvement forces τ_N = T.
6. COUPLED bottom scales (H³/H⁴/H⁵ together), not an isolated H⁵ norm.

Self-dependence danger: if `d/dt E₅ ≤ C(R₀)·E₅ + F₅` with C growing in the
H⁵ exit radius R₀ itself, Grönwall gives `e^{C(R₀)T}F₅` and enlarging R₀
need not beat R₀².  The successful structure is TAME AND TRIANGULAR: top
coefficients controlled by an already-closed LOWER norm (the genuinely
needed pointwise cap is only `‖∇P‖_∞`, i.e. H³ in dim 3 — do not let a
nominal H⁵ ball enter every coefficient), highest norm linear, per-datum
high data only on the right.

Retraction alternative (retract nonlinearity, solve globally, N-uniform
estimate, retraction never fires, identify): logically cleaner, NOT
mathematically cheaper — the same strict N-uniform estimate is the burden.

## R-3 — C1 versus C0: SOUND-WITH-CAVEAT

Counterexample CONFIRMED (explicit bump `P_λ = A·φ((x−x₀)/λ)·Θ`, dim 3:
`‖P‖_{L²} = O(λ^{3/2})`, `‖∇P‖_{L²} = O(λ^{1/2})`,
`‖|∇P|²‖_{L²} = Θ(λ^{−1/2})`).  ONE formal gap: divergence of one summand
kills the TOTAL estimate only after excluding exact cancellation of the
total quadratic `∇P·∇P` symbol.  MANDATED CHEAP CHECK: one explicit
frozen-symbol or single-component test showing a nonzero total quadratic
coefficient (Ricci–DeTurck genuinely has such terms; the decomposition
supports noncancellation; the ledger should contain the explicit test).

C1 stays ball-free IFF every summand carries exactly ONE
connection-difference factor (stop signal: finding two).

Balled C0 closes at EVERY order — no exceptional i: `H³ ⊂ C¹` gives
`‖∇P‖_∞ ≤ CR₀`; then `‖∇P·∇P‖_{H^i} ≤ C_i‖∇P‖_∞‖∇P‖_{H^i}
≤ C_i(R₀)‖P‖_{H^{i+1}}` — exactly the `range (i+2)` budget (endpoint
Leibniz terms via the L∞ cap, middle terms via GN/Moser).  C(i,R₀)
acceptable in the lower slot.  `a ≥ 3` comfortably above the needed
`a ≥ 1`.  The ball-thread statement surgery is the correct repair; do NOT
reuse `a ≥ 16` producers.

## R-4 — widened spatial-mass theorem: SOUND-WITH-CAVEAT

The widened dependencies (fixed point + trajectory ball + bridge) are
NECESSARY, not convenient.  CLARIFICATION (good news): the Lean conclusion
controls the spectral mass of the DUHAMEL STATE via continuous mode
convolutions — the right object; an L²ₜ forcing is an equivalence class
with no canonical pointwise values, so a literal pointwise forcing-mass
keystone would be ill-posed.  Forcing regularity follows downstream once a
smooth representative exists.

Weakest link = Galerkin-to-limit steps 4–6, NOT Fatou: (4) strong enough
low-order convergence; (5) passing the nonlinear smooth-core term to the
limit; (6) identifying the limit with the PRE-EXISTING A1 fixed point.
Route: compactness (Aubin–Lions/weak + diagonal) + UNIQUENESS in the
low-regularity class — the existing H¹/C⁰ uniqueness chain is well placed
PROVIDED its hypotheses exactly match the Galerkin limit.  Use ONE
approximant sequence and ONE limit trajectory for every rung σ (diagonal +
uniqueness); never unrelated limits per σ.  The supercritical
`GalerkinLimitUniformMass.lean` machinery demonstrates the shape but does
not discharge the low-base theorem (gated + retracted-Nemytskii).

## R-5 — same horizon from the m-free top constant: SOUND-WITH-CAVEAT

Principle correct (rung-independent top coefficient ⟹ one absorption
condition at every rung; C(m) on lower energies affects only that rung's
numerical bound; Grönwall needs no interval shrinking; the engine
`energy_hierarchy_explicit_bound_perScale` already allows per-scale
constants on the same T).

UNRESOLVED NUMERICAL PREMISE: `a2_ladder` gives top coefficient
`κ·δ/(1−δ)² ≤ 3κ/4` at δ = 1/3 with NO proved upper bound on κ.  The real
absorption condition is `κ·δ*/(1−δ*)² < c_par` (parabolic coercivity,
after norm-equivalence and Young constants).  SMALLEST REPAIR (no
redesign): choose the internal fibre radius
`δ* = min{1/3, δ_abs(κ, c_par)}` and cap the fixed-point/state radius so
the realized trajectory has operator bound ≤ δ*; 1/3 stays as the
universal ceiling.  Pattern precedent: `n_diff_h1_rung`
(`LowRegDissipRung.lean`) shrinks the H² radius until its top constant
< 1.

C(m) is harmless only if the pairing algebra lands it on `C(m)E_m` or
`C(m)E_{m−1}`.  DANGEROUS forms: `C(m)·D_m` (the dissipation being
absorbed), superlinear `C(m)E_m^{1+α}`, or an uncontrolled high-rung norm.
The per-scale dissipation lemma must DISPLAY this algebra once.

## R-6 — class-uniform lifetime with three derivatives: SOUND-WITH-CAVEAT

No inherent 4th-derivative need in the uniform LIFETIME (RHS second
order; order-1 static force uses orders 1–3; floor deletion removed the
one order-4 consumer).  Corner C∞ needs no uniform higher jets: per-datum
higher derivatives may be arbitrarily large across the class — they enter
the a-posteriori C∞ seminorms, NEVER τ₀.  No compatibility tower on a
closed manifold.

CAVEAT (the real audit): the implementation is REBASED at g₀ (spectral
scale and Laplacian at g₀; `staticForce g₀ g₀ 1`).  The class-uniform
sweep must verify DECLARATION BY DECLARATION that every LOW-RUNG elliptic
and norm-equivalence constant used to choose T depends only on
`(gBase, Λ, ∇_{gBase}^{≤3} g₀)`.  High-rung commutator constants may
depend on higher derivatives — only inside a-posteriori smoothing
constants, never inside τ₀.

## G-1 — DeTurck conversion: SOUND

`W(g(t), gBase)` is algebraic in g, g⁻¹, one spatial derivative of g ⟹
jointly smooth up to t = 0.  Compact M ⟹ the time-dependent flow exists
on every [0, T], T < τ₀; ODE uniqueness glues to one flow on the
half-open horizon.  With the sign matched (`∂_t φ_t = −W(t)∘φ_t, φ₀ = id`
for `∂_t g = −2Ric + L_W g`), `φ_t* g(t)` solves Ricci flow with the
one-sided derivative at t = 0.  No extra hypothesis on g₀.  Cautions:
sign/pullback convention; construct on T < τ₀ and glue — never touch the
open endpoint.

## G-2 — completeness: SOUND-WITH-CAVEAT (explicit adapters)

1. REBASING: solve `g(t) = g₀ + u(t), u(0) = 0` (the `staticForce g₀ g₀`
   language indicates this is already the route); state it explicitly and
   transport all constants back to `(gBase, Λ)` class data (= front 3).
2. GALERKIN IDENTIFICATION: A2 must identify its limit with the A1 fixed
   point — the H¹/C⁰ uniqueness chain is PART of A2, not optional.
3. A.E.→REPRESENTATIVE: promote the a.e. fixed-point identity to the
   continuous/smooth representative (plumbing largely present,
   conditional on `lowreg_spatialMass`).
4. FINITE-CHART TRANSFER: chart-Gram smoothness for EVERY chart centre
   from the finite family via smooth transitions (adapter, no new
   analysis).
5. Icc-solve vs Ico-statement: harmless.  6. No measurable selection.
7. No class compactness (only trajectory compactness inside Galerkin).

## G-3 — risk ranking

1. Galerkin bottom-scale closure + identification (R-2 + R-4) — highest.
2. C0 all-order capped currency implementation (keep the cancellation
   grouping; avoid a≥16 producers and range(i+3)).
3. Exposing the actual absorption constant (R-5's δ*).

## (i) Mandated next mathematical check (BEFORE further Galerkin Lean)

Write and verify ON PAPER the stopped, projected bottom-scale energy
proposition: for the finite-dimensional smooth-core system U_N on the
interval where the bottom ball holds,

  sup_{t≤T} E_bot^N(t) + c*·∫₀^T D_bot^N ≤ Φ(T, low class constants,
                                            per-datum high source norms)

with (1) c* > 0 independent of N and rung; (2) no inverse inequality or
max-eigenvalue dependence; (3) every top-energy coefficient controlled by
an already-closed lower norm; (4) per-datum high source norms only on the
right, never restricting T; (5) strict improvement Φ < R₀²/2 with T = τ₀
from class data alone; (6) compactness + uniqueness identifying the limit
with the A1 fixed point.  If true in this exact form, R-2 + R-4 + most of
R-5 close together.  If false, no Galerkin plumbing repairs the route.

## (ii) Stop signals (standing; any occurrence stops the brick and re-consults)

* A projected estimate with a constant depending on the largest retained
  eigenvalue or the Galerkin dimension.
* A bottom-scale exit estimate finite but not strictly improving on the
  full prescribed horizon.
* H⁵-energy coefficient superlinear in the H⁵ exit radius with no
  reduction to an independently controlled H³ norm.
* Limit passage too weak to identify `N(U_N) → N(u)`, with the uniqueness
  theorem inapplicable to the limit class.
* A C1 summand with TWO bare connection-difference factors.
* The repaired C0 estimate still needing `range (i+3)` after the H³→C¹
  cap.
* The total quadratic C0 symbol cancelling (would invalidate the
  counterexample diagnosis; new decomposition audit).
* Top coefficient not made < parabolic coercivity by a class-uniform
  internal fibre radius.
* Any τ₀ formula containing `staticForce … 2`, an H⁵ ball, a 4th
  derivative of g₀, or a high-rung commutator constant.
* DeTurck vector field/flow not jointly C¹ at t = 0.
