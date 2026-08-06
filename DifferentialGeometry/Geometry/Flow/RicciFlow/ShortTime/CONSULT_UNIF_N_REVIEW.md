# Consult prompt: mathematical review of the (N) uniform-existence architecture

Purpose: external (GPT Pro) review of whether the mathematics of the running
(N) `ricci_flow_unif_existence` campaign is RIGHT — the architecture and the
six recent design rulings — before the next multi-session estimate bricks.

Submission (per CLAUDE.md consult workflow):
- ChatGPT project "Lean Pro Consult Handoff", FRESH chat.  Expect 5–10 min.
- Evidence mode: local tree is FAR ahead of GitHub (large uncommitted verified
  content on `codex/short-time-existence-align` in the ste-align worktree; the
  agent may not push).  EITHER (a) push that branch first and keep the GitHub
  links below, OR (b) attach these files and tell Pro the GitHub branch is
  BEHIND local: `Evolution/ExtendViaUniqueness.lean`,
  `ShortTime/UNIF_EXISTENCE_PLAN3.md`, `ShortTime/A1CUR_PLAN.md`,
  `ShortTime/F6_ESTIMATE_RECON.md`, `ShortTime/OPTIONB_FLOOR_PLAN.md`.
  The prompt below is self-contained either way (key statements quoted).

---- PROMPT BEGINS (copy everything below this line) ----

I am working in a large Lean 4 / mathlib differential-geometry project.  Do
NOT write code.  This is a MATHEMATICAL DESIGN REVIEW: referee the
architecture and six specific rulings for correctness.  Setting: closed
3-manifold `M` (boundaryless, `finrank = 3`), fixed smooth background metric
`gBase`.

## Target theorem (black box (N), stated in Lean, proof 0%)

For fixed `gBase` (the statement internally fixes a finite chart-centre
family `S`): for every `Λ ≥ 1` there exists `τ₀ = τ₀(gBase, Λ, S) > 0` such
that EVERY smooth metric `g₀` with

- `Λ`-comparability: `Λ⁻¹ gBase ≤ g₀ ≤ Λ gBase` pointwise, and
- covariant jet bounds through order 3: `MetricCovDerivOrderBoundOn` for all
  `a ≤ 3` (i.e. `‖∇_gBase^a g₀‖ ≤ Λ` globally),

admits a family `rr : ℝ → metrics`, `rr 0 = g₀`, with

1. chart-Gram matrices jointly C∞ on the HALF-OPEN slab `[0, τ₀) × chart`
   (smoothness UP TO the initial corner `t = 0`),
2. the RICCI FLOW equation `∂_t rr = −2 Ric(rr)` on `[0, τ₀)` (one-sided
   derivative at `t = 0`).

Note: the conclusion is Ricci flow PROPER, and the jet budget in the
hypothesis is `a ≤ 3` — both are fixed and may not be changed.

## The architecture (what we are building)

All analysis runs on spectral Sobolev scales `H^a` of (0,2)-tensors defined
by the background connection Laplacian of `gBase`; `g(t) = gBase + T(t)`
(more precisely the campaign solves Ricci–DeTurck with background `gBase`).

Phase A (per-metric, fixed horizon `T ≤ 1`):
- A1. Low-regularity DeTurck fixed point: a forcing `f ∈ L²_t H²` fixed
  point `f(t) = N(u(t))` where `u = Duhamel(0, f)` is the maximal-regularity
  state (`u ∈ C_t H³ ∩ L²_t H⁴`-type, `u(0) = 0`), and
  `N(v) = staticForce + A₂(v) + (small remainder)(v)` with `staticForce`
  the frozen-coefficient Ricci–DeTurck RHS of `gBase + 0`.  Existence by
  contraction on a ball of radius `P` in `L²_t H²`, with an a.e. state ball
  `sup_t ‖u(t)‖_{H²} ≤ R ≤ P/4` as a separate output.  Smallness inputs:
  the fibre operator bound `‖T‖_{L∞-operator} ≤ δ ≤ 1/3` (so `gBase + T`
  stays a metric with constants), horizon smallness in `√T`.
- A2. ALL-ORDER spatial smoothness ON THE SAME HORIZON (no horizon
  shrinking per order — this is a hard design commitment).  Mechanism: for
  every `σ`, the σ-weighted spectral mass
  `sup_{t∈[0,T]} Σ_i λ_i^σ |mode_i(f(t))|²  < ∞`, proved by a Galerkin
  scheme: finite eigen-combination approximants, a per-scale energy
  hierarchy (Grönwall at every Sobolev rung `k`), passage to the limit.
- A3. The hierarchy's engine is a pair of LADDER estimates for the
  linearized coefficient arms of the DeTurck operator difference
  (`N(T) − N(0)`, schematically `a₂(T)·∇²  + a₁(T)·∇¹ + a₀(T)`):
  - `a₂` ladder (PROVED in Lean, k-uniform): for `3 ≤ a` and states in an
    `H^{a+2}` ball of radius `R₀`,
    `‖a₂(T) W‖_{H^m} ≤ κ·(δ/(1−δ)²)·‖W‖_{H^{m+2}} + C(m,R₀)·‖W‖_{H^{m+1}}`
    where the TOP constant `κ·δ/(1−δ)²` is INDEPENDENT of the rung `m`
    (mechanism: commutator against resolvent powers; the top-order
    coefficient never meets the Leibniz grid; rung costs accumulate only in
    `C(m)`).  With `δ ≤ 1/3` the top coefficient is `≤ (3/4)κ`, and the
    design claim is that per-rung Grönwall closure holds with margin
    (`Cδ < 2` in our internal notation) at EVERY rung — σ-uniformity is
    bought entirely by this m-free top constant.
  - `a₁` ladder (designed): `‖a₁(T) W‖_{H^m} ≤ C(m,R₀)·‖W‖_{H^{m+1}}` — one
    derivative, so the whole arm sits in the lower slot and m-dependent
    constants are harmless.
- A4. Joint time–space C∞ up to the corner via a maximal-regularity
  "jointly smooth" engine, whose ONLY smallness input (after ruling R-1
  below) is the state bound `sup_{t∈[0,T]} ‖u(t)‖_{H²} ≤ 1/(2C)` keeping
  `gBase + u(t)` uniformly a metric (`C` = the fibre-bilinear constant).

Phase B (class-uniformity): every constant entering the horizon and radius
choices (`τ₀`, `P`, `R`) is bounded by class data only: `Λ`, the order-≤3
chart jets, and `gBase` geometry (ellipticity/resolvent constants, Sobolev
constants, the order-1 static force size).  Hence one `τ₀(Λ)` for the class.

Phase C (assembly into (N)): the one low-regularity Ricci–DeTurck solution
on `[0, τ₀]`, a-posteriori bootstrapped (A2+A4), is converted to Ricci flow
by the DeTurck trick (pull back by the diffeomorphism flow of the DeTurck
vector field `W(g(t), gBase)`), preserving the horizon and the up-to-corner
chart-Gram smoothness.

## Status honesty

- PROVED in Lean (axiom-clean): the `a₂` ladder incl. the k-uniform
  mechanism; the all-order jet tower of the second-order coefficient (`C2`);
  the top-kernel jet estimate assembling it (Moser-window route, `δ ≤ 1/3`
  the only smallness); the front-A wiring (fixed point, realization, joint
  engine plumbing); an `H¹` C⁰-uniqueness chain; the A4 floor refactor.
- DESIGN ONLY (unproved, the review targets): rulings R-1 … R-6 below.
- Twice this week a landed frontier STATEMENT was found false by our own
  recon loop and repaired by statement surgery (missing hypotheses); one
  ratified route was refuted in implementation (a Moser-window vocabulary
  cannot express arms that are quadratic in `∇P` without a sup bound on
  `∇P`).  So we specifically want an external check of the CURRENT rulings.

## The six rulings to referee

R-1 (floor deletion).  The joint-smoothness engine originally took
`√T·‖u.deriv‖_{L²H²} ≤ 1/(2C)` and used it ONLY to derive
`sup_t ‖u(t)‖_{H²} ≤ 1/(2C)` (via `u(t) = ∫₀ᵗ u'`, `u(0) = 0`).  Ruling:
replace the hypothesis by the state bound itself, source it from the
fixed-point ball (`R ≤ P/4`, cap `P`), and DELETE the derivative-norm floor
— with the consequence that the class-uniform `τ₀` needs the static force
only at order 1 (3 metric derivatives) instead of order 2 (4 derivatives,
outside the `a ≤ 3` budget).  QUESTION: is state-smallness genuinely
sufficient everywhere — in particular, does any part of maximal-regularity
theory or the Nemytskii/tame estimates SECRETLY need the derivative-norm
smallness (not just finiteness), or is smallness-of-state + finiteness-of-
derivative enough?  Also confirm: capping the contraction radius `P` shrinks
`τ₀` by a class-uniform factor and introduces no circularity.

R-2 (ball order and the first-exit bootstrap).  The `a₂` ladder needs the
`H⁵` ball (`H^{a+2}`, `a = 3`) on the state, but the trajectory only has
`C_t H³ ∩ L²_t H⁴` a priori.  Ruling: the ball is a FIXED low order
(independent of the rung), so only the bottom three scales are circular;
close them at the GALERKIN level — finite-dimensional approximants have
continuous-in-`t` energies; run a first-exit-time argument on the bottom
scales, then pass to the limit.  QUESTION: is this sound, and what must be
checked so the exit time is UNIFORM IN THE GALERKIN DIMENSION (else the
limit horizon degenerates)?  Is there a cleaner standard alternative
(e.g. retract-and-identify) that avoids the N-uniformity subtlety at
comparable cost?

R-3 (the C0/C1 fork).  The order-1 and order-0 coefficient arms contain the
bare connection difference `∇P` (`P = g − gBase` schematically).  Our
finding: the C1 arm is LINEAR in `∇P` and its per-order estimate closes
ball-free at the jet budget `Σ_{j ≤ i+1} ‖∇^j P‖²`; the C0 arm has summands
QUADRATIC in `∇P`, and the ball-free statement is FALSE (concentration:
`‖P‖_{L²}, ‖∇P‖_{L²} → 0` with `‖|∇P|²‖_{L²} → ∞` under `‖P‖_∞ ≤ 1/3`).
Ruling: thread the available `H^{a+2}` ball through the C0 estimate; with
`a ≥ 1` in dimension 3, `H³ ⊂ C¹` gives `‖∇P‖_∞ ≤ C R₀`, the quadratic
terms become linear-in-jets, and the budget `range (i+2)` closes at every
order via Gagliardo–Nirenberg for the middle Leibniz terms.  QUESTION:
confirm the counterexample logic and that the balled estimate closes at ALL
orders `i` (top terms via the `L∞` cap, middle terms via GN within the
`i+2` budget) — or name the order where it fails.

R-4 (the widened spatial-mass statement).  The A2 keystone is stated as:
IF `f` is the fixed point (a.e. identity `f(t) = N(u(t))`), IF the
trajectory ball `sup_t ‖u(t)‖_{H²} ≤ R` holds a.e., and IF the frozen
family agrees eigen-coordinate-wise with the smooth-core operator
`N_smooth` on the radius-`R` ball (a "bridge" hypothesis available at the
call site), THEN for every `σ` the σ-weighted spectral mass of `f(t)` is
bounded on `[0, T]`.  QUESTION: is this the right intermediate statement
for A2 (all orders, same horizon), and is the five-ingredient Galerkin
route (ODE existence for projected systems; per-scale closure; Grönwall
hierarchy; Galerkin→mode-limit identification; Fatou) adequate — what is
the weakest link?

R-5 (σ-uniformity from the m-free top constant).  The design claim: with
the `a₂` top constant m-free and `< 1` after `δ ≤ 1/3`, and the `a₁`/`a₀`
arms in lower slots, the per-scale energy closure has a rung-independent
margin, so the hierarchy yields ALL σ simultaneously on the SAME horizon
(no shrinking).  QUESTION: referee this uniformity argument — in
particular, do the rung-dependent lower-slot constants `C(m)` threaten the
horizon (they multiply lower-order energies which are already bounded at
earlier rungs, so they should only enter the CONSTANTS, not the horizon) —
confirm or refute.

R-6 (class-uniform τ₀ within `a ≤ 3`).  After R-1, the horizon/radius
formulas consume: the order-1 static force norm, ellipticity/comparability
from `Λ`, resolvent/Sobolev constants of `gBase`, and the fibre constant
`C`.  QUESTION: does any of these SECRETLY need a 4th derivative of `g₀`
(e.g. through a curvature commutation in the resolvent bounds, or through
the chart-Gram C∞-up-to-corner conclusion), or is the `a ≤ 3` budget
genuinely sufficient?  (The conclusion's C∞ for `t > 0` comes from interior
smoothing; the up-to-corner statement at `t = 0` is where we most fear a
hidden jet demand.)

## Architecture-level questions

G-1.  The conclusion is RICCI flow; we build Ricci–DeTurck.  Referee Phase
C: on a closed 3-manifold with `g(t)` chart-Gram C∞ on `[0, τ₀) × M` (up to
corner) and `g(0) = g₀` smooth, does the DeTurck vector-field flow
`φ_t` exist on the same horizon and is `φ_t^* g(t)` chart-Gram C∞ up to the
corner with the one-sided Ricci-flow derivative at `t = 0`?  Any subtlety
with regularity of `φ_t` at `t = 0` (the vector field is only as good as
`∇g(t)` near the corner) that would force extra hypotheses?
G-2.  Is the OVERALL chain (A1 → A2 → A4 → B → C) logically complete for
(N) as quoted — name any missing ingredient (uniqueness input, compactness,
measurable-selection of `τ₀`, the `Ico` vs `Icc` endpoint, the choice of
chart family `S`) that the phases as described do not provide.
G-3.  Rank the remaining mathematical risk: which single item above is most
likely to be wrong or to hide a wall, and what is the cheapest probe that
would expose it?

## Constraints

- Preserve the (N) statement and the `a ≤ 3` budget; do not propose
  widening them.
- Classify each of R-1 … R-6 and G-1 … G-2 as SOUND / SOUND-WITH-CAVEAT
  (state the caveat precisely) / UNSOUND (state the smallest wrong step and
  the smallest repair).
- Prefer small corrections over redesigns; no code; no blind automation.
- End with: (i) the single most valuable next mathematical check, and
  (ii) the failure signals that should make us STOP a brick and re-consult.

GitHub reference (may be BEHIND local; attached files are current):
https://github.com/liao9yuan/differential-geometry/tree/short-time-existence
Relevant local files (attached or pushed): `Evolution/ExtendViaUniqueness.lean`
(the (N) statement, sorry at :98), `ShortTime/UNIF_EXISTENCE_PLAN3.md` (the
campaign ledger: proofs landed, executor reports, rulings Nos. 104–114),
`ShortTime/A1CUR_PLAN.md` (the C0/C1 fork analysis), `ShortTime/
F6_ESTIMATE_RECON.md` §7 (the Galerkin assembly design), `ShortTime/
OPTIONB_FLOOR_PLAN.md` (the floor-deletion design).

---- PROMPT ENDS ----
