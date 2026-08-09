# Galerkin parabolic energy

## 2026-07-13 rank-generic consumer

The spectral energy, ODE derivative identity, and uniform per-scale energy
consumer are now rank-generic in the tensor valences.  Existing DeTurck uses
continue to infer `(0,2)`, while the scalar non-autonomous lane can instantiate
the same API at `(0,0)` without a parallel energy hierarchy.

The edited module passes focused verification and its named module refresh
passes.  A direct focused verification of the existing DeTurck consumer did
not reach elaboration of these calls because its dependency chain still has
missing stale object files; refreshing one missing dependency exposed another,
and the named consumer refresh exceeded the verification time window before a
subsequent missing dependency was reported.  No DeTurck source was changed.

This refactor does not close the scalar regularity frontier.  The load-bearing
consumer hypothesis remains the per-order closure inequality in
`galerkin_energy_uniform_bound_perScale`, with a top-energy coefficient
strictly below `2`.  The current scalar `H² → H⁰` operator bound and
`conj_weak_ae` only provide the base-scale equation; they do not prove that
per-order inequality.  A direct finite-core scalar dissipation theorem would
be sufficient and is weaker than a full operator-norm `scalar_crit_tame`, but
its high-order coefficient and commutator estimate is still genuine missing
analytic content.


## 2026-08-04 — `L¹`-in-time Grönwall coefficient added (E1′ lane)

Two new sorry-free public declarations, both verified (focused check + targeted
module build + axiom census `propext, Classical.choice, Quot.sound`):

* `energy_hier_l1_bound` — `energy_hierarchy_explicit_bound_perScale` with the
  zeroth-order coefficient allowed an extra time-dependent summand `A t`.  The
  integrability is carried by a primitive `S` (`S 0 = 0`, `0 ≤ S ≤ Sbd`,
  `S' = A` on `Ico 0 T`); the conclusion is the constant-coefficient Grönwall
  bound inflated by the single factor `Real.exp Sbd`.
* `galerkin_energy_l1_bound` — the same widening of
  `galerkin_energy_uniform_bound_perScale`.  The bound stays `N`-uniform and
  `t`-uniform on `Icc 0 T`, and stays `N`-free whenever `Cδ, Cmid, seed, B0,
  Sbd` are.

**Why.**  `PSTOP_PROPOSITION.md` §6.1 v4: at the rungs where the coefficient
jets are capped by a trajectory norm the projected solve controls only in
`L²_t` (the `H³` cap of the C0 tower), the cap enters the Grönwall coefficient
QUADRATICALLY, so `A(k)(t) ≲ class + C‖U_N(t)‖²_{H³}` is `L¹_t` but not
`L∞_t`.  The pre-existing engine demands a constant `Cmid`, so it could not be
used at those rungs.

**Route that worked (first try, no failed routes).**  The substitution
`Mk ↦ Mk · exp (−S)`.  It leaves the dissipation term `−c·M_{k+1}` and the
`√`-seed term in place — the seed needs only `√(M) · e ≤ √(M · e)`, i.e.
`e ≤ √e` for `0 < e ≤ 1`, which is where `0 ≤ S` is used — and turns the
variable coefficient into the constant one exactly.  No new Grönwall
comparison argument, no `image_le_of_liminf_slope_le_deriv_boundary`, no
absolute-continuity/FTC infrastructure was needed.  Worth remembering: a
monotone primitive substitution is much cheaper than re-proving Grönwall with
a variable coefficient.

**Hypothesis shapes to note for callers.**  `seed` must now be nonnegative
(`hseed`), which the constant-coefficient engine did not need; it is what makes
the `√`-seed survive the substitution.  `S` is passed as data with its
derivative `A`, not as an integral — a caller with continuous `A` builds it
from `Analysis/ODE/IntegralGronwall.lean`'s primitive/FTC pair.

## J5 (2026-08-04): `galerkin_energy_l1_bound` generalized to an `N`-indexed coefficient

**Status: DONE, in place, sorry-free.**  `A S : ℝ → ℝ` became `A S : ℕ → ℝ → ℝ`;
the five `S`-hypotheses (`hS0`/`hSnn`/`hScont`/`hSderiv`/`hSbd`) are now `∀ N`;
`hclosure`'s coefficient is `Cmid k + A N t`.  `Sbd` deliberately stays a shared
SCALAR — that is the whole `N`-uniformity mechanism, and it is why the
CONCLUSION is unchanged.

Why the generalization was needed: the audit's counterexample is right.  A single
`A` for all `N` is not what the projected (Galerkin) hierarchy produces — the
coefficient there is the level-`N` trajectory's own `‖U_N(t)‖²_{H³}`, and
`∫ A_N ≤ c` for every `N` does NOT make `sup_N A_N` integrable (moving disjoint
spikes).  A shared bound on the PRIMITIVES `S N ≤ Sbd` is the correct uniform
hypothesis and is exactly what `‖U_N‖²_{L²_tH³} ≤ B₃²` supplies.

Why it was cheap: the body already does `intro N` (`:528`) BEFORE any use of
`A`/`S`, and the single `energy_hier_l1_bound` call sits inside that scope.  So
the edit is `(A := A N) (S := S N)` plus applying the five hypotheses at `N`.
`energy_hier_l1_bound` itself is unchanged — it is stated for one family and
applied once per `N`.

Zero call sites in the tree (only a docstring mention at
`ShortTime/LowRegAllOrderJet.lean`), so no deprecated alias and no
`A := fun _ => A` shim was added.  Verification: focused check green.

## 2026-08-05 — Brick C part 1a/part 4: the single-scale engine and the rider

Three new declarations, all sorry-free, census-clean, targeted build green.

**`energy_l1_single`** (ODE level) and **`galerkin_l1_single`** (Galerkin level)
— the JOINT-KSCOPE fix of ledger №161. Every engine in this file before today
takes the closure at `∀ k` with one shared `Cδ < 2`; a low-regularity ladder
produces it at ONE scale only, because its top-scale prefactor `Cq(k−1)` grows
with `k`. The single-scale form takes the working energy `Y`, a merely
NONNEGATIVE `Yhi` for the scale above (the dissipation term is discarded, so
only its sign is used), and — new — an additive constant `c₀` in the
differential inequality, which no existing engine carried and which §6.4's own
display needs.

Why it is a fresh proof rather than an instantiation: the `if k = 0` trick does
reduce single-scale to `energy_hier_l1_bound`, but `c₀` cannot be folded into
either the seed slot (`seed·√Y + c₀ ≤ seed'·√Y` fails at `Y = 0`) or the `A`
slot, so a new ODE-level statement was unavoidable. The proof is the same
`Y ↦ Y·exp(−S)` substitution as `energy_hier_l1_bound`, with `c₀·e ≤ c₀` the
only extra step; `c₀` lands in the Grönwall `ε` slot beside `seed²/4`.

Weakest-assumptions note: `hc : 0 ≤ c` (not `0 < c`) — only the sign of the
discarded dissipation term is used.

**`galRiderBound`** — the shape a low-regularity rung actually produces. The
`L¹` coefficient is not abstract but `Crid·(1 + E_σ)`, the concrete affine
expression in the energy being estimated; its primitive is `Crid·(t + P N t)`
and the shared bound is `Crid·(T + B)`. `P` is the a-priori `∫₀^T E_σ ≤ B`
input in primitive form — the honest input `hL2H3` of ledger №161, kept as an
explicit hypothesis and NOT discharged here. Stated at general `(σ, sseq)` so
rungs 4–5 reuse it. `hT : 0 ≤ T` was dropped after the linter flagged it: `t`'s
membership in `Icc 0 T` already gives both bounds.

## 2026-08-05 — next-scale dissipation export

`energy_l1_diss` and `galRiderDiss` are the dissipation-retaining siblings of
`energy_l1_single` and `galRiderBound`.  If `D` is a nonnegative primitive of
the next-scale energy, the augmented quantity `Y + c·D` satisfies the same
`L¹`-coefficient Grönwall bound: the `c·Yhi` derivative of `c·D` cancels the
negative dissipation in `Y'`.  The only extra coefficient hypothesis is
`0 ≤ A`, exactly the quadratic rider shape used by the low-regularity rungs.

`galRiderDiss` returns both the working-scale energy bound and
`D ≤ Bound/(2-Cδ)`.  It is metric- and scale-generic; it does not commit the
later campaign to the self-background specialization.  This closes the energy
engine gap needed before rung 4, but does not itself provide the common ordered
absorption envelope or any higher rung.

Focused verification, the targeted export refresh, and the downstream axiom
census all passed.  Both new declarations depend only on `propext`,
`Classical.choice`, and `Quot.sound`; neither depends on `sorryAx`.
