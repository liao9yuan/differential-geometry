# Scalar-source local W2 regularity

## Result

`srcSol_memW2` is the canonical compact-free Euclidean endpoint for a local
scalar-source weak equation.  Given the actual `H01` weak equation and
`f in L2(Omega)`, it proves `MemWkp 2 2 u V` on an inner open set where the
chosen cutoff is one.  Its coefficient, cutoff-room, and inner-domain
hypotheses match `homSol_memW2`; it adds no solution predicate or expanded
substitution-identity assumption.

The module also exposes the two natural producers used by the endpoint:

- `srcSol_dq_bound`: uniform local `L2` bounds for component difference
  quotients;
- `srcSol_second`: existence of every second weak partial on the inner set.

## Native route

1. `src_master_nonsmooth` supplies the same global witness and raw Nirenberg
   estimate as the homogeneous chain, now with the genuine scalar-source term.
2. The scaled source `rho^-1 * f` is extended by zero from `Omega`; the existing
   quantitative master theorem then absorbs it using only the supplied local
   `L2` hypothesis.
3. The existing Friedrichs-Korn and standard-test-square producers control the
   remaining terms, while `dq_norm_of_sum` extracts a component seminorm bound.
4. The local difference-quotient weak-limit theorem constructs each second
   weak derivative.
5. `MemWkp.two_of_wit` assembles these derivatives into `MemWkp 2 2 u V`.

This is the shortest native route.  It reuses the scalar-source master rather
than introducing a parallel vector-source Young estimate.

## Verification

The first focused check stopped at the zero-extension `MemLp` proof because a
local `let` definition was passed directly to `rw`.  The route and statement
were unaffected; exposing the indicator function with `change` before applying
`memLp_indicator_iff_restrict` fixed the shape.  Focused re-verification then
passed without warnings.  The explicit named module refresh also passed once
the H3 assembly became a real downstream consumer.

## Project position

- `srcSol_memW2`: source-written and focused-verified (100% at this endpoint).
- Dedicated scalar-source W2 machinery: 100% at this module boundary, with a
  fresh exported artifact available to downstream modules.
- The all-order local elliptic bootstrap and the P1c splitting theorem remain
  separate, unstated endpoints at 0%.
