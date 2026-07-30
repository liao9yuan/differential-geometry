# Compactness paper and presentation plan

## Current message

The metric Cheeger--Gromov compactness theorem and Hamilton compactness for
complete Ricci flows are now results of the project, not deferred inputs.  The
paper/talk should lead with those two theorems and then explain the geometric
proof.  The current provider-native Hamilton endpoint is blocked only by the
separate uniform-existence producer.

## Recommended paper structure

1. State pointed smooth metric compactness.
2. State compactness for complete Ricci flows on a common open interval.
3. Define the structured pointed convergence output.
4. Prove injectivity-radius decay from basepoint injectivity and bounded
   geometry.
5. Derive volume and finite-packing control.
6. Construct the branch-carrying H6 normal-coordinate package.
7. Stabilize nets and construct pairwise approximate diffeomorphisms.
8. Form the smooth direct limit and prove completeness with compact cores.
9. Apply complete Shi estimates and a space-time diagonal to obtain the flow
   limit.
10. Explain the Hamilton application and give the honest deferred-input
    ledger.

The mathematical proof should precede the Lean architecture.  Declaration
names belong in a compact correspondence table, not in the main proof.

## Recommended talk structure

A 35--40 minute talk can use the following slide budget.

| Slides | Content |
|---|---|
| 1--3 | Motivation, theorem statements, and exact hypotheses |
| 4--6 | Why basepoint injectivity is not enough; the CGT decay profile |
| 7--9 | Bishop--Gromov volume control, packing, and stable nets |
| 10--13 | H6 normal charts and the need to retain actual inverse branches |
| 14--17 | Center-of-mass gluing and the textbook pairwise comparison theorem |
| 18--21 | Tail system, direct limit, limiting metrics, and cocycle |
| 22--24 | Compact cores and completeness |
| 25--27 | Complete Shi estimates and the space-time flow upgrade |
| 28--30 | Lean representation: subsequences, domains, and structured output |
| 31--33 | Hamilton application, verified status, and remaining frontier |

The main visual should be the five-stage implication:

```text
bounded geometry + base injectivity
        |
        v
injectivity decay + volume/packing
        |
        v
coherent H6 charts + approximate maps
        |
        v
complete smooth direct limit
        |
        v
Shi estimates + space-time limit
```

## Deferred-input ledger for the final presentation

### Completed and not to be called deferred

- unconditional metric compactness, `metricCompactness`;
- complete/open-window Shi estimates, `movingShi_open`;
- unconditional solution compactness, `compactnessSol`;
- Perelman noncollapsing on the Hamilton route, `ham3_noncollapse`;
- volume-to-injectivity conversion, `flowInj_of_vol`;
- provider-native Hamilton compactness and transfer assembly;
- the spherical-space-form handoff, `ham3_space_box`.

### Live critical frontier

- `ham3_flow_exists_normalized`: uniform existence and continuation from
  uniform ellipticity and finite initial metric-jet bounds.

The remaining analytic bricks are the time-dependent second-order perturbation,
the time-integrable first-order operator family, the same-horizon
nonautonomous order-two bootstrap, and smoothing/realization at the initial
corner.

### Unfinished but not on the new critical path

- legacy `ham3_cgh_limit`;
- generic arbitrary-valence Weyl eigenvalue counting;
- the independent textbook Hopf--Rinow capstone.

These should be listed as maintenance or general-library frontiers, not as
assumptions of the completed compactness theorems.

## Status wording

Use:

> The metric and Ricci-flow compactness theorems are checked and axiom-audited.
> The new Hamilton adapter consumes their structured conclusions directly.
> The remaining nonstandard axiom on the Hamilton main path is the independent
> uniform-existence producer.

Avoid:

> Cheeger--Gromov--Hamilton compactness is still a deferred global input.

That wording describes the older manuscript state and is no longer accurate
for the provider-native route.
