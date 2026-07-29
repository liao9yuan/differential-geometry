# GPT Pro architecture consult: low-base uniform Ricci--DeTurck existence

Architecture ruling only.  Do not implement.

## Remotely visible repository state

- GitHub: `https://github.com/liao9yuan/differential-geometry`
- branch: `codex/short-time-existence-align`
- remote commit: `13102801f535742987e064e47982ce478b01c133`

Please inspect these repo-relative files:

- `DifferentialGeometry/Geometry/Flow/RicciFlow/Evolution/ExtendViaUniqueness.lean`
- `DifferentialGeometry/Geometry/Flow/RicciFlow/ShortTime/LowRegDenseSolve.lean`
- `DifferentialGeometry/Geometry/Flow/RicciFlow/ShortTime/LowRegBootstrapOne.lean`
- `DifferentialGeometry/Geometry/Flow/RicciFlow/ShortTime/LowRegPrincipalTime.lean`
- `DifferentialGeometry/Geometry/Flow/RicciFlow/ShortTime/LowRegSmoothBridge.lean`
- `DifferentialGeometry/Analysis/Parabolic/QuasiLinear/TensorMaximalRegularity/NonautonomousL2.lean`
- `DifferentialGeometry/Analysis/Spectral/Intrinsic/HeatSemigroup/ParabolicInteriorSmoothing.lean`
- `DifferentialGeometry/Analysis/Spectral/Intrinsic/DeTurck/PrincipalLowRegCore.lean`
- `DifferentialGeometry/Analysis/Spectral/Intrinsic/DeTurck/PrincipalCoeffH2.lean`
- `DifferentialGeometry/Analysis/Spectral/Intrinsic/DeTurck/DeTurckRemainderHigherOrderTame.lean`
- `DifferentialGeometry/Analysis/Spectral/Intrinsic/DeTurck/DeTurckRemainderPrincipalArmOpNorm.lean`
- `DifferentialGeometry/Analysis/Spectral/Intrinsic/DeTurck/StrongSolutionUniqueness.lean`
- `DifferentialGeometry/Geometry/Flow/RicciFlow/ShortTime/UNIF_N_PRO_RULING.md`

The local checkout is one unpushed commit ahead of the remote branch and also
contains uncommitted work.  You cannot inspect those additions.  The following
facts are therefore supplied as mathematical statements, not as remotely
visible source claims:

1. `rhsRefold_eq` is an exact six-field identity for the order-zero
   Ricci--DeTurck coefficient after the Ricci and DeTurck principal terms have
   been cancelled before estimation.
2. `rhs_sub_zero_refold` is an exact path-integral identity

   `N(T) - N(0) = C0(T) T + C1(T) nabla T + C2(T) nabla^2 T`,

   with complete Ricci plus DeTurck refolding in `C0` and `C2`.
3. In dimension three, `rhs0_h2_tame` proves an estimate of the shape

   `||C0(sT)||_{H2}^2 <= sum_{i<3} K_i ||nabla^(i+2)(sT)||_L2^2
       + K_4 ||nabla^4(sT)||_L2^2 + B(A)^2`,

   whenever the jets below order four are bounded by the `H3` radius `A`.
   It has no high-Sobolev-index or pointwise `H4`-ball assumption.  The fourth
   derivative is an explicit linear head.
4. `lowRegPrincipal_core` identifies the existing low-regularity principal
   operator with the geometric completed principal-cometric action
   `H4 -> H2`.

All four local results are focused/exact green and contain no `sorry`, `admit`,
axiom declaration, or final-use `whnf`.

The remotely visible high-order theorem
`exists_deTurckSmoothRemainderDiff_eq_principalCometricArm_add_smallThirdArm_add_tame`
is the structural model for the missing low-base statement.  After subtracting
the endpoint principal-cometric arm it still produces:

- a small second-order coefficient applied to `nabla^2 T`;
- an order-zero coefficient applied to `T`, whose highest coefficient jet
  becomes small only after retaining the undifferentiated small `T` factor;
- a genuinely one-order-lower tame arm.

Its final bound has the schematic form

`||third||_(H^(a+k-1)) <= eps(delta) ||T||_(H^(a+k+1))
    + Cthird(k) ||T||_(H^(a+k))`,

while `tame` loses only one derivative.  However it assumes
`a >= 2*dim+10` and an `H^(a+2)` ball, so it cannot be used to uniformize the
present `C3` input class.

The live low-base audit also established:

1. `lowRegA2Time` contains only the endpoint `lowRegPrincipal`; it does not
   contain the extra small second-order and order-zero/high-head arms above.
2. The top constants in the checked coefficient-only `rhs0_h2_tame` are
   finite but not small in `delta`.  For example, some remain positive at
   `delta = 0`.  Smallness is recovered only after the coefficient acts on
   the undifferentiated metric deviation.
3. A rank-one factorization from the value of the full `H2` residual is not
   available before the bootstrap: the rough solution is only `L2_t H3`, so
   that residual value is not yet defined in `H2`.  Such a factorization is
   acceptable only after a low-base action estimate or operator extension has
   already been constructed.

## Live obstruction

`lowreg_partial_sol` already gives the fixed-background order-one solution:
the solution field is in `L2_t H3`, its carrier has an `H2` same-horizon
representative, and the forcing is in `L2_t H1`.

`lowRegA2_data` already packages the actual measurable, uniformly bounded
`A2(t) : H4 -> H2` principal family along that `H2` state.

The mixed nonautonomous solver requires in addition

`A1(t) : H3 -> H2`, with `MemLp A1 2`.

The static `rhs0_h2_tame` cannot simply be called `A1`: its explicit fourth
metric derivative is not supplied by the order-one solution.  The input class
of the endpoint controls metric derivatives only through order three, so a
uniform `H4` or `C4` assumption is forbidden.

The generic `solField_into_all_tensorHs_interior` theorem assumes a one-order
forcing loss.  Ricci--DeTurck is genuinely second order, so a naive use of
that theorem has net gain `2 - 2 = 0`.

The endpoint `ricci_flow_unif_existence` requires chart-Gram joint smoothness
on the full `Ico 0 tau0` slab, not merely on `Ioo`.

## Ruling requested

Choose the smallest faithful route:

### A. Action-level principal subtraction

Prove a low-base identity/estimate for the complete action

`N(T) - N(0) - lowRegPrincipal(T) T`,

in which every `H4` head from the three refolded arms is absorbed into the
existing principal operator or one additional small `H4 -> H2` operator,
leaving a genuine `H3 -> H2` lower operator.  The consumer-shaped target is
schematically:

```text
extraA2 : metricH2 -> (metricH4 ->L metricH2)
lowerA1 : metricH3 -> (metricH3 ->L metricH2)

smooth core:
  N(T) - N(0) - fixedLap(T)
    = (lowRegPrincipal(T_H2) + extraA2(T_H2)) T_H4
        + lowerA1(T_H3) T_H3

||extraA2(S)|| <= c * ||S||H2
||lowerA1(S)|| <= C_R * (1 + ||S||H3)
```

The first map should be locally Lipschitz on the small `H2` ball, hence
measurable and uniformly small along the same-horizon `H2` state.  The second
bound must be at most linear in the `H3` norm, not an arbitrary envelope
`B(||S||H3)`, so that the existing `L2_t H3` control implies
`MemLp lowerA1 2`.

### B. Low-base quasilinear smoothing first

Prove a new small-data, second-order (`+2`) interior regularity theorem for the
order-one rough solution, then compare it with the existing per-datum smooth
solution near `t = 0` via `deTurckStrong_unique` and splice the two regularity
descriptions to recover full-`Ico` smoothness.

### C. A smaller RicciFlower-native factorization

For example, first extend the principal-subtracted nonlinear residual
continuously from `H3` to `H2`, then use a measurable Hilbert-space rank-one
factorization along the actual solution to obtain an admissible
`A1(t) : H3 -> H2`.  Accept this only if it is mathematically faithful and
does not hide the missing principal cancellation, evaluate an `H2` residual
before the rough solution is known to lie in `H4`, or introduce another black
box.

Please give:

1. the recommended route and why the other routes are larger or invalid;
2. the exact smallest public theorem statement(s), in Lean-shaped
   pseudocode;
3. the canonical repo-relative file(s);
4. how the route produces a family-uniform lifespan from only the `C3` /
   `MetricCovDerivOrderBoundOn` inputs;
5. how it reaches full `Ico` regularity without a uniform `H4` or `C4`
   assumption;
6. a precise stop signal: the first term or missing API that would prove the
   chosen route cannot close.

Do not recommend adding a uniform `H4`/`C4` hypothesis, rerunning the
high-order fixed point with a lifespan depending on high derivatives, or
renaming a conditional wrapper as the endpoint theorem.
