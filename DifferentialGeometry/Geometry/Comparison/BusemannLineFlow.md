# Busemann line flow

## Scope and route

This module is the smallest native complete-flow layer needed after
`busemann_grad_par`. It does not add a completeness predicate or ask the
splitting theorem to supply integral curves. For
`X = gradFun g (busemann gamma)` it:

1. bundles `X` as a smooth tangent section using
   `gradFun_contMDiff_total_section` and `busemann_smooth`;
2. uses `busemann_grad_par` and
   `Geometry.Riemannian.Exponential.intrinsic_intCurve` to show that the
   complete geodesic launched with velocity `X x` is a global integral curve
   through every `x`;
3. defines `busemannFlow` with the canonical `Analysis.ODE.curveAt` choice;
4. reuses `curveAt_zero`, `curveAt_integralCurve`, and `curveAt_add` for the
   time-zero, orbit, and additive laws;
5. reuses the generic `Analysis.ODE.curveAt_contMDiff` theorem for joint
   smoothness in `(t,x)`;
6. specializes the generic parallel-flow metric producer to show that every
   spatial differential of `busemannFlow` preserves the Riemannian inner
   product;
7. combines `busemann_grad_sq`, `inner_gradFun`, and the existing integral-curve
   fundamental-theorem calculation to prove Busemann-value translation;
8. aligns the flow with the supplied line. Since `IsMinimizingLine` currently
   exports no velocity-norm projection, a private local lemma derives unit
   speed from geodesic initial-value uniqueness and the public
   `exists_dist_eq_sqrt` small-radius distance formula.  A separate private
   isometry argument transports the line's exact distance identity to ordinary
   manifold continuity.  The identity `b(gamma s) = -s`, unit gradient and unit
   line velocity then give `gamma' = -grad b`; time reversal followed by
   integral-curve uniqueness identifies the positive-gradient orbit.

`RFreference/` and the Morgan--Tian sources were not imported or edited. The
implementation stays in `DifferentialGeometry/Geometry/Comparison` because it
specializes the generic ODE flow to the geometric Busemann producer.

## Public source exports

- `busemannFlow`
- `busemannFlow_zero`
- `busemannFlow_curve`
- `busemannFlow_add`
- `busemannFlow_smooth`
- `busemannFlow_inner`
- `busemannFlow_value`
- `busemannFlow_line`, with exact statement
  `busemannFlow g hEnorm hgamma hd hRic (-t) (gamma 0) = gamma t`.

Every theorem name is at most twenty characters. No `sorry`, `admit`, axiom,
wrapper predicate, foundational instance, or extra completeness assumption was
introduced.

## Verification state

All eight public exports, including `busemannFlow_inner` and
`busemannFlow_line`, are warning-free
focused GREEN.  The first line-alignment attempt exposed a wrong model glyph,
an over-specific private normal-radius route, the two coexisting manifold and
metric topologies, and time-reversal normal forms.  The final proof uses the
public small-radius distance theorem, the checked metric-to-manifold convergence
bridge, and explicit integral-curve function equalities; no new assumption was
needed.  The downstream-required named refresh containing the new metric
identity is also GREEN.  The upstream `curveAt_contMDiff`,
`curveAt_mfderiv_par`, `curveAt_inner_eq`, and `curveAt_pullback_eq` producers
remain warning-free focused and named-refresh green.

## Project accounting

The formal Cheeger--Gromoll splitting theorem is still unstated and remains
**0%**. The line-alignment and Busemann-flow metric identities are checked
machinery.  Splitting-dedicated machinery is about **90--92%**, whole-P1c
machinery about **80--82%**, and the whole P0--P9 program remains about
**15--25%**.  The regular-level smooth structure, product
diffeomorphism/isometry, and the aligned splitting endpoint remain separate
stages.
