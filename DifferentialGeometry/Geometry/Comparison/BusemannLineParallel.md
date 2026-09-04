# Busemann line: parallel gradient

## Endpoint

`busemann_grad_par` states the native pointwise equation that the Levi-Civita
covariant derivative of the forward Busemann gradient is the zero continuous
linear map.  It uses the same supplied minimizing line, dimension, metric-norm,
and nonnegative-Ricci hypotheses as the existing smoothness and harmonicity
endpoints; no additional predicate or geometric assumption is introduced.

## Mathematical route

1. `busemann_smooth` supplies global smoothness of the forward Busemann
   function.
2. `busemann_grad_sq`, together with the definitional
   `gradient_eq_gradFun` bridge, identifies its squared gradient norm with the
   constant function one.
3. `busemann_lap_zero` supplies the pointwise harmonic equation.  Its existing
   proof already contains the forward/backward Busemann and `Δ_g_neg` argument,
   so that argument is not duplicated here.
4. `Δ_g_congr_of_eventuallyEq` and `Δ_g_const` make the left side of the
   pointwise Bochner identity vanish.  The harmonic equation is first promoted
   to a function equality so that `gradFun` of the Laplacian rewrites to the
   gradient of the constant zero function.
5. `RicciBoundedBelow g 0` gives nonnegativity of the Ricci term, while
   `chartHessFrobeniusSq_nonneg` gives nonnegativity of the Hessian-square term.
   The concrete Bochner identity therefore forces the Hessian-square term to
   vanish.
6. `frobeniusSq_grad_vector_eq_chartHessFrobeniusSq` converts this to vanishing
   of the Frobenius square of the covariant derivative of the gradient, and
   `cov_zero_of_frob` yields the native zero-CLM conclusion.

The necessary positive-dimensional instance is constructed locally from
`2 < finrank`; it is not added to the public assumptions.

## Verification state

The proof is source-written without `sorry`, `admit`, or new axioms.  The first
focused check reached the full proof and failed only because both the operator
and connection namespaces export a `gradFun_const` lemma.  The call is now
qualified with the operator namespace; the statement and mathematical route
are unchanged.  The second focused check passed without warnings; the explicit
named module refresh also completed successfully.  `busemann_grad_par` is now
a verified native producer for the global splitting assembly.

Likely local shape sensitivities are the proof-carrying smooth-map arguments to
`Δ_g`, rewriting the pointwise harmonic equation under `gradFun`, and the
explicit `gradientFun`/`gradFun` bridge used by the eikonal theorem.
