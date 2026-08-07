# LowRegRicciOne

## Route

`ricci1_h2_tame` is the three-dimensional low-regularity producer for the
concrete order-one Ricci connection-difference coefficient.  It separates a
lower `H2` radius `R` from the full `H3` size `A` and returns the affine bound

`B0(R) + B1(R) * A`.

The original one-parameter statement `ricci1_h2` is preserved unchanged as a
compatibility wrapper, obtained by setting `R = A` and restricting the
four-term jet bound to its first three terms.

The proof has three layers:

- the moving four-trace coefficient is controlled in `H2` by `trace2_h2`, so
  this factor depends only on `R`;
- the connection-difference kernel is reduced to the lowered connection
  difference, now using `connLow_tame` in the form
  `Bc0(R) + Bc1(R) * A`; the two slot extensions cost exactly the dimension
  factor and the five permutation arms cost a fixed factor;
- `appRS_h2_h2_h2` composes those two `H2` factors.

Quantitatively, the two exported functions are

```text
B0(R) = Capp * (2 * Bt(R)) * (15 * Bc0(R))
B1(R) = Capp * (2 * Bt(R)) * (15 * Bc1(R)).
```

No derivative above order three and no high-Sobolev ball hypothesis is used.

## Class-first producer

`ricci1_h2_unif` is the three-dimensional class-first companion.  Its public
constant functions are selected from `gBase`, `Λ`, and `δ₀` before the class
metric `g₀` varies.  The class member supplies uniform equivalence and its
first two background-covariant metric-jet bounds; the path perturbation still
uses an `H2` radius `R` and an `H3` radius `A`.

The proof is the literal tame assembly with three constants-first producers:

- `appRS_h22_unif` for the final mixed `H2 × H2 → H2` application;
- `trace2_h2_unif` for the moving four-trace factor;
- `connLow_tame_unif` for the affine lowered connection-difference factor.

It retains the same explicit formulas

```text
B0(R) = Capp * (2 * Bt(R)) * (15 * Bc0(R))
B1(R) = Capp * (2 * Bt(R)) * (15 * Bc1(R)).
```

Focused verification passes without warnings.  The theorem's axiom audit
contains only `propext`, `Classical.choice`, and `Quot.sound`.

## Verification and accounting

The tame theorem, compatibility wrapper, and class-first producer are all
focused-green.  The kernel estimate uses the kernel field's actual `(3,4)`
tensor variance; the adjacent `(4,2)` variance belongs only to the four-trace
coefficient.  No local `sorry`, `admit`, or axiom was introduced.

`ricci_flow_unif_existence` remains 0%; this theorem closes only the Ricci
half of the order-one coefficient input to `rhs1_h2_of_aux`.
