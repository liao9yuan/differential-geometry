# Ricci Flow Mathematical References

This file records local mathematical references that should be checked before
adding new synthetic Ricci-flow machinery. Keep the Hamilton proof plan
separate; this note is for proof sourcing and convention checks.

## Ricci Evolution, Lemma 6.3

Current formalization status: `Evolution/Ricci.lean` has interface plumbing for
the Lichnerowicz-form Ricci evolution equation, but it does not yet prove the
geometric calculation

```text
partial_t Ric_ij = Delta Ric_ij
  + 2 R_{i k j l} Ric^{k l}
  - 2 Ric_i^k Ric_{k j}.
```

The real proof to formalize is:

1. Prove the Christoffel variation formula for a metric variation
   `v_ij = partial_s g_ij`.
2. Derive the Ricci variation formula
   ```text
   partial_s R_ij =
     -1/2 (Delta_L v_ij
       + nabla_i nabla_j V
       - nabla_i (div v)_j
       - nabla_j (div v)_i)
   ```
   with `V = tr_g v`, matching the local sign convention.
3. Substitute Ricci flow, `v = -2 Ric`.
4. Use contracted second Bianchi to cancel the gauge terms:
   ```text
   nabla_i nabla_j R
     - nabla_i (div Ric)_j
     - nabla_j (div Ric)_i = 0.
   ```
5. Expand `Delta_L Ric` using the local convention and Ricci symmetry to get
   the displayed Lemma 6.3 formula.

Primary local references:

- `RicciFlow/main.tex`: local blueprint Lemma 6.3 and Definition 6.4.
- `RicciFlow/RicciFlowBooksLatex/GSM77/tex/chapters/chapter2.tex`:
  - around lines 860-1045: variation of Christoffel and Ricci; formula
    labelled `Rc var deja vu`;
  - around lines 1231-1245: substitution of Ricci flow plus contracted
    Bianchi gives `Ricci evolution all dim`.
- `RicciFlow/RicciFlowBooksLatex/MSM110/tex/MSM110/chapters/chapter3.tex`:
  around lines 1300-1345: Ricci variation as
  `D(Rc_g)(h) = -1/2 Delta_L h - delta^* delta G(h)`.
- `RicciFlow/RicciFlowBooksLatex/GSM235/tex/GRS-Chap-4.tex`:
  around lines 1752-1759 and 2935-2938: Lichnerowicz definition and coordinate
  Ricci evolution formula.

Convention warning:

Do not assume all copied book sources use the same Riemann slot convention as
`RicciFlow/main.tex` or the Lean synthetic `Rm_lowered` definition. Before
turning a book formula into a Lean theorem, check the lowering convention
`Rm_lowered X Y Z W = g(Rm(X,Y)Z,W)`, the Ricci contraction slot, and whether
the term appears as `R_{ikjl} Ric^{kl}` or an equivalent expression after
antisymmetry/block-symmetry rewrites.

