import DifferentialGeometry.Synthetic.Flow.RicciFlow.DimensionThree.Pinching
import DifferentialGeometry.Synthetic.Analysis.Parabolic.ScalarCalculus

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# Improved Ricci Pinching: Maximum-Principle Consumer and Producer

This file keeps the analytic support for Hamilton's improved pinching estimate
small. The heavy quotient-evolution calculation is represented by a narrow
producer structure; once that structure is instantiated, the weak maximum
principle gives the final pinching estimate.

The design deliberately avoids importing the large Sobolev/De Giorgi analysis
subtree. Those files are useful as examples of `rpow` and decay estimates, but
the Ricci-flow layer only needs this narrow subsolution-to-bound step.

The intended P4 proof route is:

1. P3 proves the Hamilton 3D heat equation for `|Ric^0|^2`;
2. a quotient-evolution calculation rewrites
   `P = |Ric^0|^2 / R^(2 - epsilon)` as a scalar subsolution;
3. Lemma 10.8 supplies the `Q` lower bound, making the reaction nonpositive;
4. the scalar weak maximum principle bounds `P`;
5. the quotient algebra below rewrites
   `|Ric^0|^2 / R^2 = P * R^(-epsilon)`;
6. the rescaling/compactness interface supplies decay of `R^(-epsilon)`.

Only steps 2, 3, and 5 are synthetic/algebraic in this branch. Steps 4 and 6
remain analytic interfaces supplied by the collaborator.
-/

section ImprovedPinchingMaximumPrinciple

variable {R Time : Type*}
variable [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]

/-- The reaction expression left after the quotient evolution for
`P = |Ric^0|^2 / R^(2 - epsilon)` and the gradient terms have been put in
maximum-principle form. In Hamilton's calculation it is multiplied by a
nonnegative scalar factor, typically `2 / R^(3 - epsilon)`. -/
def hamiltonPinchingReactionExpression
    (epsilon ricciNormSq tracefreeNormSq cubicQ : R) : R :=
  epsilon * ricciNormSq * tracefreeNormSq - cubicQ

/-- Lemma 10.5 from `RicciFlow/main.tex`, with the power/division
coefficients left abstract.

For `F(phi, psi) = phi^alpha * psi^(-beta)`, the five coefficient slots stand
for

* `phiHeatCoeff = phi^(alpha - 1) / psi^beta`;
* `psiHeatCoeff = phi^alpha / psi^(beta + 1)`;
* `phiGradCoeff = phi^(alpha - 2) / psi^beta`;
* `psiGradCoeff = phi^alpha / psi^(beta + 2)`;
* `mixedGradCoeff = phi^(alpha - 1) / psi^(beta + 1)`.

This is the algebraic RHS of
`(partial_t - Delta)(phi^alpha / psi^beta)`, without choosing a concrete
power API. -/
def quotientEvolutionRHS
    (alpha beta phiHeatCoeff psiHeatCoeff phiGradCoeff psiGradCoeff mixedGradCoeff
      phiHeat psiHeat gradPhiNormSq gradPsiNormSq gradPhiGradPsi : R) : R :=
  alpha * phiHeatCoeff * phiHeat -
    beta * psiHeatCoeff * psiHeat -
    alpha * (alpha - 1) * phiGradCoeff * gradPhiNormSq -
    beta * (beta + 1) * psiGradCoeff * gradPsiNormSq +
    2 * alpha * beta * mixedGradCoeff * gradPhiGradPsi

theorem quotientEvolutionRHS_eval
    (alpha beta phiHeatCoeff psiHeatCoeff phiGradCoeff psiGradCoeff mixedGradCoeff
      phiHeat psiHeat gradPhiNormSq gradPsiNormSq gradPhiGradPsi : R) :
    quotientEvolutionRHS alpha beta phiHeatCoeff psiHeatCoeff phiGradCoeff
        psiGradCoeff mixedGradCoeff phiHeat psiHeat gradPhiNormSq
        gradPsiNormSq gradPhiGradPsi =
      alpha * phiHeatCoeff * phiHeat -
        beta * psiHeatCoeff * psiHeat -
        alpha * (alpha - 1) * phiGradCoeff * gradPhiNormSq -
        beta * (beta + 1) * psiGradCoeff * gradPsiNormSq +
        2 * alpha * beta * mixedGradCoeff * gradPhiGradPsi := by
  rfl

/-- Interface form of Lemma 10.5.

The quotient and coefficient functions are supplied by the realization layer;
this synthetic predicate records the exact five-term chain-rule identity used
to pass from Lemma 10.4 to Hamilton's pinching quantity. -/
def QuotientEvolutionIdentity
    (heat : (Time -> R) -> Time -> R)
    (quotient phi psi phiHeatCoeff psiHeatCoeff phiGradCoeff psiGradCoeff
      mixedGradCoeff gradPhiNormSq gradPsiNormSq gradPhiGradPsi : Time -> R)
    (alpha beta : R) : Prop :=
  forall t,
    heat quotient t =
      quotientEvolutionRHS alpha beta
        (phiHeatCoeff t) (psiHeatCoeff t) (phiGradCoeff t)
        (psiGradCoeff t) (mixedGradCoeff t)
        (heat phi t) (heat psi t)
        (gradPhiNormSq t) (gradPsiNormSq t) (gradPhiGradPsi t)

/-- Algebraic collection helper behind Lemma 10.5.

This helper assumes that the product-rule, power-rule, and cross-gradient
terms have already been rewritten into the coefficient slots of
`quotientEvolutionRHS`. It only collects the five terms.

The public theorem below consumes the reusable `ScalarParabolicCalculus`
product and power rules and then calls this helper. -/
theorem quotientEvolutionIdentity_algebraic_of_rewritten_contributions
    (heat : (Time -> R) -> Time -> R)
    (rho psi rhoPow psiNegPow
      phiHeatCoeff psiHeatCoeff phiGradCoeff psiGradCoeff mixedGradCoeff
      gradPhiNormSq gradPsiNormSq gradPhiGradPsi gradPowInner : Time -> R)
    (alpha beta : R)
    (h_product : forall t,
      heat (fun s => rhoPow s * psiNegPow s) t =
        psiNegPow t * heat rhoPow t +
          rhoPow t * heat psiNegPow t -
          2 * gradPowInner t)
    (h_rho_power : forall t,
      psiNegPow t * heat rhoPow t =
        alpha * phiHeatCoeff t * heat rho t -
          alpha * (alpha - 1) * phiGradCoeff t * gradPhiNormSq t)
    (h_psi_power : forall t,
      rhoPow t * heat psiNegPow t =
        -beta * psiHeatCoeff t * heat psi t -
          beta * (beta + 1) * psiGradCoeff t * gradPsiNormSq t)
    (h_cross : forall t,
      -2 * gradPowInner t =
        2 * alpha * beta * mixedGradCoeff t * gradPhiGradPsi t) :
    QuotientEvolutionIdentity heat (fun s => rhoPow s * psiNegPow s) rho psi
      phiHeatCoeff psiHeatCoeff phiGradCoeff psiGradCoeff mixedGradCoeff
      gradPhiNormSq gradPsiNormSq gradPhiGradPsi alpha beta := by
  intro t
  have h_cross' :
      -(2 * gradPowInner t) =
        2 * alpha * beta * mixedGradCoeff t * gradPhiGradPsi t := by
    simpa [neg_mul] using h_cross t
  rw [h_product t, h_rho_power t, h_psi_power t]
  rw [quotientEvolutionRHS_eval]
  rw [sub_eq_add_neg, h_cross']
  ring

/-- Lemma 10.5 from `RicciFlow/main.tex`, as a reusable scalar parabolic
calculus theorem.

This is the theorem-form version of the displayed proof: `rho` and `psi` are
smooth spacetime functions, `psi` is positive so that negative powers are
available, and the product, power, and gradient-power rules come from the
`ScalarParabolicCalculus` package rather than being proof-specific
hypotheses. -/
theorem quotientEvolutionIdentity_of_scalar_parabolic_calculus
    (P : ScalarParabolicProblem R Time)
    (C : ScalarParabolicCalculus P)
    (rho psi : Time -> R) (alpha beta : R)
    (hrho_smooth : C.Smooth rho) (hpsi_smooth : C.Smooth psi)
    (hrho_pos : C.Positive rho) (hpsi_pos : C.Positive psi) :
    QuotientEvolutionIdentity P.heat
      (fun s => C.pow alpha rho s * C.pow (-beta) psi s)
      rho psi
      (fun t => C.pow (alpha - 1) rho t * C.pow (-beta) psi t)
      (fun t => C.pow alpha rho t * C.pow ((-beta) - 1) psi t)
      (fun t => C.pow (alpha - 2) rho t * C.pow (-beta) psi t)
      (fun t => C.pow alpha rho t * C.pow ((-beta) - 2) psi t)
      (fun t => C.pow (alpha - 1) rho t * C.pow ((-beta) - 1) psi t)
      (C.gradNormSq rho) (C.gradNormSq psi) (C.gradInner rho psi)
      alpha beta := by
  have hrhoPow_smooth : C.Smooth (C.pow alpha rho) :=
    C.smooth_power alpha hrho_smooth hrho_pos
  have hpsiNegPow_smooth : C.Smooth (C.pow (-beta) psi) :=
    C.smooth_power (-beta) hpsi_smooth hpsi_pos
  apply quotientEvolutionIdentity_algebraic_of_rewritten_contributions
    (rhoPow := C.pow alpha rho) (psiNegPow := C.pow (-beta) psi)
    (gradPowInner := C.gradInner (C.pow alpha rho) (C.pow (-beta) psi))
  · intro t
    rw [C.heat_product_rule hrhoPow_smooth hpsiNegPow_smooth t]
    ring
  · intro t
    rw [C.heat_power_rule alpha hrho_smooth hrho_pos t]
    ring
  · intro t
    rw [C.heat_power_rule (-beta) hpsi_smooth hpsi_pos t]
    ring
  · intro t
    rw [C.grad_inner_power_rule alpha (-beta)
      hrho_smooth hrho_pos hpsi_smooth hpsi_pos t]
    ring

/-- Lemma 10.5 in the `alpha = 1` form used by Hamilton's pinching quantity.

This specialization is important because the numerator is
`|Ric^0|^2`, which may vanish. Only the denominator `psi = R` is assumed
positive. The unused `phiGradCoeff` slot is filled by `0`, since the
coefficient `alpha * (alpha - 1)` is zero when `alpha = 1`. -/
theorem quotientEvolutionIdentity_alpha_one_of_scalar_parabolic_calculus
    (P : ScalarParabolicProblem R Time)
    (C : ScalarParabolicCalculus P)
    (rho psi : Time -> R) (beta : R)
    (hrho_smooth : C.Smooth rho) (hpsi_smooth : C.Smooth psi)
    (hpsi_pos : C.Positive psi) :
    QuotientEvolutionIdentity P.heat
      (fun s => rho s * C.pow (-beta) psi s)
      rho psi
      (fun t => C.pow (-beta) psi t)
      (fun t => rho t * C.pow ((-beta) - 1) psi t)
      (fun _ => 0)
      (fun t => rho t * C.pow ((-beta) - 2) psi t)
      (fun t => C.pow ((-beta) - 1) psi t)
      (C.gradNormSq rho) (C.gradNormSq psi) (C.gradInner rho psi)
      (1 : R) beta := by
  have hpsiNegPow_smooth : C.Smooth (C.pow (-beta) psi) :=
    C.smooth_power (-beta) hpsi_smooth hpsi_pos
  apply quotientEvolutionIdentity_algebraic_of_rewritten_contributions
    (rhoPow := rho) (psiNegPow := C.pow (-beta) psi)
    (gradPowInner := C.gradInner rho (C.pow (-beta) psi))
  · intro t
    rw [C.heat_product_rule hrho_smooth hpsiNegPow_smooth t]
    ring
  · intro t
    ring
  · intro t
    rw [C.heat_power_rule (-beta) hpsi_smooth hpsi_pos t]
    ring
  · intro t
    rw [C.grad_inner_power_right_rule (-beta) hrho_smooth hpsi_smooth hpsi_pos t]
    ring

/-- Lemma 10.6 from `RicciFlow/main.tex`, with the scalar-power coefficients
left abstract.

For the intended specialization
`P = |Ric^0|^2 / R^(2 - epsilon)`, the coefficient slots correspond to

* `driftCoeff = 2 * (1 - epsilon) / R`;
* `completedSquareWeight = 2 / R^(4 - epsilon)`;
* `scalarGradientWeight = epsilon * (1 - epsilon) / R^(4 - epsilon)`;
* `reactionWeight = 2 / R^(3 - epsilon)`.

The two negative terms are the completed square
`|R nabla Ric - nabla R tensor Ric|^2` and the leftover scalar-gradient term
`epsilon * (1 - epsilon) * |Ric^0|^2 * |nabla R|^2 / R^(4 - epsilon)`. -/
def hamiltonPinchingEvolutionRHS
    (epsilon driftCoeff gradScalarGradP completedSquareWeight completedSquareNormSq
      scalarGradientWeight tracefreeNormSq gradScalarNormSq reactionWeight
      ricciNormSq cubicQ : R) : R :=
  driftCoeff * gradScalarGradP -
    completedSquareWeight * completedSquareNormSq -
    scalarGradientWeight * tracefreeNormSq * gradScalarNormSq +
    reactionWeight *
      hamiltonPinchingReactionExpression epsilon ricciNormSq tracefreeNormSq cubicQ

theorem hamiltonPinchingEvolutionRHS_eval
    (epsilon driftCoeff gradScalarGradP completedSquareWeight completedSquareNormSq
      scalarGradientWeight tracefreeNormSq gradScalarNormSq reactionWeight
      ricciNormSq cubicQ : R) :
    hamiltonPinchingEvolutionRHS epsilon driftCoeff gradScalarGradP
        completedSquareWeight completedSquareNormSq scalarGradientWeight
        tracefreeNormSq gradScalarNormSq reactionWeight ricciNormSq cubicQ =
      driftCoeff * gradScalarGradP -
        completedSquareWeight * completedSquareNormSq -
        scalarGradientWeight * tracefreeNormSq * gradScalarNormSq +
        reactionWeight *
          hamiltonPinchingReactionExpression epsilon ricciNormSq tracefreeNormSq cubicQ := by
  rfl

/-- Interface form of Lemma 10.6:
`(partial_t - Delta) P` equals the drift term, the two nonpositive completed
gradient terms, and Hamilton's zeroth-order reaction.

The `heat` argument is the unadjusted operator `partial_t - Delta`; later
maximum-principle producers may move the drift into the parabolic operator and
use the two negative terms only through sign hypotheses. -/
def HamiltonPinchingEvolutionEquation
    (heat : (Time -> R) -> Time -> R)
    (P driftCoeff gradScalarGradP completedSquareWeight completedSquareNormSq
      scalarGradientWeight tracefreeNormSq gradScalarNormSq reactionWeight
      ricciNormSq cubicQ : Time -> R)
    (epsilon : R) : Prop :=
  forall t,
    heat P t =
      hamiltonPinchingEvolutionRHS epsilon (driftCoeff t) (gradScalarGradP t)
        (completedSquareWeight t) (completedSquareNormSq t)
        (scalarGradientWeight t) (tracefreeNormSq t) (gradScalarNormSq t)
        (reactionWeight t) (ricciNormSq t) (cubicQ t)

/-- The algebraic step in Hamilton's improved pinching proof: the cubic
`Q`-lower bound and `epsilon <= 2 delta^2` make the remaining reaction
nonpositive. -/
theorem hamiltonPinchingReactionExpression_nonpositive_of_Q_lower_bound
    (epsilon delta ricciNormSq tracefreeNormSq cubicQ : R)
    (h_epsilon : epsilon <= 2 * delta ^ 2)
    (h_product : 0 <= ricciNormSq * tracefreeNormSq)
    (h_Q : 2 * delta ^ 2 * ricciNormSq * tracefreeNormSq <= cubicQ) :
    hamiltonPinchingReactionExpression epsilon ricciNormSq tracefreeNormSq cubicQ <= 0 := by
  unfold hamiltonPinchingReactionExpression
  have h_scaled :
      epsilon * ricciNormSq * tracefreeNormSq <=
        2 * delta ^ 2 * ricciNormSq * tracefreeNormSq := by
    calc
      epsilon * ricciNormSq * tracefreeNormSq =
          epsilon * (ricciNormSq * tracefreeNormSq) := by
        rw [mul_assoc]
      _ <= (2 * delta ^ 2) * (ricciNormSq * tracefreeNormSq) :=
          mul_le_mul_of_nonneg_right h_epsilon h_product
      _ = 2 * delta ^ 2 * ricciNormSq * tracefreeNormSq := by
        exact (mul_assoc (2 * delta ^ 2) ricciNormSq tracefreeNormSq).symm
  exact sub_nonpos.mpr (le_trans h_scaled h_Q)

/-- Weighted form of the same reaction estimate. This is the shape used after
the quotient evolution, where the reaction expression is multiplied by a
nonnegative scalar factor such as `2 / R^(3 - epsilon)`. -/
theorem hamiltonPinchingWeightedReaction_nonpositive_of_Q_lower_bound
    (epsilon delta ricciNormSq tracefreeNormSq cubicQ weight : R)
    (h_epsilon : epsilon <= 2 * delta ^ 2)
    (h_product : 0 <= ricciNormSq * tracefreeNormSq)
    (h_Q : 2 * delta ^ 2 * ricciNormSq * tracefreeNormSq <= cubicQ)
    (h_weight : 0 <= weight) :
    weight *
        hamiltonPinchingReactionExpression epsilon ricciNormSq tracefreeNormSq cubicQ <= 0 := by
  exact mul_nonpos_of_nonneg_of_nonpos h_weight
    (hamiltonPinchingReactionExpression_nonpositive_of_Q_lower_bound
      epsilon delta ricciNormSq tracefreeNormSq cubicQ h_epsilon h_product h_Q)

/-- Data for the maximum-principle part of Hamilton's improved Ricci pinching
estimate. `P` is the Hamilton quantity
`|Ric^0|^2 / R^(2 - epsilon)`. `ratio` is the scale-invariant quantity
`|Ric^0|^2 / R^2`, and `decay` is the factor intended to be `R^(-epsilon)`.

The theorem below uses only the weak maximum principle. The geometric work is
to instantiate `shifted_subsolution`, `initial_bound`, and
`ratio_decay_relation` from the Ricci-flow evolution identities. In the
intended Ricci-flow instantiation, `ratio` is
`tracefreeRicciPinchingQuantity`, `decay` is `R^(-epsilon)`, and the relation
comes from an equality under positive scalar curvature; the consumer theorem
only needs the weaker inequality. -/
structure ImprovedRicciPinchingEstimateAlongFlow where
  problem : ScalarParabolicProblem R Time
  P : Time -> R
  ratio : Time -> R
  epsilon : R
  C : R
  decay : Time -> R
  shifted_subsolution : IsScalarSubsolution problem (fun t => P t - C)
  initial_bound : IsInitiallyNonpositive problem (fun t => P t - C)
  ratio_decay_relation :
    forall t, problem.domain t -> ratio t <= P t * decay t
  decay_nonnegative : forall t, problem.domain t -> 0 <= decay t

/-- Producer data for the improved pinching maximum-principle estimate.

The quotient-evolution calculation is represented by `shifted_heat_eq_reaction`.
It should be instantiated by the future theorem proving the evolution of
`P = |Ric^0|^2 / R^(2 - epsilon)`: after gradient terms are put in
maximum-principle form, the heat operator applied to `P - C` equals a
nonnegative weight times
`epsilon * |Ric|^2 * |Ric^0|^2 - Q`.

The fields `cubicQ_lower_bound`, `epsilon_le`, and
`reaction_product_nonnegative` are the algebraic part of Lemma 10.8. They
automatically turn that heat equality into the scalar subsolution required by
the weak maximum principle. -/
structure HamiltonImprovedPinchingProducerData where
  problem : ScalarParabolicProblem R Time
  P : Time -> R
  ratio : Time -> R
  epsilon : R
  delta : R
  C : R
  decay : Time -> R
  ricciNormSq : Time -> R
  tracefreeNormSq : Time -> R
  cubicQ : Time -> R
  reactionWeight : Time -> R
  epsilon_le : epsilon <= 2 * delta ^ 2
  reaction_product_nonnegative :
    forall t, problem.domain t -> 0 <= ricciNormSq t * tracefreeNormSq t
  cubicQ_lower_bound :
    forall t, problem.domain t ->
      2 * delta ^ 2 * ricciNormSq t * tracefreeNormSq t <= cubicQ t
  reactionWeight_nonnegative :
    forall t, problem.domain t -> 0 <= reactionWeight t
  shifted_heat_eq_reaction :
    forall t, problem.domain t ->
      problem.heat (fun s => P s - C) t =
        reactionWeight t *
          hamiltonPinchingReactionExpression epsilon
            (ricciNormSq t) (tracefreeNormSq t) (cubicQ t)
  initial_bound : IsInitiallyNonpositive problem (fun t => P t - C)
  ratio_decay_relation :
    forall t, problem.domain t -> ratio t <= P t * decay t
  decay_nonnegative : forall t, problem.domain t -> 0 <= decay t

/-- Quotient-evolution handoff for Hamilton's improved pinching quantity.

`tracefreeNormSq` is the numerator `|Ric^0|^2`. `denomP` is the abstract
denominator intended to be `R^(2 - epsilon)`, so `P = |Ric^0|^2 / denomP`.
The file deliberately does not choose an `rpow` API.

The field `quotient_heat_eq_reaction` is the chain-rule and
gradient-square-completion calculation for the quotient. The field
`shifted_heat_eq_heat_P` records the harmless shift by the constant `C`, since
the abstract `ScalarParabolicProblem.heat` interface has no built-in linearity
axiom. -/
structure HamiltonPinchingQuotientEvolutionData where
  problem : ScalarParabolicProblem R Time
  tracefreeNormSq : Time -> R
  denomP : Time -> R
  P : Time -> R
  ratio : Time -> R
  epsilon : R
  C : R
  decay : Time -> R
  ricciNormSq : Time -> R
  cubicQ : Time -> R
  reactionWeight : Time -> R
  denomP_nonzero : forall t, problem.domain t -> denomP t ≠ 0
  P_mul_denomP_eq : forall t, problem.domain t -> P t * denomP t = tracefreeNormSq t
  shifted_heat_eq_heat_P :
    forall t, problem.domain t -> problem.heat (fun s => P s - C) t = problem.heat P t
  quotient_heat_eq_reaction :
    forall t, problem.domain t ->
      problem.heat P t =
        reactionWeight t *
          hamiltonPinchingReactionExpression epsilon
            (ricciNormSq t) (tracefreeNormSq t) (cubicQ t)

/-- Drift-adjusted handoff from Lemma 10.6 to the maximum-principle producer.

Lemma 10.6 gives the bare heat equation for Hamilton's pinching quantity:

```text
bareHeat P =
  drift - completedSquare - scalarGradient + reactionWeight * (epsilon |Ric|^2 |Ric^0|^2 - Q).
```

For the weak maximum principle one moves the drift and nonpositive gradient
terms into the operator applied to `P - C`. The field
`shifted_adjusted_heat_eq` records that adjusted operator. The theorem below
then extracts exactly the reaction identity expected by
`HamiltonImprovedPinchingProducerData`.

This is the formal boundary between the displayed Lemma 10.6 calculation and
the scalar maximum-principle producer. The actual quotient evolution and
gradient-square completion still have to instantiate `evolution_eq` and
`shifted_adjusted_heat_eq`. -/
structure HamiltonPinchingAdjustedEvolutionData where
  problem : ScalarParabolicProblem R Time
  bareHeat : (Time -> R) -> Time -> R
  tracefreeNormSq : Time -> R
  denomP : Time -> R
  P : Time -> R
  ratio : Time -> R
  epsilon : R
  C : R
  decay : Time -> R
  ricciNormSq : Time -> R
  cubicQ : Time -> R
  driftCoeff : Time -> R
  gradScalarGradP : Time -> R
  completedSquareWeight : Time -> R
  completedSquareNormSq : Time -> R
  scalarGradientWeight : Time -> R
  gradScalarNormSq : Time -> R
  reactionWeight : Time -> R
  denomP_nonzero : forall t, problem.domain t -> denomP t ≠ 0
  P_mul_denomP_eq : forall t, problem.domain t -> P t * denomP t = tracefreeNormSq t
  evolution_eq :
    HamiltonPinchingEvolutionEquation bareHeat P driftCoeff gradScalarGradP
      completedSquareWeight completedSquareNormSq scalarGradientWeight
      tracefreeNormSq gradScalarNormSq reactionWeight ricciNormSq cubicQ epsilon
  shifted_adjusted_heat_eq :
    forall t, problem.domain t ->
      problem.heat (fun s => P s - C) t =
        bareHeat P t - driftCoeff t * gradScalarGradP t +
          completedSquareWeight t * completedSquareNormSq t +
            scalarGradientWeight t * tracefreeNormSq t * gradScalarNormSq t

/-- The quotient-evolution handoff produces exactly the shifted heat identity
expected by `HamiltonImprovedPinchingProducerData`. -/
theorem shifted_heat_eq_reaction_of_quotient_evolution
    (D : HamiltonPinchingQuotientEvolutionData (R := R) (Time := Time)) :
    forall t, D.problem.domain t ->
      D.problem.heat (fun s => D.P s - D.C) t =
        D.reactionWeight t *
          hamiltonPinchingReactionExpression D.epsilon
            (D.ricciNormSq t) (D.tracefreeNormSq t) (D.cubicQ t) := by
  intro t ht
  rw [D.shifted_heat_eq_heat_P t ht, D.quotient_heat_eq_reaction t ht]

/-- The drift-adjusted Lemma 10.6 handoff produces exactly the shifted heat
identity expected by `HamiltonImprovedPinchingProducerData`. -/
theorem shifted_heat_eq_reaction_of_adjusted_pinching_evolution
    (D : HamiltonPinchingAdjustedEvolutionData (R := R) (Time := Time)) :
    forall t, D.problem.domain t ->
      D.problem.heat (fun s => D.P s - D.C) t =
        D.reactionWeight t *
          hamiltonPinchingReactionExpression D.epsilon
            (D.ricciNormSq t) (D.tracefreeNormSq t) (D.cubicQ t) := by
  intro t ht
  rw [D.shifted_adjusted_heat_eq t ht, D.evolution_eq t]
  rw [hamiltonPinchingEvolutionRHS_eval]
  ring

/-- Build the Hamilton P4 maximum-principle producer from a quotient-evolution
calculation and the remaining sign, initial-bound, and ratio-decay inputs.

This is the main synthetic P4 producer. It keeps analytic facts such as the
weak maximum principle, the preserved pinching cone, and rescaling decay out of
the quotient calculation. -/
def hamilton_improved_pinching_producer_data_of_quotient_evolution
    (D : HamiltonPinchingQuotientEvolutionData (R := R) (Time := Time))
    (delta : R)
    (epsilon_le : D.epsilon <= 2 * delta ^ 2)
    (reaction_product_nonnegative :
      forall t, D.problem.domain t -> 0 <= D.ricciNormSq t * D.tracefreeNormSq t)
    (cubicQ_lower_bound :
      forall t, D.problem.domain t ->
        2 * delta ^ 2 * D.ricciNormSq t * D.tracefreeNormSq t <= D.cubicQ t)
    (reactionWeight_nonnegative :
      forall t, D.problem.domain t -> 0 <= D.reactionWeight t)
    (initial_bound : IsInitiallyNonpositive D.problem (fun t => D.P t - D.C))
    (ratio_decay_relation :
      forall t, D.problem.domain t -> D.ratio t <= D.P t * D.decay t)
    (decay_nonnegative : forall t, D.problem.domain t -> 0 <= D.decay t) :
    HamiltonImprovedPinchingProducerData (R := R) (Time := Time) where
  problem := D.problem
  P := D.P
  ratio := D.ratio
  epsilon := D.epsilon
  delta := delta
  C := D.C
  decay := D.decay
  ricciNormSq := D.ricciNormSq
  tracefreeNormSq := D.tracefreeNormSq
  cubicQ := D.cubicQ
  reactionWeight := D.reactionWeight
  epsilon_le := epsilon_le
  reaction_product_nonnegative := reaction_product_nonnegative
  cubicQ_lower_bound := cubicQ_lower_bound
  reactionWeight_nonnegative := reactionWeight_nonnegative
  shifted_heat_eq_reaction :=
    shifted_heat_eq_reaction_of_quotient_evolution D
  initial_bound := initial_bound
  ratio_decay_relation := ratio_decay_relation
  decay_nonnegative := decay_nonnegative

/-- Build the Hamilton P4 maximum-principle producer from the drift-adjusted
Lemma 10.6 handoff.

Use this constructor once the quotient evolution and gradient-square completion
have produced `HamiltonPinchingAdjustedEvolutionData`. It is closer to the
displayed `main.tex` proof than `hamilton_improved_pinching_producer_data_of_quotient_evolution`:
the bare Lemma 10.6 equation may still contain drift and negative square terms,
and the adjusted operator removes them before applying the scalar weak maximum
principle. -/
def hamilton_improved_pinching_producer_data_of_adjusted_pinching_evolution
    (D : HamiltonPinchingAdjustedEvolutionData (R := R) (Time := Time))
    (delta : R)
    (epsilon_le : D.epsilon <= 2 * delta ^ 2)
    (reaction_product_nonnegative :
      forall t, D.problem.domain t -> 0 <= D.ricciNormSq t * D.tracefreeNormSq t)
    (cubicQ_lower_bound :
      forall t, D.problem.domain t ->
        2 * delta ^ 2 * D.ricciNormSq t * D.tracefreeNormSq t <= D.cubicQ t)
    (reactionWeight_nonnegative :
      forall t, D.problem.domain t -> 0 <= D.reactionWeight t)
    (initial_bound : IsInitiallyNonpositive D.problem (fun t => D.P t - D.C))
    (ratio_decay_relation :
      forall t, D.problem.domain t -> D.ratio t <= D.P t * D.decay t)
    (decay_nonnegative : forall t, D.problem.domain t -> 0 <= D.decay t) :
    HamiltonImprovedPinchingProducerData (R := R) (Time := Time) where
  problem := D.problem
  P := D.P
  ratio := D.ratio
  epsilon := D.epsilon
  delta := delta
  C := D.C
  decay := D.decay
  ricciNormSq := D.ricciNormSq
  tracefreeNormSq := D.tracefreeNormSq
  cubicQ := D.cubicQ
  reactionWeight := D.reactionWeight
  epsilon_le := epsilon_le
  reaction_product_nonnegative := reaction_product_nonnegative
  cubicQ_lower_bound := cubicQ_lower_bound
  reactionWeight_nonnegative := reactionWeight_nonnegative
  shifted_heat_eq_reaction :=
    shifted_heat_eq_reaction_of_adjusted_pinching_evolution D
  initial_bound := initial_bound
  ratio_decay_relation := ratio_decay_relation
  decay_nonnegative := decay_nonnegative

/-- The producer data imply the scalar subsolution needed by the weak maximum
principle. This is the first closed part of P4: the quotient evolution and
Hamilton's `Q` lower bound have exactly the right sign. -/
theorem hamilton_improved_pinching_shifted_subsolution
    (D : HamiltonImprovedPinchingProducerData (R := R) (Time := Time)) :
    IsScalarSubsolution D.problem (fun t => D.P t - D.C) := by
  intro t ht
  rw [D.shifted_heat_eq_reaction t ht]
  exact hamiltonPinchingWeightedReaction_nonpositive_of_Q_lower_bound
    D.epsilon D.delta (D.ricciNormSq t) (D.tracefreeNormSq t) (D.cubicQ t)
    (D.reactionWeight t) D.epsilon_le (D.reaction_product_nonnegative t ht)
    (D.cubicQ_lower_bound t ht) (D.reactionWeight_nonnegative t ht)

/-- P4-facing constructor for Hamilton's improved Ricci pinching estimate.

The hard geometric work is to prove `shifted_subsolution` from the
trace-free Ricci evolution identity, the cubic `Q` lower bound, scalar
positivity, and preservation of the `Ric >= delta R g` cone. This theorem
packages those inputs into the reusable maximum-principle data structure. -/
def improved_ricci_pinching_estimate_along_flow_of_subsolution_data
    (problem : ScalarParabolicProblem R Time)
    (P ratio : Time -> R) (epsilon C : R) (decay : Time -> R)
    (shifted_subsolution : IsScalarSubsolution problem (fun t => P t - C))
    (initial_bound : IsInitiallyNonpositive problem (fun t => P t - C))
    (ratio_decay_relation :
      forall t, problem.domain t -> ratio t <= P t * decay t)
    (decay_nonnegative : forall t, problem.domain t -> 0 <= decay t) :
    ImprovedRicciPinchingEstimateAlongFlow (R := R) (Time := Time) where
  problem := problem
  P := P
  ratio := ratio
  epsilon := epsilon
  C := C
  decay := decay
  shifted_subsolution := shifted_subsolution
  initial_bound := initial_bound
  ratio_decay_relation := ratio_decay_relation
  decay_nonnegative := decay_nonnegative

/-- Build the maximum-principle pinching estimate from Hamilton quotient
producer data. The remaining future realization work is exactly to instantiate
`HamiltonImprovedPinchingProducerData` from the trace-free Ricci evolution,
quotient evolution, scalar positivity, and the preserved Ricci pinching cone. -/
def improved_ricci_pinching_estimate_along_flow_of_hamilton_producer
    (D : HamiltonImprovedPinchingProducerData (R := R) (Time := Time)) :
    ImprovedRicciPinchingEstimateAlongFlow (R := R) (Time := Time) where
  problem := D.problem
  P := D.P
  ratio := D.ratio
  epsilon := D.epsilon
  C := D.C
  decay := D.decay
  shifted_subsolution := hamilton_improved_pinching_shifted_subsolution D
  initial_bound := D.initial_bound
  ratio_decay_relation := D.ratio_decay_relation
  decay_nonnegative := D.decay_nonnegative

/-- The weak maximum principle gives the uniform bound `P <= C`. -/
theorem improved_pinching_P_bound_from_wmp
    [ScalarWeakMaximumPrinciple R Time]
    (E : ImprovedRicciPinchingEstimateAlongFlow (R := R) (Time := Time))
    (t : Time) (ht : E.problem.domain t) :
    E.P t <= E.C :=
  scalar_wmp_preserve_upper_bound E.problem E.P E.C E.shifted_subsolution
    E.initial_bound t ht

/-- The Section 12 ratio estimate
`|Ric^0|^2 / R^2 <= C * R^(-epsilon)`, stated with an abstract decay factor. -/
theorem improved_ricci_pinching_ratio_bound_from_wmp
    [ScalarWeakMaximumPrinciple R Time]
    (E : ImprovedRicciPinchingEstimateAlongFlow (R := R) (Time := Time))
    (t : Time) (ht : E.problem.domain t) :
    E.ratio t <= E.C * E.decay t := by
  exact (E.ratio_decay_relation t ht).trans
    (mul_le_mul_of_nonneg_right
      (improved_pinching_P_bound_from_wmp E t ht) (E.decay_nonnegative t ht))

/-- Direct P4 estimate from the Hamilton quotient producer and the scalar weak
maximum principle. -/
theorem improved_ricci_pinching_ratio_bound_from_hamilton_producer
    [ScalarWeakMaximumPrinciple R Time]
    (D : HamiltonImprovedPinchingProducerData (R := R) (Time := Time))
    (t : Time) (ht : D.problem.domain t) :
    D.ratio t <= D.C * D.decay t := by
  exact improved_ricci_pinching_ratio_bound_from_wmp
    (improved_ricci_pinching_estimate_along_flow_of_hamilton_producer D) t ht

end ImprovedPinchingMaximumPrinciple

section ImprovedPinchingEvolutionCalculation

variable {R Time : Type*}
variable [Field R] [LinearOrder R] [IsStrictOrderedRing R]

/-- Pointwise reaction collection in the proof of Lemma 10.6.

After Lemma 10.5 is applied with `alpha = 1` and `beta = 2 - epsilon`, the
zeroth-order terms are

```text
phiCoeff * (4 |Ric|^2 A - 2 Q) / R
  - (2 - epsilon) * psiCoeff * (2 |Ric|^2).
```

The two coefficient identities are the abstract-power version of
`phiCoeff = R^(-(2-epsilon))`, `psiCoeff = A R^(-(3-epsilon))`, and
`reactionWeight = 2 R^(-(3-epsilon))`. With those identities, the displayed
terms collect to

```text
reactionWeight * (epsilon * |Ric|^2 * A - Q).
``` -/
theorem hamiltonPinchingReaction_collect_of_coefficients
    (epsilon scalar phiCoeff psiCoeff reactionWeight ricciNormSq tracefreeNormSq cubicQ : R)
    (h_scalar_ne : scalar ≠ 0)
    (h_phiCoeff : 2 * phiCoeff = reactionWeight * scalar)
    (h_psiCoeff : 2 * psiCoeff = reactionWeight * tracefreeNormSq) :
    phiCoeff * ((4 * ricciNormSq * tracefreeNormSq - 2 * cubicQ) / scalar) -
        (2 - epsilon) * psiCoeff * (2 * ricciNormSq) =
      reactionWeight *
        hamiltonPinchingReactionExpression epsilon ricciNormSq tracefreeNormSq cubicQ := by
  have htwo : (2 : R) ≠ 0 := by
    exact two_ne_zero
  have h_phiCoeff' : phiCoeff = reactionWeight * scalar / 2 := by
    rw [eq_div_iff htwo]
    simpa [mul_comm] using h_phiCoeff
  have h_psiCoeff' : psiCoeff = reactionWeight * tracefreeNormSq / 2 := by
    rw [eq_div_iff htwo]
    simpa [mul_comm] using h_psiCoeff
  rw [h_phiCoeff', h_psiCoeff']
  unfold hamiltonPinchingReactionExpression
  field_simp [h_scalar_ne, htwo]
  ring

/-- Lemma 10.6 from Lemma 10.5 plus the Hamilton trace-free norm and scalar
heat equations.

This theorem is the direct calculation layer. It does not choose a concrete
power API; instead it consumes the coefficient identities produced by whatever
positive scalar-curvature power convention the realization uses. The only
non-scalar-calculus input left is `h_gradient_completion`, the completed-square
identity for the gradient terms in Lemma 10.6. -/
theorem hamiltonPinchingEvolutionEquation_of_quotient_identity
    (heat : (Time -> R) -> Time -> R)
    (P tracefreeNormSq scalar phiHeatCoeff psiHeatCoeff phiGradCoeff psiGradCoeff
      mixedGradCoeff gradTracefreeNormSq gradScalarNormSq gradTracefreeGradScalar
      nablaRicNormSq ricciNormSq cubicQ driftCoeff gradScalarGradP completedSquareWeight
      completedSquareNormSq scalarGradientWeight reactionWeight : Time -> R)
    (epsilon : R)
    (h_quotient :
      QuotientEvolutionIdentity heat P tracefreeNormSq scalar
        phiHeatCoeff psiHeatCoeff phiGradCoeff psiGradCoeff mixedGradCoeff
        gradTracefreeNormSq gradScalarNormSq gradTracefreeGradScalar
        (1 : R) (2 - epsilon))
    (h_tracefree_heat : forall t,
      heat tracefreeNormSq t =
        -2 * nablaRicNormSq t + ((2 : R) / 3) * gradScalarNormSq t +
          (4 * ricciNormSq t * tracefreeNormSq t - 2 * cubicQ t) / scalar t)
    (h_scalar_heat : forall t,
      heat scalar t = 2 * ricciNormSq t)
    (h_scalar_ne : forall t, scalar t ≠ 0)
    (h_phiCoeff : forall t,
      2 * phiHeatCoeff t = reactionWeight t * scalar t)
    (h_psiCoeff : forall t,
      2 * psiHeatCoeff t = reactionWeight t * tracefreeNormSq t)
    (h_gradient_completion : forall t,
      phiHeatCoeff t *
          (-2 * nablaRicNormSq t + ((2 : R) / 3) * gradScalarNormSq t) -
        (2 - epsilon) * ((2 - epsilon) + 1) * psiGradCoeff t * gradScalarNormSq t +
        2 * (2 - epsilon) * mixedGradCoeff t * gradTracefreeGradScalar t =
          driftCoeff t * gradScalarGradP t -
            completedSquareWeight t * completedSquareNormSq t -
            scalarGradientWeight t * tracefreeNormSq t * gradScalarNormSq t) :
    HamiltonPinchingEvolutionEquation heat P driftCoeff gradScalarGradP
      completedSquareWeight completedSquareNormSq scalarGradientWeight
      tracefreeNormSq gradScalarNormSq reactionWeight ricciNormSq cubicQ epsilon := by
  intro t
  have h_reaction :
      phiHeatCoeff t *
            ((4 * ricciNormSq t * tracefreeNormSq t - 2 * cubicQ t) / scalar t) -
          (2 - epsilon) * psiHeatCoeff t * (2 * ricciNormSq t) =
        reactionWeight t *
          hamiltonPinchingReactionExpression epsilon
            (ricciNormSq t) (tracefreeNormSq t) (cubicQ t) :=
    hamiltonPinchingReaction_collect_of_coefficients
      epsilon (scalar t) (phiHeatCoeff t) (psiHeatCoeff t) (reactionWeight t)
      (ricciNormSq t) (tracefreeNormSq t) (cubicQ t)
      (h_scalar_ne t) (h_phiCoeff t) (h_psiCoeff t)
  rw [h_quotient t, quotientEvolutionRHS_eval, h_tracefree_heat t, h_scalar_heat t]
  rw [hamiltonPinchingEvolutionRHS_eval]
  calc
    1 * phiHeatCoeff t *
          (-2 * nablaRicNormSq t + (2 / 3) * gradScalarNormSq t +
            (4 * ricciNormSq t * tracefreeNormSq t - 2 * cubicQ t) / scalar t) -
        (2 - epsilon) * psiHeatCoeff t * (2 * ricciNormSq t) -
        1 * (1 - 1) * phiGradCoeff t * gradTracefreeNormSq t -
        (2 - epsilon) * ((2 - epsilon) + 1) * psiGradCoeff t * gradScalarNormSq t +
        2 * 1 * (2 - epsilon) * mixedGradCoeff t * gradTracefreeGradScalar t
        =
      (phiHeatCoeff t *
          (-2 * nablaRicNormSq t + ((2 : R) / 3) * gradScalarNormSq t) -
        (2 - epsilon) * ((2 - epsilon) + 1) * psiGradCoeff t * gradScalarNormSq t +
        2 * (2 - epsilon) * mixedGradCoeff t * gradTracefreeGradScalar t) +
      (phiHeatCoeff t *
            ((4 * ricciNormSq t * tracefreeNormSq t - 2 * cubicQ t) / scalar t) -
          (2 - epsilon) * psiHeatCoeff t * (2 * ricciNormSq t)) := by
        ring
    _ =
      (driftCoeff t * gradScalarGradP t -
            completedSquareWeight t * completedSquareNormSq t -
            scalarGradientWeight t * tracefreeNormSq t * gradScalarNormSq t) +
        reactionWeight t *
          hamiltonPinchingReactionExpression epsilon
            (ricciNormSq t) (tracefreeNormSq t) (cubicQ t) := by
        rw [h_gradient_completion t, h_reaction]
    _ =
      driftCoeff t * gradScalarGradP t -
        completedSquareWeight t * completedSquareNormSq t -
        scalarGradientWeight t * tracefreeNormSq t * gradScalarNormSq t +
        reactionWeight t *
          hamiltonPinchingReactionExpression epsilon
            (ricciNormSq t) (tracefreeNormSq t) (cubicQ t) := by
        ring

/-- Direct constructor for the Lemma 10.6 handoff data from the quotient
identity of Lemma 10.5, the trace-free norm heat equation of Lemma 10.4, and
the scalar heat equation. -/
def hamiltonPinchingAdjustedEvolutionData_of_quotient_identity
    (problem : ScalarParabolicProblem R Time)
    (bareHeat : (Time -> R) -> Time -> R)
    (tracefreeNormSq scalar denomP P ratio : Time -> R)
    (epsilon C : R) (decay ricciNormSq cubicQ : Time -> R)
    (driftCoeff gradScalarGradP completedSquareWeight completedSquareNormSq
      scalarGradientWeight gradScalarNormSq reactionWeight : Time -> R)
    (phiHeatCoeff psiHeatCoeff phiGradCoeff psiGradCoeff mixedGradCoeff
      gradTracefreeNormSq gradTracefreeGradScalar nablaRicNormSq : Time -> R)
    (denomP_nonzero : forall t, problem.domain t -> denomP t ≠ 0)
    (P_mul_denomP_eq : forall t, problem.domain t -> P t * denomP t = tracefreeNormSq t)
    (h_quotient :
      QuotientEvolutionIdentity bareHeat P tracefreeNormSq scalar
        phiHeatCoeff psiHeatCoeff phiGradCoeff psiGradCoeff mixedGradCoeff
        gradTracefreeNormSq gradScalarNormSq gradTracefreeGradScalar
        (1 : R) (2 - epsilon))
    (h_tracefree_heat : forall t,
      bareHeat tracefreeNormSq t =
        -2 * nablaRicNormSq t + ((2 : R) / 3) * gradScalarNormSq t +
          (4 * ricciNormSq t * tracefreeNormSq t - 2 * cubicQ t) / scalar t)
    (h_scalar_heat : forall t,
      bareHeat scalar t = 2 * ricciNormSq t)
    (h_scalar_ne : forall t, scalar t ≠ 0)
    (h_phiCoeff : forall t,
      2 * phiHeatCoeff t = reactionWeight t * scalar t)
    (h_psiCoeff : forall t,
      2 * psiHeatCoeff t = reactionWeight t * tracefreeNormSq t)
    (h_gradient_completion : forall t,
      phiHeatCoeff t *
          (-2 * nablaRicNormSq t + ((2 : R) / 3) * gradScalarNormSq t) -
        (2 - epsilon) * ((2 - epsilon) + 1) * psiGradCoeff t * gradScalarNormSq t +
        2 * (2 - epsilon) * mixedGradCoeff t * gradTracefreeGradScalar t =
          driftCoeff t * gradScalarGradP t -
            completedSquareWeight t * completedSquareNormSq t -
            scalarGradientWeight t * tracefreeNormSq t * gradScalarNormSq t)
    (shifted_adjusted_heat_eq :
      forall t, problem.domain t ->
        problem.heat (fun s => P s - C) t =
          bareHeat P t - driftCoeff t * gradScalarGradP t +
            completedSquareWeight t * completedSquareNormSq t +
              scalarGradientWeight t * tracefreeNormSq t * gradScalarNormSq t) :
    HamiltonPinchingAdjustedEvolutionData (R := R) (Time := Time) where
  problem := problem
  bareHeat := bareHeat
  tracefreeNormSq := tracefreeNormSq
  denomP := denomP
  P := P
  ratio := ratio
  epsilon := epsilon
  C := C
  decay := decay
  ricciNormSq := ricciNormSq
  cubicQ := cubicQ
  driftCoeff := driftCoeff
  gradScalarGradP := gradScalarGradP
  completedSquareWeight := completedSquareWeight
  completedSquareNormSq := completedSquareNormSq
  scalarGradientWeight := scalarGradientWeight
  gradScalarNormSq := gradScalarNormSq
  reactionWeight := reactionWeight
  denomP_nonzero := denomP_nonzero
  P_mul_denomP_eq := P_mul_denomP_eq
  evolution_eq :=
    hamiltonPinchingEvolutionEquation_of_quotient_identity bareHeat P
      tracefreeNormSq scalar phiHeatCoeff psiHeatCoeff phiGradCoeff psiGradCoeff
      mixedGradCoeff gradTracefreeNormSq gradScalarNormSq gradTracefreeGradScalar
      nablaRicNormSq ricciNormSq cubicQ driftCoeff gradScalarGradP
      completedSquareWeight completedSquareNormSq scalarGradientWeight reactionWeight
      epsilon h_quotient h_tracefree_heat h_scalar_heat h_scalar_ne h_phiCoeff
      h_psiCoeff h_gradient_completion
  shifted_adjusted_heat_eq := shifted_adjusted_heat_eq

/-- Direct P4 constructor from scalar parabolic calculus and the geometric
heat inputs.

This is the `alpha = 1`, `beta = 2 - epsilon` specialization of Lemma 10.5
used in Lemma 10.6. It intentionally assumes positivity only for the scalar
curvature denominator `scalar`; the numerator `tracefreeNormSq = |Ric^0|^2`
may vanish. Power-law coefficient identities remain explicit because the
power operation in `ScalarParabolicCalculus` is abstract. -/
def hamiltonPinchingAdjustedEvolutionData_of_tracefree_heat_and_scalar_calculus
    (problem bareProblem : ScalarParabolicProblem R Time)
    (Calc : ScalarParabolicCalculus bareProblem)
    (tracefreeNormSq scalar denomP ratio : Time -> R)
    (epsilon bound : R) (decay ricciNormSq cubicQ : Time -> R)
    (driftCoeff gradScalarGradP completedSquareWeight completedSquareNormSq
      scalarGradientWeight reactionWeight : Time -> R)
    (nablaRicNormSq : Time -> R)
    (h_tracefree_smooth : Calc.Smooth tracefreeNormSq)
    (h_scalar_smooth : Calc.Smooth scalar)
    (h_scalar_pos : Calc.Positive scalar)
    (denomP_nonzero : forall t, problem.domain t -> denomP t ≠ 0)
    (P_mul_denomP_eq : forall t, problem.domain t ->
      (tracefreeNormSq t * Calc.pow (-(2 - epsilon)) scalar t) * denomP t =
        tracefreeNormSq t)
    (h_tracefree_heat : forall t,
      bareProblem.heat tracefreeNormSq t =
        -2 * nablaRicNormSq t + ((2 : R) / 3) * Calc.gradNormSq scalar t +
          (4 * ricciNormSq t * tracefreeNormSq t - 2 * cubicQ t) / scalar t)
    (h_scalar_heat : forall t,
      bareProblem.heat scalar t = 2 * ricciNormSq t)
    (h_scalar_ne : forall t, scalar t ≠ 0)
    (h_phiCoeff : forall t,
      2 * Calc.pow (-(2 - epsilon)) scalar t = reactionWeight t * scalar t)
    (h_psiCoeff : forall t,
      2 * (tracefreeNormSq t * Calc.pow (-(2 - epsilon) - 1) scalar t) =
        reactionWeight t * tracefreeNormSq t)
    (h_gradient_completion : forall t,
      Calc.pow (-(2 - epsilon)) scalar t *
          (-2 * nablaRicNormSq t + ((2 : R) / 3) * Calc.gradNormSq scalar t) -
        (2 - epsilon) * ((2 - epsilon) + 1) *
            (tracefreeNormSq t * Calc.pow (-(2 - epsilon) - 2) scalar t) *
            Calc.gradNormSq scalar t +
        2 * (2 - epsilon) * Calc.pow (-(2 - epsilon) - 1) scalar t *
            Calc.gradInner tracefreeNormSq scalar t =
          driftCoeff t * gradScalarGradP t -
            completedSquareWeight t * completedSquareNormSq t -
            scalarGradientWeight t * tracefreeNormSq t * Calc.gradNormSq scalar t)
    (shifted_adjusted_heat_eq :
      forall t, problem.domain t ->
        problem.heat
            (fun s => tracefreeNormSq s * Calc.pow (-(2 - epsilon)) scalar s - bound) t =
          bareProblem.heat
              (fun s => tracefreeNormSq s * Calc.pow (-(2 - epsilon)) scalar s) t -
            driftCoeff t * gradScalarGradP t +
              completedSquareWeight t * completedSquareNormSq t +
                scalarGradientWeight t * tracefreeNormSq t * Calc.gradNormSq scalar t) :
    HamiltonPinchingAdjustedEvolutionData (R := R) (Time := Time) :=
  hamiltonPinchingAdjustedEvolutionData_of_quotient_identity problem bareProblem.heat
    tracefreeNormSq scalar denomP
    (fun t => tracefreeNormSq t * Calc.pow (-(2 - epsilon)) scalar t)
    ratio epsilon bound decay ricciNormSq cubicQ driftCoeff gradScalarGradP
    completedSquareWeight completedSquareNormSq scalarGradientWeight (Calc.gradNormSq scalar)
    reactionWeight
    (fun t => Calc.pow (-(2 - epsilon)) scalar t)
    (fun t => tracefreeNormSq t * Calc.pow (-(2 - epsilon) - 1) scalar t)
    (fun _ => 0)
    (fun t => tracefreeNormSq t * Calc.pow (-(2 - epsilon) - 2) scalar t)
    (fun t => Calc.pow (-(2 - epsilon) - 1) scalar t)
    (Calc.gradNormSq tracefreeNormSq) (Calc.gradInner tracefreeNormSq scalar)
    nablaRicNormSq denomP_nonzero P_mul_denomP_eq
    (quotientEvolutionIdentity_alpha_one_of_scalar_parabolic_calculus
      bareProblem Calc tracefreeNormSq scalar (2 - epsilon)
      h_tracefree_smooth h_scalar_smooth h_scalar_pos)
    h_tracefree_heat h_scalar_heat h_scalar_ne h_phiCoeff h_psiCoeff
    h_gradient_completion shifted_adjusted_heat_eq

/-- Public P4-A constructor for the improved-pinching quotient evolution.

This is the named handoff for LaTeX item (8):
`P = |Ric^0|^2 / R^(2 - epsilon)`. It is deliberately stated over the concrete
heat-equation inputs instead of importing the Ricci-norm evolution module into
the dimension-three pinching file. In applications, the trace-free heat input
is supplied by `hamilton3D_tracefree_norm_eq_of_heat_components` and the scalar
heat input by `scalar_heat_eq_of_full_evolution`, both from
`Evolution/RicciNorm.lean`.

The realization-sensitive pieces remain explicit: scalar positivity,
denominator nonzero, the power-coefficient identities for `beta = 2 - epsilon`,
the gradient-square completion, and the shifted adjusted heat identity. -/
@[reducible] def hamiltonPinchingAdjustedEvolutionData_of_tracefree_ricci_norm_heat
    (problem bareProblem : ScalarParabolicProblem R Time)
    (Calc : ScalarParabolicCalculus bareProblem)
    (tracefreeNormSq scalar denomP ratio : Time -> R)
    (epsilon bound : R) (decay ricciNormSq cubicQ : Time -> R)
    (driftCoeff gradScalarGradP completedSquareWeight completedSquareNormSq
      scalarGradientWeight reactionWeight : Time -> R)
    (nablaRicNormSq : Time -> R)
    (h_tracefree_smooth : Calc.Smooth tracefreeNormSq)
    (h_scalar_smooth : Calc.Smooth scalar)
    (h_scalar_pos : Calc.Positive scalar)
    (denomP_nonzero : forall t, problem.domain t -> denomP t ≠ 0)
    (P_mul_denomP_eq : forall t, problem.domain t ->
      (tracefreeNormSq t * Calc.pow (-(2 - epsilon)) scalar t) * denomP t =
        tracefreeNormSq t)
    (h_tracefree_heat : forall t,
      bareProblem.heat tracefreeNormSq t =
        -2 * nablaRicNormSq t + ((2 : R) / 3) * Calc.gradNormSq scalar t +
          (4 * ricciNormSq t * tracefreeNormSq t - 2 * cubicQ t) / scalar t)
    (h_scalar_heat : forall t,
      bareProblem.heat scalar t = 2 * ricciNormSq t)
    (h_scalar_ne : forall t, scalar t ≠ 0)
    (h_phiCoeff : forall t,
      2 * Calc.pow (-(2 - epsilon)) scalar t = reactionWeight t * scalar t)
    (h_psiCoeff : forall t,
      2 * (tracefreeNormSq t * Calc.pow (-(2 - epsilon) - 1) scalar t) =
        reactionWeight t * tracefreeNormSq t)
    (h_gradient_completion : forall t,
      Calc.pow (-(2 - epsilon)) scalar t *
          (-2 * nablaRicNormSq t + ((2 : R) / 3) * Calc.gradNormSq scalar t) -
        (2 - epsilon) * ((2 - epsilon) + 1) *
            (tracefreeNormSq t * Calc.pow (-(2 - epsilon) - 2) scalar t) *
            Calc.gradNormSq scalar t +
        2 * (2 - epsilon) * Calc.pow (-(2 - epsilon) - 1) scalar t *
            Calc.gradInner tracefreeNormSq scalar t =
          driftCoeff t * gradScalarGradP t -
            completedSquareWeight t * completedSquareNormSq t -
            scalarGradientWeight t * tracefreeNormSq t * Calc.gradNormSq scalar t)
    (shifted_adjusted_heat_eq :
      forall t, problem.domain t ->
        problem.heat
            (fun s => tracefreeNormSq s * Calc.pow (-(2 - epsilon)) scalar s - bound) t =
          bareProblem.heat
              (fun s => tracefreeNormSq s * Calc.pow (-(2 - epsilon)) scalar s) t -
            driftCoeff t * gradScalarGradP t +
              completedSquareWeight t * completedSquareNormSq t +
                scalarGradientWeight t * tracefreeNormSq t * Calc.gradNormSq scalar t) :
    HamiltonPinchingAdjustedEvolutionData (R := R) (Time := Time) :=
  hamiltonPinchingAdjustedEvolutionData_of_tracefree_heat_and_scalar_calculus
    problem bareProblem Calc tracefreeNormSq scalar denomP ratio epsilon bound decay
    ricciNormSq cubicQ driftCoeff gradScalarGradP completedSquareWeight
    completedSquareNormSq scalarGradientWeight reactionWeight nablaRicNormSq
    h_tracefree_smooth h_scalar_smooth h_scalar_pos denomP_nonzero P_mul_denomP_eq
    h_tracefree_heat h_scalar_heat h_scalar_ne h_phiCoeff h_psiCoeff
    h_gradient_completion shifted_adjusted_heat_eq

/-- One-stop P4 producer from the trace-free Ricci-norm heat equation.

This composes the public P4-A quotient-evolution constructor with the
maximum-principle producer constructor. The remaining inputs are precisely the
realization-sensitive signs, initial bound, coefficient identities, and decay
relations that are not part of the synthetic quotient calculation. -/
@[reducible] def hamilton_improved_pinching_producer_data_of_tracefree_ricci_norm_heat
    (problem bareProblem : ScalarParabolicProblem R Time)
    (Calc : ScalarParabolicCalculus bareProblem)
    (tracefreeNormSq scalar denomP ratio : Time -> R)
    (epsilon bound : R) (decay ricciNormSq cubicQ : Time -> R)
    (driftCoeff gradScalarGradP completedSquareWeight completedSquareNormSq
      scalarGradientWeight reactionWeight : Time -> R)
    (nablaRicNormSq : Time -> R)
    (h_tracefree_smooth : Calc.Smooth tracefreeNormSq)
    (h_scalar_smooth : Calc.Smooth scalar)
    (h_scalar_pos : Calc.Positive scalar)
    (denomP_nonzero : forall t, problem.domain t -> denomP t ≠ 0)
    (P_mul_denomP_eq : forall t, problem.domain t ->
      (tracefreeNormSq t * Calc.pow (-(2 - epsilon)) scalar t) * denomP t =
        tracefreeNormSq t)
    (h_tracefree_heat : forall t,
      bareProblem.heat tracefreeNormSq t =
        -2 * nablaRicNormSq t + ((2 : R) / 3) * Calc.gradNormSq scalar t +
          (4 * ricciNormSq t * tracefreeNormSq t - 2 * cubicQ t) / scalar t)
    (h_scalar_heat : forall t,
      bareProblem.heat scalar t = 2 * ricciNormSq t)
    (h_scalar_ne : forall t, scalar t ≠ 0)
    (h_phiCoeff : forall t,
      2 * Calc.pow (-(2 - epsilon)) scalar t = reactionWeight t * scalar t)
    (h_psiCoeff : forall t,
      2 * (tracefreeNormSq t * Calc.pow (-(2 - epsilon) - 1) scalar t) =
        reactionWeight t * tracefreeNormSq t)
    (h_gradient_completion : forall t,
      Calc.pow (-(2 - epsilon)) scalar t *
          (-2 * nablaRicNormSq t + ((2 : R) / 3) * Calc.gradNormSq scalar t) -
        (2 - epsilon) * ((2 - epsilon) + 1) *
            (tracefreeNormSq t * Calc.pow (-(2 - epsilon) - 2) scalar t) *
            Calc.gradNormSq scalar t +
        2 * (2 - epsilon) * Calc.pow (-(2 - epsilon) - 1) scalar t *
            Calc.gradInner tracefreeNormSq scalar t =
          driftCoeff t * gradScalarGradP t -
            completedSquareWeight t * completedSquareNormSq t -
            scalarGradientWeight t * tracefreeNormSq t * Calc.gradNormSq scalar t)
    (shifted_adjusted_heat_eq :
      forall t, problem.domain t ->
        problem.heat
            (fun s => tracefreeNormSq s * Calc.pow (-(2 - epsilon)) scalar s - bound) t =
          bareProblem.heat
              (fun s => tracefreeNormSq s * Calc.pow (-(2 - epsilon)) scalar s) t -
            driftCoeff t * gradScalarGradP t +
              completedSquareWeight t * completedSquareNormSq t +
                scalarGradientWeight t * tracefreeNormSq t * Calc.gradNormSq scalar t)
    (delta : R)
    (epsilon_le : epsilon <= 2 * delta ^ 2)
    (reaction_product_nonnegative :
      forall t, problem.domain t -> 0 <= ricciNormSq t * tracefreeNormSq t)
    (cubicQ_lower_bound :
      forall t, problem.domain t ->
        2 * delta ^ 2 * ricciNormSq t * tracefreeNormSq t <= cubicQ t)
    (reactionWeight_nonnegative :
      forall t, problem.domain t -> 0 <= reactionWeight t)
    (initial_bound :
      IsInitiallyNonpositive problem
        (fun t => tracefreeNormSq t * Calc.pow (-(2 - epsilon)) scalar t - bound))
    (ratio_decay_relation :
      forall t, problem.domain t ->
        ratio t <=
          (tracefreeNormSq t * Calc.pow (-(2 - epsilon)) scalar t) * decay t)
    (decay_nonnegative : forall t, problem.domain t -> 0 <= decay t) :
    HamiltonImprovedPinchingProducerData (R := R) (Time := Time) :=
  hamilton_improved_pinching_producer_data_of_adjusted_pinching_evolution
    (hamiltonPinchingAdjustedEvolutionData_of_tracefree_ricci_norm_heat
      problem bareProblem Calc tracefreeNormSq scalar denomP ratio epsilon bound
      decay ricciNormSq cubicQ driftCoeff gradScalarGradP completedSquareWeight
      completedSquareNormSq scalarGradientWeight reactionWeight nablaRicNormSq
      h_tracefree_smooth h_scalar_smooth h_scalar_pos denomP_nonzero
      P_mul_denomP_eq h_tracefree_heat h_scalar_heat h_scalar_ne h_phiCoeff
      h_psiCoeff h_gradient_completion shifted_adjusted_heat_eq)
    delta epsilon_le reaction_product_nonnegative cubicQ_lower_bound
    reactionWeight_nonnegative initial_bound ratio_decay_relation decay_nonnegative

end ImprovedPinchingEvolutionCalculation

section ImprovedPinchingQuotientAlgebra

variable {R Time : Type*}
variable [Field R] [LinearOrder R] [IsStrictOrderedRing R]

/-- Definition 10.2 from `RicciFlow/main.tex`, with
`denomP = R^(2 - epsilon)` supplied abstractly:
`P = |Ric^0|^2 / denomP`.

The denominator is abstract so concrete realizations may use the power API that
fits their scalar-curvature positivity hypotheses. -/
def hamiltonImprovedPinchingQuantity (tracefreeNormSq denomP : R) : R :=
  tracefreeNormSq / denomP

theorem hamiltonImprovedPinchingQuantity_eval
    (tracefreeNormSq denomP : R) :
    hamiltonImprovedPinchingQuantity tracefreeNormSq denomP =
      tracefreeNormSq / denomP := by
  rfl

/-- Definition 10.2 after substituting Definition 10.1:
`P = (|Ric|^2 - (1/3)R^2) / R^(2 - epsilon)`, with both `1/3` and the
denominator supplied abstractly. -/
def hamiltonImprovedPinchingQuantityFromRicci
    (ricciNormSq scalar nInv denomP : R) : R :=
  (ricciNormSq - nInv * scalar * scalar) / denomP

theorem hamiltonImprovedPinchingQuantity_eq_from_ricci
    (tracefreeNormSq ricciNormSq scalar nInv denomP : R)
    (h_tracefree : tracefreeNormSq = ricciNormSq - nInv * scalar * scalar) :
    hamiltonImprovedPinchingQuantity tracefreeNormSq denomP =
      hamiltonImprovedPinchingQuantityFromRicci ricciNormSq scalar nInv denomP := by
  rw [hamiltonImprovedPinchingQuantity_eval, h_tracefree]
  rfl

/-- Pointwise quotient algebra for the P4 ratio-decay bridge.

If `P = tracefree / denomP`, `ratio = tracefree / denomRatio`, and
`decay = denomP / denomRatio`, then `ratio = P * decay`. In the intended
Ricci-flow application,

```text
denomP = R^(2 - epsilon)
denomRatio = R^2
decay = R^(-epsilon).
```

The analytic realization is responsible for the exponent identity
`R^(-epsilon) = R^(2 - epsilon) / R^2`; this theorem keeps the remaining
division algebra out of the geometric proof. -/
theorem pinching_ratio_eq_P_mul_decay_of_denominator_decay
    (tracefree denomP denomRatio decay : R)
    (h_denomP : denomP ≠ 0)
    (h_decay : decay = denomP / denomRatio) :
    tracefree / denomRatio = (tracefree / denomP) * decay := by
  by_cases h_denomRatio : denomRatio = 0
  · subst h_denomRatio
    simp only [div_zero, h_decay, mul_zero]
  · rw [h_decay]
    field_simp [h_denomP, h_denomRatio]

/-- Domain-wise quotient realization for P4.

This is the coordinate/analysis handoff object for the algebraic identity
`ratio = P * decay`. It deliberately avoids choosing an `rpow` API. A concrete
analysis layer may instantiate `denomP`, `denomRatio`, and `decay` using real
powers, integer powers, or any local positive-scalar convention. -/
structure HamiltonPinchingQuotientRealizationData
    (problem : ScalarParabolicProblem R Time) where
  tracefreeNormSq : Time -> R
  denomP : Time -> R
  denomRatio : Time -> R
  P : Time -> R
  ratio : Time -> R
  decay : Time -> R
  denomP_nonzero : forall t, problem.domain t -> denomP t ≠ 0
  P_eq : forall t, problem.domain t -> P t = tracefreeNormSq t / denomP t
  ratio_eq : forall t, problem.domain t -> ratio t = tracefreeNormSq t / denomRatio t
  decay_eq : forall t, problem.domain t -> decay t = denomP t / denomRatio t

/-- The quotient realization gives the exact ratio-decay identity. -/
theorem HamiltonPinchingQuotientRealizationData.ratio_decay_eq
    {problem : ScalarParabolicProblem R Time}
    (D : HamiltonPinchingQuotientRealizationData (R := R) (Time := Time) problem)
    (t : Time) (ht : problem.domain t) :
    D.ratio t = D.P t * D.decay t := by
  calc
    D.ratio t = D.tracefreeNormSq t / D.denomRatio t := D.ratio_eq t ht
    _ = (D.tracefreeNormSq t / D.denomP t) * D.decay t :=
        pinching_ratio_eq_P_mul_decay_of_denominator_decay
          (D.tracefreeNormSq t) (D.denomP t) (D.denomRatio t) (D.decay t)
          (D.denomP_nonzero t ht) (D.decay_eq t ht)
    _ = D.P t * D.decay t := by rw [← D.P_eq t ht]

/-- The quotient realization supplies the weaker inequality expected by
`HamiltonImprovedPinchingProducerData`. -/
theorem ratio_decay_relation_of_quotient_realization
    {problem : ScalarParabolicProblem R Time}
    (D : HamiltonPinchingQuotientRealizationData (R := R) (Time := Time) problem) :
    forall t, problem.domain t -> D.ratio t <= D.P t * D.decay t := by
  intro t ht
  exact le_of_eq (D.ratio_decay_eq t ht)

end ImprovedPinchingQuotientAlgebra
