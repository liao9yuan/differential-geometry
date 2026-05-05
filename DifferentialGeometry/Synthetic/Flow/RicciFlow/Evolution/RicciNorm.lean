import DifferentialGeometry.Synthetic.Flow.RicciFlow.Evolution.ScalarCurvature
import DifferentialGeometry.Synthetic.Operator.Laplacian
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.style.emptyLine false

/-!
# Ricci Norm and Trace-Free Ricci Interfaces

This module collects the algebraic objects needed for the pinching part of
`RicciFlow/main.tex`: the trace-free Ricci tensor, its squared norm, and named
evolution-equation interfaces.
-/

open SyntheticTensor

section TracefreeRicci

variable {k R V : Type*}
variable [Field k] [CommRing R] [Algebra k R]
variable [AddCommGroup V] [Module R V] [Module k V] [IsScalarTower k R V]

/-- Trace-free Ricci tensor, with `nInv` standing for `1 / n`. -/
noncomputable def tracefree_ricci_tensor
    (emb : DerivationEmbedding k R V) (conn : V -> V -> V)
    (ha : forall X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : forall X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : forall (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (hl : forall X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (atr : AbstractTrace R V) (met : MetricDuality R V) (nInv : R) :
    TensorData R V 0 2 :=
  ricciForm_tensor emb conn ha hal hsl hl atr -
    ((nInv * ScalarCurvature emb conn ha hal hsl hl atr met) • met.g_tensor)

theorem tracefree_ricci_tensor_eval
    (emb : DerivationEmbedding k R V) (conn : V -> V -> V)
    (ha : forall X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : forall X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : forall (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (hl : forall X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (atr : AbstractTrace R V) (met : MetricDuality R V) (nInv : R) (X Y : V) :
    tracefree_ricci_tensor emb conn ha hal hsl hl atr met nInv ![X, Y] ![] =
    ricciForm_tensor emb conn ha hal hsl hl atr ![X, Y] ![] -
      (nInv * ScalarCurvature emb conn ha hal hsl hl atr met) * met.g X Y := by
  simp [tracefree_ricci_tensor, MetricDuality.g, smul_eq_mul]

/-- Squared norm of trace-free Ricci. -/
noncomputable def tracefree_ricci_norm_sq
    (emb : DerivationEmbedding k R V) (conn : V -> V -> V)
    (ha : forall X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : forall X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : forall (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (hl : forall X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (atr : AbstractTrace R V) (met : MetricDuality R V) (nInv : R) : R :=
  tensor_inner_02 met atr
    (tracefree_ricci_tensor emb conn ha hal hsl hl atr met nInv)
    (tracefree_ricci_tensor emb conn ha hal hsl hl atr met nInv)

/-- Expansion of `|Rc - (R/n)g|^2` into the four bilinear terms. -/
theorem tracefree_ricci_norm_sq_expand
    (emb : DerivationEmbedding k R V) (conn : V -> V -> V)
    (ha : forall X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : forall X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : forall (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (hl : forall X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (atr : AbstractTrace R V) (met : MetricDuality R V) (nInv : R) :
    tracefree_ricci_norm_sq emb conn ha hal hsl hl atr met nInv =
      tensor_inner_02 met atr
        (ricciForm_tensor emb conn ha hal hsl hl atr)
        (ricciForm_tensor emb conn ha hal hsl hl atr) -
      tensor_inner_02 met atr
        (ricciForm_tensor emb conn ha hal hsl hl atr)
        ((nInv * ScalarCurvature emb conn ha hal hsl hl atr met) • met.g_tensor) -
      tensor_inner_02 met atr
        ((nInv * ScalarCurvature emb conn ha hal hsl hl atr met) • met.g_tensor)
        (ricciForm_tensor emb conn ha hal hsl hl atr) +
      tensor_inner_02 met atr
        ((nInv * ScalarCurvature emb conn ha hal hsl hl atr met) • met.g_tensor)
        ((nInv * ScalarCurvature emb conn ha hal hsl hl atr met) • met.g_tensor) := by
  unfold tracefree_ricci_norm_sq tracefree_ricci_tensor
  rw [tensor_inner_02_sub_sub]

/-- Expansion of `|Rc - (R/n)g|^2` with scalar multiples pulled out. -/
theorem tracefree_ricci_norm_sq_expand_scalar
    (emb : DerivationEmbedding k R V) (conn : V -> V -> V)
    (ha : forall X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : forall X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : forall (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (hl : forall X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (atr : AbstractTrace R V) (met : MetricDuality R V) (nInv : R) :
    tracefree_ricci_norm_sq emb conn ha hal hsl hl atr met nInv =
      ricci_norm_sq emb conn ha hal hsl hl atr met -
      (nInv * ScalarCurvature emb conn ha hal hsl hl atr met) *
        tensor_inner_02 met atr
          (ricciForm_tensor emb conn ha hal hsl hl atr) met.g_tensor -
      (nInv * ScalarCurvature emb conn ha hal hsl hl atr met) *
        tensor_inner_02 met atr met.g_tensor
          (ricciForm_tensor emb conn ha hal hsl hl atr) +
      (nInv * ScalarCurvature emb conn ha hal hsl hl atr met) *
        ((nInv * ScalarCurvature emb conn ha hal hsl hl atr met) *
          tensor_inner_02 met atr met.g_tensor met.g_tensor) := by
  rw [tracefree_ricci_norm_sq_expand, tensor_inner_02_ricciForm]
  repeat rw [tensor_inner_02_smul_right]
  repeat rw [tensor_inner_02_smul_left]

/-- Closed trace-free Ricci norm expansion, assuming the missing metric-contraction bridge.

The hypotheses are exactly the remaining realization/contraction facts needed
to turn the algebraic expansion into the classical identity:
`<Rc,g> = R`, `<g,g> = dim`, and `nInv * dim = 1`. -/
theorem tracefree_ricci_norm_sq_expand_closed
    (emb : DerivationEmbedding k R V) (conn : V -> V -> V)
    (ha : forall X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : forall X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : forall (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (hl : forall X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (atr : AbstractTrace R V) (met : MetricDuality R V) (nInv dim : R)
    (h_Rc_g :
      tensor_inner_02 met atr
        (ricciForm_tensor emb conn ha hal hsl hl atr) met.g_tensor =
      ScalarCurvature emb conn ha hal hsl hl atr met)
    (h_g_g : tensor_inner_02 met atr met.g_tensor met.g_tensor = dim)
    (h_nInv_dim : nInv * dim = 1) :
    tracefree_ricci_norm_sq emb conn ha hal hsl hl atr met nInv =
      ricci_norm_sq emb conn ha hal hsl hl atr met -
        nInv * ScalarCurvature emb conn ha hal hsl hl atr met *
          ScalarCurvature emb conn ha hal hsl hl atr met := by
  rw [tracefree_ricci_norm_sq_expand_scalar, h_Rc_g,
    tensor_inner_02_symm met atr met.g_tensor
      (ricciForm_tensor emb conn ha hal hsl hl atr),
    h_Rc_g, h_g_g]
  have h_last :
      (nInv * ScalarCurvature emb conn ha hal hsl hl atr met) *
        ((nInv * ScalarCurvature emb conn ha hal hsl hl atr met) * dim) =
      nInv * ScalarCurvature emb conn ha hal hsl hl atr met *
        ScalarCurvature emb conn ha hal hsl hl atr met := by
    calc
      (nInv * ScalarCurvature emb conn ha hal hsl hl atr met) *
          ((nInv * ScalarCurvature emb conn ha hal hsl hl atr met) * dim)
          = (nInv * dim) *
              (nInv * ScalarCurvature emb conn ha hal hsl hl atr met *
                ScalarCurvature emb conn ha hal hsl hl atr met) := by ring
      _ = 1 *
              (nInv * ScalarCurvature emb conn ha hal hsl hl atr met *
                ScalarCurvature emb conn ha hal hsl hl atr met) := by rw [h_nInv_dim]
      _ = nInv * ScalarCurvature emb conn ha hal hsl hl atr met *
            ScalarCurvature emb conn ha hal hsl hl atr met := by ring
  rw [h_last]
  ring

/-- Closed trace-free Ricci norm expansion using the abstract trace dimension `tr(id)`.

This removes the previously separate contraction bridge hypotheses:
`<Rc,g> = R` and `<g,g> = tr(id)` are now proved in `ScalarCurvature.lean`.
The only remaining dimension normalization is `nInv * tr(id) = 1`. -/
theorem tracefree_ricci_norm_sq_expand_abstractTraceDimension
    (emb : DerivationEmbedding k R V) (conn : V -> V -> V)
    (ha : forall X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : forall X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : forall (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (hl : forall X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (atr : AbstractTrace R V) (met : MetricDuality R V) (nInv : R)
    (h_nInv_dim : nInv * abstractTraceDimension atr = 1) :
    tracefree_ricci_norm_sq emb conn ha hal hsl hl atr met nInv =
      ricci_norm_sq emb conn ha hal hsl hl atr met -
        nInv * ScalarCurvature emb conn ha hal hsl hl atr met *
          ScalarCurvature emb conn ha hal hsl hl atr met :=
  tracefree_ricci_norm_sq_expand_closed emb conn ha hal hsl hl atr met nInv
    (abstractTraceDimension atr)
    (tensor_inner_02_ricciForm_metric emb conn ha hal hsl hl atr met)
    (tensor_inner_02_metric_metric met atr)
    h_nInv_dim

end TracefreeRicci

section NormEvolutionInterfaces

variable {k R V Time : Type*} {A : Type*}
variable [Field k] [CommRing R] [Algebra k R]
variable [AddCommGroup V] [Module R V] [Module k V] [IsScalarTower k R V]
variable [CommRing A] [Algebra R A]

/-- Interface for the Ricci norm evolution equation. -/
def RicciNormEvolutionEquation
    (emb : DerivationEmbedding k R V)
    (td : TimeDerivativeData R A Time) [TimeRegularFam td]
    (atr : AbstractTrace R V)
    (g_fam : Time -> MetricDuality R V)
    (conn_fam : Time -> V -> V -> V)
    (ha_fam : forall s, forall X Y Z, conn_fam s X (Y + Z) = conn_fam s X Y + conn_fam s X Z)
    (hal_fam : forall s, forall X Y Z, conn_fam s (X + Y) Z = conn_fam s X Z + conn_fam s Y Z)
    (hsl_fam : forall s, forall (f : R) X Z, conn_fam s (f • X) Z = f • conn_fam s X Z)
    (hl_fam : forall s, forall X (f : R) Y,
      conn_fam s X (f • Y) = (emb.embed X) f • Y + f • conn_fam s X Y)
    (rhs : Time -> R) : Prop :=
  forall t,
    td.dt_apply (fun s =>
      ricci_norm_sq emb (conn_fam s) (ha_fam s) (hal_fam s) (hsl_fam s) (hl_fam s)
        atr (g_fam s)) t = rhs t

theorem ricci_norm_evolution_from_interface
    (emb : DerivationEmbedding k R V)
    (td : TimeDerivativeData R A Time) [TimeRegularFam td]
    (atr : AbstractTrace R V)
    (g_fam : Time -> MetricDuality R V)
    (conn_fam : Time -> V -> V -> V)
    (ha_fam : forall s, forall X Y Z, conn_fam s X (Y + Z) = conn_fam s X Y + conn_fam s X Z)
    (hal_fam : forall s, forall X Y Z, conn_fam s (X + Y) Z = conn_fam s X Z + conn_fam s Y Z)
    (hsl_fam : forall s, forall (f : R) X Z, conn_fam s (f • X) Z = f • conn_fam s X Z)
    (hl_fam : forall s, forall X (f : R) Y,
      conn_fam s X (f • Y) = (emb.embed X) f • Y + f • conn_fam s X Y)
    (rhs : Time -> R)
    (h : RicciNormEvolutionEquation emb td atr g_fam conn_fam ha_fam hal_fam hsl_fam hl_fam rhs)
    (t : Time) :
    td.dt_apply (fun s =>
      ricci_norm_sq emb (conn_fam s) (ha_fam s) (hal_fam s) (hsl_fam s) (hl_fam s)
        atr (g_fam s)) t = rhs t :=
  h t

/-- Interface for the trace-free Ricci norm evolution equation. -/
def TracefreeRicciNormEvolutionEquation
    (emb : DerivationEmbedding k R V)
    (td : TimeDerivativeData R A Time) [TimeRegularFam td]
    (atr : AbstractTrace R V)
    (g_fam : Time -> MetricDuality R V)
    (conn_fam : Time -> V -> V -> V)
    (ha_fam : forall s, forall X Y Z, conn_fam s X (Y + Z) = conn_fam s X Y + conn_fam s X Z)
    (hal_fam : forall s, forall X Y Z, conn_fam s (X + Y) Z = conn_fam s X Z + conn_fam s Y Z)
    (hsl_fam : forall s, forall (f : R) X Z, conn_fam s (f • X) Z = f • conn_fam s X Z)
    (hl_fam : forall s, forall X (f : R) Y,
      conn_fam s X (f • Y) = (emb.embed X) f • Y + f • conn_fam s X Y)
    (nInv : R) (rhs : Time -> R) : Prop :=
  forall t,
    td.dt_apply (fun s =>
      tracefree_ricci_norm_sq emb (conn_fam s) (ha_fam s) (hal_fam s) (hsl_fam s)
        (hl_fam s) atr (g_fam s) nInv) t = rhs t

theorem tracefree_ricci_norm_evolution_from_interface
    (emb : DerivationEmbedding k R V)
    (td : TimeDerivativeData R A Time) [TimeRegularFam td]
    (atr : AbstractTrace R V)
    (g_fam : Time -> MetricDuality R V)
    (conn_fam : Time -> V -> V -> V)
    (ha_fam : forall s, forall X Y Z, conn_fam s X (Y + Z) = conn_fam s X Y + conn_fam s X Z)
    (hal_fam : forall s, forall X Y Z, conn_fam s (X + Y) Z = conn_fam s X Z + conn_fam s Y Z)
    (hsl_fam : forall s, forall (f : R) X Z, conn_fam s (f • X) Z = f • conn_fam s X Z)
    (hl_fam : forall s, forall X (f : R) Y,
      conn_fam s X (f • Y) = (emb.embed X) f • Y + f • conn_fam s X Y)
    (nInv : R) (rhs : Time -> R)
    (h : TracefreeRicciNormEvolutionEquation emb td atr g_fam conn_fam ha_fam hal_fam
      hsl_fam hl_fam nInv rhs)
    (t : Time) :
    td.dt_apply (fun s =>
      tracefree_ricci_norm_sq emb (conn_fam s) (ha_fam s) (hal_fam s) (hsl_fam s)
        (hl_fam s) atr (g_fam s) nInv) t = rhs t :=
  h t

/-- Ricci-norm heat evolution after the two standard component formulas have
been identified.

The intended component formulas are

  * `ricciNormDt = 2 * lapInner + 4 * reaction`, where `reaction` is the
    Riemann-Ricci-Ricci contraction scalar
    `R_{ikjl} Ric^{kl} Ric^{ij}` in the fixed curvature slot convention. This
    comes from differentiating
    `|Ric|^2` in time, substituting the Ricci evolution equation, and cancelling
    the cubic metric-variation terms;
* `ricciNormLap = 2 * lapInner + 2 * nablaRicNormSq`, the Bochner product rule
  for the rough Laplacian of `|Ric|^2`.

This lemma is the cancellation step in P3.1/P3.2; the real geometric work is to
produce the two displayed component formulas. -/
theorem ricci_norm_heat_eq_of_dt_laplacian_components
    (ricciNormDt ricciNormLap lapInner nablaRicNormSq reaction : Time -> R)
    (h_dt : forall t, ricciNormDt t = 2 * lapInner t + 4 * reaction t)
    (h_lap : forall t, ricciNormLap t = 2 * lapInner t + 2 * nablaRicNormSq t) :
    forall t,
      ricciNormDt t - ricciNormLap t =
        -2 * nablaRicNormSq t + 4 * reaction t := by
  intro t
  rw [h_dt t, h_lap t]
  ring

/-- Lemma 6.7 (`Evolution of the Ricci norm`) in the form used by the
synthetic Ricci-flow layer.

The coordinate proof has two tensor-calculus inputs:

* `h_dt_component`: differentiate
  `|Ric|^2 = g^{ia} g^{jb} Ric_{ij} Ric_{ab}`, use
  `partial_t g^{-1} = 2 Ric#`, substitute the Ricci evolution equation, and
  cancel the two cubic metric-variation terms. This gives
  `ricciNormDt = 2 * lapInner + 4 * curvRicciRicci`.
* `h_lap_component`: use metric compatibility and the product rule for the
  rough Laplacian of the tensor norm,
  `Delta |Ric|^2 = 2 <Delta Ric, Ric> + 2 |nabla Ric|^2`.

After those two component identities are supplied, Lemma 6.7 is pure scalar
algebra. -/
theorem ricci_norm_heat_eq_lemma67
    (ricciNormDt ricciNormLap lapInner nablaRicNormSq curvRicciRicci : Time -> R)
    (h_dt_component :
      forall t, ricciNormDt t = 2 * lapInner t + 4 * curvRicciRicci t)
    (h_lap_component :
      forall t, ricciNormLap t = 2 * lapInner t + 2 * nablaRicNormSq t) :
    forall t,
      ricciNormDt t - ricciNormLap t =
        -2 * nablaRicNormSq t + 4 * curvRicciRicci t :=
  ricci_norm_heat_eq_of_dt_laplacian_components
    ricciNormDt ricciNormLap lapInner nablaRicNormSq curvRicciRicci
    h_dt_component h_lap_component

/-- The cubic cancellation in the time-derivative half of Lemma 6.7.

After differentiating `|Ric|^2`, the two inverse-metric variation terms produce
`+4 * ricciTraceCube`, while the `-2 Ric_i^k Ric_kj` part of the Ricci
evolution contributes `-4 * ricciTraceCube`. This lemma records the scalar
cancellation once both cubic contractions have been identified with the same
trace-cube quantity. -/
theorem ricci_norm_dt_component_of_trace_cube_cancellation
    (ricciNormDt lapInner curvRicciRicci ricciTraceCube : Time -> R)
    (h_expand : forall t,
      ricciNormDt t =
        4 * ricciTraceCube t +
          (2 * lapInner t + 4 * curvRicciRicci t - 4 * ricciTraceCube t)) :
    forall t,
      ricciNormDt t = 2 * lapInner t + 4 * curvRicciRicci t := by
  intro t
  rw [h_expand t]
  ring

/-- Local-coordinate product-rule expansion for the time derivative of a Ricci
norm expression.

This is only the Ricci specialization of the generic tensor-norm rule
`TimeDerivativeData.dt_apply_tensor_norm_sq_coordinate_evaluation`. The
geometric work is the coordinate norm evaluation; once that is known, the time
derivative is just the scalar product rule for the two inverse-metric factors
and the two tensor-component factors.

The proof is written out here so this module can still be checked against a
stale dependency build in a shared workspace; mathematically it is the same
finite-coordinate product rule as the generic algebra lemma. -/
theorem ricci_norm_dt_coordinate_product_rule
    (td : TimeDerivativeData R A Time) [TimeRegularFam td]
    {ι : Type*} [Fintype ι]
    (ricciNormSq : Time -> R)
    (gInvLeft gInvRight ricciLeft ricciRight : ι -> Time -> R)
    (h_coord : forall s,
      ricciNormSq s =
        ∑ I : ι,
          gInvLeft I s * gInvRight I s * ricciLeft I s * ricciRight I s)
    (h_gInvLeft : forall I, td.isSmoothFam (gInvLeft I))
    (h_gInvRight : forall I, td.isSmoothFam (gInvRight I))
    (h_ricciLeft : forall I, td.isSmoothFam (ricciLeft I))
    (h_ricciRight : forall I, td.isSmoothFam (ricciRight I)) :
    forall t,
      td.dt_apply ricciNormSq t =
        ∑ I : ι,
          (td.dt_apply (gInvLeft I) t * gInvRight I t *
              ricciLeft I t * ricciRight I t +
            gInvLeft I t * td.dt_apply (gInvRight I) t *
              ricciLeft I t * ricciRight I t +
            gInvLeft I t * gInvRight I t *
              td.dt_apply (ricciLeft I) t * ricciRight I t +
            gInvLeft I t * gInvRight I t *
              ricciLeft I t * td.dt_apply (ricciRight I) t) := by
  intro t
  have hfun :
      ricciNormSq =
        fun s =>
          ∑ I : ι,
            gInvLeft I s * gInvRight I s * ricciLeft I s * ricciRight I s := by
    ext s
    exact h_coord s
  rw [hfun]
  exact td.dt_apply_sum_mul_four gInvLeft gInvRight ricciLeft ricciRight t
    h_gInvLeft h_gInvRight h_ricciLeft h_ricciRight

/-- Split the coordinate time-derivative terms into their two mathematical
sources.

The first two summands are the inverse-metric variation contribution. The last
two summands are the Ricci-variation contribution. This removes the monolithic
`h_terms` obligation from callers: they prove the two standard contraction
identifications separately, and this lemma recombines them by finite-sum
algebra. -/
theorem ricci_norm_dt_coordinate_terms_of_split_terms
    (td : TimeDerivativeData R A Time) [TimeRegularFam td]
    {ι : Type*} [Fintype ι]
    (lapInner curvRicciRicci ricciTraceCube : Time -> R)
    (gInvLeft gInvRight ricciLeft ricciRight : ι -> Time -> R)
    (h_metric_terms : forall t,
      (∑ I : ι,
        (td.dt_apply (gInvLeft I) t * gInvRight I t *
            ricciLeft I t * ricciRight I t +
          gInvLeft I t * td.dt_apply (gInvRight I) t *
            ricciLeft I t * ricciRight I t)) =
        4 * ricciTraceCube t)
    (h_ricci_terms : forall t,
      (∑ I : ι,
        (gInvLeft I t * gInvRight I t *
            td.dt_apply (ricciLeft I) t * ricciRight I t +
          gInvLeft I t * gInvRight I t *
            ricciLeft I t * td.dt_apply (ricciRight I) t)) =
        2 * lapInner t + 4 * curvRicciRicci t - 4 * ricciTraceCube t) :
    forall t,
      (∑ I : ι,
        (td.dt_apply (gInvLeft I) t * gInvRight I t *
            ricciLeft I t * ricciRight I t +
          gInvLeft I t * td.dt_apply (gInvRight I) t *
            ricciLeft I t * ricciRight I t +
          gInvLeft I t * gInvRight I t *
            td.dt_apply (ricciLeft I) t * ricciRight I t +
          gInvLeft I t * gInvRight I t *
            ricciLeft I t * td.dt_apply (ricciRight I) t)) =
        4 * ricciTraceCube t +
          (2 * lapInner t + 4 * curvRicciRicci t - 4 * ricciTraceCube t) := by
  intro t
  calc
    (∑ I : ι,
        (td.dt_apply (gInvLeft I) t * gInvRight I t *
            ricciLeft I t * ricciRight I t +
          gInvLeft I t * td.dt_apply (gInvRight I) t *
            ricciLeft I t * ricciRight I t +
          gInvLeft I t * gInvRight I t *
            td.dt_apply (ricciLeft I) t * ricciRight I t +
          gInvLeft I t * gInvRight I t *
            ricciLeft I t * td.dt_apply (ricciRight I) t))
        =
          (∑ I : ι,
            (td.dt_apply (gInvLeft I) t * gInvRight I t *
                ricciLeft I t * ricciRight I t +
              gInvLeft I t * td.dt_apply (gInvRight I) t *
                ricciLeft I t * ricciRight I t)) +
          (∑ I : ι,
            (gInvLeft I t * gInvRight I t *
                td.dt_apply (ricciLeft I) t * ricciRight I t +
              gInvLeft I t * gInvRight I t *
                ricciLeft I t * td.dt_apply (ricciRight I) t)) := by
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro I _
          ring
    _ = 4 * ricciTraceCube t +
          (2 * lapInner t + 4 * curvRicciRicci t - 4 * ricciTraceCube t) := by
          rw [h_metric_terms t, h_ricci_terms t]

/-- Time-derivative component of Lemma 6.7 from local-coordinate product rule
plus the trace-cube cancellation.

The remaining geometric hypothesis `h_terms` is the tensor-contraction
identification of the four coordinate product-rule terms: the two inverse-metric
variation terms combine to `+4 * traceCube`, and the two Ricci-variation terms
give `2 * lapInner + 4 * curvRicciRicci - 4 * traceCube`. -/
theorem ricci_norm_dt_component_of_coordinate_product_rule
    (td : TimeDerivativeData R A Time) [TimeRegularFam td]
    {ι : Type*} [Fintype ι]
    (ricciNormSq ricciNormDt lapInner curvRicciRicci ricciTraceCube : Time -> R)
    (gInvLeft gInvRight ricciLeft ricciRight : ι -> Time -> R)
    (h_coord : forall s,
      ricciNormSq s =
        ∑ I : ι,
          gInvLeft I s * gInvRight I s * ricciLeft I s * ricciRight I s)
    (h_gInvLeft : forall I, td.isSmoothFam (gInvLeft I))
    (h_gInvRight : forall I, td.isSmoothFam (gInvRight I))
    (h_ricciLeft : forall I, td.isSmoothFam (ricciLeft I))
    (h_ricciRight : forall I, td.isSmoothFam (ricciRight I))
    (h_dt_eval : forall t, td.dt_apply ricciNormSq t = ricciNormDt t)
    (h_terms : forall t,
      (∑ I : ι,
        (td.dt_apply (gInvLeft I) t * gInvRight I t *
            ricciLeft I t * ricciRight I t +
          gInvLeft I t * td.dt_apply (gInvRight I) t *
            ricciLeft I t * ricciRight I t +
          gInvLeft I t * gInvRight I t *
            td.dt_apply (ricciLeft I) t * ricciRight I t +
          gInvLeft I t * gInvRight I t *
            ricciLeft I t * td.dt_apply (ricciRight I) t)) =
        4 * ricciTraceCube t +
          (2 * lapInner t + 4 * curvRicciRicci t - 4 * ricciTraceCube t)) :
    forall t,
      ricciNormDt t = 2 * lapInner t + 4 * curvRicciRicci t := by
  apply ricci_norm_dt_component_of_trace_cube_cancellation
  intro t
  calc
    ricciNormDt t = td.dt_apply ricciNormSq t := (h_dt_eval t).symm
    _ =
        ∑ I : ι,
          (td.dt_apply (gInvLeft I) t * gInvRight I t *
              ricciLeft I t * ricciRight I t +
            gInvLeft I t * td.dt_apply (gInvRight I) t *
              ricciLeft I t * ricciRight I t +
            gInvLeft I t * gInvRight I t *
              td.dt_apply (ricciLeft I) t * ricciRight I t +
            gInvLeft I t * gInvRight I t *
              ricciLeft I t * td.dt_apply (ricciRight I) t) :=
      ricci_norm_dt_coordinate_product_rule td ricciNormSq
        gInvLeft gInvRight ricciLeft ricciRight h_coord
        h_gInvLeft h_gInvRight h_ricciLeft h_ricciRight t
    _ = 4 * ricciTraceCube t +
          (2 * lapInner t + 4 * curvRicciRicci t - 4 * ricciTraceCube t) :=
      h_terms t

/-- Time-derivative component of Lemma 6.7 from coordinate product rule and
split geometric term identifications. -/
theorem ricci_norm_dt_component_of_coordinate_split_terms
    (td : TimeDerivativeData R A Time) [TimeRegularFam td]
    {ι : Type*} [Fintype ι]
    (ricciNormSq ricciNormDt lapInner curvRicciRicci ricciTraceCube : Time -> R)
    (gInvLeft gInvRight ricciLeft ricciRight : ι -> Time -> R)
    (h_coord : forall s,
      ricciNormSq s =
        ∑ I : ι,
          gInvLeft I s * gInvRight I s * ricciLeft I s * ricciRight I s)
    (h_gInvLeft : forall I, td.isSmoothFam (gInvLeft I))
    (h_gInvRight : forall I, td.isSmoothFam (gInvRight I))
    (h_ricciLeft : forall I, td.isSmoothFam (ricciLeft I))
    (h_ricciRight : forall I, td.isSmoothFam (ricciRight I))
    (h_dt_eval : forall t, td.dt_apply ricciNormSq t = ricciNormDt t)
    (h_metric_terms : forall t,
      (∑ I : ι,
        (td.dt_apply (gInvLeft I) t * gInvRight I t *
            ricciLeft I t * ricciRight I t +
          gInvLeft I t * td.dt_apply (gInvRight I) t *
            ricciLeft I t * ricciRight I t)) =
        4 * ricciTraceCube t)
    (h_ricci_terms : forall t,
      (∑ I : ι,
        (gInvLeft I t * gInvRight I t *
            td.dt_apply (ricciLeft I) t * ricciRight I t +
          gInvLeft I t * gInvRight I t *
            ricciLeft I t * td.dt_apply (ricciRight I) t)) =
        2 * lapInner t + 4 * curvRicciRicci t - 4 * ricciTraceCube t) :
    forall t,
      ricciNormDt t = 2 * lapInner t + 4 * curvRicciRicci t :=
  ricci_norm_dt_component_of_coordinate_product_rule td ricciNormSq ricciNormDt
    lapInner curvRicciRicci ricciTraceCube gInvLeft gInvRight ricciLeft
    ricciRight h_coord h_gInvLeft h_gInvRight h_ricciLeft h_ricciRight
    h_dt_eval
    (ricci_norm_dt_coordinate_terms_of_split_terms td lapInner curvRicciRicci
      ricciTraceCube gInvLeft gInvRight ricciLeft ricciRight h_metric_terms
      h_ricci_terms)

/-- Laplacian component of Lemma 6.7 from the named tensor-norm Bochner product
rule. -/
theorem ricci_norm_laplacian_component_of_tensor_norm_product_rule
    (ricciNormLap lapInner nablaRicNormSq : Time -> R)
    (h_lap_rule : forall t,
      TensorNormLaplacianProductRule
        (ricciNormLap t) (lapInner t) (nablaRicNormSq t)) :
    forall t,
      ricciNormLap t = 2 * lapInner t + 2 * nablaRicNormSq t := by
  intro t
  exact tensor_norm_laplacian_eq_of_product_rule
    (ricciNormLap t) (lapInner t) (nablaRicNormSq t) (h_lap_rule t)

/-- Ricci-norm Laplacian component from the coordinate Bochner sum.

This is the time-dependent Ricci-flow specialization of the tensor-norm
Bochner proof: after the realization identifies the coordinate trace of
`Delta |Ric|^2`, the rough-Laplacian pairing, and the first-derivative norm,
the formula is finite-sum algebra. -/
theorem ricci_norm_laplacian_component_of_coordinate_bochner_sum
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (ricciNormLap lapInner nablaRicNormSq : Time -> R)
    (second first : Time -> κ -> ι -> R) (component : Time -> ι -> R)
    (h_lap_bochner : forall t,
      ricciNormLap t =
        ∑ a : κ, ∑ I : ι,
          (2 * second t a I * component t I +
            2 * first t a I * first t a I))
    (h_rough_bochner : forall t,
      lapInner t =
        ∑ a : κ, ∑ I : ι, second t a I * component t I)
    (h_cov_bochner : forall t,
      nablaRicNormSq t =
        ∑ a : κ, ∑ I : ι, first t a I * first t a I) :
    forall t,
      ricciNormLap t = 2 * lapInner t + 2 * nablaRicNormSq t := by
  intro t
  rw [h_lap_bochner t, h_rough_bochner t, h_cov_bochner t]
  have hrough :
      (∑ a : κ, ∑ I : ι, 2 * (second t a I * component t I)) =
        2 * (∑ a : κ, ∑ I : ι, second t a I * component t I) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    rw [Finset.mul_sum]
  have hcov :
      (∑ a : κ, ∑ I : ι, 2 * (first t a I * first t a I)) =
        2 * (∑ a : κ, ∑ I : ι, first t a I * first t a I) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    rw [Finset.mul_sum]
  rw [← hrough, ← hcov]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro I _
  ring

/-- Lemma 6.7 heat identity with the coordinate time-derivative product rule
and the tensor-norm Laplacian product rule consumed directly. -/
theorem ricci_norm_heat_eq_of_coordinate_dt_and_laplacian_product_rule
    (td : TimeDerivativeData R A Time) [TimeRegularFam td]
    {ι : Type*} [Fintype ι]
    (ricciNormSq ricciNormDt ricciNormLap lapInner nablaRicNormSq
        curvRicciRicci ricciTraceCube : Time -> R)
    (gInvLeft gInvRight ricciLeft ricciRight : ι -> Time -> R)
    (h_coord : forall s,
      ricciNormSq s =
        ∑ I : ι,
          gInvLeft I s * gInvRight I s * ricciLeft I s * ricciRight I s)
    (h_gInvLeft : forall I, td.isSmoothFam (gInvLeft I))
    (h_gInvRight : forall I, td.isSmoothFam (gInvRight I))
    (h_ricciLeft : forall I, td.isSmoothFam (ricciLeft I))
    (h_ricciRight : forall I, td.isSmoothFam (ricciRight I))
    (h_dt_eval : forall t, td.dt_apply ricciNormSq t = ricciNormDt t)
    (h_terms : forall t,
      (∑ I : ι,
        (td.dt_apply (gInvLeft I) t * gInvRight I t *
            ricciLeft I t * ricciRight I t +
          gInvLeft I t * td.dt_apply (gInvRight I) t *
            ricciLeft I t * ricciRight I t +
          gInvLeft I t * gInvRight I t *
            td.dt_apply (ricciLeft I) t * ricciRight I t +
          gInvLeft I t * gInvRight I t *
            ricciLeft I t * td.dt_apply (ricciRight I) t)) =
        4 * ricciTraceCube t +
          (2 * lapInner t + 4 * curvRicciRicci t - 4 * ricciTraceCube t))
    (h_lap_rule : forall t,
      TensorNormLaplacianProductRule
        (ricciNormLap t) (lapInner t) (nablaRicNormSq t)) :
    forall t,
      ricciNormDt t - ricciNormLap t =
        -2 * nablaRicNormSq t + 4 * curvRicciRicci t :=
  ricci_norm_heat_eq_lemma67 ricciNormDt ricciNormLap lapInner
    nablaRicNormSq curvRicciRicci
    (ricci_norm_dt_component_of_coordinate_product_rule td ricciNormSq
      ricciNormDt lapInner curvRicciRicci ricciTraceCube
      gInvLeft gInvRight ricciLeft ricciRight h_coord
      h_gInvLeft h_gInvRight h_ricciLeft h_ricciRight h_dt_eval h_terms)
    (ricci_norm_laplacian_component_of_tensor_norm_product_rule
      ricciNormLap lapInner nablaRicNormSq h_lap_rule)

/-- Lemma 6.7 heat identity from split coordinate time-derivative terms and
the coordinate Bochner sum for the Laplacian side. -/
theorem ricci_norm_heat_eq_of_coordinate_split_dt_and_bochner_sum
    (td : TimeDerivativeData R A Time) [TimeRegularFam td]
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (ricciNormSq ricciNormDt ricciNormLap lapInner nablaRicNormSq
        curvRicciRicci ricciTraceCube : Time -> R)
    (gInvLeft gInvRight ricciLeft ricciRight : ι -> Time -> R)
    (second first : Time -> κ -> ι -> R) (component : Time -> ι -> R)
    (h_coord : forall s,
      ricciNormSq s =
        ∑ I : ι,
          gInvLeft I s * gInvRight I s * ricciLeft I s * ricciRight I s)
    (h_gInvLeft : forall I, td.isSmoothFam (gInvLeft I))
    (h_gInvRight : forall I, td.isSmoothFam (gInvRight I))
    (h_ricciLeft : forall I, td.isSmoothFam (ricciLeft I))
    (h_ricciRight : forall I, td.isSmoothFam (ricciRight I))
    (h_dt_eval : forall t, td.dt_apply ricciNormSq t = ricciNormDt t)
    (h_metric_terms : forall t,
      (∑ I : ι,
        (td.dt_apply (gInvLeft I) t * gInvRight I t *
            ricciLeft I t * ricciRight I t +
          gInvLeft I t * td.dt_apply (gInvRight I) t *
            ricciLeft I t * ricciRight I t)) =
        4 * ricciTraceCube t)
    (h_ricci_terms : forall t,
      (∑ I : ι,
        (gInvLeft I t * gInvRight I t *
            td.dt_apply (ricciLeft I) t * ricciRight I t +
          gInvLeft I t * gInvRight I t *
            ricciLeft I t * td.dt_apply (ricciRight I) t)) =
        2 * lapInner t + 4 * curvRicciRicci t - 4 * ricciTraceCube t)
    (h_lap_bochner : forall t,
      ricciNormLap t =
        ∑ a : κ, ∑ I : ι,
          (2 * second t a I * component t I +
            2 * first t a I * first t a I))
    (h_rough_bochner : forall t,
      lapInner t =
        ∑ a : κ, ∑ I : ι, second t a I * component t I)
    (h_cov_bochner : forall t,
      nablaRicNormSq t =
        ∑ a : κ, ∑ I : ι, first t a I * first t a I) :
    forall t,
      ricciNormDt t - ricciNormLap t =
        -2 * nablaRicNormSq t + 4 * curvRicciRicci t :=
  ricci_norm_heat_eq_lemma67 ricciNormDt ricciNormLap lapInner
    nablaRicNormSq curvRicciRicci
    (ricci_norm_dt_component_of_coordinate_split_terms td ricciNormSq
      ricciNormDt lapInner curvRicciRicci ricciTraceCube
      gInvLeft gInvRight ricciLeft ricciRight h_coord
      h_gInvLeft h_gInvRight h_ricciLeft h_ricciRight h_dt_eval
      h_metric_terms h_ricci_terms)
    (ricci_norm_laplacian_component_of_coordinate_bochner_sum
      ricciNormLap lapInner nablaRicNormSq second first component
      h_lap_bochner h_rough_bochner h_cov_bochner)

/-- Operator-level Ricci-norm heat evolution from the component formulas and
the existing time-derivative/Laplacian interfaces.

This is the concrete bridge for the P3 input
`h_ricciNorm_heat`: once the realization supplies the time-derivative formula
and Bochner Laplacian formula for `|Ric|^2`, the heat equation follows. -/
theorem ricci_norm_heat_operator_eq_of_dt_laplacian_components
    (emb : DerivationEmbedding k R V)
    (td : TimeDerivativeData R A Time) [TimeRegularFam td]
    (atr : AbstractTrace R V)
    (g_fam : Time -> MetricDuality R V)
    (conn_fam : Time -> V -> V -> V)
    (ha_fam : forall s, forall X Y Z, conn_fam s X (Y + Z) = conn_fam s X Y + conn_fam s X Z)
    (hal_fam : forall s, forall X Y Z, conn_fam s (X + Y) Z = conn_fam s X Z + conn_fam s Y Z)
    (hsl_fam : forall s, forall (f : R) X Z, conn_fam s (f • X) Z = f • conn_fam s X Z)
    (hl_fam : forall s, forall X (f : R) Y,
      conn_fam s X (f • Y) = (emb.embed X) f • Y + f • conn_fam s X Y)
    (ricciNormDt ricciNormLap lapInner nablaRicNormSq reaction : Time -> R)
    (h_ricciNorm_dt :
      RicciNormEvolutionEquation emb td atr g_fam conn_fam ha_fam hal_fam
        hsl_fam hl_fam ricciNormDt)
    (laplacianOp : (Time -> R) -> Time -> R)
    (h_ricciNorm_lap : forall t,
      laplacianOp
        (fun s =>
          ricci_norm_sq emb (conn_fam s) (ha_fam s) (hal_fam s)
            (hsl_fam s) (hl_fam s) atr (g_fam s)) t =
        ricciNormLap t)
    (h_dt : forall t, ricciNormDt t = 2 * lapInner t + 4 * reaction t)
    (h_lap : forall t, ricciNormLap t = 2 * lapInner t + 2 * nablaRicNormSq t) :
    forall t,
      td.dt_apply
          (fun s =>
            ricci_norm_sq emb (conn_fam s) (ha_fam s) (hal_fam s)
              (hsl_fam s) (hl_fam s) atr (g_fam s)) t -
        laplacianOp
          (fun s =>
            ricci_norm_sq emb (conn_fam s) (ha_fam s) (hal_fam s)
              (hsl_fam s) (hl_fam s) atr (g_fam s)) t =
          -2 * nablaRicNormSq t + 4 * reaction t := by
  intro t
  rw [h_ricciNorm_dt t, h_ricciNorm_lap t]
  exact ricci_norm_heat_eq_of_dt_laplacian_components
    ricciNormDt ricciNormLap lapInner nablaRicNormSq reaction h_dt h_lap t

end NormEvolutionInterfaces

section Hamilton3DTracefreeEvolutionInterface

variable {R Time : Type*}
variable [Field R]

/-- Hamilton's three-dimensional heat-operator RHS for the trace-free Ricci
norm:

`(dt - Delta)|Ric^0|^2 =
  -2|nabla Ric|^2 + (2/3)|nabla R|^2 +
    (4|Ric|^2|Ric^0|^2 - 2Q)/R`.

This names the scalar algebraic expression used by the P3 trace-free evolution
target. The tensor calculation still has to identify the geometric quantities
with these scalar inputs. -/
noncomputable def tracefreeRicciNormHamilton3DRHS
    (nablaRicNormSq nablaScalarNormSq ricciNormSq tracefreeNormSq cubicQ scalar : R) : R :=
  -2 * nablaRicNormSq + ((2 : R) / 3) * nablaScalarNormSq +
    (4 * ricciNormSq * tracefreeNormSq - 2 * cubicQ) / scalar

theorem tracefreeRicciNormHamilton3DRHS_eval
    (nablaRicNormSq nablaScalarNormSq ricciNormSq tracefreeNormSq cubicQ scalar : R) :
    tracefreeRicciNormHamilton3DRHS nablaRicNormSq nablaScalarNormSq
        ricciNormSq tracefreeNormSq cubicQ scalar =
      -2 * nablaRicNormSq + ((2 : R) / 3) * nablaScalarNormSq +
        (4 * ricciNormSq * tracefreeNormSq - 2 * cubicQ) / scalar := by
  rfl

/-- Scalar heat operator assembled from a time derivative and scalar
Laplacian. This is the concrete operator form of `dt - Delta` used by the
Hamilton 3D trace-free Ricci norm identity. -/
noncomputable def scalarHeatOperator
    (dt laplacian : (Time -> R) -> Time -> R) :
    (Time -> R) -> Time -> R :=
  fun u t => dt u t - laplacian u t

theorem scalarHeatOperator_eval
    (dt laplacian : (Time -> R) -> Time -> R) (u : Time -> R) (t : Time) :
    scalarHeatOperator dt laplacian u t = dt u t - laplacian u t := by
  rfl

/-- P3-facing interface for the closed Hamilton 3D trace-free Ricci norm
identity written for an abstract heat operator `heat = dt - Delta`. -/
def TracefreeRicciNormHamilton3DHeatOperatorEquation
    (heat : (Time -> R) -> Time -> R)
    (tracefreeNormSq nablaRicNormSq nablaScalarNormSq ricciNormSq cubicQ scalar : Time -> R) :
    Prop :=
  forall t,
    heat tracefreeNormSq t =
      tracefreeRicciNormHamilton3DRHS
        (nablaRicNormSq t) (nablaScalarNormSq t) (ricciNormSq t)
        (tracefreeNormSq t) (cubicQ t) (scalar t)

theorem tracefree_ricci_norm_hamilton3D_heat_operator_from_interface
    (heat : (Time -> R) -> Time -> R)
    (tracefreeNormSq nablaRicNormSq nablaScalarNormSq ricciNormSq cubicQ scalar : Time -> R)
    (h :
      TracefreeRicciNormHamilton3DHeatOperatorEquation heat tracefreeNormSq
        nablaRicNormSq nablaScalarNormSq ricciNormSq cubicQ scalar)
    (t : Time) :
    heat tracefreeNormSq t =
      tracefreeRicciNormHamilton3DRHS
        (nablaRicNormSq t) (nablaScalarNormSq t) (ricciNormSq t)
        (tracefreeNormSq t) (cubicQ t) (scalar t) :=
  h t

/-- P3-facing interface with the heat operator expanded as `dt - laplacian`.
This is the target shape for the component calculation that combines Ricci
evolution, norm expansion, and the three-dimensional curvature algebra. -/
def TracefreeRicciNormHamilton3DTimeLaplacianEquation
    (dt laplacian : (Time -> R) -> Time -> R)
    (tracefreeNormSq nablaRicNormSq nablaScalarNormSq ricciNormSq cubicQ scalar : Time -> R) :
    Prop :=
  forall t,
    dt tracefreeNormSq t - laplacian tracefreeNormSq t =
      tracefreeRicciNormHamilton3DRHS
        (nablaRicNormSq t) (nablaScalarNormSq t) (ricciNormSq t)
        (tracefreeNormSq t) (cubicQ t) (scalar t)

theorem tracefree_ricci_norm_hamilton3D_heat_operator_from_time_laplacian
    (dt laplacian : (Time -> R) -> Time -> R)
    (tracefreeNormSq nablaRicNormSq nablaScalarNormSq ricciNormSq cubicQ scalar : Time -> R)
    (h :
      TracefreeRicciNormHamilton3DTimeLaplacianEquation dt laplacian tracefreeNormSq
        nablaRicNormSq nablaScalarNormSq ricciNormSq cubicQ scalar) :
    TracefreeRicciNormHamilton3DHeatOperatorEquation (scalarHeatOperator dt laplacian)
      tracefreeNormSq nablaRicNormSq nablaScalarNormSq ricciNormSq cubicQ scalar := by
  intro t
  exact h t

theorem tracefree_ricci_norm_hamilton3D_time_laplacian_from_interface
    (dt laplacian : (Time -> R) -> Time -> R)
    (tracefreeNormSq nablaRicNormSq nablaScalarNormSq ricciNormSq cubicQ scalar : Time -> R)
    (h :
      TracefreeRicciNormHamilton3DTimeLaplacianEquation dt laplacian tracefreeNormSq
        nablaRicNormSq nablaScalarNormSq ricciNormSq cubicQ scalar)
    (t : Time) :
    dt tracefreeNormSq t - laplacian tracefreeNormSq t =
      tracefreeRicciNormHamilton3DRHS
        (nablaRicNormSq t) (nablaScalarNormSq t) (ricciNormSq t)
        (tracefreeNormSq t) (cubicQ t) (scalar t) :=
  h t

/-- P3.3 scalar Riemann-Ricci-Ricci contraction simplification.

The geometric input from the 3D Riemann-from-Ricci formula is compressed into
`h_reaction`: after contracting the 3D curvature formula against two Ricci
tensors, the Riemann-Ricci-Ricci contraction scalar satisfies
`2 * R * reaction = 2 * |Ric|^4 - Q`. The parameter name `reaction` is legacy
API terminology for that contraction scalar. This theorem turns that
contraction identity into the cubic term in Hamilton's trace-free norm
evolution. -/
theorem hamilton3D_cubic_reaction_simplification
    (nInv scalar ricciNormSq tracefreeNormSq cubicQ reaction : R)
    (h_scalar_ne : scalar ≠ 0)
    (h_nInv : nInv = (1 : R) / 3)
    (h_tracefree : tracefreeNormSq = ricciNormSq - nInv * scalar * scalar)
    (h_reaction : 2 * scalar * reaction = 2 * ricciNormSq ^ 2 - cubicQ) :
    4 * reaction - 4 * nInv * scalar * ricciNormSq =
      (4 * ricciNormSq * tracefreeNormSq - 2 * cubicQ) / scalar := by
  subst nInv
  rw [h_tracefree]
  rw [eq_div_iff h_scalar_ne]
  calc
    (4 * reaction - 4 * ((1 : R) / 3) * scalar * ricciNormSq) * scalar
        = 2 * (2 * scalar * reaction) -
            (4 * ((1 : R) / 3) * scalar * ricciNormSq) * scalar := by ring
    _ = 2 * (2 * ricciNormSq ^ 2 - cubicQ) -
            (4 * ((1 : R) / 3) * scalar * ricciNormSq) * scalar := by rw [h_reaction]
    _ = 4 * ricciNormSq * (ricciNormSq - (1 : R) / 3 * scalar * scalar) -
          2 * cubicQ := by ring

/-- P3.3 pointwise RHS discharge after the component `dt` and Laplacian
formulas have been substituted. The only geometric contraction input left is
`h_reaction`, which states the P2-driven Riemann-Ricci-Ricci contraction identity
obtained by contracting the 3D Riemann-from-Ricci formula against two Ricci
tensors. -/
theorem hamilton3D_tracefree_norm_rhs_of_cubic_reaction
    (nInv : R)
    (ricciNormDt scalarDt ricciNormLap scalarLap gradScalarNormSq
        nablaRicNormSq ricciNormSq tracefreeNormSq cubicQ scalar reaction : Time -> R)
    (h_nInv : nInv = (1 : R) / 3)
    (h_scalar_ne : forall t, scalar t ≠ 0)
    (h_tracefree : forall t,
      tracefreeNormSq t = ricciNormSq t - nInv * scalar t * scalar t)
    (h_ricciNorm_heat : forall t,
      ricciNormDt t - ricciNormLap t =
        -2 * nablaRicNormSq t + 4 * reaction t)
    (h_scalar_heat : forall t,
      scalarDt t - scalarLap t = 2 * ricciNormSq t)
    (h_reaction : forall t,
      2 * scalar t * reaction t = 2 * ricciNormSq t ^ 2 - cubicQ t) :
    forall t,
      (ricciNormDt t - 2 * nInv * scalar t * scalarDt t) -
          (ricciNormLap t -
            nInv * (2 * scalar t * scalarLap t + 2 * gradScalarNormSq t)) =
        tracefreeRicciNormHamilton3DRHS
          (nablaRicNormSq t) (gradScalarNormSq t) (ricciNormSq t)
          (tracefreeNormSq t) (cubicQ t) (scalar t) := by
  intro t
  have hcubic :
      4 * reaction t - 4 * nInv * scalar t * ricciNormSq t =
        (4 * ricciNormSq t * tracefreeNormSq t - 2 * cubicQ t) / scalar t :=
    hamilton3D_cubic_reaction_simplification
      nInv (scalar t) (ricciNormSq t) (tracefreeNormSq t) (cubicQ t)
      (reaction t) (h_scalar_ne t) h_nInv (h_tracefree t) (h_reaction t)
  rw [tracefreeRicciNormHamilton3DRHS_eval]
  calc
    (ricciNormDt t - 2 * nInv * scalar t * scalarDt t) -
        (ricciNormLap t -
          nInv * (2 * scalar t * scalarLap t + 2 * gradScalarNormSq t))
        = (ricciNormDt t - ricciNormLap t) -
            2 * nInv * scalar t * (scalarDt t - scalarLap t) +
            2 * nInv * gradScalarNormSq t := by ring
    _ = (-2 * nablaRicNormSq t + 4 * reaction t) -
          2 * nInv * scalar t * (2 * ricciNormSq t) +
          2 * nInv * gradScalarNormSq t := by
        rw [h_ricciNorm_heat t, h_scalar_heat t]
    _ = -2 * nablaRicNormSq t +
          ((2 : R) / 3) * gradScalarNormSq t +
          (4 * reaction t - 4 * nInv * scalar t * ricciNormSq t) := by
        rw [h_nInv]
        ring
    _ = -2 * nablaRicNormSq t +
          ((2 : R) / 3) * gradScalarNormSq t +
          (4 * ricciNormSq t * tracefreeNormSq t - 2 * cubicQ t) / scalar t := by
        rw [hcubic]

end Hamilton3DTracefreeEvolutionInterface

section Hamilton3DTracefreeEvolutionSyntheticBridge

variable {k R V Time : Type*} {A : Type*}
variable [Field k] [Field R] [Algebra k R]
variable [AddCommGroup V] [Module R V] [Module k V] [IsScalarTower k R V]
variable [CommRing A] [Algebra R A]

/-- Time-slice scalar Laplacian for a time-dependent scalar family, using the
metric and connection at the same time. -/
noncomputable def scalarLaplacianAlongTimeSlice
    (emb : DerivationEmbedding k R V) (atr : AbstractTrace R V)
    (g_fam : Time -> MetricDuality R V)
    (conn_fam : Time -> V -> V -> V)
    (ha_fam : forall s, forall X Y Z, conn_fam s X (Y + Z) = conn_fam s X Y + conn_fam s X Z)
    (hal_fam : forall s, forall X Y Z, conn_fam s (X + Y) Z = conn_fam s X Z + conn_fam s Y Z)
    (hsl_fam : forall s, forall (f : R) X Z, conn_fam s (f • X) Z = f • conn_fam s X Z)
    (hl_fam : forall s, forall X (f : R) Y,
      conn_fam s X (f • Y) = (emb.embed X) f • Y + f • conn_fam s X Y) :
    (Time -> R) -> Time -> R :=
  fun u t => laplacian emb (g_fam t) atr (conn_fam t)
    (ha_fam t) (hl_fam t) (hal_fam t) (hsl_fam t) (u t)

theorem scalarLaplacianAlongTimeSlice_eval
    (emb : DerivationEmbedding k R V) (atr : AbstractTrace R V)
    (g_fam : Time -> MetricDuality R V)
    (conn_fam : Time -> V -> V -> V)
    (ha_fam : forall s, forall X Y Z, conn_fam s X (Y + Z) = conn_fam s X Y + conn_fam s X Z)
    (hal_fam : forall s, forall X Y Z, conn_fam s (X + Y) Z = conn_fam s X Z + conn_fam s Y Z)
    (hsl_fam : forall s, forall (f : R) X Z, conn_fam s (f • X) Z = f • conn_fam s X Z)
    (hl_fam : forall s, forall X (f : R) Y,
      conn_fam s X (f • Y) = (emb.embed X) f • Y + f • conn_fam s X Y)
    (u : Time -> R) (t : Time) :
    scalarLaplacianAlongTimeSlice emb atr g_fam conn_fam ha_fam hal_fam hsl_fam hl_fam
        u t =
      laplacian emb (g_fam t) atr (conn_fam t)
        (ha_fam t) (hl_fam t) (hal_fam t) (hsl_fam t) (u t) := by
  rfl

/-- Ricci norm squared as a time-dependent scalar along a family of metrics
and connections. -/
noncomputable def ricciNormSqAlongFlow
    (emb : DerivationEmbedding k R V) (atr : AbstractTrace R V)
    (g_fam : Time -> MetricDuality R V)
    (conn_fam : Time -> V -> V -> V)
    (ha_fam : forall s, forall X Y Z, conn_fam s X (Y + Z) = conn_fam s X Y + conn_fam s X Z)
    (hal_fam : forall s, forall X Y Z, conn_fam s (X + Y) Z = conn_fam s X Z + conn_fam s Y Z)
    (hsl_fam : forall s, forall (f : R) X Z, conn_fam s (f • X) Z = f • conn_fam s X Z)
    (hl_fam : forall s, forall X (f : R) Y,
      conn_fam s X (f • Y) = (emb.embed X) f • Y + f • conn_fam s X Y) :
    Time -> R :=
  fun t =>
    ricci_norm_sq emb (conn_fam t) (ha_fam t) (hal_fam t)
      (hsl_fam t) (hl_fam t) atr (g_fam t)

theorem ricciNormSqAlongFlow_eval
    (emb : DerivationEmbedding k R V) (atr : AbstractTrace R V)
    (g_fam : Time -> MetricDuality R V)
    (conn_fam : Time -> V -> V -> V)
    (ha_fam : forall s, forall X Y Z, conn_fam s X (Y + Z) = conn_fam s X Y + conn_fam s X Z)
    (hal_fam : forall s, forall X Y Z, conn_fam s (X + Y) Z = conn_fam s X Z + conn_fam s Y Z)
    (hsl_fam : forall s, forall (f : R) X Z, conn_fam s (f • X) Z = f • conn_fam s X Z)
    (hl_fam : forall s, forall X (f : R) Y,
      conn_fam s X (f • Y) = (emb.embed X) f • Y + f • conn_fam s X Y)
    (t : Time) :
    ricciNormSqAlongFlow emb atr g_fam conn_fam ha_fam hal_fam hsl_fam hl_fam t =
      ricci_norm_sq emb (conn_fam t) (ha_fam t) (hal_fam t)
        (hsl_fam t) (hl_fam t) atr (g_fam t) := by
  rfl

/-- Scalar curvature as a time-dependent scalar along a family of metrics and
connections. -/
noncomputable def scalarCurvatureAlongFlow
    (emb : DerivationEmbedding k R V) (atr : AbstractTrace R V)
    (g_fam : Time -> MetricDuality R V)
    (conn_fam : Time -> V -> V -> V)
    (ha_fam : forall s, forall X Y Z, conn_fam s X (Y + Z) = conn_fam s X Y + conn_fam s X Z)
    (hal_fam : forall s, forall X Y Z, conn_fam s (X + Y) Z = conn_fam s X Z + conn_fam s Y Z)
    (hsl_fam : forall s, forall (f : R) X Z, conn_fam s (f • X) Z = f • conn_fam s X Z)
    (hl_fam : forall s, forall X (f : R) Y,
      conn_fam s X (f • Y) = (emb.embed X) f • Y + f • conn_fam s X Y) :
    Time -> R :=
  fun t =>
    ScalarCurvature emb (conn_fam t) (ha_fam t) (hal_fam t)
      (hsl_fam t) (hl_fam t) atr (g_fam t)

theorem scalarCurvatureAlongFlow_eval
    (emb : DerivationEmbedding k R V) (atr : AbstractTrace R V)
    (g_fam : Time -> MetricDuality R V)
    (conn_fam : Time -> V -> V -> V)
    (ha_fam : forall s, forall X Y Z, conn_fam s X (Y + Z) = conn_fam s X Y + conn_fam s X Z)
    (hal_fam : forall s, forall X Y Z, conn_fam s (X + Y) Z = conn_fam s X Z + conn_fam s Y Z)
    (hsl_fam : forall s, forall (f : R) X Z, conn_fam s (f • X) Z = f • conn_fam s X Z)
    (hl_fam : forall s, forall X (f : R) Y,
      conn_fam s X (f • Y) = (emb.embed X) f • Y + f • conn_fam s X Y)
    (t : Time) :
    scalarCurvatureAlongFlow emb atr g_fam conn_fam ha_fam hal_fam hsl_fam hl_fam t =
      ScalarCurvature emb (conn_fam t) (ha_fam t) (hal_fam t)
        (hsl_fam t) (hl_fam t) atr (g_fam t) := by
  rfl

/-- Scalar heat equation from the existing scalar-curvature evolution theorem.

This is the Lean form of `partial_t R = Delta R + 2 |Ric|^2`: once the
realization has identified the trace of `partial_t Ric` with the scalar
Laplacian term `scalarLap`, the P3 scalar input
`scalarDt - scalarLap = 2 |Ric|^2` follows by subtraction. -/
theorem scalar_heat_eq_of_full_evolution
    (emb : DerivationEmbedding k R V)
    (td : TimeDerivativeData R A Time) [TimeRegularFam td]
    (atr : AbstractTrace R V)
    (g_fam : Time -> MetricDuality R V)
    (h_met : forall vs covs, td.isSmoothFam (fun s => (g_fam s).g_tensor vs covs))
    (conn_fam : Time -> V -> V -> V)
    (ha_fam : forall s, forall X Y Z, conn_fam s X (Y + Z) = conn_fam s X Y + conn_fam s X Z)
    (hal_fam : forall s, forall X Y Z, conn_fam s (X + Y) Z = conn_fam s X Z + conn_fam s Y Z)
    (hsl_fam : forall s, forall (f : R) X Z, conn_fam s (f • X) Z = f • conn_fam s X Z)
    (hl_fam : forall s, forall X (f : R) Y,
      conn_fam s X (f • Y) = (emb.embed X) f • Y + f • conn_fam s X Y)
    (h_Rc_smooth : forall vs covs, td.isSmoothFam
      (fun s =>
        ricciForm_tensor emb (conn_fam s) (ha_fam s) (hal_fam s)
          (hsl_fam s) (hl_fam s) atr vs covs))
    (h_rf : IsRicciFlow emb td atr g_fam h_met conn_fam ha_fam hal_fam hsl_fam hl_fam)
    (h_sc_prod : ScalarCurvatureProductRule emb td atr g_fam h_met conn_fam
      ha_fam hal_fam hsl_fam hl_fam h_Rc_smooth)
    (scalarDt scalarLap : Time -> R)
    (h_scalar_dt : forall t,
      td.dt_apply
        (scalarCurvatureAlongFlow emb atr g_fam conn_fam ha_fam hal_fam hsl_fam hl_fam)
        t = scalarDt t)
    (h_trace : RicciTraceIdentity emb td atr g_fam conn_fam ha_fam hal_fam hsl_fam
      hl_fam h_Rc_smooth scalarLap) :
    forall t,
      scalarDt t - scalarLap t =
        2 * ricciNormSqAlongFlow emb atr g_fam conn_fam ha_fam hal_fam hsl_fam hl_fam t := by
  intro t
  have h_full :=
    scalar_curvature_evolution_full emb td atr g_fam h_met conn_fam ha_fam
      hal_fam hsl_fam hl_fam h_Rc_smooth h_rf h_sc_prod scalarLap h_trace t
  have h_dt :
      scalarDt t =
        scalarLap t +
          2 * ricciNormSqAlongFlow emb atr g_fam conn_fam ha_fam hal_fam
            hsl_fam hl_fam t := by
    rw [← h_scalar_dt t]
    simpa [scalarCurvatureAlongFlow, ricciNormSqAlongFlow] using h_full
  rw [h_dt]
  ring

/-- Trace-free Ricci norm squared as a time-dependent scalar along a family of
metrics and connections. -/
noncomputable def tracefreeRicciNormSqAlongFlow
    (emb : DerivationEmbedding k R V) (atr : AbstractTrace R V)
    (g_fam : Time -> MetricDuality R V)
    (conn_fam : Time -> V -> V -> V)
    (ha_fam : forall s, forall X Y Z, conn_fam s X (Y + Z) = conn_fam s X Y + conn_fam s X Z)
    (hal_fam : forall s, forall X Y Z, conn_fam s (X + Y) Z = conn_fam s X Z + conn_fam s Y Z)
    (hsl_fam : forall s, forall (f : R) X Z, conn_fam s (f • X) Z = f • conn_fam s X Z)
    (hl_fam : forall s, forall X (f : R) Y,
      conn_fam s X (f • Y) = (emb.embed X) f • Y + f • conn_fam s X Y)
    (nInv : R) : Time -> R :=
  fun t =>
    tracefree_ricci_norm_sq emb (conn_fam t) (ha_fam t) (hal_fam t)
      (hsl_fam t) (hl_fam t) atr (g_fam t) nInv

theorem tracefreeRicciNormSqAlongFlow_eval
    (emb : DerivationEmbedding k R V) (atr : AbstractTrace R V)
    (g_fam : Time -> MetricDuality R V)
    (conn_fam : Time -> V -> V -> V)
    (ha_fam : forall s, forall X Y Z, conn_fam s X (Y + Z) = conn_fam s X Y + conn_fam s X Z)
    (hal_fam : forall s, forall X Y Z, conn_fam s (X + Y) Z = conn_fam s X Z + conn_fam s Y Z)
    (hsl_fam : forall s, forall (f : R) X Z, conn_fam s (f • X) Z = f • conn_fam s X Z)
    (hl_fam : forall s, forall X (f : R) Y,
      conn_fam s X (f • Y) = (emb.embed X) f • Y + f • conn_fam s X Y)
    (nInv : R) (t : Time) :
    tracefreeRicciNormSqAlongFlow emb atr g_fam conn_fam ha_fam hal_fam hsl_fam hl_fam
        nInv t =
      tracefree_ricci_norm_sq emb (conn_fam t) (ha_fam t) (hal_fam t)
        (hsl_fam t) (hl_fam t) atr (g_fam t) nInv := by
  rfl

/-- P3.1 time-derivative component. The trace-free norm derivative follows
from `|Ric^0|^2 = |Ric|^2 - nInv * R^2`, the Ricci-norm derivative, the scalar
derivative, and the ordinary time-product rule. -/
theorem tracefree_ricci_norm_dt_eq_of_ricci_norm_dt_and_scalar_dt
    (emb : DerivationEmbedding k R V)
    (td : TimeDerivativeData R A Time) [TimeRegularFam td]
    (atr : AbstractTrace R V)
    (g_fam : Time -> MetricDuality R V)
    (conn_fam : Time -> V -> V -> V)
    (ha_fam : forall s, forall X Y Z, conn_fam s X (Y + Z) = conn_fam s X Y + conn_fam s X Z)
    (hal_fam : forall s, forall X Y Z, conn_fam s (X + Y) Z = conn_fam s X Z + conn_fam s Y Z)
    (hsl_fam : forall s, forall (f : R) X Z, conn_fam s (f • X) Z = f • conn_fam s X Z)
    (hl_fam : forall s, forall X (f : R) Y,
      conn_fam s X (f • Y) = (emb.embed X) f • Y + f • conn_fam s X Y)
    (nInv : R)
    (h_nInv_dim : nInv * abstractTraceDimension atr = 1)
    (ricciNormDt scalarDt : Time -> R)
    (h_ricciNorm_dt :
      RicciNormEvolutionEquation emb td atr g_fam conn_fam ha_fam hal_fam
        hsl_fam hl_fam ricciNormDt)
    (h_scalar_dt : forall t,
      td.dt_apply
        (scalarCurvatureAlongFlow emb atr g_fam conn_fam ha_fam hal_fam hsl_fam hl_fam)
        t = scalarDt t)
    (h_ricciNorm_smooth :
      td.isSmoothFam
        (ricciNormSqAlongFlow emb atr g_fam conn_fam ha_fam hal_fam hsl_fam hl_fam))
    (h_scalar_smooth :
      td.isSmoothFam
        (scalarCurvatureAlongFlow emb atr g_fam conn_fam ha_fam hal_fam hsl_fam hl_fam)) :
    TracefreeRicciNormEvolutionEquation emb td atr g_fam conn_fam ha_fam hal_fam
      hsl_fam hl_fam nInv
      (fun t =>
        ricciNormDt t -
          2 * nInv *
            scalarCurvatureAlongFlow emb atr g_fam conn_fam ha_fam hal_fam hsl_fam hl_fam t *
            scalarDt t) := by
  intro t
  let ricciNorm :=
    ricciNormSqAlongFlow emb atr g_fam conn_fam ha_fam hal_fam hsl_fam hl_fam
  let scalar :=
    scalarCurvatureAlongFlow emb atr g_fam conn_fam ha_fam hal_fam hsl_fam hl_fam
  have h_expand_fun :
      (fun s =>
        tracefree_ricci_norm_sq emb (conn_fam s) (ha_fam s) (hal_fam s)
          (hsl_fam s) (hl_fam s) atr (g_fam s) nInv) =
      (fun s => ricciNorm s - nInv * scalar s * scalar s) := by
    ext s
    dsimp [ricciNorm, scalar, ricciNormSqAlongFlow, scalarCurvatureAlongFlow]
    exact tracefree_ricci_norm_sq_expand_abstractTraceDimension emb
      (conn_fam s) (ha_fam s) (hal_fam s) (hsl_fam s) (hl_fam s)
      atr (g_fam s) nInv h_nInv_dim
  have h_ricciNorm_smooth' : td.isSmoothFam ricciNorm := by
    simpa [ricciNorm] using h_ricciNorm_smooth
  have h_scalar_smooth' : td.isSmoothFam scalar := by
    simpa [scalar] using h_scalar_smooth
  have h_scalar_sq_smooth : td.isSmoothFam (fun s => scalar s * scalar s) := by
    simpa using td.isSmoothFam_mul scalar scalar h_scalar_smooth' h_scalar_smooth'
  have h_nInv_scalar_sq_smooth : td.isSmoothFam (fun s => nInv * scalar s * scalar s) := by
    have h :=
      td.isSmoothFam_const_mul nInv (fun s => scalar s * scalar s) h_scalar_sq_smooth
    simpa [mul_assoc] using h
  have h_square_dt :
      td.dt_apply (fun s => nInv * scalar s * scalar s) t =
        2 * nInv * scalar t * scalarDt t := by
    have h_assoc :
        (fun s => nInv * scalar s * scalar s) =
          (fun s => nInv * (scalar s * scalar s)) := by
      ext s
      ring
    calc
      td.dt_apply (fun s => nInv * scalar s * scalar s) t
          = td.dt_apply (fun s => nInv * (scalar s * scalar s)) t := by
              exact congr_arg (fun f : Time -> R => td.dt_apply f t) h_assoc
      _ = nInv * td.dt_apply (fun s => scalar s * scalar s) t := by
          exact td.dt_apply_const_mul nInv (fun s => scalar s * scalar s) t
            h_scalar_sq_smooth
      _ = nInv * (scalar t * td.dt_apply scalar t + scalar t * td.dt_apply scalar t) := by
          have h_mul := td.dt_apply_mul scalar scalar t h_scalar_smooth' h_scalar_smooth'
          exact congr_arg (fun a => nInv * a) (by simpa [Pi.mul_apply] using h_mul)
      _ = nInv * (scalar t * scalarDt t + scalar t * scalarDt t) := by
          rw [h_scalar_dt t]
      _ = 2 * nInv * scalar t * scalarDt t := by ring
  have h_dt_expand := congr_arg (fun f : Time -> R => td.dt_apply f t) h_expand_fun
  calc
    td.dt_apply
        (fun s =>
          tracefree_ricci_norm_sq emb (conn_fam s) (ha_fam s) (hal_fam s)
            (hsl_fam s) (hl_fam s) atr (g_fam s) nInv) t
        = td.dt_apply (fun s => ricciNorm s - nInv * scalar s * scalar s) t := h_dt_expand
    _ = td.dt_apply ricciNorm t -
          td.dt_apply (fun s => nInv * scalar s * scalar s) t := by
        have h_sub_fun :
            (fun s => ricciNorm s - nInv * scalar s * scalar s) =
              ricciNorm - (fun s => nInv * scalar s * scalar s) := by
          ext s
          rfl
        calc
          td.dt_apply (fun s => ricciNorm s - nInv * scalar s * scalar s) t
              = td.dt_apply (ricciNorm - (fun s => nInv * scalar s * scalar s)) t := by
                  exact congr_arg (fun f : Time -> R => td.dt_apply f t) h_sub_fun
          _ = td.dt_apply ricciNorm t -
                td.dt_apply (fun s => nInv * scalar s * scalar s) t := by
              rw [td.dt_apply_sub ricciNorm (fun s => nInv * scalar s * scalar s) t
                h_ricciNorm_smooth' h_nInv_scalar_sq_smooth]
    _ = ricciNormDt t - 2 * nInv * scalar t * scalarDt t := by
        rw [h_square_dt]
        change td.dt_apply
          (fun s =>
            ricci_norm_sq emb (conn_fam s) (ha_fam s) (hal_fam s)
              (hsl_fam s) (hl_fam s) atr (g_fam s)) t -
            2 * nInv * scalar t * scalarDt t =
          ricciNormDt t - 2 * nInv * scalar t * scalarDt t
        rw [h_ricciNorm_dt t]

/-- P3.2 Laplacian component. The trace-free norm Laplacian follows from
`|Ric^0|^2 = |Ric|^2 - nInv * R^2`, linearity of the scalar Laplacian, and a
supplied square rule `Delta(R^2) = 2 R Delta R + 2 |nabla R|^2`.

The square rule is explicit because `Operator/Laplacian.lean` currently has
add/sub/constant-smul linearity but no general `laplacian_mul` theorem. -/
theorem tracefree_ricci_norm_laplacian_eq_of_ricci_norm_laplacian_and_scalar_square
    (emb : DerivationEmbedding k R V) (atr : AbstractTrace R V)
    (g_fam : Time -> MetricDuality R V)
    (conn_fam : Time -> V -> V -> V)
    (ha_fam : forall s, forall X Y Z, conn_fam s X (Y + Z) = conn_fam s X Y + conn_fam s X Z)
    (hal_fam : forall s, forall X Y Z, conn_fam s (X + Y) Z = conn_fam s X Z + conn_fam s Y Z)
    (hsl_fam : forall s, forall (f : R) X Z, conn_fam s (f • X) Z = f • conn_fam s X Z)
    (hl_fam : forall s, forall X (f : R) Y,
      conn_fam s X (f • Y) = (emb.embed X) f • Y + f • conn_fam s X Y)
    (nInv : R)
    (h_nInv_dim : nInv * abstractTraceDimension atr = 1)
    (h_nInv_const : forall X : V, action emb X nInv = 0)
    (ricciNormLap scalarLap gradScalarNormSq : Time -> R)
    (h_ricciNorm_lap : forall t,
      scalarLaplacianAlongTimeSlice emb atr g_fam conn_fam ha_fam hal_fam hsl_fam hl_fam
        (ricciNormSqAlongFlow emb atr g_fam conn_fam ha_fam hal_fam hsl_fam hl_fam) t =
      ricciNormLap t)
    (h_scalar_square_lap : forall t,
      scalarLaplacianAlongTimeSlice emb atr g_fam conn_fam ha_fam hal_fam hsl_fam hl_fam
        (fun s =>
          scalarCurvatureAlongFlow emb atr g_fam conn_fam ha_fam hal_fam hsl_fam hl_fam s *
          scalarCurvatureAlongFlow emb atr g_fam conn_fam ha_fam hal_fam hsl_fam hl_fam s) t =
      2 *
          scalarCurvatureAlongFlow emb atr g_fam conn_fam ha_fam hal_fam hsl_fam hl_fam t *
          scalarLap t +
        2 * gradScalarNormSq t) :
    forall t,
      scalarLaplacianAlongTimeSlice emb atr g_fam conn_fam ha_fam hal_fam hsl_fam hl_fam
          (tracefreeRicciNormSqAlongFlow emb atr g_fam conn_fam ha_fam hal_fam
            hsl_fam hl_fam nInv) t =
        ricciNormLap t -
          nInv *
            (2 *
                scalarCurvatureAlongFlow emb atr g_fam conn_fam ha_fam hal_fam hsl_fam hl_fam t *
                scalarLap t +
              2 * gradScalarNormSq t) := by
  intro t
  let ricciNorm :=
    ricciNormSqAlongFlow emb atr g_fam conn_fam ha_fam hal_fam hsl_fam hl_fam
  let scalar :=
    scalarCurvatureAlongFlow emb atr g_fam conn_fam ha_fam hal_fam hsl_fam hl_fam
  have hric := h_ricciNorm_lap t
  have hsquare := h_scalar_square_lap t
  change laplacian emb (g_fam t) atr (conn_fam t)
      (ha_fam t) (hl_fam t) (hal_fam t) (hsl_fam t)
      (tracefree_ricci_norm_sq emb (conn_fam t) (ha_fam t) (hal_fam t)
        (hsl_fam t) (hl_fam t) atr (g_fam t) nInv) =
    ricciNormLap t - nInv * (2 * scalar t * scalarLap t + 2 * gradScalarNormSq t)
  rw [tracefree_ricci_norm_sq_expand_abstractTraceDimension emb
    (conn_fam t) (ha_fam t) (hal_fam t) (hsl_fam t) (hl_fam t)
    atr (g_fam t) nInv h_nInv_dim]
  change laplacian emb (g_fam t) atr (conn_fam t)
      (ha_fam t) (hl_fam t) (hal_fam t) (hsl_fam t)
      (ricciNorm t - nInv * scalar t * scalar t) =
    ricciNormLap t - nInv * (2 * scalar t * scalarLap t + 2 * gradScalarNormSq t)
  rw [show nInv * scalar t * scalar t = nInv * (scalar t * scalar t) by ring]
  rw [laplacian_sub emb (g_fam t) atr (conn_fam t) (ha_fam t) (hl_fam t)
    (hal_fam t) (hsl_fam t)]
  rw [laplacian_smul emb (g_fam t) atr (conn_fam t) (ha_fam t) (hl_fam t)
    (hal_fam t) (hsl_fam t) nInv (scalar t * scalar t) h_nInv_const]
  change
    scalarLaplacianAlongTimeSlice emb atr g_fam conn_fam ha_fam hal_fam hsl_fam hl_fam
        ricciNorm t -
      nInv *
        scalarLaplacianAlongTimeSlice emb atr g_fam conn_fam ha_fam hal_fam hsl_fam hl_fam
          (fun s => scalar s * scalar s) t =
    ricciNormLap t - nInv * (2 * scalar t * scalarLap t + 2 * gradScalarNormSq t)
  rw [hric, hsquare]

/-- Component bridge for P3. If the time derivative of `|Ric^0|^2`, the
time-slice scalar Laplacian of `|Ric^0|^2`, and the scalar Hamilton algebraic
RHS have been identified, then the closed `(dt - Delta)|Ric^0|^2` equation
follows.

The `h_rhs` hypothesis is the hard cubic simplification after the
Riemann-Ricci-Ricci contraction has been substituted: after expanding Ricci and
scalar evolution, it identifies the remaining terms with Hamilton's 3D RHS. This
is where the Lemma 10.7 factorization and Lemma 10.8 pinching lower-bound
application enter the future proof. -/
theorem hamilton3D_tracefree_norm_evolution_eq_of_components
    (emb : DerivationEmbedding k R V)
    (td : TimeDerivativeData R A Time) [TimeRegularFam td]
    (atr : AbstractTrace R V)
    (g_fam : Time -> MetricDuality R V)
    (conn_fam : Time -> V -> V -> V)
    (ha_fam : forall s, forall X Y Z, conn_fam s X (Y + Z) = conn_fam s X Y + conn_fam s X Z)
    (hal_fam : forall s, forall X Y Z, conn_fam s (X + Y) Z = conn_fam s X Z + conn_fam s Y Z)
    (hsl_fam : forall s, forall (f : R) X Z, conn_fam s (f • X) Z = f • conn_fam s X Z)
    (hl_fam : forall s, forall X (f : R) Y,
      conn_fam s X (f • Y) = (emb.embed X) f • Y + f • conn_fam s X Y)
    (nInv : R)
    (dtRhs laplacianRhs nablaRicNormSq nablaScalarNormSq ricciNormSq cubicQ scalar :
      Time -> R)
    (h_dt :
      TracefreeRicciNormEvolutionEquation emb td atr g_fam conn_fam ha_fam hal_fam
        hsl_fam hl_fam nInv dtRhs)
    (h_laplacian : forall t,
      scalarLaplacianAlongTimeSlice emb atr g_fam conn_fam ha_fam hal_fam hsl_fam hl_fam
          (tracefreeRicciNormSqAlongFlow emb atr g_fam conn_fam ha_fam hal_fam
            hsl_fam hl_fam nInv) t =
        laplacianRhs t)
    (h_rhs : forall t,
      dtRhs t - laplacianRhs t =
        tracefreeRicciNormHamilton3DRHS
          (nablaRicNormSq t) (nablaScalarNormSq t) (ricciNormSq t)
          (tracefreeRicciNormSqAlongFlow emb atr g_fam conn_fam ha_fam hal_fam
            hsl_fam hl_fam nInv t)
          (cubicQ t) (scalar t)) :
    TracefreeRicciNormHamilton3DTimeLaplacianEquation
      (fun u t => td.dt_apply u t)
      (scalarLaplacianAlongTimeSlice emb atr g_fam conn_fam ha_fam hal_fam hsl_fam hl_fam)
      (tracefreeRicciNormSqAlongFlow emb atr g_fam conn_fam ha_fam hal_fam hsl_fam hl_fam nInv)
      nablaRicNormSq nablaScalarNormSq ricciNormSq cubicQ scalar := by
  intro t
  change
    td.dt_apply (fun s =>
      tracefree_ricci_norm_sq emb (conn_fam s) (ha_fam s) (hal_fam s)
        (hsl_fam s) (hl_fam s) atr (g_fam s) nInv) t -
      scalarLaplacianAlongTimeSlice emb atr g_fam conn_fam ha_fam hal_fam hsl_fam hl_fam
        (tracefreeRicciNormSqAlongFlow emb atr g_fam conn_fam ha_fam hal_fam
          hsl_fam hl_fam nInv) t =
      tracefreeRicciNormHamilton3DRHS
        (nablaRicNormSq t) (nablaScalarNormSq t) (ricciNormSq t)
        (tracefreeRicciNormSqAlongFlow emb atr g_fam conn_fam ha_fam hal_fam
          hsl_fam hl_fam nInv t)
        (cubicQ t) (scalar t)
  rw [h_dt t, h_laplacian t]
  exact h_rhs t

/-- P3 composition theorem with the `h_dt` and `h_laplacian` bridge inputs
discharged by the trace-free expansion. The remaining `h_rhs` assumption is the
Hamilton 3D cubic simplification after substituting the Riemann-Ricci-Ricci
contraction identity and these component time-derivative and Laplacian
formulas. -/
theorem hamilton3D_tracefree_norm_eq_of_dt_lap_components
    (emb : DerivationEmbedding k R V)
    (td : TimeDerivativeData R A Time) [TimeRegularFam td]
    (atr : AbstractTrace R V)
    (g_fam : Time -> MetricDuality R V)
    (conn_fam : Time -> V -> V -> V)
    (ha_fam : forall s, forall X Y Z, conn_fam s X (Y + Z) = conn_fam s X Y + conn_fam s X Z)
    (hal_fam : forall s, forall X Y Z, conn_fam s (X + Y) Z = conn_fam s X Z + conn_fam s Y Z)
    (hsl_fam : forall s, forall (f : R) X Z, conn_fam s (f • X) Z = f • conn_fam s X Z)
    (hl_fam : forall s, forall X (f : R) Y,
      conn_fam s X (f • Y) = (emb.embed X) f • Y + f • conn_fam s X Y)
    (nInv : R)
    (h_nInv_dim : nInv * abstractTraceDimension atr = 1)
    (h_nInv_const : forall X : V, action emb X nInv = 0)
    (ricciNormDt scalarDt ricciNormLap scalarLap gradScalarNormSq
        nablaRicNormSq nablaScalarNormSq ricciNormSq cubicQ scalar : Time -> R)
    (h_ricciNorm_dt :
      RicciNormEvolutionEquation emb td atr g_fam conn_fam ha_fam hal_fam
        hsl_fam hl_fam ricciNormDt)
    (h_scalar_dt : forall t,
      td.dt_apply
        (scalarCurvatureAlongFlow emb atr g_fam conn_fam ha_fam hal_fam hsl_fam hl_fam)
        t = scalarDt t)
    (h_ricciNorm_smooth :
      td.isSmoothFam
        (ricciNormSqAlongFlow emb atr g_fam conn_fam ha_fam hal_fam hsl_fam hl_fam))
    (h_scalar_smooth :
      td.isSmoothFam
        (scalarCurvatureAlongFlow emb atr g_fam conn_fam ha_fam hal_fam hsl_fam hl_fam))
    (h_ricciNorm_lap : forall t,
      scalarLaplacianAlongTimeSlice emb atr g_fam conn_fam ha_fam hal_fam hsl_fam hl_fam
        (ricciNormSqAlongFlow emb atr g_fam conn_fam ha_fam hal_fam hsl_fam hl_fam) t =
      ricciNormLap t)
    (h_scalar_square_lap : forall t,
      scalarLaplacianAlongTimeSlice emb atr g_fam conn_fam ha_fam hal_fam hsl_fam hl_fam
        (fun s =>
          scalarCurvatureAlongFlow emb atr g_fam conn_fam ha_fam hal_fam hsl_fam hl_fam s *
          scalarCurvatureAlongFlow emb atr g_fam conn_fam ha_fam hal_fam hsl_fam hl_fam s) t =
      2 *
          scalarCurvatureAlongFlow emb atr g_fam conn_fam ha_fam hal_fam hsl_fam hl_fam t *
          scalarLap t +
        2 * gradScalarNormSq t)
    (h_rhs : forall t,
      (ricciNormDt t -
            2 * nInv *
              scalarCurvatureAlongFlow emb atr g_fam conn_fam ha_fam hal_fam hsl_fam hl_fam t *
              scalarDt t) -
          (ricciNormLap t -
            nInv *
              (2 *
                  scalarCurvatureAlongFlow emb atr g_fam conn_fam ha_fam hal_fam hsl_fam hl_fam t *
                  scalarLap t +
                2 * gradScalarNormSq t)) =
        tracefreeRicciNormHamilton3DRHS
          (nablaRicNormSq t) (nablaScalarNormSq t) (ricciNormSq t)
          (tracefreeRicciNormSqAlongFlow emb atr g_fam conn_fam ha_fam hal_fam
            hsl_fam hl_fam nInv t)
          (cubicQ t) (scalar t)) :
    TracefreeRicciNormHamilton3DTimeLaplacianEquation
      (fun u t => td.dt_apply u t)
      (scalarLaplacianAlongTimeSlice emb atr g_fam conn_fam ha_fam hal_fam hsl_fam hl_fam)
      (tracefreeRicciNormSqAlongFlow emb atr g_fam conn_fam ha_fam hal_fam hsl_fam hl_fam nInv)
      nablaRicNormSq nablaScalarNormSq ricciNormSq cubicQ scalar :=
  hamilton3D_tracefree_norm_evolution_eq_of_components emb td atr g_fam conn_fam
    ha_fam hal_fam hsl_fam hl_fam nInv
    (fun t =>
      ricciNormDt t -
        2 * nInv *
          scalarCurvatureAlongFlow emb atr g_fam conn_fam ha_fam hal_fam hsl_fam hl_fam t *
          scalarDt t)
    (fun t =>
      ricciNormLap t -
        nInv *
          (2 *
              scalarCurvatureAlongFlow emb atr g_fam conn_fam ha_fam hal_fam hsl_fam hl_fam t *
              scalarLap t +
            2 * gradScalarNormSq t))
    nablaRicNormSq nablaScalarNormSq ricciNormSq cubicQ scalar
    (tracefree_ricci_norm_dt_eq_of_ricci_norm_dt_and_scalar_dt emb td atr g_fam
      conn_fam ha_fam hal_fam hsl_fam hl_fam nInv h_nInv_dim ricciNormDt scalarDt
      h_ricciNorm_dt h_scalar_dt h_ricciNorm_smooth h_scalar_smooth)
    (tracefree_ricci_norm_laplacian_eq_of_ricci_norm_laplacian_and_scalar_square emb atr
      g_fam conn_fam ha_fam hal_fam hsl_fam hl_fam nInv h_nInv_dim h_nInv_const
      ricciNormLap scalarLap gradScalarNormSq h_ricciNorm_lap h_scalar_square_lap)
    h_rhs

/-- P3.3 wrapper: the Hamilton trace-free norm equation after discharging the
component `dt`, component Laplacian, and cubic Riemann-Ricci-Ricci contraction
RHS obligations.

The new geometric input relative to P3.1/P3.2 is `h_reaction`, the identity for
the Riemann-Ricci-Ricci contraction scalar obtained from the 3D
Riemann-from-Ricci formula:
`2 R * reaction = 2 |Ric|^4 - Q`. The name `reaction` here is the existing
parameter name for that contraction scalar. -/
theorem hamilton3D_tracefree_norm_eq_of_cubic_reaction_components
    (emb : DerivationEmbedding k R V)
    (td : TimeDerivativeData R A Time) [TimeRegularFam td]
    (atr : AbstractTrace R V)
    (g_fam : Time -> MetricDuality R V)
    (conn_fam : Time -> V -> V -> V)
    (ha_fam : forall s, forall X Y Z, conn_fam s X (Y + Z) = conn_fam s X Y + conn_fam s X Z)
    (hal_fam : forall s, forall X Y Z, conn_fam s (X + Y) Z = conn_fam s X Z + conn_fam s Y Z)
    (hsl_fam : forall s, forall (f : R) X Z, conn_fam s (f • X) Z = f • conn_fam s X Z)
    (hl_fam : forall s, forall X (f : R) Y,
      conn_fam s X (f • Y) = (emb.embed X) f • Y + f • conn_fam s X Y)
    (nInv : R)
    (h_nInv_dim : nInv * abstractTraceDimension atr = 1)
    (h_nInv_const : forall X : V, action emb X nInv = 0)
    (h_nInv : nInv = (1 : R) / 3)
    (ricciNormDt scalarDt ricciNormLap scalarLap gradScalarNormSq
        nablaRicNormSq cubicQ reaction : Time -> R)
    (h_scalar_ne : forall t,
      scalarCurvatureAlongFlow emb atr g_fam conn_fam ha_fam hal_fam hsl_fam hl_fam t ≠ 0)
    (h_ricciNorm_dt :
      RicciNormEvolutionEquation emb td atr g_fam conn_fam ha_fam hal_fam
        hsl_fam hl_fam ricciNormDt)
    (h_scalar_dt : forall t,
      td.dt_apply
        (scalarCurvatureAlongFlow emb atr g_fam conn_fam ha_fam hal_fam hsl_fam hl_fam)
        t = scalarDt t)
    (h_ricciNorm_smooth :
      td.isSmoothFam
        (ricciNormSqAlongFlow emb atr g_fam conn_fam ha_fam hal_fam hsl_fam hl_fam))
    (h_scalar_smooth :
      td.isSmoothFam
        (scalarCurvatureAlongFlow emb atr g_fam conn_fam ha_fam hal_fam hsl_fam hl_fam))
    (h_ricciNorm_lap : forall t,
      scalarLaplacianAlongTimeSlice emb atr g_fam conn_fam ha_fam hal_fam hsl_fam hl_fam
        (ricciNormSqAlongFlow emb atr g_fam conn_fam ha_fam hal_fam hsl_fam hl_fam) t =
      ricciNormLap t)
    (h_scalar_square_lap : forall t,
      scalarLaplacianAlongTimeSlice emb atr g_fam conn_fam ha_fam hal_fam hsl_fam hl_fam
        (fun s =>
          scalarCurvatureAlongFlow emb atr g_fam conn_fam ha_fam hal_fam hsl_fam hl_fam s *
          scalarCurvatureAlongFlow emb atr g_fam conn_fam ha_fam hal_fam hsl_fam hl_fam s) t =
      2 *
          scalarCurvatureAlongFlow emb atr g_fam conn_fam ha_fam hal_fam hsl_fam hl_fam t *
          scalarLap t +
        2 * gradScalarNormSq t)
    (h_ricciNorm_heat : forall t,
      ricciNormDt t - ricciNormLap t =
        -2 * nablaRicNormSq t + 4 * reaction t)
    (h_scalar_heat : forall t,
      scalarDt t - scalarLap t =
        2 * ricciNormSqAlongFlow emb atr g_fam conn_fam ha_fam hal_fam hsl_fam hl_fam t)
    (h_reaction : forall t,
      2 *
          scalarCurvatureAlongFlow emb atr g_fam conn_fam ha_fam hal_fam hsl_fam hl_fam t *
          reaction t =
        2 *
            ricciNormSqAlongFlow emb atr g_fam conn_fam ha_fam hal_fam hsl_fam hl_fam t ^ 2 -
          cubicQ t) :
    TracefreeRicciNormHamilton3DTimeLaplacianEquation
      (fun u t => td.dt_apply u t)
      (scalarLaplacianAlongTimeSlice emb atr g_fam conn_fam ha_fam hal_fam hsl_fam hl_fam)
      (tracefreeRicciNormSqAlongFlow emb atr g_fam conn_fam ha_fam hal_fam hsl_fam hl_fam nInv)
      nablaRicNormSq gradScalarNormSq
      (ricciNormSqAlongFlow emb atr g_fam conn_fam ha_fam hal_fam hsl_fam hl_fam)
      cubicQ
      (scalarCurvatureAlongFlow emb atr g_fam conn_fam ha_fam hal_fam hsl_fam hl_fam) := by
  let ricciNorm :=
    ricciNormSqAlongFlow emb atr g_fam conn_fam ha_fam hal_fam hsl_fam hl_fam
  let scalar :=
    scalarCurvatureAlongFlow emb atr g_fam conn_fam ha_fam hal_fam hsl_fam hl_fam
  let tracefree :=
    tracefreeRicciNormSqAlongFlow emb atr g_fam conn_fam ha_fam hal_fam hsl_fam hl_fam nInv
  have h_tracefree : forall t, tracefree t = ricciNorm t - nInv * scalar t * scalar t := by
    intro t
    dsimp [tracefree, ricciNorm, scalar, tracefreeRicciNormSqAlongFlow,
      ricciNormSqAlongFlow, scalarCurvatureAlongFlow]
    exact tracefree_ricci_norm_sq_expand_abstractTraceDimension emb
      (conn_fam t) (ha_fam t) (hal_fam t) (hsl_fam t) (hl_fam t)
      atr (g_fam t) nInv h_nInv_dim
  exact hamilton3D_tracefree_norm_eq_of_dt_lap_components emb td atr g_fam conn_fam
    ha_fam hal_fam hsl_fam hl_fam nInv h_nInv_dim h_nInv_const
    ricciNormDt scalarDt ricciNormLap scalarLap gradScalarNormSq nablaRicNormSq
    gradScalarNormSq ricciNorm cubicQ scalar h_ricciNorm_dt h_scalar_dt
    h_ricciNorm_smooth h_scalar_smooth h_ricciNorm_lap h_scalar_square_lap
    (hamilton3D_tracefree_norm_rhs_of_cubic_reaction nInv ricciNormDt scalarDt
      ricciNormLap scalarLap gradScalarNormSq nablaRicNormSq ricciNorm tracefree
      cubicQ scalar reaction h_nInv (by simpa [scalar] using h_scalar_ne)
      h_tracefree h_ricciNorm_heat (by simpa [ricciNorm] using h_scalar_heat)
      (by simpa [ricciNorm, scalar] using h_reaction))

/-- P3 wrapper with the scalar heat and Ricci-norm heat inputs discharged from
their component evolution formulas.

The remaining explicitly supplied analytic input is the scalar-square
Laplacian rule `Delta(R^2) = 2 R Delta R + 2 |nabla R|^2`; the current
synthetic Laplacian API has linearity but no general multiplication theorem. -/
theorem hamilton3D_tracefree_norm_eq_of_heat_components
    (emb : DerivationEmbedding k R V)
    (td : TimeDerivativeData R A Time) [TimeRegularFam td]
    (atr : AbstractTrace R V)
    (g_fam : Time -> MetricDuality R V)
    (h_met : forall vs covs, td.isSmoothFam (fun s => (g_fam s).g_tensor vs covs))
    (conn_fam : Time -> V -> V -> V)
    (ha_fam : forall s, forall X Y Z, conn_fam s X (Y + Z) = conn_fam s X Y + conn_fam s X Z)
    (hal_fam : forall s, forall X Y Z, conn_fam s (X + Y) Z = conn_fam s X Z + conn_fam s Y Z)
    (hsl_fam : forall s, forall (f : R) X Z, conn_fam s (f • X) Z = f • conn_fam s X Z)
    (hl_fam : forall s, forall X (f : R) Y,
      conn_fam s X (f • Y) = (emb.embed X) f • Y + f • conn_fam s X Y)
    (h_Rc_smooth : forall vs covs, td.isSmoothFam
      (fun s =>
        ricciForm_tensor emb (conn_fam s) (ha_fam s) (hal_fam s)
          (hsl_fam s) (hl_fam s) atr vs covs))
    (h_rf : IsRicciFlow emb td atr g_fam h_met conn_fam ha_fam hal_fam hsl_fam hl_fam)
    (h_sc_prod : ScalarCurvatureProductRule emb td atr g_fam h_met conn_fam
      ha_fam hal_fam hsl_fam hl_fam h_Rc_smooth)
    (nInv : R)
    (h_nInv_dim : nInv * abstractTraceDimension atr = 1)
    (h_nInv_const : forall X : V, action emb X nInv = 0)
    (h_nInv : nInv = (1 : R) / 3)
    (ricciNormDt scalarDt ricciNormLap scalarLap gradScalarNormSq
        nablaRicNormSq cubicQ reaction lapInner : Time -> R)
    (h_scalar_ne : forall t,
      scalarCurvatureAlongFlow emb atr g_fam conn_fam ha_fam hal_fam hsl_fam hl_fam t ≠ 0)
    (h_ricciNorm_dt :
      RicciNormEvolutionEquation emb td atr g_fam conn_fam ha_fam hal_fam
        hsl_fam hl_fam ricciNormDt)
    (h_scalar_dt : forall t,
      td.dt_apply
        (scalarCurvatureAlongFlow emb atr g_fam conn_fam ha_fam hal_fam hsl_fam hl_fam)
        t = scalarDt t)
    (h_ricciNorm_smooth :
      td.isSmoothFam
        (ricciNormSqAlongFlow emb atr g_fam conn_fam ha_fam hal_fam hsl_fam hl_fam))
    (h_scalar_smooth :
      td.isSmoothFam
        (scalarCurvatureAlongFlow emb atr g_fam conn_fam ha_fam hal_fam hsl_fam hl_fam))
    (h_ricciNorm_lap : forall t,
      scalarLaplacianAlongTimeSlice emb atr g_fam conn_fam ha_fam hal_fam hsl_fam hl_fam
        (ricciNormSqAlongFlow emb atr g_fam conn_fam ha_fam hal_fam hsl_fam hl_fam) t =
      ricciNormLap t)
    (h_scalar_square_lap : forall t,
      scalarLaplacianAlongTimeSlice emb atr g_fam conn_fam ha_fam hal_fam hsl_fam hl_fam
        (fun s =>
          scalarCurvatureAlongFlow emb atr g_fam conn_fam ha_fam hal_fam hsl_fam hl_fam s *
          scalarCurvatureAlongFlow emb atr g_fam conn_fam ha_fam hal_fam hsl_fam hl_fam s) t =
      2 *
          scalarCurvatureAlongFlow emb atr g_fam conn_fam ha_fam hal_fam hsl_fam hl_fam t *
          scalarLap t +
        2 * gradScalarNormSq t)
    (h_scalar_trace : RicciTraceIdentity emb td atr g_fam conn_fam ha_fam hal_fam
      hsl_fam hl_fam h_Rc_smooth scalarLap)
    (h_ricciNorm_dt_component : forall t,
      ricciNormDt t = 2 * lapInner t + 4 * reaction t)
    (h_ricciNorm_lap_component : forall t,
      ricciNormLap t = 2 * lapInner t + 2 * nablaRicNormSq t)
    (h_reaction : forall t,
      2 *
          scalarCurvatureAlongFlow emb atr g_fam conn_fam ha_fam hal_fam hsl_fam hl_fam t *
          reaction t =
        2 *
            ricciNormSqAlongFlow emb atr g_fam conn_fam ha_fam hal_fam hsl_fam hl_fam t ^ 2 -
          cubicQ t) :
    TracefreeRicciNormHamilton3DTimeLaplacianEquation
      (fun u t => td.dt_apply u t)
      (scalarLaplacianAlongTimeSlice emb atr g_fam conn_fam ha_fam hal_fam hsl_fam hl_fam)
      (tracefreeRicciNormSqAlongFlow emb atr g_fam conn_fam ha_fam hal_fam hsl_fam hl_fam nInv)
      nablaRicNormSq gradScalarNormSq
      (ricciNormSqAlongFlow emb atr g_fam conn_fam ha_fam hal_fam hsl_fam hl_fam)
      cubicQ
      (scalarCurvatureAlongFlow emb atr g_fam conn_fam ha_fam hal_fam hsl_fam hl_fam) := by
  exact hamilton3D_tracefree_norm_eq_of_cubic_reaction_components emb td atr
    g_fam conn_fam ha_fam hal_fam hsl_fam hl_fam nInv h_nInv_dim
    h_nInv_const h_nInv ricciNormDt scalarDt ricciNormLap scalarLap
    gradScalarNormSq nablaRicNormSq cubicQ reaction h_scalar_ne h_ricciNorm_dt
    h_scalar_dt h_ricciNorm_smooth h_scalar_smooth h_ricciNorm_lap
    h_scalar_square_lap
    (ricci_norm_heat_eq_of_dt_laplacian_components
      ricciNormDt ricciNormLap lapInner nablaRicNormSq reaction
      h_ricciNorm_dt_component h_ricciNorm_lap_component)
    (scalar_heat_eq_of_full_evolution emb td atr g_fam h_met conn_fam ha_fam
      hal_fam hsl_fam hl_fam h_Rc_smooth h_rf h_sc_prod scalarDt scalarLap
      h_scalar_dt h_scalar_trace)
    h_reaction

/-- P3 wrapper with the Ricci-norm heat identity discharged through local
coordinate product rules.

Compared with `hamilton3D_tracefree_norm_eq_of_heat_components`, this theorem
does not ask for the two anonymous component hypotheses
`ricciNormDt = 2 lapInner + 4 reaction` and
`ricciNormLap = 2 lapInner + 2 |nabla Ric|^2`. The time-derivative side is
reduced to the finite-coordinate product rule for
`g^{ia} g^{jb} Ric_ij Ric_ab`, followed by the trace-cube cancellation; the
Laplacian side is reduced to the named tensor-norm Bochner product rule. -/
theorem hamilton3D_tracefree_norm_eq_of_coordinate_heat_components
    (emb : DerivationEmbedding k R V)
    (td : TimeDerivativeData R A Time) [TimeRegularFam td]
    (atr : AbstractTrace R V)
    (g_fam : Time -> MetricDuality R V)
    (h_met : forall vs covs, td.isSmoothFam (fun s => (g_fam s).g_tensor vs covs))
    (conn_fam : Time -> V -> V -> V)
    (ha_fam : forall s, forall X Y Z, conn_fam s X (Y + Z) = conn_fam s X Y + conn_fam s X Z)
    (hal_fam : forall s, forall X Y Z, conn_fam s (X + Y) Z = conn_fam s X Z + conn_fam s Y Z)
    (hsl_fam : forall s, forall (f : R) X Z, conn_fam s (f • X) Z = f • conn_fam s X Z)
    (hl_fam : forall s, forall X (f : R) Y,
      conn_fam s X (f • Y) = (emb.embed X) f • Y + f • conn_fam s X Y)
    (h_Rc_smooth : forall vs covs, td.isSmoothFam
      (fun s =>
        ricciForm_tensor emb (conn_fam s) (ha_fam s) (hal_fam s)
          (hsl_fam s) (hl_fam s) atr vs covs))
    (h_rf : IsRicciFlow emb td atr g_fam h_met conn_fam ha_fam hal_fam hsl_fam hl_fam)
    (h_sc_prod : ScalarCurvatureProductRule emb td atr g_fam h_met conn_fam
      ha_fam hal_fam hsl_fam hl_fam h_Rc_smooth)
    (nInv : R)
    (h_nInv_dim : nInv * abstractTraceDimension atr = 1)
    (h_nInv_const : forall X : V, action emb X nInv = 0)
    (h_nInv : nInv = (1 : R) / 3)
    (ricciNormDt scalarDt ricciNormLap scalarLap gradScalarNormSq
        nablaRicNormSq cubicQ reaction lapInner ricciTraceCube : Time -> R)
    (h_scalar_ne : forall t,
      scalarCurvatureAlongFlow emb atr g_fam conn_fam ha_fam hal_fam hsl_fam hl_fam t ≠ 0)
    (h_ricciNorm_dt :
      RicciNormEvolutionEquation emb td atr g_fam conn_fam ha_fam hal_fam
        hsl_fam hl_fam ricciNormDt)
    (h_scalar_dt : forall t,
      td.dt_apply
        (scalarCurvatureAlongFlow emb atr g_fam conn_fam ha_fam hal_fam hsl_fam hl_fam)
        t = scalarDt t)
    (h_ricciNorm_smooth :
      td.isSmoothFam
        (ricciNormSqAlongFlow emb atr g_fam conn_fam ha_fam hal_fam hsl_fam hl_fam))
    (h_scalar_smooth :
      td.isSmoothFam
        (scalarCurvatureAlongFlow emb atr g_fam conn_fam ha_fam hal_fam hsl_fam hl_fam))
    (h_ricciNorm_lap : forall t,
      scalarLaplacianAlongTimeSlice emb atr g_fam conn_fam ha_fam hal_fam hsl_fam hl_fam
        (ricciNormSqAlongFlow emb atr g_fam conn_fam ha_fam hal_fam hsl_fam hl_fam) t =
      ricciNormLap t)
    (h_scalar_square_lap : forall t,
      scalarLaplacianAlongTimeSlice emb atr g_fam conn_fam ha_fam hal_fam hsl_fam hl_fam
        (fun s =>
          scalarCurvatureAlongFlow emb atr g_fam conn_fam ha_fam hal_fam hsl_fam hl_fam s *
          scalarCurvatureAlongFlow emb atr g_fam conn_fam ha_fam hal_fam hsl_fam hl_fam s) t =
      2 *
          scalarCurvatureAlongFlow emb atr g_fam conn_fam ha_fam hal_fam hsl_fam hl_fam t *
          scalarLap t +
        2 * gradScalarNormSq t)
    (h_scalar_trace : RicciTraceIdentity emb td atr g_fam conn_fam ha_fam hal_fam
      hsl_fam hl_fam h_Rc_smooth scalarLap)
    {ι : Type*} [Fintype ι]
    (gInvLeft gInvRight ricciLeft ricciRight : ι -> Time -> R)
    (h_coord : forall s,
      ricciNormSqAlongFlow emb atr g_fam conn_fam ha_fam hal_fam hsl_fam hl_fam s =
        ∑ I : ι,
          gInvLeft I s * gInvRight I s * ricciLeft I s * ricciRight I s)
    (h_gInvLeft : forall I, td.isSmoothFam (gInvLeft I))
    (h_gInvRight : forall I, td.isSmoothFam (gInvRight I))
    (h_ricciLeft : forall I, td.isSmoothFam (ricciLeft I))
    (h_ricciRight : forall I, td.isSmoothFam (ricciRight I))
    (h_terms : forall t,
      (∑ I : ι,
        (td.dt_apply (gInvLeft I) t * gInvRight I t *
            ricciLeft I t * ricciRight I t +
          gInvLeft I t * td.dt_apply (gInvRight I) t *
            ricciLeft I t * ricciRight I t +
          gInvLeft I t * gInvRight I t *
            td.dt_apply (ricciLeft I) t * ricciRight I t +
          gInvLeft I t * gInvRight I t *
            ricciLeft I t * td.dt_apply (ricciRight I) t)) =
        4 * ricciTraceCube t +
          (2 * lapInner t + 4 * reaction t - 4 * ricciTraceCube t))
    (h_lap_rule : forall t,
      TensorNormLaplacianProductRule
        (ricciNormLap t) (lapInner t) (nablaRicNormSq t))
    (h_reaction : forall t,
      2 *
          scalarCurvatureAlongFlow emb atr g_fam conn_fam ha_fam hal_fam hsl_fam hl_fam t *
          reaction t =
        2 *
            ricciNormSqAlongFlow emb atr g_fam conn_fam ha_fam hal_fam hsl_fam hl_fam t ^ 2 -
          cubicQ t) :
    TracefreeRicciNormHamilton3DTimeLaplacianEquation
      (fun u t => td.dt_apply u t)
      (scalarLaplacianAlongTimeSlice emb atr g_fam conn_fam ha_fam hal_fam hsl_fam hl_fam)
      (tracefreeRicciNormSqAlongFlow emb atr g_fam conn_fam ha_fam hal_fam hsl_fam hl_fam nInv)
      nablaRicNormSq gradScalarNormSq
      (ricciNormSqAlongFlow emb atr g_fam conn_fam ha_fam hal_fam hsl_fam hl_fam)
      cubicQ
      (scalarCurvatureAlongFlow emb atr g_fam conn_fam ha_fam hal_fam hsl_fam hl_fam) := by
  exact hamilton3D_tracefree_norm_eq_of_cubic_reaction_components emb td atr
    g_fam conn_fam ha_fam hal_fam hsl_fam hl_fam nInv h_nInv_dim
    h_nInv_const h_nInv ricciNormDt scalarDt ricciNormLap scalarLap
    gradScalarNormSq nablaRicNormSq cubicQ reaction h_scalar_ne h_ricciNorm_dt
    h_scalar_dt h_ricciNorm_smooth h_scalar_smooth h_ricciNorm_lap
    h_scalar_square_lap
    (ricci_norm_heat_eq_of_coordinate_dt_and_laplacian_product_rule td
      (ricciNormSqAlongFlow emb atr g_fam conn_fam ha_fam hal_fam hsl_fam hl_fam)
      ricciNormDt ricciNormLap lapInner nablaRicNormSq reaction ricciTraceCube
      gInvLeft gInvRight ricciLeft ricciRight h_coord h_gInvLeft h_gInvRight
      h_ricciLeft h_ricciRight h_ricciNorm_dt h_terms h_lap_rule)
    (scalar_heat_eq_of_full_evolution emb td atr g_fam h_met conn_fam ha_fam
      hal_fam hsl_fam hl_fam h_Rc_smooth h_rf h_sc_prod scalarDt scalarLap
      h_scalar_dt h_scalar_trace)
    h_reaction

/-- P3 wrapper with both the monolithic `h_terms` and the abstract
`TensorNormLaplacianProductRule` discharged into their coordinate pieces.

The time-derivative side is split into the inverse-metric variation
contribution and the Ricci-variation contribution. The Laplacian side is the
coordinate Bochner sum:
`Delta |Ric|^2 = 2 <Delta Ric, Ric> + 2 |nabla Ric|^2`. -/
theorem hamilton3D_tracefree_norm_eq_of_coordinate_bochner_components
    (emb : DerivationEmbedding k R V)
    (td : TimeDerivativeData R A Time) [TimeRegularFam td]
    (atr : AbstractTrace R V)
    (g_fam : Time -> MetricDuality R V)
    (h_met : forall vs covs, td.isSmoothFam (fun s => (g_fam s).g_tensor vs covs))
    (conn_fam : Time -> V -> V -> V)
    (ha_fam : forall s, forall X Y Z, conn_fam s X (Y + Z) = conn_fam s X Y + conn_fam s X Z)
    (hal_fam : forall s, forall X Y Z, conn_fam s (X + Y) Z = conn_fam s X Z + conn_fam s Y Z)
    (hsl_fam : forall s, forall (f : R) X Z, conn_fam s (f • X) Z = f • conn_fam s X Z)
    (hl_fam : forall s, forall X (f : R) Y,
      conn_fam s X (f • Y) = (emb.embed X) f • Y + f • conn_fam s X Y)
    (h_Rc_smooth : forall vs covs, td.isSmoothFam
      (fun s =>
        ricciForm_tensor emb (conn_fam s) (ha_fam s) (hal_fam s)
          (hsl_fam s) (hl_fam s) atr vs covs))
    (h_rf : IsRicciFlow emb td atr g_fam h_met conn_fam ha_fam hal_fam hsl_fam hl_fam)
    (h_sc_prod : ScalarCurvatureProductRule emb td atr g_fam h_met conn_fam
      ha_fam hal_fam hsl_fam hl_fam h_Rc_smooth)
    (nInv : R)
    (h_nInv_dim : nInv * abstractTraceDimension atr = 1)
    (h_nInv_const : forall X : V, action emb X nInv = 0)
    (h_nInv : nInv = (1 : R) / 3)
    (ricciNormDt scalarDt ricciNormLap scalarLap gradScalarNormSq
        nablaRicNormSq cubicQ reaction lapInner ricciTraceCube : Time -> R)
    (h_scalar_ne : forall t,
      scalarCurvatureAlongFlow emb atr g_fam conn_fam ha_fam hal_fam hsl_fam hl_fam t ≠ 0)
    (h_ricciNorm_dt :
      RicciNormEvolutionEquation emb td atr g_fam conn_fam ha_fam hal_fam
        hsl_fam hl_fam ricciNormDt)
    (h_scalar_dt : forall t,
      td.dt_apply
        (scalarCurvatureAlongFlow emb atr g_fam conn_fam ha_fam hal_fam hsl_fam hl_fam)
        t = scalarDt t)
    (h_ricciNorm_smooth :
      td.isSmoothFam
        (ricciNormSqAlongFlow emb atr g_fam conn_fam ha_fam hal_fam hsl_fam hl_fam))
    (h_scalar_smooth :
      td.isSmoothFam
        (scalarCurvatureAlongFlow emb atr g_fam conn_fam ha_fam hal_fam hsl_fam hl_fam))
    (h_ricciNorm_lap : forall t,
      scalarLaplacianAlongTimeSlice emb atr g_fam conn_fam ha_fam hal_fam hsl_fam hl_fam
        (ricciNormSqAlongFlow emb atr g_fam conn_fam ha_fam hal_fam hsl_fam hl_fam) t =
      ricciNormLap t)
    (h_scalar_square_lap : forall t,
      scalarLaplacianAlongTimeSlice emb atr g_fam conn_fam ha_fam hal_fam hsl_fam hl_fam
        (fun s =>
          scalarCurvatureAlongFlow emb atr g_fam conn_fam ha_fam hal_fam hsl_fam hl_fam s *
          scalarCurvatureAlongFlow emb atr g_fam conn_fam ha_fam hal_fam hsl_fam hl_fam s) t =
      2 *
          scalarCurvatureAlongFlow emb atr g_fam conn_fam ha_fam hal_fam hsl_fam hl_fam t *
          scalarLap t +
        2 * gradScalarNormSq t)
    (h_scalar_trace : RicciTraceIdentity emb td atr g_fam conn_fam ha_fam hal_fam
      hsl_fam hl_fam h_Rc_smooth scalarLap)
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (gInvLeft gInvRight ricciLeft ricciRight : ι -> Time -> R)
    (second first : Time -> κ -> ι -> R) (component : Time -> ι -> R)
    (h_coord : forall s,
      ricciNormSqAlongFlow emb atr g_fam conn_fam ha_fam hal_fam hsl_fam hl_fam s =
        ∑ I : ι,
          gInvLeft I s * gInvRight I s * ricciLeft I s * ricciRight I s)
    (h_gInvLeft : forall I, td.isSmoothFam (gInvLeft I))
    (h_gInvRight : forall I, td.isSmoothFam (gInvRight I))
    (h_ricciLeft : forall I, td.isSmoothFam (ricciLeft I))
    (h_ricciRight : forall I, td.isSmoothFam (ricciRight I))
    (h_metric_terms : forall t,
      (∑ I : ι,
        (td.dt_apply (gInvLeft I) t * gInvRight I t *
            ricciLeft I t * ricciRight I t +
          gInvLeft I t * td.dt_apply (gInvRight I) t *
            ricciLeft I t * ricciRight I t)) =
        4 * ricciTraceCube t)
    (h_ricci_terms : forall t,
      (∑ I : ι,
        (gInvLeft I t * gInvRight I t *
            td.dt_apply (ricciLeft I) t * ricciRight I t +
          gInvLeft I t * gInvRight I t *
            ricciLeft I t * td.dt_apply (ricciRight I) t)) =
        2 * lapInner t + 4 * reaction t - 4 * ricciTraceCube t)
    (h_lap_bochner : forall t,
      ricciNormLap t =
        ∑ a : κ, ∑ I : ι,
          (2 * second t a I * component t I +
            2 * first t a I * first t a I))
    (h_rough_bochner : forall t,
      lapInner t =
        ∑ a : κ, ∑ I : ι, second t a I * component t I)
    (h_cov_bochner : forall t,
      nablaRicNormSq t =
        ∑ a : κ, ∑ I : ι, first t a I * first t a I)
    (h_reaction : forall t,
      2 *
          scalarCurvatureAlongFlow emb atr g_fam conn_fam ha_fam hal_fam hsl_fam hl_fam t *
          reaction t =
        2 *
            ricciNormSqAlongFlow emb atr g_fam conn_fam ha_fam hal_fam hsl_fam hl_fam t ^ 2 -
          cubicQ t) :
    TracefreeRicciNormHamilton3DTimeLaplacianEquation
      (fun u t => td.dt_apply u t)
      (scalarLaplacianAlongTimeSlice emb atr g_fam conn_fam ha_fam hal_fam hsl_fam hl_fam)
      (tracefreeRicciNormSqAlongFlow emb atr g_fam conn_fam ha_fam hal_fam hsl_fam hl_fam nInv)
      nablaRicNormSq gradScalarNormSq
      (ricciNormSqAlongFlow emb atr g_fam conn_fam ha_fam hal_fam hsl_fam hl_fam)
      cubicQ
      (scalarCurvatureAlongFlow emb atr g_fam conn_fam ha_fam hal_fam hsl_fam hl_fam) := by
  exact hamilton3D_tracefree_norm_eq_of_cubic_reaction_components emb td atr
    g_fam conn_fam ha_fam hal_fam hsl_fam hl_fam nInv h_nInv_dim
    h_nInv_const h_nInv ricciNormDt scalarDt ricciNormLap scalarLap
    gradScalarNormSq nablaRicNormSq cubicQ reaction h_scalar_ne h_ricciNorm_dt
    h_scalar_dt h_ricciNorm_smooth h_scalar_smooth h_ricciNorm_lap
    h_scalar_square_lap
    (ricci_norm_heat_eq_of_coordinate_split_dt_and_bochner_sum td
      (ricciNormSqAlongFlow emb atr g_fam conn_fam ha_fam hal_fam hsl_fam hl_fam)
      ricciNormDt ricciNormLap lapInner nablaRicNormSq reaction ricciTraceCube
      gInvLeft gInvRight ricciLeft ricciRight second first component
      h_coord h_gInvLeft h_gInvRight h_ricciLeft h_ricciRight h_ricciNorm_dt
      h_metric_terms h_ricci_terms h_lap_bochner h_rough_bochner h_cov_bochner)
    (scalar_heat_eq_of_full_evolution emb td atr g_fam h_met conn_fam ha_fam
      hal_fam hsl_fam hl_fam h_Rc_smooth h_rf h_sc_prod scalarDt scalarLap
      h_scalar_dt h_scalar_trace)
    h_reaction

end Hamilton3DTracefreeEvolutionSyntheticBridge
