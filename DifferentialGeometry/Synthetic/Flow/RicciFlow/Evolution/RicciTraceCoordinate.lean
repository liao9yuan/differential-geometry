import DifferentialGeometry.Synthetic.Flow.RicciFlow.Evolution.RicciTrace

/-!
# Ricci Trace Commutation via Finite-Basis Representatives

This file contains the finite-basis representatives and coordinate-style
trace commutation lemmas needed to identify `partial_t (tr Rm)` with
`tr (partial_t Rm)`.
-/

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.style.emptyLine false

open SyntheticTensor

section RicciEvolutionInterface

variable {k R V Time : Type*} {A : Type*}
variable [Field k] [CommRing R] [Algebra k R]
variable [AddCommGroup V] [Module R V] [Module k V] [IsScalarTower k R V]
variable [CommRing A] [Algebra R A]

/-- In a finite basis, a linear functional on the dual space is represented by
the vector with the corresponding coordinate values.

This is the non-time-dependent analogue of
`finiteBasisTimeDerivativeVector`: it turns scalar covector evaluations into an
actual vector, provided the scalar expression is linear in the covector. -/
noncomputable def finiteBasisVectorOfDualFunctional
    {ι : Type*} [Fintype ι]
    (basis : Module.Basis ι R V) (F : (V →ₗ[R] R) -> R) : V :=
  basis.equivFun.symm (fun i => F (basis.coord i))

/-- The vector represented by a finite-basis dual functional has the expected
evaluation against every covector. -/
theorem finiteBasisVectorOfDualFunctional_eval
    {ι : Type*} [Fintype ι]
    (basis : Module.Basis ι R V) (F : (V →ₗ[R] R) -> R)
    (hF_add : forall α β, F (α + β) = F α + F β)
    (hF_smul : forall (c : R) α, F (c • α) = c * F α)
    (ω : V →ₗ[R] R) :
    ω (finiteBasisVectorOfDualFunctional basis F) = F ω := by
  classical
  let L : (V →ₗ[R] R) →ₗ[R] R := {
    toFun := F
    map_add' := hF_add
    map_smul' := by
      intro c α
      simpa [smul_eq_mul] using hF_smul c α }
  have hω_expand : ω = ∑ i, (ω (basis i)) • basis.coord i := by
    ext v
    calc
      ω v = ω (∑ i, basis.coord i v • basis i) := by
        rw [show (∑ i, basis.coord i v • basis i) = v by
          simpa only [Module.Basis.coord_apply] using basis.sum_repr v]
      _ = ∑ i, basis.coord i v * ω (basis i) := by
        simp only [map_sum, map_smul, smul_eq_mul]
      _ = ∑ i, ω (basis i) * basis.coord i v := by
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = (∑ i, (ω (basis i)) • basis.coord i) v := by
        simp only [LinearMap.coe_sum, Finset.sum_apply, LinearMap.smul_apply, smul_eq_mul]
  unfold finiteBasisVectorOfDualFunctional
  rw [basis.equivFun_symm_apply]
  calc
    ω (∑ i, F (basis.coord i) • basis i) =
        ∑ i, F (basis.coord i) * ω (basis i) := by
      simp only [map_sum, map_smul, smul_eq_mul]
    _ = ∑ i, ω (basis i) * F (basis.coord i) := by
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = L (∑ i, (ω (basis i)) • basis.coord i) := by
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [map_smul]
      rfl
    _ = F ω := by
      rw [← hω_expand]
      rfl

/-- Finite-basis endomorphism representing the Ricci-slot slice of
`Q_rm_independent`:

`Z |-> Q(X, Z, Y)` as a vector-valued map. -/
noncomputable def qHamiltonRicciSlotEndomorphism_of_finite_basis
    {ι : Type*} [Fintype ι]
    (basis : Module.Basis ι R V)
    (emb : DerivationEmbedding k R V) (conn : V -> V -> V)
    (ha : forall X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : forall X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : forall (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (hl : forall X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (atr : AbstractTrace R V) (met : MetricDuality R V)
    (X Y : V) : V →ₗ[R] V where
  toFun Z :=
    finiteBasisVectorOfDualFunctional basis
      (fun ω => Q_rm_independent emb conn ha hal hsl hl atr met ![X, Z, Y] ![ω])
  map_add' := by
    intro Z₁ Z₂
    unfold finiteBasisVectorOfDualFunctional
    apply basis.equivFun.injective
    ext i
    simp only [LinearEquiv.map_add, Pi.add_apply, LinearEquiv.apply_symm_apply]
    exact Q_hamilton_add_Y emb conn ha hal hsl hl atr met X Z₁ Z₂ Y (basis.coord i)
  map_smul' := by
    intro c Z
    unfold finiteBasisVectorOfDualFunctional
    apply basis.equivFun.injective
    ext i
    simp only [LinearEquiv.map_smul, Pi.smul_apply, LinearEquiv.apply_symm_apply,
      smul_eq_mul]
    exact Q_hamilton_smul_Y emb conn ha hal hsl hl atr met c X Z Y (basis.coord i)

/-- Evaluation of the finite-basis Ricci-slot endomorphism representing
`Q_rm_independent`. -/
theorem qHamiltonRicciSlotEndomorphism_of_finite_basis_eval
    {ι : Type*} [Fintype ι]
    (basis : Module.Basis ι R V)
    (emb : DerivationEmbedding k R V) (conn : V -> V -> V)
    (ha : forall X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : forall X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : forall (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (hl : forall X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (atr : AbstractTrace R V) (met : MetricDuality R V)
    (X Y Z : V) (ω : V →ₗ[R] R) :
    ω (qHamiltonRicciSlotEndomorphism_of_finite_basis basis emb conn ha hal hsl hl atr met
        X Y Z) =
      Q_rm_independent emb conn ha hal hsl hl atr met ![X, Z, Y] ![ω] := by
  unfold qHamiltonRicciSlotEndomorphism_of_finite_basis
  exact finiteBasisVectorOfDualFunctional_eval basis
    (fun η => Q_rm_independent emb conn ha hal hsl hl atr met ![X, Z, Y] ![η])
    (by
      intro η₁ η₂
      exact Q_hamilton_add_omega emb conn ha hal hsl hl atr met X Z Y η₁ η₂)
    (by
      intro c η
      exact Q_hamilton_smul_omega emb conn ha hal hsl hl atr met c X Z Y η)
    ω

/-- Finite-basis reduction of the canonical quadratic trace target.

The contraction side is converted, via `RicciSlotTraceEval`, to the trace of
the explicit endomorphism `Z |-> Q(X,Z,Y)`. The remaining hypothesis is the
coordinate trace calculation identifying that endomorphism trace with
`2 Rm*Ric - 2 Ric^2`. -/
theorem RiemannToRicciCanonicalQuadraticTrace_of_finite_basis_trace
    {ι : Type*} [Fintype ι]
    (basis : Module.Basis ι R V)
    (emb : DerivationEmbedding k R V) (conn : V -> V -> V)
    (ha : forall X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : forall X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : forall (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (hl : forall X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (atr : AbstractTrace R V) (met : MetricDuality R V)
    (h_eval : RicciSlotTraceEval atr)
    (h_trace : forall X Y,
      atr.tr (qHamiltonRicciSlotEndomorphism_of_finite_basis basis emb conn ha hal hsl hl
        atr met X Y) =
        2 * riemannRicciReactionTensor emb conn ha hal hsl hl atr met ![X, Y] ![] -
          2 * ricciSquareTensor emb conn ha hal hsl hl atr met ![X, Y] ![]) :
    RiemannToRicciCanonicalQuadraticTrace emb conn ha hal hsl hl atr met := by
  intro X Y
  calc
    riemann_to_ricci_trace atr
        (Q_rm_independent emb conn ha hal hsl hl atr met) ![X, Y] ![] =
      atr.tr (qHamiltonRicciSlotEndomorphism_of_finite_basis basis emb conn ha hal hsl hl
        atr met X Y) := by
        exact riemann_to_ricci_trace_eq_trace_of_slice atr h_eval
          (Q_rm_independent emb conn ha hal hsl hl atr met) X Y
          (qHamiltonRicciSlotEndomorphism_of_finite_basis basis emb conn ha hal hsl hl
            atr met X Y)
          (by
            intro Z ω
            exact (qHamiltonRicciSlotEndomorphism_of_finite_basis_eval basis emb conn
              ha hal hsl hl atr met X Y Z ω).symm)
    _ = 2 * riemannRicciReactionTensor emb conn ha hal hsl hl atr met ![X, Y] ![] -
          2 * ricciSquareTensor emb conn ha hal hsl hl atr met ![X, Y] ![] :=
        h_trace X Y

/-- Finite-basis reduction of the canonical quadratic trace after the two
curvature-reaction traces have been discharged.

The remaining hypothesis is the true Hessian/rough-laplacian cancellation:
after subtracting the exposed reaction-pair endomorphism from
`Z |-> Q(X,Z,Y)`, its trace must be another copy of `Rm*Ric - Ric^2`. -/
theorem RiemannToRicciCanonicalQuadraticTrace_of_finite_basis_hessian_residual
    {ι : Type*} [Fintype ι]
    (basis : Module.Basis ι R V)
    (emb : DerivationEmbedding k R V) (conn : V -> V -> V)
    (ha : forall X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : forall X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : forall (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (hl : forall X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (atr : AbstractTrace R V) (met : MetricDuality R V)
    (h_eval : RicciSlotTraceEval atr)
    (h_Rc_symm : forall X Y,
      Rc emb conn ha hal hsl hl atr X Y =
        Rc emb conn ha hal hsl hl atr Y X)
    (h_residual : forall X Y,
      atr.tr
          (qHamiltonRicciSlotEndomorphism_of_finite_basis basis emb conn ha hal hsl hl
            atr met X Y -
          commutedReactionPairEndomorphism emb conn ha hal hsl hl atr met X Y) =
        riemannRicciReactionTensor emb conn ha hal hsl hl atr met ![X, Y] ![] -
          ricciSquareTensor emb conn ha hal hsl hl atr met ![X, Y] ![]) :
    RiemannToRicciCanonicalQuadraticTrace emb conn ha hal hsl hl atr met := by
  apply RiemannToRicciCanonicalQuadraticTrace_of_finite_basis_trace
    basis emb conn ha hal hsl hl atr met h_eval
  intro X Y
  let Q := qHamiltonRicciSlotEndomorphism_of_finite_basis basis emb conn ha hal hsl hl
    atr met X Y
  let P := commutedReactionPairEndomorphism emb conn ha hal hsl hl atr met X Y
  have hsplit : Q = P + (Q - P) := by
    ext Z
    simp [Q, P, sub_eq_add_neg]
  calc
    atr.tr Q = atr.tr (P + (Q - P)) := by
      exact congr_arg atr.tr hsplit
    _ = atr.tr P + atr.tr (Q - P) := by exact map_add atr.tr P (Q - P)
    _ = (riemannRicciReactionTensor emb conn ha hal hsl hl atr met ![X, Y] ![] -
          ricciSquareTensor emb conn ha hal hsl hl atr met ![X, Y] ![]) +
        (riemannRicciReactionTensor emb conn ha hal hsl hl atr met ![X, Y] ![] -
          ricciSquareTensor emb conn ha hal hsl hl atr met ![X, Y] ![]) := by
          rw [trace_commutedReactionPairEndomorphism_eq_riemannRicci_sub_ricciSquare
            emb conn ha hal hsl hl atr met h_Rc_symm X Y]
          rw [h_residual X Y]
    _ = 2 * riemannRicciReactionTensor emb conn ha hal hsl hl atr met ![X, Y] ![] -
          2 * ricciSquareTensor emb conn ha hal hsl hl atr met ![X, Y] ![] := by
          ring

/-- Build the general quadratic decomposition package from the canonical
Lemma 6.3 quadratic trace identity. -/
noncomputable def riemannToRicciQuadraticTraceDecomposition_of_canonical
    (emb : DerivationEmbedding k R V) (atr : AbstractTrace R V)
    (g_fam : Time -> MetricDuality R V)
    (conn_fam : Time -> V -> V -> V)
    (ha_fam : forall s, forall X Y Z,
      conn_fam s X (Y + Z) = conn_fam s X Y + conn_fam s X Z)
    (hal_fam : forall s, forall X Y Z,
      conn_fam s (X + Y) Z = conn_fam s X Z + conn_fam s Y Z)
    (hsl_fam : forall s, forall (f : R) X Z,
      conn_fam s (f • X) Z = f • conn_fam s X Z)
    (hl_fam : forall s, forall X (f : R) Y,
      conn_fam s X (f • Y) = (emb.embed X) f • Y + f • conn_fam s X Y)
    (h_trace : forall t,
      RiemannToRicciCanonicalQuadraticTrace emb (conn_fam t) (ha_fam t)
        (hal_fam t) (hsl_fam t) (hl_fam t) atr (g_fam t)) :
    RiemannToRicciQuadraticTraceDecomposition emb atr g_fam conn_fam
      ha_fam hal_fam hsl_fam hl_fam where
  riemannRicci := fun t =>
    riemannRicciReactionTensor emb (conn_fam t) (ha_fam t) (hal_fam t)
      (hsl_fam t) (hl_fam t) atr (g_fam t)
  ricciSquare := fun t =>
    ricciSquareTensor emb (conn_fam t) (ha_fam t) (hal_fam t)
      (hsl_fam t) (hl_fam t) atr (g_fam t)
  trace_eq := by
    intro t X Y
    exact h_trace t X Y

/-- A vector-valued representative for the time derivative of the Riemann
curvature slice used in the Ricci trace.

For fixed `t X Y`, `endo t X Y` represents the endomorphism
`Z |-> ∂_t (Rm_t(X,Z)Y)`. The `eval_endo` field is the only data the trace
calculus needs: every covector evaluation of this vector-valued slice agrees
with the corresponding slot evaluation of `dt_tensor Rm`.

This is intentionally a package, not a proof of existence. The scalar Riemann
variation formulas identify covector evaluations of `dt_tensor Rm`; a concrete
or finite-frame realization still has to provide the vector representative. -/
structure RiemannTimeDerivativeSliceEndomorphism
    (emb : DerivationEmbedding k R V)
    (td : TimeDerivativeData R A Time) [TimeRegularFam td]
    (conn_fam : Time -> V -> V -> V)
    (ha_fam : forall s, forall X Y Z,
      conn_fam s X (Y + Z) = conn_fam s X Y + conn_fam s X Z)
    (hal_fam : forall s, forall X Y Z,
      conn_fam s (X + Y) Z = conn_fam s X Z + conn_fam s Y Z)
    (hsl_fam : forall s, forall (f : R) X Z,
      conn_fam s (f • X) Z = f • conn_fam s X Z)
    (hl_fam : forall s, forall X (f : R) Y,
      conn_fam s X (f • Y) = (emb.embed X) f • Y + f • conn_fam s X Y)
    (h_Rm_smooth : forall vs αs, td.isSmoothFam
      (fun τ => Rm_tensor emb (conn_fam τ) (ha_fam τ) (hal_fam τ) (hsl_fam τ)
        (hl_fam τ) vs αs)) where
  endo : Time -> V -> V -> V →ₗ[R] V
  eval_endo : forall t X Y Z (α : V →ₗ[R] R),
    α (endo t X Y Z) =
      tensor_eval
        (dt_tensor td t
          (fun s => Rm_tensor emb (conn_fam s) (ha_fam s) (hal_fam s)
            (hsl_fam s) (hl_fam s))
          h_Rm_smooth) ![X, Z, Y] ![α]

/-- In a finite basis, the derivative of a vector-valued family can be
represented by differentiating each coordinate. -/
noncomputable def finiteBasisTimeDerivativeVector
    {ι : Type*} [Fintype ι]
    (td : TimeDerivativeData R A Time) [TimeRegularFam td]
    (basis : Module.Basis ι R V) (F : Time -> V) (t : Time) : V :=
  basis.equivFun.symm (fun i => td.dt_apply (fun s => basis.coord i (F s)) t)

/-- The finite-basis vector derivative has the expected covector evaluations. -/
theorem finiteBasisTimeDerivativeVector_eval
    {ι : Type*} [Fintype ι]
    (td : TimeDerivativeData R A Time) [TimeRegularFam td]
    (basis : Module.Basis ι R V) (F : Time -> V)
    (hF_smooth : forall α : V →ₗ[R] R, td.isSmoothFam (fun s => α (F s)))
    (t : Time) (α : V →ₗ[R] R) :
    α (finiteBasisTimeDerivativeVector td basis F t) =
      td.dt_apply (fun s => α (F s)) t := by
  classical
  unfold finiteBasisTimeDerivativeVector
  rw [basis.equivFun_symm_apply]
  have h_eval_sum :
      α (∑ i, td.dt_apply (fun s => basis.coord i (F s)) t • basis i) =
        ∑ i, td.dt_apply (fun s => basis.coord i (F s)) t * α (basis i) := by
    simp only [map_sum, map_smul, smul_eq_mul]
  rw [h_eval_sum]
  have h_expand : (fun s => α (F s)) =
      (∑ i : ι, fun s => α (basis i) * basis.coord i (F s)) := by
    ext s
    calc
      α (F s) = α (∑ i, basis.coord i (F s) • basis i) := by
        rw [show (∑ i, basis.coord i (F s) • basis i) = F s by
          simpa only [Module.Basis.coord_apply] using basis.sum_repr (F s)]
      _ = ∑ i, basis.coord i (F s) * α (basis i) := by
        simp only [map_sum, map_smul, smul_eq_mul]
      _ = ∑ i, α (basis i) * basis.coord i (F s) := by
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = (∑ i : ι, fun s => α (basis i) * basis.coord i (F s)) s := by
        simp only [Finset.sum_apply]
  rw [h_expand]
  rw [td.dt_apply_sum Finset.univ
    (fun i s => α (basis i) * basis.coord i (F s)) t]
  · apply Finset.sum_congr rfl
    intro i _
    rw [td.dt_apply_const_mul (α (basis i)) (fun s => basis.coord i (F s)) t
      (hF_smooth (basis.coord i))]
    ring
  · intro i _
    exact td.isSmoothFam_const_mul (α (basis i))
      (fun s => basis.coord i (F s)) (hF_smooth (basis.coord i))

/-- Finite-basis constructor for the derivative of a family of linear maps:
differentiate each output vector in coordinates. -/
noncomputable def finiteBasisTimeDerivativeLinearMap
    {ι : Type*} [Fintype ι]
    (td : TimeDerivativeData R A Time) [TimeRegularFam td]
    (basis : Module.Basis ι R V) (F : Time -> V -> V)
    (hF_add : forall s Z₁ Z₂, F s (Z₁ + Z₂) = F s Z₁ + F s Z₂)
    (hF_smul : forall s (c : R) Z, F s (c • Z) = c • F s Z)
    (hF_smooth : forall Z (α : V →ₗ[R] R), td.isSmoothFam (fun s => α (F s Z)))
    (t : Time) : V →ₗ[R] V where
  toFun Z := finiteBasisTimeDerivativeVector td basis (fun s => F s Z) t
  map_add' := by
    classical
    intro Z₁ Z₂
    unfold finiteBasisTimeDerivativeVector
    apply basis.equivFun.injective
    ext i
    simp only [LinearEquiv.map_add, Pi.add_apply, LinearEquiv.apply_symm_apply]
    have hfun : (fun s => basis.coord i (F s (Z₁ + Z₂))) =
        (fun s => basis.coord i (F s Z₁)) +
          (fun s => basis.coord i (F s Z₂)) := by
      ext s
      rw [hF_add s Z₁ Z₂]
      simp only [map_add, Pi.add_apply]
    rw [hfun]
    exact td.dt_apply_add _ _ _ (hF_smooth Z₁ (basis.coord i))
      (hF_smooth Z₂ (basis.coord i))
  map_smul' := by
    classical
    intro c Z
    unfold finiteBasisTimeDerivativeVector
    apply basis.equivFun.injective
    ext i
    simp only [LinearEquiv.map_smul, Pi.smul_apply, LinearEquiv.apply_symm_apply,
      smul_eq_mul]
    have hfun : (fun s => basis.coord i (F s (c • Z))) =
        (fun s => c * basis.coord i (F s Z)) := by
      ext s
      rw [hF_smul s c Z]
      simp only [map_smul, smul_eq_mul]
    rw [hfun]
    exact td.dt_apply_const_mul c (fun s => basis.coord i (F s Z)) t
      (hF_smooth Z (basis.coord i))

/-- Covector evaluation of the finite-basis linear-map derivative. -/
theorem finiteBasisTimeDerivativeLinearMap_eval
    {ι : Type*} [Fintype ι]
    (td : TimeDerivativeData R A Time) [TimeRegularFam td]
    (basis : Module.Basis ι R V) (F : Time -> V -> V)
    (hF_add : forall s Z₁ Z₂, F s (Z₁ + Z₂) = F s Z₁ + F s Z₂)
    (hF_smul : forall s (c : R) Z, F s (c • Z) = c • F s Z)
    (hF_smooth : forall Z (α : V →ₗ[R] R), td.isSmoothFam (fun s => α (F s Z)))
    (t : Time) (Z : V) (α : V →ₗ[R] R) :
    α (finiteBasisTimeDerivativeLinearMap td basis F hF_add hF_smul
      hF_smooth t Z) =
      td.dt_apply (fun s => α (F s Z)) t :=
  finiteBasisTimeDerivativeVector_eval td basis (fun s => F s Z)
    (hF_smooth Z) t α

/-- Finite-basis constructor for the represented Riemann time-derivative slice.

This is the concrete representability step needed by the Ricci trace
commutation: for each `t X Y`, the map `Z |-> ∂_t(Rm_t(X,Z)Y)` is built by
differentiating its basis coordinates. -/
noncomputable def riemannTimeDerivativeSliceEndomorphism_of_finite_basis
    {ι : Type*} [Fintype ι]
    (emb : DerivationEmbedding k R V)
    (td : TimeDerivativeData R A Time) [TimeRegularFam td]
    (conn_fam : Time -> V -> V -> V)
    (ha_fam : forall s, forall X Y Z,
      conn_fam s X (Y + Z) = conn_fam s X Y + conn_fam s X Z)
    (hal_fam : forall s, forall X Y Z,
      conn_fam s (X + Y) Z = conn_fam s X Z + conn_fam s Y Z)
    (hsl_fam : forall s, forall (f : R) X Z,
      conn_fam s (f • X) Z = f • conn_fam s X Z)
    (hl_fam : forall s, forall X (f : R) Y,
      conn_fam s X (f • Y) = (emb.embed X) f • Y + f • conn_fam s X Y)
    (h_Rm_smooth : forall vs αs, td.isSmoothFam
      (fun τ => Rm_tensor emb (conn_fam τ) (ha_fam τ) (hal_fam τ) (hsl_fam τ)
        (hl_fam τ) vs αs))
    (basis : Module.Basis ι R V) :
    RiemannTimeDerivativeSliceEndomorphism emb td conn_fam
      ha_fam hal_fam hsl_fam hl_fam h_Rm_smooth where
  endo := fun t X Y =>
    finiteBasisTimeDerivativeLinearMap td basis
      (fun s Z => Rm emb (conn_fam s) X Z Y)
      (fun s Z₁ Z₂ =>
        Rm_add_Y emb (conn_fam s) (ha_fam s) (hal_fam s) X Z₁ Z₂ Y)
      (fun s c Z =>
        Rm_smul_Y emb (conn_fam s) (hal_fam s) (hsl_fam s) (hl_fam s) c X Z Y)
      (fun Z α => by
        simpa [Rm_tensor_eval] using h_Rm_smooth ![X, Z, Y] ![α])
      t
  eval_endo := by
    intro t X Y Z α
    calc
      α (finiteBasisTimeDerivativeLinearMap td basis
          (fun s Z => Rm emb (conn_fam s) X Z Y)
          (fun s Z₁ Z₂ =>
            Rm_add_Y emb (conn_fam s) (ha_fam s) (hal_fam s) X Z₁ Z₂ Y)
          (fun s c Z =>
            Rm_smul_Y emb (conn_fam s) (hal_fam s) (hsl_fam s) (hl_fam s) c X Z Y)
          (fun Z α => by
            simpa [Rm_tensor_eval] using h_Rm_smooth ![X, Z, Y] ![α])
          t Z) =
          td.dt_apply (fun s => α (Rm emb (conn_fam s) X Z Y)) t := by
        exact finiteBasisTimeDerivativeLinearMap_eval td basis
          (fun s Z => Rm emb (conn_fam s) X Z Y)
          (fun s Z₁ Z₂ =>
            Rm_add_Y emb (conn_fam s) (ha_fam s) (hal_fam s) X Z₁ Z₂ Y)
          (fun s c Z =>
            Rm_smul_Y emb (conn_fam s) (hal_fam s) (hsl_fam s) (hl_fam s) c X Z Y)
          (fun Z α => by
            simpa [Rm_tensor_eval] using h_Rm_smooth ![X, Z, Y] ![α])
          t Z α
      _ = tensor_eval
          (dt_tensor td t
            (fun s => Rm_tensor emb (conn_fam s) (ha_fam s) (hal_fam s)
              (hsl_fam s) (hl_fam s))
            h_Rm_smooth) ![X, Z, Y] ![α] := by
        simp [tensor_eval, dt_tensor_eval, Rm_tensor_eval]

/-- Evaluate the Ricci-slot trace of the time derivative of Riemann as the
trace of a chosen sliced endomorphism. This discharges the `h_contract_trace`
input used by `ricci_time_trace_commutation_from_endomorphism_trace` whenever
the coordinate trace-evaluation law is available. -/
theorem riemann_to_ricci_trace_dt_tensor_eval
    (emb : DerivationEmbedding k R V)
    (td : TimeDerivativeData R A Time) [TimeRegularFam td]
    (atr : AbstractTrace R V) (h_eval : RicciSlotTraceEval atr)
    (conn_fam : Time -> V -> V -> V)
    (ha_fam : forall s, forall X Y Z, conn_fam s X (Y + Z) = conn_fam s X Y + conn_fam s X Z)
    (hal_fam : forall s, forall X Y Z, conn_fam s (X + Y) Z = conn_fam s X Z + conn_fam s Y Z)
    (hsl_fam : forall s, forall (f : R) X Z, conn_fam s (f • X) Z = f • conn_fam s X Z)
    (hl_fam : forall s, forall X (f : R) Y,
      conn_fam s X (f • Y) = (emb.embed X) f • Y + f • conn_fam s X Y)
    (h_Rm_smooth : forall vs αs, td.isSmoothFam
      (fun τ => Rm_tensor emb (conn_fam τ) (ha_fam τ) (hal_fam τ) (hsl_fam τ)
        (hl_fam τ) vs αs))
    (dRmEndo : Time -> V -> V -> V →ₗ[R] V)
    (h_dRmEndo_eval : forall t X Y Z (α : V →ₗ[R] R),
      α (dRmEndo t X Y Z) =
        tensor_eval
          (dt_tensor td t
            (fun s => Rm_tensor emb (conn_fam s) (ha_fam s) (hal_fam s)
              (hsl_fam s) (hl_fam s))
            h_Rm_smooth) ![X, Z, Y] ![α]) :
    forall t X Y,
      riemann_to_ricci_trace atr
        (dt_tensor td t
          (fun s => Rm_tensor emb (conn_fam s) (ha_fam s) (hal_fam s)
            (hsl_fam s) (hl_fam s))
          h_Rm_smooth) ![X, Y] ![] =
      atr.tr (dRmEndo t X Y) := by
  intro t X Y
  exact riemann_to_ricci_trace_eq_trace_of_slice atr h_eval
    (dt_tensor td t
      (fun s => Rm_tensor emb (conn_fam s) (ha_fam s) (hal_fam s)
        (hsl_fam s) (hl_fam s))
      h_Rm_smooth) X Y (dRmEndo t X Y)
    (by
      intro Z α
      simpa [tensor_eval] using (h_dRmEndo_eval t X Y Z α).symm)

/-- Version of `riemann_to_ricci_trace_dt_tensor_eval` consuming the named
Riemann time-derivative slice package. -/
theorem riemann_to_ricci_trace_dt_tensor_eval_of_slice
    (emb : DerivationEmbedding k R V)
    (td : TimeDerivativeData R A Time) [TimeRegularFam td]
    (atr : AbstractTrace R V) (h_eval : RicciSlotTraceEval atr)
    (conn_fam : Time -> V -> V -> V)
    (ha_fam : forall s, forall X Y Z, conn_fam s X (Y + Z) = conn_fam s X Y + conn_fam s X Z)
    (hal_fam : forall s, forall X Y Z, conn_fam s (X + Y) Z = conn_fam s X Z + conn_fam s Y Z)
    (hsl_fam : forall s, forall (f : R) X Z, conn_fam s (f • X) Z = f • conn_fam s X Z)
    (hl_fam : forall s, forall X (f : R) Y,
      conn_fam s X (f • Y) = (emb.embed X) f • Y + f • conn_fam s X Y)
    (h_Rm_smooth : forall vs αs, td.isSmoothFam
      (fun τ => Rm_tensor emb (conn_fam τ) (ha_fam τ) (hal_fam τ) (hsl_fam τ)
        (hl_fam τ) vs αs))
    (D : RiemannTimeDerivativeSliceEndomorphism emb td conn_fam
      ha_fam hal_fam hsl_fam hl_fam h_Rm_smooth) :
    forall t X Y,
      riemann_to_ricci_trace atr
        (dt_tensor td t
          (fun s => Rm_tensor emb (conn_fam s) (ha_fam s) (hal_fam s)
            (hsl_fam s) (hl_fam s))
          h_Rm_smooth) ![X, Y] ![] =
      atr.tr (D.endo t X Y) :=
  riemann_to_ricci_trace_dt_tensor_eval emb td atr h_eval conn_fam
    ha_fam hal_fam hsl_fam hl_fam h_Rm_smooth D.endo D.eval_endo

/-- Time derivative commutes with the Ricci trace of Riemann, provided the
Riemann time derivative has been represented by a vector-valued endomorphism
and `riemann_to_ricci_trace` is known to evaluate as the trace of that slice.

Mathematically, for fixed `X Y`, set `A_s Z = Rm_s(X,Z)Y`. Then this is just
`d/dt (tr A_s) = tr (dA_s/dt)`. The final hypothesis identifies the abstract
tensor contraction on `dt_tensor Rm` with `tr (dA_s/dt)`. -/
theorem ricci_time_trace_commutation_from_endomorphism_trace
    (emb : DerivationEmbedding k R V)
    (td : TimeDerivativeData R A Time) [TimeRegularFam td]
    (atr : AbstractTrace R V)
    (h_tt : TimeTrComm atr td)
    (conn_fam : Time -> V -> V -> V)
    (ha_fam : forall s, forall X Y Z, conn_fam s X (Y + Z) = conn_fam s X Y + conn_fam s X Z)
    (hal_fam : forall s, forall X Y Z, conn_fam s (X + Y) Z = conn_fam s X Z + conn_fam s Y Z)
    (hsl_fam : forall s, forall (f : R) X Z, conn_fam s (f • X) Z = f • conn_fam s X Z)
    (hl_fam : forall s, forall X (f : R) Y,
      conn_fam s X (f • Y) = (emb.embed X) f • Y + f • conn_fam s X Y)
    (h_Rc_smooth : forall vs αs, td.isSmoothFam
      (fun τ => ricciForm_tensor emb (conn_fam τ) (ha_fam τ) (hal_fam τ) (hsl_fam τ)
        (hl_fam τ) atr vs αs))
    (h_Rm_smooth : forall vs αs, td.isSmoothFam
      (fun τ => Rm_tensor emb (conn_fam τ) (ha_fam τ) (hal_fam τ) (hsl_fam τ)
        (hl_fam τ) vs αs))
    (dRmEndo : Time -> V -> V -> V →ₗ[R] V)
    (h_dRmEndo_eval : forall t X Y Z (α : V →ₗ[R] R),
      α (dRmEndo t X Y Z) =
        tensor_eval
          (dt_tensor td t
            (fun s => Rm_tensor emb (conn_fam s) (ha_fam s) (hal_fam s)
              (hsl_fam s) (hl_fam s))
            h_Rm_smooth) ![X, Z, Y] ![α])
    (h_contract_trace : forall t X Y,
      riemann_to_ricci_trace atr
        (dt_tensor td t
          (fun s => Rm_tensor emb (conn_fam s) (ha_fam s) (hal_fam s)
            (hsl_fam s) (hl_fam s))
          h_Rm_smooth) ![X, Y] ![] =
      atr.tr (dRmEndo t X Y)) :
    forall t X Y,
      tensor_eval
        (dt_tensor td t
          (fun s => ricciForm_tensor emb (conn_fam s) (ha_fam s) (hal_fam s)
            (hsl_fam s) (hl_fam s) atr)
          h_Rc_smooth) ![X, Y] ![] =
      riemann_to_ricci_trace atr
        (dt_tensor td t
          (fun s => Rm_tensor emb (conn_fam s) (ha_fam s) (hal_fam s)
            (hsl_fam s) (hl_fam s))
          h_Rm_smooth) ![X, Y] ![] := by
  intro t X Y
  let L : Time -> V →ₗ[R] V := fun s =>
    RcEndo emb (conn_fam s) (ha_fam s) (hal_fam s) (hsl_fam s) (hl_fam s) X Y
  have hαLv_smooth : forall (Z : V) (α : V →ₗ[R] R),
      td.isSmoothFam (fun s => α (L s Z)) := by
    intro Z α
    simpa [L, Rm_tensor_eval] using h_Rm_smooth ![X, Z, Y] ![α]
  have h_trL_smooth : td.isSmoothFam (fun s => atr.tr (L s)) := by
    simpa [L, Rc, ricciForm_tensor_eval] using h_Rc_smooth ![X, Y] ![]
  have h_char : forall (Z : V) (α : V →ₗ[R] R),
      α (dRmEndo t X Y Z) = td.dt_apply (fun s => α (L s Z)) t := by
    intro Z α
    calc
      α (dRmEndo t X Y Z) =
          tensor_eval
            (dt_tensor td t
              (fun s => Rm_tensor emb (conn_fam s) (ha_fam s) (hal_fam s)
                (hsl_fam s) (hl_fam s))
              h_Rm_smooth) ![X, Z, Y] ![α] := h_dRmEndo_eval t X Y Z α
      _ = td.dt_apply
            (fun s => Rm_tensor emb (conn_fam s) (ha_fam s) (hal_fam s)
              (hsl_fam s) (hl_fam s) ![X, Z, Y] ![α]) t := by
          rfl
      _ = td.dt_apply (fun s => α (L s Z)) t := by
          simp [L, Rm_tensor_eval, RcEndo]
  calc
    tensor_eval
        (dt_tensor td t
          (fun s => ricciForm_tensor emb (conn_fam s) (ha_fam s) (hal_fam s)
            (hsl_fam s) (hl_fam s) atr)
          h_Rc_smooth) ![X, Y] ![] =
        td.dt_apply
          (fun s => ricciForm_tensor emb (conn_fam s) (ha_fam s) (hal_fam s)
            (hsl_fam s) (hl_fam s) atr ![X, Y] ![]) t := by
          rfl
    _ = td.dt_apply (fun s => atr.tr (L s)) t := by
          simp [L, Rc, ricciForm_tensor_eval]
    _ = atr.tr (dRmEndo t X Y) := by
          exact dt_tr td atr h_tt L (dRmEndo t X Y) t hαLv_smooth h_trL_smooth h_char
    _ = riemann_to_ricci_trace atr
        (dt_tensor td t
          (fun s => Rm_tensor emb (conn_fam s) (ha_fam s) (hal_fam s)
            (hsl_fam s) (hl_fam s))
          h_Rm_smooth) ![X, Y] ![] := by
          exact (h_contract_trace t X Y).symm

/-- Time derivative commutes with the Ricci trace of Riemann using the reusable
coordinate trace-evaluation law for the middle Ricci slot. -/
theorem ricci_time_trace_commutation_from_coordinate_trace
    (emb : DerivationEmbedding k R V)
    (td : TimeDerivativeData R A Time) [TimeRegularFam td]
    (atr : AbstractTrace R V)
    (h_eval : RicciSlotTraceEval atr)
    (h_tt : TimeTrComm atr td)
    (conn_fam : Time -> V -> V -> V)
    (ha_fam : forall s, forall X Y Z, conn_fam s X (Y + Z) = conn_fam s X Y + conn_fam s X Z)
    (hal_fam : forall s, forall X Y Z, conn_fam s (X + Y) Z = conn_fam s X Z + conn_fam s Y Z)
    (hsl_fam : forall s, forall (f : R) X Z, conn_fam s (f • X) Z = f • conn_fam s X Z)
    (hl_fam : forall s, forall X (f : R) Y,
      conn_fam s X (f • Y) = (emb.embed X) f • Y + f • conn_fam s X Y)
    (h_Rc_smooth : forall vs αs, td.isSmoothFam
      (fun τ => ricciForm_tensor emb (conn_fam τ) (ha_fam τ) (hal_fam τ) (hsl_fam τ)
        (hl_fam τ) atr vs αs))
    (h_Rm_smooth : forall vs αs, td.isSmoothFam
      (fun τ => Rm_tensor emb (conn_fam τ) (ha_fam τ) (hal_fam τ) (hsl_fam τ)
        (hl_fam τ) vs αs))
    (dRmEndo : Time -> V -> V -> V →ₗ[R] V)
    (h_dRmEndo_eval : forall t X Y Z (α : V →ₗ[R] R),
      α (dRmEndo t X Y Z) =
        tensor_eval
          (dt_tensor td t
            (fun s => Rm_tensor emb (conn_fam s) (ha_fam s) (hal_fam s)
              (hsl_fam s) (hl_fam s))
            h_Rm_smooth) ![X, Z, Y] ![α]) :
    forall t X Y,
      tensor_eval
        (dt_tensor td t
          (fun s => ricciForm_tensor emb (conn_fam s) (ha_fam s) (hal_fam s)
            (hsl_fam s) (hl_fam s) atr)
          h_Rc_smooth) ![X, Y] ![] =
      riemann_to_ricci_trace atr
        (dt_tensor td t
          (fun s => Rm_tensor emb (conn_fam s) (ha_fam s) (hal_fam s)
            (hsl_fam s) (hl_fam s))
          h_Rm_smooth) ![X, Y] ![] := by
  exact ricci_time_trace_commutation_from_endomorphism_trace emb td atr h_tt
    conn_fam ha_fam hal_fam hsl_fam hl_fam h_Rc_smooth h_Rm_smooth
    dRmEndo h_dRmEndo_eval
    (riemann_to_ricci_trace_dt_tensor_eval emb td atr h_eval conn_fam
      ha_fam hal_fam hsl_fam hl_fam h_Rm_smooth dRmEndo h_dRmEndo_eval)

/-- Version of `ricci_time_trace_commutation_from_coordinate_trace` consuming
the named Riemann time-derivative slice package. -/
theorem ricci_time_trace_commutation_from_coordinate_trace_of_slice
    (emb : DerivationEmbedding k R V)
    (td : TimeDerivativeData R A Time) [TimeRegularFam td]
    (atr : AbstractTrace R V)
    (h_eval : RicciSlotTraceEval atr)
    (h_tt : TimeTrComm atr td)
    (conn_fam : Time -> V -> V -> V)
    (ha_fam : forall s, forall X Y Z, conn_fam s X (Y + Z) = conn_fam s X Y + conn_fam s X Z)
    (hal_fam : forall s, forall X Y Z, conn_fam s (X + Y) Z = conn_fam s X Z + conn_fam s Y Z)
    (hsl_fam : forall s, forall (f : R) X Z, conn_fam s (f • X) Z = f • conn_fam s X Z)
    (hl_fam : forall s, forall X (f : R) Y,
      conn_fam s X (f • Y) = (emb.embed X) f • Y + f • conn_fam s X Y)
    (h_Rc_smooth : forall vs αs, td.isSmoothFam
      (fun τ => ricciForm_tensor emb (conn_fam τ) (ha_fam τ) (hal_fam τ) (hsl_fam τ)
        (hl_fam τ) atr vs αs))
    (h_Rm_smooth : forall vs αs, td.isSmoothFam
      (fun τ => Rm_tensor emb (conn_fam τ) (ha_fam τ) (hal_fam τ) (hsl_fam τ)
        (hl_fam τ) vs αs))
    (D : RiemannTimeDerivativeSliceEndomorphism emb td conn_fam
      ha_fam hal_fam hsl_fam hl_fam h_Rm_smooth) :
    forall t X Y,
      tensor_eval
        (dt_tensor td t
          (fun s => ricciForm_tensor emb (conn_fam s) (ha_fam s) (hal_fam s)
            (hsl_fam s) (hl_fam s) atr)
          h_Rc_smooth) ![X, Y] ![] =
      riemann_to_ricci_trace atr
        (dt_tensor td t
          (fun s => Rm_tensor emb (conn_fam s) (ha_fam s) (hal_fam s)
            (hsl_fam s) (hl_fam s))
          h_Rm_smooth) ![X, Y] ![] :=
  ricci_time_trace_commutation_from_coordinate_trace emb td atr h_eval h_tt
    conn_fam ha_fam hal_fam hsl_fam hl_fam h_Rc_smooth h_Rm_smooth
    D.endo D.eval_endo

/-- Constructor for the `h_dt_trace` input in the Riemann-trace proof of the
explicit Ricci evolution equation.

Mathematically: `Ric(X,Y) = tr (Z |-> Rm(X,Z)Y)`, so after applying the time
trace-commutation rule and the coordinate evaluation law, `∂ₜ Ric(X,Y)` is the
Ricci-slot trace of `∂ₜ Rm`. The remaining geometric input is the represented
slice `dRmEndo`, whose covector evaluations are exactly those of
`dt_tensor Rm`. -/
theorem ricci_dt_trace_from_coordinate_trace
    (emb : DerivationEmbedding k R V)
    (td : TimeDerivativeData R A Time) [TimeRegularFam td]
    (atr : AbstractTrace R V)
    (h_eval : RicciSlotTraceEval atr)
    (h_tt : TimeTrComm atr td)
    (conn_fam : Time -> V -> V -> V)
    (ha_fam : forall s, forall X Y Z, conn_fam s X (Y + Z) = conn_fam s X Y + conn_fam s X Z)
    (hal_fam : forall s, forall X Y Z, conn_fam s (X + Y) Z = conn_fam s X Z + conn_fam s Y Z)
    (hsl_fam : forall s, forall (f : R) X Z, conn_fam s (f • X) Z = f • conn_fam s X Z)
    (hl_fam : forall s, forall X (f : R) Y,
      conn_fam s X (f • Y) = (emb.embed X) f • Y + f • conn_fam s X Y)
    (h_Rc_smooth : forall vs αs, td.isSmoothFam
      (fun τ => ricciForm_tensor emb (conn_fam τ) (ha_fam τ) (hal_fam τ) (hsl_fam τ)
        (hl_fam τ) atr vs αs))
    (h_Rm_smooth : forall vs αs, td.isSmoothFam
      (fun τ => Rm_tensor emb (conn_fam τ) (ha_fam τ) (hal_fam τ) (hsl_fam τ)
        (hl_fam τ) vs αs))
    (dRmEndo : Time -> V -> V -> V →ₗ[R] V)
    (h_dRmEndo_eval : forall t X Y Z (α : V →ₗ[R] R),
      α (dRmEndo t X Y Z) =
        tensor_eval
          (dt_tensor td t
            (fun s => Rm_tensor emb (conn_fam s) (ha_fam s) (hal_fam s)
              (hsl_fam s) (hl_fam s))
            h_Rm_smooth) ![X, Z, Y] ![α]) :
    forall t X Y,
      tensor_eval
        (dt_tensor td t
          (fun s => ricciForm_tensor emb (conn_fam s) (ha_fam s) (hal_fam s)
            (hsl_fam s) (hl_fam s) atr)
          h_Rc_smooth) ![X, Y] ![] =
      riemann_to_ricci_trace atr
        (dt_tensor td t
          (fun s => Rm_tensor emb (conn_fam s) (ha_fam s) (hal_fam s) (hsl_fam s)
            (hl_fam s)) h_Rm_smooth) ![X, Y] ![] :=
  ricci_time_trace_commutation_from_coordinate_trace emb td atr h_eval h_tt
    conn_fam ha_fam hal_fam hsl_fam hl_fam h_Rc_smooth h_Rm_smooth
    dRmEndo h_dRmEndo_eval

/-- Constructor for the `h_dt_trace` input, with the Riemann time derivative
slice supplied as a named package. -/
theorem ricci_dt_trace_from_coordinate_trace_of_slice
    (emb : DerivationEmbedding k R V)
    (td : TimeDerivativeData R A Time) [TimeRegularFam td]
    (atr : AbstractTrace R V)
    (h_eval : RicciSlotTraceEval atr)
    (h_tt : TimeTrComm atr td)
    (conn_fam : Time -> V -> V -> V)
    (ha_fam : forall s, forall X Y Z, conn_fam s X (Y + Z) = conn_fam s X Y + conn_fam s X Z)
    (hal_fam : forall s, forall X Y Z, conn_fam s (X + Y) Z = conn_fam s X Z + conn_fam s Y Z)
    (hsl_fam : forall s, forall (f : R) X Z, conn_fam s (f • X) Z = f • conn_fam s X Z)
    (hl_fam : forall s, forall X (f : R) Y,
      conn_fam s X (f • Y) = (emb.embed X) f • Y + f • conn_fam s X Y)
    (h_Rc_smooth : forall vs αs, td.isSmoothFam
      (fun τ => ricciForm_tensor emb (conn_fam τ) (ha_fam τ) (hal_fam τ) (hsl_fam τ)
        (hl_fam τ) atr vs αs))
    (h_Rm_smooth : forall vs αs, td.isSmoothFam
      (fun τ => Rm_tensor emb (conn_fam τ) (ha_fam τ) (hal_fam τ) (hsl_fam τ)
        (hl_fam τ) vs αs))
    (D : RiemannTimeDerivativeSliceEndomorphism emb td conn_fam
      ha_fam hal_fam hsl_fam hl_fam h_Rm_smooth) :
    forall t X Y,
      tensor_eval
        (dt_tensor td t
          (fun s => ricciForm_tensor emb (conn_fam s) (ha_fam s) (hal_fam s)
            (hsl_fam s) (hl_fam s) atr)
          h_Rc_smooth) ![X, Y] ![] =
      riemann_to_ricci_trace atr
        (dt_tensor td t
          (fun s => Rm_tensor emb (conn_fam s) (ha_fam s) (hal_fam s) (hsl_fam s)
            (hl_fam s)) h_Rm_smooth) ![X, Y] ![] :=
  ricci_dt_trace_from_coordinate_trace emb td atr h_eval h_tt conn_fam
    ha_fam hal_fam hsl_fam hl_fam h_Rc_smooth h_Rm_smooth
    D.endo D.eval_endo


end RicciEvolutionInterface
