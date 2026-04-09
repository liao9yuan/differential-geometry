import DifferentialGeometry.Synthetic.Algebra.VectorField
import DifferentialGeometry.Synthetic.Algebra.Metric
import DifferentialGeometry.Synthetic.Algebra.Trace
import DifferentialGeometry.Synthetic.Geometry.Connection
import DifferentialGeometry.Synthetic.Operator.Hessian
import DifferentialGeometry.Synthetic.Operator.Laplacian
import DifferentialGeometry.Synthetic.Geometry.Curvature
import DifferentialGeometry.Synthetic.Geometry.CurvatureTensor
import DifferentialGeometry.Synthetic.Geometry.RicciTensor
import DifferentialGeometry.Synthetic.Geometry.RicciIdentity
import DifferentialGeometry.Synthetic.Operator.Gradient
import DifferentialGeometry.Synthetic.Analysis.TensorInnerProduct
import DifferentialGeometry.VectorField
import DifferentialGeometry.Synthetic.Algebra.TensorAlgebra
import DifferentialGeometry.Synthetic.Algebra.BilinearForm
import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.style.emptyLine false

open AbstractDerivationAction AbstractLieBracket DifferentialGeometry TensorAlgebra

variable {R V : Type}
variable [Field R] [LinearOrder R] [IsStrictOrderedRing R] [AddCommGroup V] [Module R V] [TensorAlgebra R V]
variable [AbstractDerivationAction R V] [AbstractLieBracket V] [DerivationRules R V]


-- Proves the expansion of the directional derivative of the squared norm of the gradient.
lemma grad_norm_sq_deriv
  (metric : MetricDuality R V)
  (conn : AbstractAffineConnection R V) [MetricCompatible conn metric.toNonDegenerateMetric.toAbstractMetricTensor]
  (f : R) (X : V) :
  action X (metric.g (grad metric f) (grad metric f)) =
  metric.g (conn.nabla X (grad metric f)) (grad metric f) + metric.g (conn.nabla X (grad metric f)) (grad metric f) := by
  exact norm_sq_deriv conn metric.toNonDegenerateMetric.toAbstractMetricTensor X (grad metric f)

-- Proves the swapping of third-order derivatives of a function by injecting the Riemann curvature tensor.
lemma hessian_commute_ricci [AbstractLieBracket V]
  (conn : AbstractAffineConnection R V) [TorsionFree conn]
  (metric : MetricDuality R V)
  (f : R) (X Y : V) :
  conn.nabla X (conn.nabla Y (grad metric f)) =
  conn.nabla Y (conn.nabla X (grad metric f)) + conn.nabla (bracket X Y) (grad metric f) + Rm conn X Y (grad metric f) := by
  have h := ricci_identity conn X Y (grad metric f)
  have he := secondCovDerivCommutator_expand conn X Y (grad metric f)
  rw [TorsionFree.torsion_zero (conn := conn) X Y] at he
  rw [he] at h
  calc conn.nabla X (conn.nabla Y (grad metric f))
    _ = conn.nabla X (conn.nabla Y (grad metric f)) - conn.nabla Y (conn.nabla X (grad metric f)) - conn.nabla (bracket X Y) (grad metric f) + conn.nabla (bracket X Y) (grad metric f) + conn.nabla Y (conn.nabla X (grad metric f)) := by abel
    _ = Rm conn X Y (grad metric f) + conn.nabla (bracket X Y) (grad metric f) + conn.nabla Y (conn.nabla X (grad metric f)) := by rw [h]
    _ = conn.nabla Y (conn.nabla X (grad metric f)) + conn.nabla (bracket X Y) (grad metric f) + Rm conn X Y (grad metric f) := by abel

variable [AbstractLieBracket V] [DerivationRules R V]



lemma hessian_norm_sq_grad
  (metric : MetricDuality R V)
  (conn : AbstractAffineConnection R V) [MetricCompatible conn metric.toNonDegenerateMetric.toAbstractMetricTensor]
  (f : R) (X Y : V) :
  Hess conn (metric.g (grad metric f) (grad metric f)) X Y =
  2 * metric.g (secondCovDeriv conn X Y (grad metric f)) (grad metric f) +
  2 * metric.g (conn.nabla X (grad metric f)) (conn.nabla Y (grad metric f)) := by
  dsimp [Hess]
  have h1 : action Y (metric.g (grad metric f) (grad metric f)) = metric.g (conn.nabla Y (grad metric f)) (grad metric f) + metric.g (conn.nabla Y (grad metric f)) (grad metric f) := norm_sq_deriv conn metric.toNonDegenerateMetric.toAbstractMetricTensor Y (grad metric f)
  rw [h1]
  rw [DerivationRules.action_add_right]
  have h2 : action X (metric.g (conn.nabla Y (grad metric f)) (grad metric f)) = metric.g (conn.nabla X (conn.nabla Y (grad metric f))) (grad metric f) + metric.g (conn.nabla Y (grad metric f)) (conn.nabla X (grad metric f)) := MetricCompatible.compat (conn:=conn) X (conn.nabla Y (grad metric f)) (grad metric f)
  rw [h2]
  have h3 : action (conn.nabla X Y) (metric.g (grad metric f) (grad metric f)) = metric.g (conn.nabla (conn.nabla X Y) (grad metric f)) (grad metric f) + metric.g (conn.nabla (conn.nabla X Y) (grad metric f)) (grad metric f) := norm_sq_deriv conn metric.toNonDegenerateMetric.toAbstractMetricTensor (conn.nabla X Y) (grad metric f)
  rw [h3]
  have hsym : metric.g (conn.nabla Y (grad metric f)) (conn.nabla X (grad metric f)) = metric.g (conn.nabla X (grad metric f)) (conn.nabla Y (grad metric f)) := metric.symm _ _
  rw [hsym]
  dsimp [secondCovDeriv]
  have hsplit : metric.g (conn.nabla X (conn.nabla Y (grad metric f)) - conn.nabla (conn.nabla X Y) (grad metric f)) (grad metric f) = metric.g (conn.nabla X (conn.nabla Y (grad metric f))) (grad metric f) - metric.g (conn.nabla (conn.nabla X Y) (grad metric f)) (grad metric f) := by
    calc metric.g (conn.nabla X (conn.nabla Y (grad metric f)) - conn.nabla (conn.nabla X Y) (grad metric f)) (grad metric f)
      _ = metric.g (conn.nabla X (conn.nabla Y (grad metric f)) + - conn.nabla (conn.nabla X Y) (grad metric f)) (grad metric f) := by rw [sub_eq_add_neg]
      _ = metric.g (conn.nabla X (conn.nabla Y (grad metric f))) (grad metric f) + metric.g (- conn.nabla (conn.nabla X Y) (grad metric f)) (grad metric f) := metric.bilinear_add_left _ _ _
      _ = metric.g (conn.nabla X (conn.nabla Y (grad metric f))) (grad metric f) + - metric.g (conn.nabla (conn.nabla X Y) (grad metric f)) (grad metric f) := by rw [metric_neg_left]
      _ = metric.g (conn.nabla X (conn.nabla Y (grad metric f))) (grad metric f) - metric.g (conn.nabla (conn.nabla X Y) (grad metric f)) (grad metric f) := (sub_eq_add_neg _ _).symm
  rw [hsplit]
  ring

/-!
## Bochner-Weitzenböck Calculus

The `secondCovDeriv_02_tensor` encodes the (0,2) tensor `(X, Y) ↦ g(∇²_{X,Y}∇f, ∇f)`.
It is defined algebraically as the residual of `hessianForm(|∇f|²)` after subtracting
the Hessian norm contribution, scaled by `⅟2`.

The two main theorems are:
- `bochner_lap_expand_thm`: Δ(|∇f|²) = 2·tr(SCT) + 2·|∇²f|²
- `bochner_commutation_thm`: tr(SCT) = Ric(∇f,∇f) + ⟨∇f, ∇Δf⟩
Together they give the Bochner-Weitzenböck identity.
-/

noncomputable def secondCovDeriv_02_tensor
    [Invertible (2 : R)]
    (metric : MetricDuality R V)
    (conn : AbstractAffineConnection R V)
    [AffineTensorCalculus conn]
    [MetricCompatible conn metric.toNonDegenerateMetric.toAbstractMetricTensor]
    [TensorInnerProductRules R V metric]
    (f : R) : AbstractBilinearForm R V :=
  let hF := hessianForm metric conn f
  let Q := TensorAlgebra.contract (r:=0) (s:=2)
    (TensorAlgebra.tensor_prod (r1:=1) (s1:=1) (r2:=0) (s2:=2)
      (raise_index metric (0 : Fin 2) hF) hF)
  TensorAlgebra.smul (⅟(2 : R))
    (TensorAlgebra.add
      (hessianForm metric conn (metric.g (grad metric f) (grad metric f)))
      (TensorAlgebra.smul (-2 : R) Q))

private noncomputable def hessNormQ
    (metric : MetricDuality R V)
    (conn : AbstractAffineConnection R V)
    [AffineTensorCalculus conn]
    (f : R) : AbstractBilinearForm R V :=
  let hF := hessianForm metric conn f
  TensorAlgebra.contract (r:=0) (s:=2)
    (TensorAlgebra.tensor_prod (r1:=1) (s1:=1) (r2:=0) (s2:=2)
      (raise_index metric (0 : Fin 2) hF) hF)

private lemma tensorNormSq_eq_trace_hessNormQ
    (metric : MetricDuality R V)
    (conn : AbstractAffineConnection R V)
    [AffineTensorCalculus conn]
    [MetricCompatible conn metric.toNonDegenerateMetric.toAbstractMetricTensor]
    [TensorInnerProductRules R V metric]
    (f : R) :
    tensorNormSq metric (hessianForm metric conn f) =
    tensor_eval (metric_trace metric (0 : Fin 2) (0 : Fin 1) (hessNormQ metric conn f)) ![] ![] := by
  unfold tensorNormSq hessNormQ
  exact TensorInnerProductRules.inner_trace (hessianForm metric conn f) (hessianForm metric conn f)

theorem bochner_lap_expand_thm
    [Invertible (2 : R)]
    (metric : MetricDuality R V)
    (conn : AbstractAffineConnection R V)
    [AffineTensorCalculus conn] [RiemannCurvatureTensorOp conn] [TorsionFree conn]
    [MetricCompatible conn metric.toNonDegenerateMetric.toAbstractMetricTensor]
    [TensorInnerProductRules R V metric]
    [BilinearFormExt R V]
    [MetricEvaluationRules R V metric.toNonDegenerateMetric.toAbstractMetricTensor]
    (f : R) :
    laplacian metric conn (metric.g (grad metric f) (grad metric f)) =
    2 * (tensor_eval (metric_trace metric (0 : Fin 2) (0 : Fin 1)
      (secondCovDeriv_02_tensor metric conn f)) ![] ![]) +
    2 * tensorNormSq metric (hessianForm metric conn f) := by
  simp only [laplacian, secondCovDeriv_02_tensor]
  rw [metric_trace_smul, metric_trace_add, metric_trace_smul]
  rw [tensor_eval_smul, tensor_eval_add, tensor_eval_smul]
  rw [tensorNormSq_eq_trace_hessNormQ metric conn f]
  simp only [hessNormQ]
  set L := tensor_eval (metric_trace metric (0 : Fin 2) (0 : Fin 1) (hessianForm metric conn (metric.g (grad metric f) (grad metric f)))) ![] ![]
  set N := tensor_eval (metric_trace metric (0 : Fin 2) (0 : Fin 1) (TensorAlgebra.contract (r:=0) (s:=2) (TensorAlgebra.tensor_prod (r1:=1) (s1:=1) (r2:=0) (s2:=2) (raise_index metric (0 : Fin 2) (hessianForm metric conn f)) (hessianForm metric conn f)))) ![] ![]
  have h2 : (2 : R) * ⅟(2 : R) = 1 := mul_invOf_self (2 : R)
  have key : 2 * (⅟(2 : R) * (L + (-2) * N)) + 2 * N = L := by
    have : 2 * (⅟(2 : R) * (L + (-2) * N)) = L + (-2) * N := by
      calc 2 * (⅟(2 : R) * (L + (-2) * N))
        _ = (2 * ⅟(2 : R)) * (L + (-2) * N) := by ring
        _ = 1 * (L + (-2) * N) := by rw [h2]
        _ = L + (-2) * N := by ring
    linarith
  linarith [key]

/-- The rough Bochner trace defined directly via `secondCovDeriv_02_tensor`. -/
noncomputable def roughBochnerTrace
    [Invertible (2 : R)]
    (metric : MetricDuality R V)
    (conn : AbstractAffineConnection R V)
    [AffineTensorCalculus conn]
    [MetricCompatible conn metric.toNonDegenerateMetric.toAbstractMetricTensor]
    [TensorInnerProductRules R V metric]
    (f : R) : R :=
  tensor_eval (metric_trace metric (0 : Fin 2) (0 : Fin 1)
    (secondCovDeriv_02_tensor metric conn f)) ![] ![]

/-!
### Hessian metric symmetry

For a torsion-free metric-compatible connection, the Hessian pairing is symmetric:
`g(∇_A ∇f, B) = g(∇_B ∇f, A)`.
-/
private lemma hessian_metric_symm
    [LieDerivation R V] [ActionLinear R V]
    (metric : MetricDuality R V)
    (conn : AbstractAffineConnection R V)
    [TorsionFree conn]
    [MetricCompatible conn metric.toNonDegenerateMetric.toAbstractMetricTensor]
    (f : R) (A B : V) :
    metric.g (conn.nabla A (grad metric f)) B =
    metric.g (conn.nabla B (grad metric f)) A := by
  set m := metric.toNonDegenerateMetric.toAbstractMetricTensor
  -- g(∇_A ∇f, B) = Hess(f)(A, B) via metric compat + g_grad
  have hAB : m.g (conn.nabla A (grad metric f)) B = Hess conn f A B := by
    have mc := MetricCompatible.compat (conn:=conn) (metric:=m) A B (grad metric f)
    have g1 : m.g B (grad metric f) = action B f := by
      rw [m.symm]; exact g_grad metric f B
    have g2 : m.g (conn.nabla A B) (grad metric f) = action (conn.nabla A B) f := by
      rw [m.symm]; exact g_grad metric f (conn.nabla A B)
    rw [g1, g2] at mc
    -- mc: action A (action B f) = action (∇_A B) f + g(B, ∇_A ∇f)
    -- So g(B, ∇_A ∇f) = action A (action B f) - action (∇_A B) f = Hess f A B
    have : m.g B (conn.nabla A (grad metric f)) = Hess conn f A B := by
      dsimp [Hess]; linarith
    rw [m.symm] at this; exact this
  have hBA : m.g (conn.nabla B (grad metric f)) A = Hess conn f B A := by
    have mc := MetricCompatible.compat (conn:=conn) (metric:=m) B A (grad metric f)
    have g1 : m.g A (grad metric f) = action A f := by
      rw [m.symm]; exact g_grad metric f A
    have g2 : m.g (conn.nabla B A) (grad metric f) = action (conn.nabla B A) f := by
      rw [m.symm]; exact g_grad metric f (conn.nabla B A)
    rw [g1, g2] at mc
    have : m.g A (conn.nabla B (grad metric f)) = Hess conn f B A := by
      dsimp [Hess]; linarith
    rw [m.symm] at this; exact this
  rw [hAB, hBA, hessian_symm]

/-!
### Weitzenböck pointwise decomposition

`g(∇²_{X,Y}∇f, ∇f) = g(∇²_{∇f,X}∇f, Y) - g(Rm(X,∇f)Y, ∇f)`
-/
private lemma secondCovDeriv_weitzenbock
    [LieDerivation R V] [ActionLinear R V] [LieDerivationRules R V]
    (metric : MetricDuality R V)
    (conn : AbstractAffineConnection R V) [TorsionFree conn]
    [MetricCompatible conn metric.toNonDegenerateMetric.toAbstractMetricTensor]
    (f : R) (X Y : V) :
    metric.g (secondCovDeriv conn X Y (grad metric f)) (grad metric f) =
    metric.g (secondCovDeriv conn (grad metric f) X (grad metric f)) Y -
    metric.g (Rm conn X (grad metric f) Y) (grad metric f) := by
  set m := metric.toNonDegenerateMetric.toAbstractMetricTensor
  set gf := grad metric f
  -- Abbreviation for hessian metric symmetry
  have hms : ∀ A B : V, m.g (conn.nabla A gf) B = m.g (conn.nabla B gf) A :=
    hessian_metric_symm metric conn f
  -- Step 1: g(∇²_{X,Y}∇f, ∇f) = g(∇²_{X,∇f}∇f, Y)
  -- Expand both secondCovDeriv's
  have lhs : m.g (secondCovDeriv conn X Y gf) gf =
      m.g (conn.nabla X (conn.nabla Y gf)) gf - m.g (conn.nabla (conn.nabla X Y) gf) gf := by
    dsimp [secondCovDeriv]; rw [metric_sub_left]
  have rhs_step : m.g (secondCovDeriv conn X gf gf) Y =
      m.g (conn.nabla X (conn.nabla gf gf)) Y - m.g (conn.nabla (conn.nabla X gf) gf) Y := by
    dsimp [secondCovDeriv]; rw [metric_sub_left]
  -- Metric compat: g(∇_X(∇_Y∇f), ∇f) = X(g(∇_Y∇f, ∇f)) - g(∇_Y∇f, ∇_X∇f)
  have mc1 : action X (m.g (conn.nabla Y gf) gf) =
      m.g (conn.nabla X (conn.nabla Y gf)) gf + m.g (conn.nabla Y gf) (conn.nabla X gf) :=
    MetricCompatible.compat (conn:=conn) (metric:=m) X (conn.nabla Y gf) gf
  -- Metric compat: X(g(∇_{∇f}∇f, Y)) = g(∇_X(∇_{∇f}∇f), Y) + g(∇_{∇f}∇f, ∇_XY)
  have mc2 : action X (m.g (conn.nabla gf gf) Y) =
      m.g (conn.nabla X (conn.nabla gf gf)) Y + m.g (conn.nabla gf gf) (conn.nabla X Y) :=
    MetricCompatible.compat (conn:=conn) (metric:=m) X (conn.nabla gf gf) Y
  -- Hessian symmetry gives: g(∇_Y∇f, ∇f) = g(∇_{∇f}∇f, Y) and g(∇_{∇_XY}∇f, ∇f) = g(∇_{∇f}∇f, ∇_XY)
  have hsym1 : m.g (conn.nabla Y gf) gf = m.g (conn.nabla gf gf) Y := hms Y gf
  have hsym2 : m.g (conn.nabla (conn.nabla X Y) gf) gf = m.g (conn.nabla gf gf) (conn.nabla X Y) := hms (conn.nabla X Y) gf
  have hsym3 : m.g (conn.nabla (conn.nabla X gf) gf) Y = m.g (conn.nabla Y gf) (conn.nabla X gf) := hms (conn.nabla X gf) Y
  -- Key bridge: action X respects the symmetry hsym1
  have hsym1_action : action X (m.g (conn.nabla Y gf) gf) = action X (m.g (conn.nabla gf gf) Y) := by
    rw [hsym1]
  -- Now show the two sides are equal
  have step1 : m.g (secondCovDeriv conn X Y gf) gf = m.g (secondCovDeriv conn X gf gf) Y := by
    rw [lhs, rhs_step]
    linarith [hsym1_action, hsym2, hsym3, mc1, mc2]
  -- Step 2: Ricci identity: ∇²_{X,∇f}∇f = ∇²_{∇f,X}∇f + Rm(X,∇f)∇f
  have ricci_id : secondCovDeriv conn X gf gf = secondCovDeriv conn gf X gf + Rm conn X gf gf := by
    have h_comm := ricci_identity conn X gf gf
    dsimp [secondCovDerivCommutator] at h_comm
    -- h_comm: secondCovDeriv X gf gf - secondCovDeriv gf X gf = Rm X gf gf
    have := sub_eq_iff_eq_add.mp h_comm
    rwa [add_comm] at this
  -- Step 3: Rm_metric_antisymm: g(Rm(X,∇f)∇f, Y) = -g(Rm(X,∇f)Y, ∇f)
  have rm_flip : m.g (Rm conn X gf gf) Y = - m.g (Rm conn X gf Y) gf :=
    Rm_metric_antisymm conn metric X gf gf Y
  -- Combine
  calc m.g (secondCovDeriv conn X Y gf) gf
    _ = m.g (secondCovDeriv conn X gf gf) Y := step1
    _ = m.g (secondCovDeriv conn gf X gf + Rm conn X gf gf) Y := by rw [ricci_id]
    _ = m.g (secondCovDeriv conn gf X gf) Y + m.g (Rm conn X gf gf) Y := m.bilinear_add_left _ _ _
    _ = m.g (secondCovDeriv conn gf X gf) Y - m.g (Rm conn X gf Y) gf := by rw [rm_flip]; ring

/-!
### Pointwise evaluation bridge for SCT

Proves that `tensor_eval SCT ![X,Y] ![]` = `tensor_eval (∇_{∇f} hessianForm(f)) ![X,Y] ![]` -
`g(Rm(X,∇f)Y, ∇f)` using:
- `hessianForm_eval` + `hessian_norm_sq_grad` + `RaiseIndexEvaluationRules` + `ContractCompositionRules`
- `covDeriv_eval` + `hessianForm_eval` + metric compatibility for ∇(hessianForm) evaluation
- `secondCovDeriv_weitzenbock` for the geometric identity
-/
private lemma SCT_eval_eq
    [Invertible (2 : R)]
    [LieDerivation R V] [ActionLinear R V] [LieDerivationRules R V]
    (metric : MetricDuality R V)
    (conn : AbstractAffineConnection R V)
    [AffineTensorCalculus conn] [TorsionFree conn]
    [MetricCompatible conn metric.toNonDegenerateMetric.toAbstractMetricTensor]
    [TensorInnerProductRules R V metric]
    [MetricEvaluationRules R V metric.toNonDegenerateMetric.toAbstractMetricTensor]
    [RaiseIndexEvaluationRules R V metric]
    [ContractCompositionRules R V]
    (f : R) (X Y : V) :
    tensor_eval (secondCovDeriv_02_tensor metric conn f) ![X, Y] ![] =
    metric.g (secondCovDeriv conn X Y (grad metric f)) (grad metric f) := by
  set m := metric.toNonDegenerateMetric.toAbstractMetricTensor
  set gf := grad metric f
  set hF := hessianForm metric conn f
  -- Unfold SCT = ⅟2 * (hessianForm(|∇f|²) + (-2) * Q)
  simp only [secondCovDeriv_02_tensor]
  rw [tensor_eval_smul, tensor_eval_add, tensor_eval_smul]
  -- Evaluate hessianForm(|∇f|²)(X,Y) = Hess(|∇f|²)(X,Y) via hessianForm_eval
  have h_hF_norm := hessianForm_eval metric conn (m.g gf gf) X Y
  -- Expand using hessian_norm_sq_grad
  have h_norm := hessian_norm_sq_grad metric conn f X Y
  rw [h_hF_norm, h_norm]
  -- Evaluate Q = contract(raise(hF) ⊗ hF) via RaiseIndexEvaluationRules + ContractCompositionRules
  -- hF(X,Y) = g(X, ∇_Y∇f) (from hessianForm_eval proof chain)
  have h_hF_eval : ∀ A B : V, tensor_eval hF ![A, B] ![] = m.g A (conn.nabla B gf) := by
    intro A B
    rw [hessianForm_eval metric conn f A B]
    dsimp [Hess]
    have mc := MetricCompatible.compat (conn:=conn) (metric:=m) B A gf
    have g1 : m.g A gf = action A f := by rw [m.symm]; exact g_grad metric f A
    have g2 : m.g (conn.nabla B A) gf = action (conn.nabla B A) f := by rw [m.symm]; exact g_grad metric f (conn.nabla B A)
    rw [g1, g2] at mc
    have : m.g A (conn.nabla B gf) = action B (action A f) - action (conn.nabla B A) f := by linarith
    rw [this]; exact (hessian_symm conn f B A).symm
  -- Build the Hessian endomorphism L_hF : Y ↦ ∇_Y(∇f)
  let L_hF : V →ₗ[R] V :=
    { toFun := fun Z => conn.nabla Z gf
      map_add' := fun a b => conn.nabla_add_left a b gf
      map_smul' := fun r a => conn.nabla_smul_left r a gf }
  -- Axiom 1: raise(hF)(X,n) = n(L_hF X)
  have h_raise := RaiseIndexEvaluationRules.raise_eval hF L_hF h_hF_eval
  -- Axiom 3: Q(X,Y) = hF(Y, L_hF X) = hF(Y, ∇_X ∇f)
  have h_Q_step := ContractCompositionRules.contract_comp_eval
    (raise_index metric (0 : Fin 2) hF) hF L_hF h_raise X Y
  -- Q(X,Y) = hF(Y, ∇_X∇f) = g(Y, ∇_{∇_X∇f}∇f) = g(∇_X∇f, ∇_Y∇f) via hessian_metric_symm
  have h_Q : tensor_eval (TensorAlgebra.contract (r := 0) (s := 2)
      (TensorAlgebra.tensor_prod (r1 := 1) (s1 := 1) (r2 := 0) (s2 := 2)
        (raise_index metric (0 : Fin 2) hF) hF)) ![X, Y] ![] =
      m.g (conn.nabla X gf) (conn.nabla Y gf) := by
    calc tensor_eval (TensorAlgebra.contract (r := 0) (s := 2)
          (TensorAlgebra.tensor_prod (r1 := 1) (s1 := 1) (r2 := 0) (s2 := 2)
            (raise_index metric (0 : Fin 2) hF) hF)) ![X, Y] ![]
      _ = tensor_eval hF ![Y, L_hF X] ![] := h_Q_step
      _ = m.g Y (conn.nabla (L_hF X) gf) := h_hF_eval Y (L_hF X)
      _ = m.g (conn.nabla (L_hF X) gf) Y := m.symm _ _
      _ = m.g (conn.nabla Y gf) (L_hF X) := hessian_metric_symm metric conn f _ Y
      _ = m.g (conn.nabla X gf) (conn.nabla Y gf) := m.symm _ _
  rw [h_Q]
  -- Algebra: ⅟2 * (2 * g(∇²∇f, ∇f) + 2 * g(∇_X∇f, ∇_Y∇f) + (-2) * g(∇_X∇f, ∇_Y∇f))
  -- = g(∇²∇f, ∇f)
  have h2 : (2 : R) * ⅟(2 : R) = 1 := mul_invOf_self (2 : R)
  have : ⅟(2 : R) * (2 * m.g (secondCovDeriv conn X Y gf) gf + 2 * m.g (conn.nabla X gf) (conn.nabla Y gf) + (-2) * m.g (conn.nabla X gf) (conn.nabla Y gf)) = m.g (secondCovDeriv conn X Y gf) gf := by
    have : ⅟(2 : R) * (2 * m.g (secondCovDeriv conn X Y gf) gf + 2 * m.g (conn.nabla X gf) (conn.nabla Y gf) + (-2) * m.g (conn.nabla X gf) (conn.nabla Y gf))
      = ⅟(2 : R) * (2 * m.g (secondCovDeriv conn X Y gf) gf) := by ring
    rw [this]; calc ⅟(2 : R) * (2 * m.g (secondCovDeriv conn X Y gf) gf)
      _ = (2 * ⅟(2 : R)) * m.g (secondCovDeriv conn X Y gf) gf := by ring
      _ = 1 * m.g (secondCovDeriv conn X Y gf) gf := by rw [h2]
      _ = m.g (secondCovDeriv conn X Y gf) gf := by ring
  linarith

private lemma T_lap_eval
    [LieDerivation R V] [ActionLinear R V]
    (metric : MetricDuality R V)
    (conn : AbstractAffineConnection R V)
    [AffineTensorCalculus conn] [TorsionFree conn]
    [MetricCompatible conn metric.toNonDegenerateMetric.toAbstractMetricTensor]
    [MetricEvaluationRules R V metric.toNonDegenerateMetric.toAbstractMetricTensor]
    (f : R) (X Y : V) :
    tensor_eval (genericCovDeriv conn (grad metric f) (hessianForm metric conn f)) ![X, Y] ![] =
    metric.g (secondCovDeriv conn (grad metric f) X (grad metric f)) Y := by
  set m := metric.toNonDegenerateMetric.toAbstractMetricTensor
  set gf := grad metric f
  set hF := hessianForm metric conn f
  -- Step 1: tensor_eval = rawCovDeriv via covDeriv_eval
  have h_cov := covDeriv_eval conn gf hF X Y
  dsimp [covDerivOp, genericCovDeriv] at h_cov ⊢; rw [h_cov]
  -- Step 2: rawCovDeriv of symmetric hF is symmetric in X,Y
  -- So rawCovDeriv gf hF X Y = rawCovDeriv gf hF Y X
  have h_sym : rawCovDeriv conn gf hF X Y = rawCovDeriv conn gf hF Y X := by
    dsimp [rawCovDeriv]
    rw [hessianForm_eval metric conn f X Y, hessianForm_eval metric conn f Y X,
        hessianForm_eval metric conn f (conn.nabla gf X) Y,
        hessianForm_eval metric conn f (conn.nabla gf Y) X,
        hessianForm_eval metric conn f X (conn.nabla gf Y),
        hessianForm_eval metric conn f Y (conn.nabla gf X)]
    rw [hessian_symm conn f X Y,
        hessian_symm conn f (conn.nabla gf X) Y,
        hessian_symm conn f X (conn.nabla gf Y)]
    ring
  -- Step 3: Evaluate rawCovDeriv gf hF Y X = g(Y, secondCovDeriv gf X gf)
  -- by the natural expansion
  have h_nat : rawCovDeriv conn gf hF Y X = m.g Y (secondCovDeriv conn gf X gf) := by
    dsimp [rawCovDeriv]
    rw [hessianForm_eval metric conn f Y X,
        hessianForm_eval metric conn f (conn.nabla gf Y) X,
        hessianForm_eval metric conn f Y (conn.nabla gf X)]
    -- Now: action gf (Hess f Y X) - Hess f (∇_{gf}Y) X - Hess f Y (∇_{gf}X)
    -- Hess f Y X = g(Y, ∇_X gf) (by hess_gXY + hessian_symm)
    have hess_to_g : ∀ A B : V, Hess conn f A B = m.g A (conn.nabla B gf) := by
      intro A B
      have mc' := MetricCompatible.compat (conn:=conn) (metric:=m) B A gf
      have g1 : m.g A gf = action A f := by rw [m.symm]; exact g_grad metric f A
      have g2 : m.g (conn.nabla B A) gf = action (conn.nabla B A) f := by rw [m.symm]; exact g_grad metric f (conn.nabla B A)
      rw [g1, g2] at mc'; dsimp [Hess]
      have h := hessian_symm conn f B A; dsimp [Hess] at h; linarith
    rw [hess_to_g Y X, hess_to_g (conn.nabla gf Y) X, hess_to_g Y (conn.nabla gf X)]
    -- action gf (g(Y, ∇_X gf)) - g(∇_{gf}Y, ∇_X gf) - g(Y, ∇_{∇_{gf}X} gf)
    have mc := MetricCompatible.compat (conn:=conn) (metric:=m) gf Y (conn.nabla X gf)
    -- mc: gf(g(Y, ∇_X gf)) = g(∇_{gf}Y, ∇_X gf) + g(Y, ∇_{gf}(∇_X gf))
    dsimp [secondCovDeriv]
    -- Goal: ... = g(Y, ∇_{gf}(∇_X gf) - ∇_{∇_{gf}X} gf)
    -- Expand g(Y, A - B) = g(Y, A) - g(Y, B) using metric symmetry + metric_sub_left
    have hsub : m.g Y (conn.nabla gf (conn.nabla X gf) - conn.nabla (conn.nabla gf X) gf) =
        m.g Y (conn.nabla gf (conn.nabla X gf)) - m.g Y (conn.nabla (conn.nabla gf X) gf) := by
      rw [m.symm Y, metric_sub_left, m.symm (conn.nabla gf (conn.nabla X gf)),
          m.symm (conn.nabla (conn.nabla gf X) gf)]
    rw [hsub]; linarith
  -- Step 4: g(Y, secondCovDeriv gf X gf) = g(secondCovDeriv gf X gf, Y) by metric symm
  rw [h_sym, h_nat, m.symm]

private lemma pw_decomp
    [Invertible (2 : R)]
    [LieDerivation R V] [ActionLinear R V] [LieDerivationRules R V]
    (metric : MetricDuality R V)
    (conn : AbstractAffineConnection R V)
    [AffineTensorCalculus conn] [TorsionFree conn]
    [MetricCompatible conn metric.toNonDegenerateMetric.toAbstractMetricTensor]
    [TensorInnerProductRules R V metric]
    [MetricEvaluationRules R V metric.toNonDegenerateMetric.toAbstractMetricTensor]
    [RaiseIndexEvaluationRules R V metric]
    [ContractCompositionRules R V]
    (f : R) (X Y : V) :
    tensor_eval (secondCovDeriv_02_tensor metric conn f) ![X, Y] ![] =
    tensor_eval (genericCovDeriv conn (grad metric f) (hessianForm metric conn f)) ![X, Y] ![] -
    metric.g (Rm conn X (grad metric f) Y) (grad metric f) := by
  rw [SCT_eval_eq metric conn f X Y, T_lap_eval metric conn f X Y]
  exact secondCovDeriv_weitzenbock metric conn f X Y

/-!
### Bochner commutation theorem

The Weitzenböck trace identity: `tr_g(SCT) = Rc(∇f,∇f) + ⟨∇f, ∇Δf⟩`.
-/
theorem bochner_commutation_thm
    [Invertible (2 : R)]
    [LieDerivation R V] [ActionLinear R V] [LieDerivationRules R V]
    (metric : MetricDuality R V)
    (conn : AbstractAffineConnection R V)
    [AffineTensorCalculus conn] [RiemannCurvatureTensorOp conn] [TorsionFree conn]
    [JacobiIdentity V]
    [MetricCompatible conn metric.toNonDegenerateMetric.toAbstractMetricTensor]
    [TensorInnerProductRules R V metric]
    [BilinearFormExt R V]
    [MetricEvaluationRules R V metric.toNonDegenerateMetric.toAbstractMetricTensor]
    [AbstractTraceRules R V]
    [RaiseIndexEvaluationRules R V metric]
    [Contract11EvaluationRules R V]
    [ContractCompositionRules R V]
    [Contract13EvaluationRules R V]
    (f : R)
    (h_ginv : ∀ X : V, AffineTensorCalculus.nabla_tensor conn X metric.g_inv = 0) :
    tensor_eval (metric_trace metric (0 : Fin 2) (0 : Fin 1)
      (secondCovDeriv_02_tensor metric conn f)) ![] ![] =
    Rc conn (grad metric f) (grad metric f) +
    metric.g (grad metric f) (grad metric (laplacian metric conn f)) := by
  -- Abbreviations
  let gf := grad metric f
  let hF := hessianForm metric conn f
  let SCT := secondCovDeriv_02_tensor metric conn f
  let T_lap := genericCovDeriv conn gf hF
  -- Step 1: Build T_neg_rm = SCT - T_lap, which evaluates to -g(Rm(X,∇f)Y, ∇f)
  let T_neg_rm := TensorAlgebra.add SCT (TensorAlgebra.smul (-1 : R) T_lap)
  -- Step 2: Use BilinearFormExt to show SCT = T_lap + T_neg_rm
  have h_decomp : SCT = TensorAlgebra.add T_lap T_neg_rm := by
    apply BilinearFormExt.ext
    intro X Y
    rw [tensor_eval_add, tensor_eval_add, tensor_eval_smul]
    have := pw_decomp metric conn f X Y
    linarith
  -- Step 3: Trace linearity
  have trace_split : tensor_eval (metric_trace metric (0 : Fin 2) (0 : Fin 1) SCT) ![] ![] =
      tensor_eval (metric_trace metric (0 : Fin 2) (0 : Fin 1) T_lap) ![] ![] +
      tensor_eval (metric_trace metric (0 : Fin 2) (0 : Fin 1) T_neg_rm) ![] ![] := by
    rw [h_decomp, metric_trace_add, tensor_eval_add]
  -- Step 4: T_neg_rm evaluates to -g(Rm(X,gf)Y, gf) → trace_rm_eval gives Rc(gf,gf)
  have trace_neg_rm_val : tensor_eval (metric_trace metric (0 : Fin 2) (0 : Fin 1) T_neg_rm) ![] ![] =
      Rc conn gf gf := by
    apply trace_rm_eval metric conn _ gf gf
    intro X Y
    -- Show: T_neg_rm(X,Y) = -g(Rm(X, gf)Y, gf)
    change tensor_eval (TensorAlgebra.add SCT (TensorAlgebra.smul (-1 : R) T_lap)) ![X, Y] ![] = _
    rw [tensor_eval_add, tensor_eval_smul]
    have := pw_decomp metric conn f X Y
    linarith
  -- Step 5: Trace of T_lap = g(∇f, ∇Δf) via nabla_metric_trace
  have trace_lap : tensor_eval (metric_trace metric (0 : Fin 2) (0 : Fin 1) T_lap) ![] ![] =
      metric.g gf (grad metric (laplacian metric conn f)) := by
    have h_comm := nabla_metric_trace metric conn gf (0 : Fin 2) (0 : Fin 1) hF (h_ginv gf)
    have h_mt_eq : metric_trace metric (0 : Fin 2) (0 : Fin 1) T_lap =
        genericCovDeriv conn gf (metric_trace metric (0 : Fin 2) (0 : Fin 1) hF) := h_comm.symm
    rw [h_mt_eq]
    dsimp [genericCovDeriv]
    set S := metric_trace metric (0 : Fin 2) (0 : Fin 1) hF
    have h_S_scalar : S = TensorAlgebra.fromData (scalarToData (tensor_eval S ![] ![])) := by
      have h_td : scalarToData (tensor_eval S ![] ![]) = TensorAlgebra.toData S := by
        ext m n; dsimp [tensor_eval, scalarToData, MultilinearMap.constOfIsEmpty]
        rw [show m = ![] from Subsingleton.elim _ _, show n = ![] from Subsingleton.elim _ _]
      rw [h_td, TensorAlgebra.fromData_toData]
    have h_lap_val : tensor_eval S ![] ![] = laplacian metric conn f := rfl
    rw [h_S_scalar, AffineTensorCalculus.nabla_scalar gf, h_lap_val]
    dsimp [tensor_eval]; rw [TensorAlgebra.toData_fromData]
    dsimp [scalarToData, MultilinearMap.constOfIsEmpty]
    rw [metric.toNonDegenerateMetric.toAbstractMetricTensor.symm gf (grad metric (laplacian metric conn f))]
    exact (g_grad metric (laplacian metric conn f) gf).symm
  -- Step 6: Combine
  rw [trace_split, trace_lap, trace_neg_rm_val]; ring

/-- The Bochner-Weitzenböck identity:
    `Δ|∇f|² = 2|∇²f|² + 2 Rc(∇f,∇f) + 2⟨∇f, ∇Δf⟩`. -/
theorem bochner_identity
  [Invertible (2 : R)]
  [LieDerivation R V] [ActionLinear R V] [LieDerivationRules R V]
  (metric : MetricDuality R V)
  (conn : AbstractAffineConnection R V) [AffineTensorCalculus conn] [RiemannCurvatureTensorOp conn] [TorsionFree conn]
  [JacobiIdentity V]
  [MetricCompatible conn metric.toNonDegenerateMetric.toAbstractMetricTensor]
  [TensorInnerProductRules R V metric]
  [BilinearFormExt R V]
  [MetricEvaluationRules R V metric.toNonDegenerateMetric.toAbstractMetricTensor]
  [AbstractTraceRules R V]
  [RaiseIndexEvaluationRules R V metric]
  [Contract11EvaluationRules R V]
  [ContractCompositionRules R V]
  [Contract13EvaluationRules R V]
  (f : R)
  (h_ginv : ∀ X : V, AffineTensorCalculus.nabla_tensor conn X metric.g_inv = 0) :
  laplacian metric conn (metric.g (grad metric f) (grad metric f)) =
  2 * tensorNormSq metric (hessianForm metric conn f) +
  2 * Rc conn (grad metric f) (grad metric f) +
  2 * metric.g (grad metric f) (grad metric (laplacian metric conn f)) := by
  have h1 := bochner_lap_expand_thm metric conn f
  have h2 := bochner_commutation_thm metric conn f h_ginv
  rw [h1, h2]
  ring
