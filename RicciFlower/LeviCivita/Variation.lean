import RicciFlower.Coordinates.Christoffel
import RicciFlower.Curvature.Basic
import RicciFlower.LeviCivita.Basic
import RicciFlower.LeviCivita.Torsion
import RicciFlower.VectorBundle.PartialMfderiv

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

/-!
# First variation of Levi-Civita Christoffel components

This file contains the RicciFlower-native arbitrary metric-variation interface
needed by Perelman's formula 5.10.  Unlike the Ricci-flow evolution files, this
layer does not assume `partial_t g = -2 Ric`.

The central producer is `lcGammaVar`: from a path of Levi-Civita connections,
raw metric-component derivatives, fixed-base covariant derivatives of the
metric variation, and derivatives of Christoffel components, it derives the
standard formula

`delta Gamma^k_ij = 1/2 g^{kl} (nabla_i v_jl + nabla_j v_il - nabla_l v_ij)`.
-/

noncomputable section

namespace RicciFlower
namespace LeviCivita

open Bundle
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]
variable {Idx : Type*} [Fintype Idx]
variable {u : Set M}

/-- Difference of two time-slice connections evaluated on a fixed local frame. -/
def connDiffVec
    (G : Realized.RealizedMetricFamily (I := I) (M := M) Real)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (base var : Real) (x : M) (i j : Idx) : TangentSpace I x :=
  (G.connection var (frame j) x) (frame i x) -
    (G.connection base (frame j) x) (frame i x)

/-- Lowered connection difference with an explicitly chosen metric time. -/
def connDiffLow
    (G : Realized.RealizedMetricFamily (I := I) (M := M) Real)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (metricTime base var : Real) (x : M) (i j l : Idx) : Real :=
  (G.metric metricTime).inner x
    (connDiffVec (I := I) G frame base var x i j) (frame l x)

@[simp] theorem connDiffVec_self
    (G : Realized.RealizedMetricFamily (I := I) (M := M) Real)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (base : Real) (x : M) (i j : Idx) :
    connDiffVec (I := I) G frame base base x i j = 0 := by
  simp [connDiffVec]

@[simp] theorem connDiffLow_self
    (G : Realized.RealizedMetricFamily (I := I) (M := M) Real)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (metricTime base : Real) (x : M) (i j l : Idx) :
    connDiffLow (I := I) G frame metricTime base base x i j l = 0 := by
  simp [connDiffLow]

/-- Fixed-base covariant derivative of the metric components of `g_var`.

The connection is frozen at `base`, while the metric is evaluated at `var`. -/
def metricCovAtBase
    (G : Realized.RealizedMetricFamily (I := I) (M := M) Real)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (base var : Real) (x : M) (d a b : Idx) : Real :=
  extDerivFun (I := I)
      (fun y : M => (G.metric var).inner y (frame a y) (frame b y))
      x (frame d x) -
    (G.metric var).inner x
      ((G.connection base (frame a) x) (frame d x)) (frame b x) -
    (G.metric var).inner x (frame a x)
      ((G.connection base (frame b) x) (frame d x))

/-- The lowered metric-variation RHS
`1/2 (nabla_i v_jl + nabla_j v_il - nabla_l v_ij)`. -/
def metricVarLowerRHS
    (metricCovDerivDt : M -> Idx -> Idx -> Idx -> Real)
    (x : M) (i j l : Idx) : Real :=
  (1 / 2 : Real) *
    (metricCovDerivDt x i j l + metricCovDerivDt x j i l -
      metricCovDerivDt x l i j)

/-- The raised Christoffel metric-variation RHS
`1/2 g^{kl} (nabla_i v_jl + nabla_j v_il - nabla_l v_ij)`. -/
def metricVarGammaRHS
    (gInv : Curvature.InverseMetricComponents M Idx)
    (metricCovDerivDt : M -> Idx -> Idx -> Idx -> Real)
    (x : M) (i j k : Idx) : Real :=
  ∑ l : Idx, gInv x k l * metricVarLowerRHS metricCovDerivDt x i j l

/-- Local derivative package for the fixed-base covariant derivative of the
metric components. -/
def metricCovVarOn
    (G : Realized.RealizedMetricFamily (I := I) (M := M) Real)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (base : Real) (u : Set M)
    (metricCovDerivDt : M -> Idx -> Idx -> Idx -> Real) : Prop :=
  ∀ x : M, x ∈ u -> ∀ d a b : Idx,
    HasDerivAt
      (fun s : Real => metricCovAtBase (I := I) G frame base s x d a b)
      (metricCovDerivDt x d a b)
      base

/-- Local derivative package for raw metric components `g_s(e_a,e_b)`. -/
def metricVarOn
    (G : Realized.RealizedMetricFamily (I := I) (M := M) Real)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (base : Real) (u : Set M)
    (metricDot : M -> Idx -> Idx -> Real) : Prop :=
  ∀ x : M, x ∈ u -> ∀ a b : Idx,
    HasDerivAt
      (fun s : Real => (G.metric s).inner x (frame a x) (frame b x))
      (metricDot x a b)
      base

private theorem localFrame_mdiffAt
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (hu : IsOpen u) {x : M} (hx : x ∈ u) (i : Idx) :
    MDiffAt (T% (frame i)) x :=
  (hframe.contMDiffAt hu hx i).mdifferentiableAt one_ne_zero

private theorem connDiffVec_symm
    (G : Realized.RealizedMetricFamily (I := I) (M := M) Real)
    (hLC : ∀ s : Real,
      IsLeviCivita (I := I) (G.connection s) (G.metric s))
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (hu : IsOpen u) {x : M} (hx : x ∈ u)
    (base var : Real) (i j : Idx) :
    connDiffVec (I := I) G frame base var x i j =
      connDiffVec (I := I) G frame base var x j i := by
  have hfi : MDiffAt (T% (frame i)) x :=
    localFrame_mdiffAt (I := I) frame hframe hu hx i
  have hfj : MDiffAt (T% (frame j)) x :=
    localFrame_mdiffAt (I := I) frame hframe hu hx j
  have hvar_torsion :=
    RicciFlower.LeviCivita.torsion_free_apply
      (I := I) (hLC var).2 (hX := hfi) (hY := hfj)
  have hbase_torsion :=
    RicciFlower.LeviCivita.torsion_free_apply
      (I := I) (hLC base).2 (hX := hfi) (hY := hfj)
  have hdiff :
      (G.connection var (frame j) x) (frame i x) -
          (G.connection var (frame i) x) (frame j x) =
        (G.connection base (frame j) x) (frame i x) -
          (G.connection base (frame i) x) (frame j x) := by
    exact hvar_torsion.trans hbase_torsion.symm
  unfold connDiffVec
  apply sub_eq_zero.mp
  calc
    ((G.connection var (frame j) x) (frame i x) -
          (G.connection base (frame j) x) (frame i x)) -
        ((G.connection var (frame i) x) (frame j x) -
          (G.connection base (frame i) x) (frame j x))
        =
      ((G.connection var (frame j) x) (frame i x) -
          (G.connection var (frame i) x) (frame j x)) -
        ((G.connection base (frame j) x) (frame i x) -
          (G.connection base (frame i) x) (frame j x)) := by
        abel
    _ = 0 := by
        rw [hdiff, sub_self]

private theorem connDiffLow_symm
    (G : Realized.RealizedMetricFamily (I := I) (M := M) Real)
    (hLC : ∀ s : Real,
      IsLeviCivita (I := I) (G.connection s) (G.metric s))
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (hu : IsOpen u) {x : M} (hx : x ∈ u)
    (metricTime base var : Real) (i j l : Idx) :
    connDiffLow (I := I) G frame metricTime base var x i j l =
      connDiffLow (I := I) G frame metricTime base var x j i l := by
  unfold connDiffLow
  rw [connDiffVec_symm (I := I) G hLC frame hframe hu hx base var i j]

/-- Metric compatibility rewrites `(nabla^base_d g_var)_{ab}` as the two
connection-difference terms produced by changing the Levi-Civita connection
from `base` to `var`. -/
theorem metricCovAtBase_eq_connDiff
    (G : Realized.RealizedMetricFamily (I := I) (M := M) Real)
    (hLC : ∀ s : Real,
      IsLeviCivita (I := I) (G.connection s) (G.metric s))
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (hu : IsOpen u) {x : M} (hx : x ∈ u)
    (base var : Real) (d a b : Idx) :
    metricCovAtBase (I := I) G frame base var x d a b =
      connDiffLow (I := I) G frame var base var x d a b +
        (G.metric var).inner x (frame a x)
          (connDiffVec (I := I) G frame base var x d b) := by
  have hfd : MDiffAt (T% (frame d)) x :=
    localFrame_mdiffAt (I := I) frame hframe hu hx d
  have hfa : MDiffAt (T% (frame a)) x :=
    localFrame_mdiffAt (I := I) frame hframe hu hx a
  have hfb : MDiffAt (T% (frame b)) x :=
    localFrame_mdiffAt (I := I) frame hframe hu hx b
  have hmc :=
    RicciFlower.Connection.metric_compatible_apply
      (I := I) (hLC var).1 (frame d) (frame a) (frame b) hfd hfa hfb
  unfold metricCovAtBase connDiffLow connDiffVec
  have hmc' :
      extDerivFun (I := I)
          (fun y : M => (G.metric var).inner y (frame a y) (frame b y))
          x (frame d x) =
        (G.metric var).inner x
            ((G.connection var (frame a) x) (frame d x)) (frame b x) +
          (G.metric var).inner x (frame a x)
            ((G.connection var (frame b) x) (frame d x)) := by
    simpa [extDerivFun] using hmc
  rw [hmc']
  simp
  ring

/-- Finite-difference Koszul formula for two Levi-Civita connections in the
same fixed local frame. -/
theorem finiteDiffKoszul
    (G : Realized.RealizedMetricFamily (I := I) (M := M) Real)
    (hLC : ∀ s : Real,
      IsLeviCivita (I := I) (G.connection s) (G.metric s))
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (hu : IsOpen u) {x : M} (hx : x ∈ u)
    (base var : Real) (i j l : Idx) :
    2 * connDiffLow (I := I) G frame var base var x i j l =
      metricCovAtBase (I := I) G frame base var x i j l +
        metricCovAtBase (I := I) G frame base var x j i l -
          metricCovAtBase (I := I) G frame base var x l i j := by
  rw [metricCovAtBase_eq_connDiff
    (I := I) G hLC frame hframe hu hx base var i j l]
  rw [metricCovAtBase_eq_connDiff
    (I := I) G hLC frame hframe hu hx base var j i l]
  rw [metricCovAtBase_eq_connDiff
    (I := I) G hLC frame hframe hu hx base var l i j]
  have hji := connDiffLow_symm
    (I := I) G hLC frame hframe hu hx var base var j i l
  have hli := connDiffLow_symm
    (I := I) G hLC frame hframe hu hx var base var l i j
  have hlj := connDiffVec_symm
    (I := I) G hLC frame hframe hu hx base var l j
  have hsym1 :
      (G.metric var).inner x (frame j x)
          (connDiffVec (I := I) G frame base var x i l) =
        connDiffLow (I := I) G frame var base var x i l j := by
    unfold connDiffLow
    exact (G.metric var).symm x (frame j x)
      (connDiffVec (I := I) G frame base var x i l)
  rw [hji, hli, hlj, hsym1]
  ring

/-- Variable-metric lowered connection difference expressed by Christoffel
component differences in the fixed local frame. -/
theorem connDiffLow_eq_sum_gammaSub [DecidableEq Idx]
    (G : Realized.RealizedMetricFamily (I := I) (M := M) Real)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    {x : M} (hx : x ∈ u)
    (metricTime base var : Real) (i j l : Idx) :
    connDiffLow (I := I) G frame metricTime base var x i j l =
      ∑ k : Idx,
        (Coordinates.christoffelSymbolInFrame
            (G.connection var) frame hframe x i j k -
          Coordinates.christoffelSymbolInFrame
            (G.connection base) frame hframe x i j k) *
          (G.metric metricTime).inner x (frame k x) (frame l x) := by
  let Vvar : TangentSpace I x :=
    (G.connection var (frame j) x) (frame i x)
  let Vbase : TangentSpace I x :=
    (G.connection base (frame j) x) (frame i x)
  have hvar :
      Vvar =
        ∑ k : Idx,
          Coordinates.christoffelSymbolInFrame
              (G.connection var) frame hframe x i j k • frame k x := by
    simpa [Vvar, Coordinates.christoffelSymbolInFrame] using
      hframe.coeff_sum_eq
        (fun y : M => (G.connection var (frame j) y) (frame i y)) hx
  have hbase :
      Vbase =
        ∑ k : Idx,
          Coordinates.christoffelSymbolInFrame
              (G.connection base) frame hframe x i j k • frame k x := by
    simpa [Vbase, Coordinates.christoffelSymbolInFrame] using
      hframe.coeff_sum_eq
        (fun y : M => (G.connection base (frame j) y) (frame i y)) hx
  have hdiff :
      Vvar - Vbase =
        ∑ k : Idx,
          (Coordinates.christoffelSymbolInFrame
              (G.connection var) frame hframe x i j k -
            Coordinates.christoffelSymbolInFrame
              (G.connection base) frame hframe x i j k) • frame k x := by
    calc
      Vvar - Vbase =
          (∑ k : Idx,
            Coordinates.christoffelSymbolInFrame
                (G.connection var) frame hframe x i j k • frame k x) -
            (∑ k : Idx,
              Coordinates.christoffelSymbolInFrame
                  (G.connection base) frame hframe x i j k • frame k x) := by
            rw [hvar, hbase]
      _ = ∑ k : Idx,
            (Coordinates.christoffelSymbolInFrame
                (G.connection var) frame hframe x i j k • frame k x -
              Coordinates.christoffelSymbolInFrame
                (G.connection base) frame hframe x i j k • frame k x) := by
            rw [Finset.sum_sub_distrib]
      _ = ∑ k : Idx,
            (Coordinates.christoffelSymbolInFrame
                (G.connection var) frame hframe x i j k -
              Coordinates.christoffelSymbolInFrame
                (G.connection base) frame hframe x i j k) • frame k x := by
            refine Finset.sum_congr rfl fun k _ => ?_
            rw [sub_smul]
  calc
    connDiffLow (I := I) G frame metricTime base var x i j l =
        (G.metric metricTime).inner x (Vvar - Vbase) (frame l x) := by
          rfl
    _ = (G.metric metricTime).inner x
        (∑ k : Idx,
          (Coordinates.christoffelSymbolInFrame
              (G.connection var) frame hframe x i j k -
            Coordinates.christoffelSymbolInFrame
              (G.connection base) frame hframe x i j k) • frame k x)
        (frame l x) := by
          rw [hdiff]
    _ = (G.metric metricTime).inner x (frame l x)
        (∑ k : Idx,
          (Coordinates.christoffelSymbolInFrame
              (G.connection var) frame hframe x i j k -
            Coordinates.christoffelSymbolInFrame
              (G.connection base) frame hframe x i j k) • frame k x) := by
          rw [(G.metric metricTime).symm x]
    _ = ∑ k : Idx,
        (Coordinates.christoffelSymbolInFrame
            (G.connection var) frame hframe x i j k -
          Coordinates.christoffelSymbolInFrame
            (G.connection base) frame hframe x i j k) *
          (G.metric metricTime).inner x (frame l x) (frame k x) := by
          rw [map_sum]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [map_smul]
          simp [smul_eq_mul]
    _ = ∑ k : Idx,
        (Coordinates.christoffelSymbolInFrame
            (G.connection var) frame hframe x i j k -
          Coordinates.christoffelSymbolInFrame
            (G.connection base) frame hframe x i j k) *
          (G.metric metricTime).inner x (frame k x) (frame l x) := by
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [(G.metric metricTime).symm x (frame l x) (frame k x)]

/-- Local derivative package for Christoffel components in a fixed frame. -/
def gammaDerivOn
    (G : Realized.RealizedMetricFamily (I := I) (M := M) Real)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (base : Real) (u : Set M)
    (gammaDot : M -> Idx -> Idx -> Idx -> Real) : Prop :=
  ∀ x : M, x ∈ u -> ∀ i j k : Idx,
    HasDerivAt
      (fun s : Real =>
        Coordinates.christoffelSymbolInFrame
          (G.connection s) frame hframe x i j k)
      (gammaDot x k i j)
      base

/-- Product-rule bridge: the variable-metric lowered connection difference has
derivative obtained by lowering `gammaDot` with the base metric. -/
theorem varLowDeriv [DecidableEq Idx]
    (G : Realized.RealizedMetricFamily (I := I) (M := M) Real)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (base : Real)
    (metricDot : M -> Idx -> Idx -> Real)
    (gammaDot : M -> Idx -> Idx -> Idx -> Real)
    (hmetricVar : metricVarOn (I := I) G frame base u metricDot)
    (hgamma : gammaDerivOn (I := I) G frame hframe base u gammaDot)
    {x : M} (hx : x ∈ u) (i j l : Idx) :
    HasDerivAt
      (fun s : Real => connDiffLow (I := I) G frame s base s x i j l)
      (∑ k : Idx,
        gammaDot x k i j * (G.metric base).inner x (frame k x) (frame l x))
      base := by
  let gammaSub : Idx -> Real -> Real :=
    fun k s =>
      Coordinates.christoffelSymbolInFrame
          (G.connection s) frame hframe x i j k -
        Coordinates.christoffelSymbolInFrame
          (G.connection base) frame hframe x i j k
  let metricComp : Idx -> Real -> Real :=
    fun k s => (G.metric s).inner x (frame k x) (frame l x)
  have hsum :
      HasDerivAt
        (fun s : Real => ∑ k : Idx, gammaSub k s * metricComp k s)
        (∑ k : Idx,
          gammaDot x k i j * (G.metric base).inner x (frame k x) (frame l x))
        base := by
    simpa [gammaSub, metricComp] using
      (HasDerivAt.fun_sum
        (u := (Finset.univ : Finset Idx))
        (A := fun k s => gammaSub k s * metricComp k s)
        (A' := fun k =>
          gammaDot x k i j * (G.metric base).inner x (frame k x) (frame l x))
        (x := base)
        (fun k _hk => by
          have hγ :
              HasDerivAt (fun s : Real => gammaSub k s)
                (gammaDot x k i j) base := by
            simpa [gammaSub] using
              (hgamma x hx i j k).sub_const
                (Coordinates.christoffelSymbolInFrame
                  (G.connection base) frame hframe x i j k)
          have hm :
              HasDerivAt (fun s : Real => metricComp k s)
                (metricDot x k l) base := by
            simpa [metricComp] using hmetricVar x hx k l
          have hmul := hγ.mul hm
          simpa [gammaSub, metricComp] using hmul))
  have hEq :
      (fun s : Real => connDiffLow (I := I) G frame s base s x i j l) =ᶠ[nhds base]
        (fun s : Real => ∑ k : Idx, gammaSub k s * metricComp k s) := by
    exact Filter.Eventually.of_forall fun s => by
      simpa [gammaSub, metricComp] using
        connDiffLow_eq_sum_gammaSub (I := I) G frame hframe hx s base s i j l
  exact hsum.congr_of_eventuallyEq hEq

/-- Local arbitrary metric-variation Christoffel formula in a fixed frame. -/
def gammaVarEqOn
    (gInv : Curvature.InverseMetricComponents M Idx)
    (metricCovDerivDt gammaDot : M -> Idx -> Idx -> Idx -> Real)
    (u : Set M) : Prop :=
  ∀ x : M, x ∈ u -> ∀ i j k : Idx,
    gammaDot x k i j =
      metricVarGammaRHS gInv metricCovDerivDt x i j k

/-- A static frame coefficient is obtained by raising the frozen metric
pairings with inverse metric components. -/
theorem coeff_invMetric [DecidableEq Idx]
    (g : SmoothRiemannianMetric I M)
    (gInv : Curvature.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (hinv :
      Curvature.InverseMetricComponentsInFrame
        (I := I) g gInv frame)
    {x : M} (hx : x ∈ u)
    (k : Idx) (V : TangentSpace I x) :
    hframe.coeff k x V =
      ∑ l : Idx, gInv x k l * g.inner x (frame l x) V := by
  let basis := hframe.toBasisAt hx
  have hcoord :
      basis.coord k V =
        ∑ l : Idx, gInv x k l * g.inner x (basis l) V := by
    symm
    calc
      (∑ l : Idx, gInv x k l * g.inner x (basis l) V)
          = ∑ l : Idx, gInv x k l *
              g.inner x (basis l) (∑ j : Idx, basis.coord j V • basis j) := by
            rw [show (∑ j : Idx, basis.coord j V • basis j) = V from basis.sum_repr V]
      _ = ∑ l : Idx, ∑ j : Idx,
            gInv x k l * (basis.coord j V * g.inner x (basis l) (basis j)) := by
            refine Finset.sum_congr rfl fun l _ => ?_
            rw [map_sum]
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [map_smul]
            simp [smul_eq_mul]
      _ = ∑ j : Idx, basis.coord j V *
            (∑ l : Idx, gInv x k l * g.inner x (basis l) (basis j)) := by
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun l _ => ?_
            ring
      _ = ∑ j : Idx, basis.coord j V * (if k = j then 1 else 0) := by
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [show
              (∑ l : Idx, gInv x k l * g.inner x (basis l) (basis j)) =
                (if k = j then 1 else 0) by
                  simpa [basis, IsLocalFrameOn.toBasisAt_coe] using (hinv x k j).1]
      _ = basis.coord k V := by
            simp
  calc
    hframe.coeff k x V = basis.coord k V := by
      simp [basis, IsLocalFrameOn.coeff, hx]
    _ = ∑ l : Idx, gInv x k l * g.inner x (frame l x) V := by
      simpa [basis, IsLocalFrameOn.toBasisAt_coe] using hcoord

/-- Derivative package for the frozen-metric lowered connection-variation
pairing.  The metric in the pairing is fixed at `base`; only the connection
varies. -/
def lowerPairDerivOn
    (G : Realized.RealizedMetricFamily (I := I) (M := M) Real)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (base : Real) (u : Set M)
    (lowerDot : M -> Idx -> Idx -> Idx -> Real) : Prop :=
  ∀ x : M, x ∈ u -> ∀ i j l : Idx,
    HasDerivAt
      (fun s : Real =>
        (G.metric base).inner x (frame l x)
          ((G.connection s (frame j) x) (frame i x)))
      (lowerDot x i j l)
      base

/-- Raise a supplied lowered connection-variation pairing. -/
def gammaFromLower
    (gInv : Curvature.InverseMetricComponents M Idx)
    (lowerDot : M -> Idx -> Idx -> Idx -> Real)
    (x : M) (i j k : Idx) : Real :=
  ∑ l : Idx, gInv x k l * lowerDot x i j l

/-- A lowered pairing derivative gives the derivative of the Christoffel
components after raising with the frozen inverse metric. -/
theorem gammaDerivOfLower [DecidableEq Idx]
    (G : Realized.RealizedMetricFamily (I := I) (M := M) Real)
    (gInv : Curvature.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (base : Real)
    (lowerDot : M -> Idx -> Idx -> Idx -> Real)
    (hinv :
      Curvature.InverseMetricComponentsInFrame
        (I := I) (G.metric base) gInv frame)
    (hlower : lowerPairDerivOn (I := I) G frame base u lowerDot) :
    gammaDerivOn (I := I) G frame hframe base u
      (fun x k i j => gammaFromLower gInv lowerDot x i j k) := by
  intro x hx i j k
  let pair : Idx -> Real -> Real :=
    fun l s =>
      (G.metric base).inner x (frame l x)
        ((G.connection s (frame j) x) (frame i x))
  have hsum :
      HasDerivAt
        (fun s : Real => ∑ l : Idx, gInv x k l * pair l s)
        (∑ l : Idx, gInv x k l * lowerDot x i j l)
        base := by
    simpa [pair] using
      (HasDerivAt.fun_sum
        (u := (Finset.univ : Finset Idx))
        (A := fun l s => gInv x k l * pair l s)
        (A' := fun l => gInv x k l * lowerDot x i j l)
        (x := base)
        (fun l _hl =>
          HasDerivAt.const_mul
            (gInv x k l) (hlower x hx i j l)))
  have hEq :
      (fun s : Real =>
        Coordinates.christoffelSymbolInFrame
          (G.connection s) frame hframe x i j k) =ᶠ[nhds base]
        (fun s : Real => ∑ l : Idx, gInv x k l * pair l s) := by
    exact Filter.Eventually.of_forall fun s => by
      simpa [Coordinates.christoffelSymbolInFrame, pair] using
        coeff_invMetric (I := I) (M := M)
          (G.metric base) gInv frame hframe hinv hx k
          ((G.connection s (frame j) x) (frame i x))
  simpa [gammaFromLower, pair] using hsum.congr_of_eventuallyEq hEq

/-- Uniqueness of one-dimensional derivatives turns a produced Christoffel
derivative into the component formula for a supplied `gammaDot`. -/
theorem gammaEqOfDeriv
    (G : Realized.RealizedMetricFamily (I := I) (M := M) Real)
    (gInv : Curvature.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (base : Real)
    (metricCovDerivDt gammaDot : M -> Idx -> Idx -> Idx -> Real)
    (hformula :
      gammaDerivOn (I := I) G frame hframe base u
        (fun x k i j =>
          gammaFromLower gInv (metricVarLowerRHS metricCovDerivDt) x i j k))
    (hgamma : gammaDerivOn (I := I) G frame hframe base u gammaDot) :
    gammaVarEqOn gInv metricCovDerivDt gammaDot u := by
  intro x hx i j k
  have huniq := (hformula x hx i j k).unique (hgamma x hx i j k)
  simpa [metricVarGammaRHS, gammaFromLower] using huniq.symm

/-- Arbitrary Levi-Civita metric-variation producer for Christoffel symbols.

This is the non-Ricci-flow version of the calculation used in the connection
evolution file.  The proof should be extracted from the finite-difference
Koszul route there, replacing `SolutionOn` and `partial_t g = -2 Ric` by the
plain hypotheses below. -/
theorem lcGammaVar [DecidableEq Idx]
    (G : Realized.RealizedMetricFamily (I := I) (M := M) Real)
    (hLC : ∀ s : Real,
      IsLeviCivita (I := I) (G.connection s) (G.metric s))
    (gInv : Curvature.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (_hu : IsOpen u)
    (base : Real)
    (metricDot : M -> Idx -> Idx -> Real)
    (metricCovDerivDt gammaDot : M -> Idx -> Idx -> Idx -> Real)
    (_hinv :
      Curvature.InverseMetricComponentsInFrame
        (I := I) (G.metric base) gInv frame)
    (hmetricVar :
      metricVarOn (I := I) G frame base u metricDot)
    (_hmetric :
      metricCovVarOn (I := I) G frame base u metricCovDerivDt)
    (_hgamma :
      gammaDerivOn (I := I) G frame hframe base u gammaDot) :
    gammaVarEqOn gInv metricCovDerivDt gammaDot u := by
  intro x hx i j k
  have hlow :
      ∀ l : Idx,
        (∑ a : Idx,
          gammaDot x a i j * (G.metric base).inner x (frame a x) (frame l x)) =
          metricVarLowerRHS metricCovDerivDt x i j l := by
    intro l
    have hL :
        HasDerivAt
          (fun s : Real =>
            2 * connDiffLow (I := I) G frame s base s x i j l)
          (2 * ∑ a : Idx,
            gammaDot x a i j * (G.metric base).inner x (frame a x) (frame l x))
          base := by
      exact HasDerivAt.const_mul (2 : Real)
        (varLowDeriv (I := I) G frame hframe base metricDot gammaDot
          hmetricVar _hgamma hx i j l)
    have hR :
        HasDerivAt
          (fun s : Real =>
            metricCovAtBase (I := I) G frame base s x i j l +
              metricCovAtBase (I := I) G frame base s x j i l -
                metricCovAtBase (I := I) G frame base s x l i j)
          (metricCovDerivDt x i j l +
            metricCovDerivDt x j i l - metricCovDerivDt x l i j)
          base := by
      exact ((_hmetric x hx i j l).add (_hmetric x hx j i l)).sub
        (_hmetric x hx l i j)
    have hEq :
        (fun s : Real =>
            metricCovAtBase (I := I) G frame base s x i j l +
              metricCovAtBase (I := I) G frame base s x j i l -
                metricCovAtBase (I := I) G frame base s x l i j) =ᶠ[nhds base]
          (fun s : Real =>
            2 * connDiffLow (I := I) G frame s base s x i j l) := by
      exact Filter.Eventually.of_forall fun s => by
        exact (finiteDiffKoszul (I := I) G hLC frame hframe _hu hx base s i j l).symm
    have hL_as_R :
        HasDerivAt
          (fun s : Real =>
            metricCovAtBase (I := I) G frame base s x i j l +
              metricCovAtBase (I := I) G frame base s x j i l -
                metricCovAtBase (I := I) G frame base s x l i j)
          (2 * ∑ a : Idx,
            gammaDot x a i j * (G.metric base).inner x (frame a x) (frame l x))
          base := hL.congr_of_eventuallyEq hEq
    have hderiv :
        2 * (∑ a : Idx,
          gammaDot x a i j * (G.metric base).inner x (frame a x) (frame l x)) =
          metricCovDerivDt x i j l +
            metricCovDerivDt x j i l - metricCovDerivDt x l i j :=
      hL_as_R.unique hR
    unfold metricVarLowerRHS
    linarith
  let V : TangentSpace I x :=
    ∑ a : Idx, gammaDot x a i j • frame a x
  have hcoeff :
      hframe.coeff k x V = gammaDot x k i j := by
    let basis := hframe.toBasisAt hx
    have hbasis :
        ∀ a : Idx, basis.repr (frame a x) k = if a = k then 1 else 0 := by
      intro a
      have hframe_eq : frame a x = basis a := by
        simp [basis]
      rw [hframe_eq]
      by_cases h : a = k
      · subst k
        simp
      · simp [h]
    calc
      hframe.coeff k x V = basis.repr V k := by
        simp [basis, IsLocalFrameOn.coeff, hx]
      _ = ∑ a : Idx, gammaDot x a i j * basis.repr (frame a x) k := by
        simp [V, map_sum, map_smul, smul_eq_mul]
      _ = ∑ a : Idx, gammaDot x a i j * (if a = k then 1 else 0) := by
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [hbasis a]
      _ = gammaDot x k i j := by
        simp
  have hinner :
      ∀ l : Idx,
        (G.metric base).inner x (frame l x) V =
          metricVarLowerRHS metricCovDerivDt x i j l := by
    intro l
    calc
      (G.metric base).inner x (frame l x) V =
          ∑ a : Idx,
            gammaDot x a i j * (G.metric base).inner x (frame l x) (frame a x) := by
            simp [V, map_sum, smul_eq_mul]
      _ = ∑ a : Idx,
            gammaDot x a i j * (G.metric base).inner x (frame a x) (frame l x) := by
            refine Finset.sum_congr rfl fun a _ => ?_
            rw [(G.metric base).symm x (frame l x) (frame a x)]
      _ = metricVarLowerRHS metricCovDerivDt x i j l := hlow l
  calc
    gammaDot x k i j = hframe.coeff k x V := hcoeff.symm
    _ = ∑ l : Idx, gInv x k l * (G.metric base).inner x (frame l x) V := by
      exact coeff_invMetric (I := I) (M := M)
        (G.metric base) gInv frame hframe _hinv hx k V
    _ = ∑ l : Idx, gInv x k l * metricVarLowerRHS metricCovDerivDt x i j l := by
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [hinner l]
    _ = metricVarGammaRHS gInv metricCovDerivDt x i j k := by
      rfl

end LeviCivita
end RicciFlower
