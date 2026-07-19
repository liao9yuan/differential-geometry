# P4 producer architecture ruling

## Scope and baseline

Treat commit `b63efe882031def127790cdac3b6adef72ff6e34` as the source
baseline and the focused-green post-baseline theorem `open_upgrade_of_raw` as
the consumer endpoint.  This document governs only the remaining producers of
that theorem.  It does not change the public statement of Theorem 3.9 or add a
new hypothesis to `compactnessSol`.

The producer architecture has two independent lanes that meet only near
`ConvFieldOpenAssembly`:

1. the analytic lane: arbitrary-dimensional complete-noncompact Shi estimates,
   then a constants-first source-flow covariant/Lipschitz producer;
2. the provenance lane: a concrete Step-D sidecar retaining canonical-reference
   facts intentionally forgotten by `MetricCompactnessConclusion`.

Do not derive the final data from an arbitrary bare `mc`.  Do not repair or
parameterize the old compact `Fin 3` StarSum chain.  Do not retain the
whole-source bump-collar covariant estimate.

## Analytic lane

### Arbitrary-dimensional curvature tower

The canonical owner is a new
`Evolution/IteratedRmTowerSolution.lean`.  It must complete the existing
variable-rank `IteratedRmTowerOn` route rather than modify the `Fin 3` residual
files.  The missing mathematical content is the solution-specific construction
of `IteratedRmTowerOn`: the all-order commuted-curvature identity split into
genuine `nabla^j Rm * nabla^(k-j) Rm` factors.  The existing generic consumer
already supplies the orthonormal contraction estimate and the constant
`2 * card Idx ^ (6 + k)`.

The first public capstone is:

```lean
theorem towerHeatSol_any
    {alpha t0 omega : Real} {halphaomega : alpha < omega}
    {S : SolutionOn (I := I) (M := M)
      (RealTimeInterval.closedOpen alpha omega halphaomega)}
    (hS : IsSolutionOn (I := I) S)
    (halphat0 : alpha < t0) (ht0omega : t0 < omega)
    (k : Nat) :
    let D' := RealTimeInterval.closedOpen t0 omega ht0omega
    let S' := S.timeRestrict D'
    TowerHeatBoundOn (D := D')
      (nablaKRm04NormSqIntrinsic (I := I) S')
      (nablaKNormLap (I := I) S')
      (2 * (Module.finrank Real E : Real) ^ (6 + k)) k
```

It must not require `CompactSpace` or `Module.finrank Real E = 3`.

### Complete-noncompact Bernstein theorem

The owner is a new `Evolution/BernsteinComplete.lean`.  The low-level public
consumer is `BernsteinTower.estimate_complete`.  It uses one fixed complete
anchor metric, slabwise metric equivalence and Ricci lower control, spatial
cutoffs or an exhaustion, and the existing truncated-tower induction.  It does
not consume injectivity radius, noncollapse, connectedness, or completeness at
every time.

### Single-flow and sequence Shi theorems

The HCG-facing owner is a new `HCGCompactness/MovingShiOpen.lean`.

```lean
theorem movingShi_complete
    {D : RealTimeInterval}
    (F : PointedFlowData (I := I) D)
    {alpha beta psi C : Real}
    (halphabeta : alpha < beta)
    (hbetapsi : beta <= psi)
    (hslab : Set.Icc alpha psi <= D.carrier)
    (hreg : Set.Ioc alpha psi <= D.regular)
    (hcomplete : MetricComplete (I := I) (F.atTime (I := I) alpha))
    (hC : 0 <= C)
    (hcurv : forall t in Set.Icc alpha psi, forall x : F.M,
      F.rmNormSq (I := I) t x <= C)
    (N : Nat) :
    exists KShi : Real, 0 <= KShi /\
      MovingShiBoundOn (I := I) Set.univ beta psi
        (fun _ t => F.S.family.metric t) N KShi
```

Only a positive left buffer is required.  There is no future-time buffer.
Completeness is assumed only for the anchor slice `alpha`.

```lean
theorem CurvBoundInput.movingShi_open
    {a b : Real} (h0 : (0 : Real) in Set.Ioo a b)
    (X : PointedFlowSeq (I := I))
    (hD : X.D = RealTimeInterval.openInterval a b 0 h0)
    (hcomplete : CompleteInput (I := I) X)
    (hcurv : CurvBoundInput (I := I) X) :
    forall n N : Nat, exists KShi : Real, 0 <= KShi /\
      forall k : Nat,
        MovingShiBoundOn (I := I) Set.univ
          (RealTimeInterval.openWindowLeft a 0 n)
          (RealTimeInterval.openWindowRight b 0 n)
          (fun _ t => (X.term k).S.family.metric t) N KShi
```

The wrapper chooses a strictly larger left window, obtains one curvature
constant uniform in the member index from `CurvBoundInput`, and anchors at the
larger window's left endpoint.  The Shi constant must then be selected by a
constants-first core before the member index.  Merely applying the displayed
single-flow existential separately to each member would choose constants in
the wrong order and does not prove `movingShi_open`.

## Grow-local covariant tail

Change the current `hcovTail` API from all of `Phi.source k` to `bf.grow k`
now.  Keep the public name `covTail_of_bounds`, but replace its statement and
proof with the grow-local form.  Its proof follows `lipTail_of_src`: use
`bf.chi_one` to obtain an open neighborhood on which `gSeqExt = srcMetric`,
then apply restriction invariance of the covariant norm.

Delete from this route:

- `hchi`;
- the support/collar split;
- the uniform bump-family Leibniz estimate;
- target-side reference/equivalence data used only on the collar.

The finite head terms may still use derivatives of each fixed bump and take a
finite maximum after fixing the compact set.

## Constants-first source producer

The owner is a new `HCGCompactness/SourceCovLip.lean`.  It must be source-native:
no `BumpFamily`, `gSeqExt`, target domains, or target-side reference metric.

```lean
structure SrcCovLipData
    (Phi : PointedCGHMaps (I := I) X P subseq)
    (R : SmoothRiemannianMetric I P.M)
    (hsrc : SrcSigma Phi) (htgt : TgtSigma Phi)
    (beta psi : Real) : Prop where
  cov :
    forall q : Nat, exists Cq : Real, 0 <= Cq /\
      forall k t, t in Set.Icc beta psi ->
        forall y : SourceDomain (I := I) Phi k,
          metricCovDerivNorm (I := I) q
            (srcMetric (I := I) Phi hsrc htgt k t)
            (refRes (I := I) Phi R hsrc k) y <= Cq
  lip :
    forall p : Nat, exists Lp : Real, 0 <= Lp /\
      forall k s t, s in Set.Icc beta psi -> t in Set.Icc beta psi ->
        forall q, q <= p -> forall y : SourceDomain (I := I) Phi k,
          metricDerivNorm (I := I) q
            (srcMetric (I := I) Phi hsrc htgt k s)
            (srcMetric (I := I) Phi hsrc htgt k t)
            (refRes (I := I) Phi R hsrc k) y <= Lp * |s - t|
```

The producer `srcCovLip_of_soln` consumes one constants-first metric
equivalence, moving-Shi tower, and time-zero covariant envelope.  All output
constants occur before `k`.  It must not invoke compact boundedness separately
for each sequence member.

## Provenance lane

Keep `MetricCompactnessConclusion` unchanged.  Its free `referenceMetric` is a
valid abstraction, so no canonical-reference fact may be asserted for an
arbitrary value of that type.

The concrete owner is `C4/StepDAssembly.lean`:

```lean
structure StepDCanonData
    (X : PointedRiemannianSeq (I := I)) where
  mc : MetricCompactnessConclusion (I := I) X
  ref_eq :
    forall k,
      (mc.convergence.metrics.domain k).referenceMetric =
        (mc.convergence.metrics.domain k).limitMetric
  rel :
    exists Crel : Real, 1 <= Crel /\
      forall k,
        MetricUniformEquivalentOn (I := I) Set.univ
          (mc.convergence.metrics.domain k).limitMetric
          (mc.convergence.metrics.domain k).pullbackMetric Crel
  init_cov :
    forall q, exists Cq : Real, 0 <= Cq /\
      forall k x,
        metricCovDerivNorm (I := I) q
          (mc.convergence.metrics.domain k).pullbackMetric
          (mc.convergence.metrics.domain k).limitMetric x <= Cq
```

The actual source statement includes the stored per-domain instances omitted
above for readability.

Refactor the concrete constructor to:

```lean
noncomputable def compactness_canon
    (P : forall k, ProperMetricOn (I := I) (X.obj k))
    (B : StepB1RawInput (X := X) P) :
    StepDCanonData (I := I) X
```

and retain the existing public entry point by projection:

```lean
noncomputable def compactness_of_b1 ... :
    MetricCompactnessConclusion (I := I) X :=
  (compactness_canon (I := I) P B).mc
```

Add `StepDCanonData.ofSeqSubseq`, then add
`MetricCompactnessInputs.metricCanon` in `C4/MetricCompactnessEndpoint.lean`.
Keep the existing conditional Theorem 3.9 endpoint exactly by projecting `.mc`.

Short adapters `canon_cp`, `canon_rel`, and `canon_init` expose the concrete
facts to P4.  `canon_cp` rewrites the stored convergence by `ref_eq` into the
exact canonical `hcp` shape.  There is no corresponding theorem for arbitrary
`MetricCompactnessConclusion`.

## Ordered implementation

The analytic and provenance lanes run in parallel:

1. build the arbitrary-dimensional solution tower;
2. prove `BernsteinTower.estimate_complete`;
3. expose `movingShi_complete` and `CurvBoundInput.movingShi_open`;
4. build `StepDCanonData`, `compactness_canon`, and `metricCanon`;
5. prove `srcCovLip_of_soln`;
6. consume grow-local `covTail_of_bounds` and the existing Lipschitz adapters;
7. keep `canon`, `mc`, `Phi`, `bf`, `srcData`, and `raw` explicit in the
   eventual `compactnessSol` proof before calling `open_upgrade_of_raw`.

## Live implementation status (2026-07-18)

- `open_upgrade_of_raw`: theorem 100%; dedicated consumer machinery 100%.
- grow-local covariant-tail migration: 100%.  The ten-module chain is
  focused-green and exact-refreshed; `hchi` and the whole-source bump-collar
  estimate have been removed from the API and every caller.
- `towerHeatSol_any`: public assembly stated and focused-green, but theorem
  completion remains 0% because `exists_rmTowerSol` contains the one genuine
  commuted-curvature factorization `sorry`; dedicated arbitrary-dimensional
  solution-tower machinery is about 70%.
- `BernsteinTower.estimate_complete`: interface stated and focused-green;
  theorem completion remains 0% at its single complete-noncompact scalar
  maximum-principle/cutoff `sorry`; dedicated machinery is about 10%.
- `movingShi_complete` and `CurvBoundInput.movingShi_open`: the wrappers and a
  full source proof of `movingShi_of_bound` are assembled with one explicit
  constant chosen before the sequence member.  The latest source revision is
  awaiting focused verification after the framed-coordinate refresh; its
  trusted analytic foundation still depends on the explicit lower-level
  frontiers in `exists_rmTowerSol` and `BernsteinTower.estimate_complete`.
- `StepDCanonData` / `compactness_canon`: the sidecar, subsequence transport,
  and public projection are stated; the source was focused-green around one
  honest `HasCanonBounds` frontier.  Its exact refresh is paused while H6
  migrates the shared framed normal-coordinate import chain.
- `SrcCovLipData`: source-native interface stated and focused-green.
  `srcCovLip_of_soln` remains theorem-level 0% at its single constants-first
  varying-source analytic `sorry`.
- unconditional `compactnessSol`: theorem 0%.
- dedicated P4 consumer machinery remains about 97%; whole-HCG support
  machinery remains about 60%.
