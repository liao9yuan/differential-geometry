# CGT collision/propeller producer consultation

Repository:

- `https://github.com/qinz1yang/differential-geometry`
- branch: `codex/short-time-existence-align`

The live aligned worktree also contains the following uncommitted new file, so
please treat the declarations pasted below as authoritative even if they are
not yet visible on GitHub:

- `DifferentialGeometry/Geometry/Comparison/CGTInjectivity.lean`

## Goal

We need the first honest pointwise Cheeger--Gromov--Taylor producer used later
to construct the HCG `InjRadiusDecayInput`. The analytic pullback-volume half is
already focused-green:

```lean
noncomputable def intrPullVol
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (y : M) (w : TangentSpace I y),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner y w w)))
    (p : M) (R : Real) : ENNReal :=
  ∫⁻ z in Metric.ball (0 : E) R,
    ENNReal.ofReal
      (curveDensity (I := I) g
        (intrinsicGeodesic (I := I) g hEnorm p
          (normalFrame (I := I) g p z))
        (fun i t =>
          intrinsicJacobi (I := I) g hEnorm p
            (normalFrame (I := I) g p z)
            ((normalBasis (I := I) g p) i) t)
        1)
    ∂(volume : Measure E)

theorem intrPullVol_le_hyp
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (y : M) (w : TangentSpace I y),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner y w w)))
    (p : M) {q R : Real} (hq : 0 ≤ q) (hR : 0 < R)
    (hno : ∀ z, z ∈ Metric.ball (0 : E) R → z ≠ 0 →
      ∀ t, t ∈ Set.Ioo (0 : Real) 1 →
        ¬ IsConjVec (I := I) g hEnorm p
          ((t • normalFrame (I := I) g p z :
            TangentSpace I p) : E))
    (hRic : RicciBoundedBelow (I := I) g
      (-(((Module.finrank Real E - 1 : Nat) : Real) * q ^ 2))) :
    intrPullVol (I := I) g hEnorm p R ≤
      (volume : Measure E).toSphere Set.univ *
        ENNReal.ofReal
          (hypRadVol q (Module.finrank Real E - 1) R)
```

The corrected first topological target is the original CGT geodesic-loop
estimate, not a direct injectivity-radius estimate:

```lean
theorem intrLoop_ge_cgt
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (y : M) (w : TangentSpace I y),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner y w w)))
    (p : M) {K R r₀ s ell : Real}
    (hK : 0 < K) (hR : 0 < R)
    (hRpi : R ≤ Real.pi / Real.sqrt K)
    (hRm : Rm04GlobalBound (I := I) (M := M) g K)
    (hloc :
      IsLocalDiffeomorphOn (modelWithCornersSelf Real E) I
        (↑(⊤ : ℕ∞) : WithTop ℕ∞)
        (intrinsicFramedExp (I := I) g hEnorm p)
        (Metric.ball (0 : E) R))
    (hr₀ : 0 < r₀) (hs : 0 < s)
    (hfit : r₀ + 2 * s < R) (hquarter : r₀ < R / 4)
    {u : E} (hell : 0 < ell) (hlen : ‖u‖ = 2 * ell)
    (hloop : intrinsicFramedExp (I := I) g hEnorm p u = p) :
    ENNReal.ofReal (r₀ / 2) *
          riemannianVolumeMeasure (I := I) (M := M) g
            {y : M | riemannianEDist I p y < ENNReal.ofReal s} /
        (riemannianVolumeMeasure (I := I) (M := M) g
            {y : M | riemannianEDist I p y < ENNReal.ofReal s} +
          intrPullVol (I := I) g hEnorm p (r₀ + s))
      ≤ ENNReal.ofReal ell
```

This statement matches CGT Theorem 4.3. In the later specialization
`r₀ = s = r`, the coefficient is `r / 2`, the pullback radius is `2r`, and a
safe strict ambient choice is `R = 5r`.

## Live repository audit

Reusable ingredients already present:

- `IntrinsicInjectivityRadius.lean`: intrinsic framed injectivity radius and
  injectivity on a model ball;
- `intrinsicFramedExp`, `normalFrame`, intrinsic geodesic/Jacobi APIs;
- `Manifold.pathELength` and its interval/reparametrization lemmas;
- ordinary fixed-endpoint `Path.Homotopy`;
- Mathlib homotopy lifting and monodromy for an already established covering;
- `CenterOfMass.centerEnergy`, `exists_minOn_compact`,
  `centerEnergy_strict`, and `min_unique_of_mid`;
- `HessianAlongGeodesic.strictConvex_geo` and
  `GeodesicConvexity.IsGeodesicallyConvexWith`;
- the completed non-injective exponential area formula and segment-volume
  comparison chain.

Missing from the live tree:

1. a homotopy relation that retains a uniform length bound on every path
   slice;
2. a theorem lifting every path of length `< R` through
   `intrinsicFramedExp` while keeping the lift inside `Metric.ball 0 R`,
   assuming only `hloc`;
3. the CGT small pullback-ball strict-convexity/unique-center theorem from
   `hRm` and `R ≤ π / sqrt K`;
4. CGT Lemmas 4.4--4.6: cancellation, distinct loop iterates, even sheets, and
   the multiplicity estimate;
5. after the loop theorem, a local collision-to-short-loop lemma deriving the
   injectivity-radius corollary.

Ordinary `Path.Homotopic.Quotient` loses the length bound. The existing
universal-cover/deck machinery also does not itself prove that short loop
iterates are distinct. `GaussLemma.path_confined_to_normalBall` currently
depends on an injectivity-radius hypothesis and therefore cannot be used
circularly in this producer.

## Questions

Please audit the repository and give the smallest project-native Lean
decomposition that proves `intrLoop_ge_cgt`.

1. Is the proposed first auxiliary theorem actually derivable from `hloc`
   alone?

   ```lean
   theorem exists_short_expLift
       -- same fixed metric/exponential data
       (hloc : IsLocalDiffeomorphOn ... intrinsicFramedExp (Metric.ball 0 R))
       (γ : Real → M)
       (hγ : ContMDiffOn 𝓘(Real, Real) I 1 γ (Set.Icc 0 1))
       (hγ0 : γ 0 = p)
       (hlen : Manifold.pathELength I γ 0 1 < ENNReal.ofReal R) :
       ∃! γ̃ : Real → E,
         γ̃ 0 = 0 ∧
         (∀ t ∈ Set.Icc 0 1, γ̃ t ∈ Metric.ball 0 R) ∧
         (∀ t ∈ Set.Icc 0 1,
           intrinsicFramedExp (I := I) g hEnorm p (γ̃ t) = γ t)
   ```

   If not, identify the precise missing hypothesis or the smallest continuation
   lemma that replaces it without assuming injectivity radius or a covering
   map.

2. Give exact Lean-facing signatures for the bounded-length homotopy object and
   the cancellation/concatenation lemmas. Should it wrap
   `Path.Homotopy.eval`, or should it use `Real → M` paths on `[0,1]` so that
   `Manifold.pathELength` applies directly?

3. What is the smallest honest strict-convexity/center theorem needed for CGT
   Lemma 4.6? Please state it with the existing `Rm04GlobalBound`, radius, and
   local pullback geometry, and show how the existing center-of-mass and
   Hessian-along-geodesic APIs should be composed. Do not package convexity as a
   new HCG input.

4. Give the next five declarations, in dependency order, that close:

   ```text
   bounded short paths
     → short exponential lifts
     → center uniqueness
     → distinct loop iterates/even sheets
     → intrLoop_ge_cgt
   ```

5. Is there a strictly smaller route using the existing universal-cover or
   monodromy APIs that genuinely preserves the length constraint and eliminates
   either the short-lift or center theorem? If not, say so explicitly.

6. After `intrLoop_ge_cgt`, give the smallest local
   `loop_of_not_inj` statement needed to derive the intrinsic injectivity
   estimate. Avoid importing a full cut-locus/Klingenberg hierarchy unless it
   is genuinely smaller.

Constraints:

- do not add a new field to HCG compactness inputs;
- do not assume the desired injectivity-radius bound;
- do not introduce a fake convexity, collision, or no-torsion hypothesis;
- do not replace the project-native intrinsic framed exponential by a raw
  model-norm exponential;
- do not use an endpoint radius assumption;
- keep one canonical API per concept and place new lemmas below the HCG layer;
- preserve the corrected CGT constants above.

