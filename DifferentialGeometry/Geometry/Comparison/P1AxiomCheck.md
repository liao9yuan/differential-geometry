# P1AxiomCheck

This narrow audit file prints the axioms of the P1a project endpoints, the
compact-tail continuation bridges used by the incomplete-manifold route, and
the strict-volume producer chain through sectional curvature.  It cannot
certify the still-missing local compact-closure Bishop--Gromov endpoint.

Focused verification passed after refreshing the two upstream modules whose
new declarations had stale artifacts.  Every printed endpoint and continuation
bridge depends only on `propext`, `Classical.choice`, and `Quot.sound`; no
project axiom or `sorryAx` appears.

That result now applies to all seven accepted project-used endpoints and the
listed continuation/producer bridges.  The expanded audit includes the
pole-Haar, Euclidean model-ball, radial rigidity, sectional-to-Ricci, and final
strict sectional-volume declarations.  The two Euclidean wrappers live in the
dedicated `SegmentBallEuclideanStrict` module so their global inner-product and
measure instances match the checked Euclidean normalization layer.  After its
warning-free focused check and named refresh, the expanded audit passed: all 20
printed declarations depend only on the three standard logical axioms above.
The eighth endpoint, local compact-closure Bishop--Gromov, remains unstated and
therefore remains outside this audit.

The P1b expansion includes the radial-control adapters, both local and global
CGT injectivity producers, the explicit volume-to-injectivity assembly, and the
realized bounded-geometry and Ricci-flow injectivity consumers.  The expanded
audit passed focused verification: all 28 printed declarations depend only on
`propext`, `Classical.choice`, and `Quot.sound`.

This certifies the listed P1b producer and consumer machinery, not the two exact
local-on-balls P1b endpoints.  Those remain zero of two because the incomplete-
ambient compact-closure bridge and the bounded-ball propagation adapter are not
yet stated and proved.

The P1c expansion adds the proper-Riemannian-metric input, the minimizing-ray
producer, the finite Busemann metric core, the checked radial-Laplacian chain,
the Calabi smooth upper support, and the new epsilon-relaxed distance-barrier
adapter.  The first expanded run reached every new declaration but failed on
two audit-only namespace typos.  After replacing them by the declarations'
actual full names, focused verification passed.  After adding the local
Laplacian subtraction producer and the barrier-to-lower-test-viscosity bridge,
the expanded audit passed again: all 41 printed P1a--P1c
declarations depend only on `propext`, `Classical.choice`, and `Quot.sound`.

This does not certify any of the four formal P1c endpoints.  The lower-test
viscosity bridge is checked infrastructure, while the viscosity-to-
distributional Laplacian bridge, the weak and Sobolev parts of the Busemann
endpoint, splitting, and soul remain unstated and therefore remain at 0%.

The final P1c infrastructure expansion adds the compact-support Green second
identity, the noncompact signed chart-integral adapter, the intrinsic
compact-test distributional predicate and its open-set restriction, and the
smooth pointwise-to-distributional producer.  Focused verification passed for
all 46 printed P1a--P1c declarations; every declaration again depends only on
`propext`, `Classical.choice`, and `Quot.sound`.  This still does not certify a
formal P1c endpoint: the genuine viscosity-to-distributional conversion theorem
is absent.

The direct polar-distance route adds four more audited declarations:
`expJac_map_eq`, `expJac_lintegral`, `segInt_lintegral`, and
`expJac_radial`.  Focused verification passed for all 50 printed declarations;
the four additions also depend only on `propext`, `Classical.choice`, and
`Quot.sound`.  They supply function-level exponential change of variables and
the radial Jacobian scaling identity, but not yet the distance distributional
Laplacian endpoint.

The completed signed polar reassembly now adds the public distance-gradient
pairing inequality and the formal distributional distance-Laplacian endpoint
to this audit.  Focused verification passes for all 52 printed P1 declarations;
the two additions, like the earlier declarations, depend only on `propext`,
`Classical.choice`, and `Quot.sound`.

The supplied-ray Busemann weak-Laplacian endpoint is now included directly.
Focused verification passes for all 53 printed declarations; `busemann_lap`
depends only on `propext`, `Classical.choice`, and `Quot.sound`.

The supplied-line ray adapters, Busemann-pair metric lemmas, weak-Laplacian
addition rule, and Busemann-pair Laplacian assembly are now included.  Their
focused axiom verification passes.  All 58 printed declarations depend only on
`propext`, `Classical.choice`, and `Quot.sound`.

The next splitting-infrastructure expansion adds the intrinsic Lipschitz
energy inequality, its zero-source specialization, local chart `W^{1,2}`
membership for the Busemann pair, and the normalized-coefficient local strong
minimum principle.  All four producers were warning-free focused checked and
their explicitly named modules were refreshed before this downstream audit.
The expanded 62-declaration focused audit passed; all printed declarations
again depend only on `propext`, `Classical.choice`, and `Quot.sound`.  The
splitting endpoint itself remains unstated and therefore remains 0%; these
declarations are dedicated machinery only.

The current 70-declaration expansion additionally audits the canonical
Euclidean and manifold local Sobolev producers, nonnegative `H₀¹` density,
normalized chart coefficients, arbitrary-ball strong minimum, the
distributional-to-De-Giorgi chart bridge, global Busemann-pair zero propagation,
and the local Busemann weak-solution assembly.  Every newly printed producer has
warning-free focused verification, and every new declaration required by an
importing downstream module has a fresh named artifact.  The unified focused
70-declaration axiom audit passed without warnings.  Every printed declaration
depends only on `propext`, `Classical.choice`, and `Quot.sound`; no project
axiom or `sorryAx` appears.

The current 73-declaration expansion adds the scale-retaining Busemann chart
solution data, the supplied-ray asymptotic support producer, and the
pointwise differentiable Busemann eikonal identity.  Each producer passed its
focused check, and the two new exporting modules were refreshed before this
downstream audit.  The unified focused audit passed without warnings; all 73
printed declarations depend only on `propext`, `Classical.choice`, and
`Quot.sound`.  The splitting theorem remains unstated and therefore 0%
complete: the new entries are dedicated post-regularity machinery, not a
substitute for the missing local elliptic regularity, parallel-gradient, or
global product producers.

The current 77-declaration expansion adds the public compact-in-open smooth
cutoff, signed smooth-test bilinear equality, smooth-test density extension,
and `IsSolution.to_homogeneous`.  The unified focused audit passed without
warnings; all 77 printed declarations depend only on `propext`,
`Classical.choice`, and `Quot.sound`.  This closes the weak-solution interface
gap but not the local `W^{2,2}` theorem, which remains unstated and therefore
0% complete.

The current 88-declaration expansion audits the complete compact-free
difference-quotient chain through `homSol_memW2`, its chart application
`busemann_chart_h2`, and the differentiated weak identity `homSol_diff_id`.
All exporting modules passed warning-free focused verification and the required
named refreshes before this downstream check.  The unified focused audit passed
without warnings; every printed declaration depends only on `propext`,
`Classical.choice`, and `Quot.sound`.  This verifies local chart `W^{2,2}` and
the first differentiated equation as dedicated splitting machinery; the
Cheeger--Gromoll splitting endpoint remains unstated and therefore 0% complete.

The current 101-declaration expansion adds the scalar-source substitution and
master chain, weak-divergence lowering, differentiated source integrability,
the full differentiated weak equation, scalar-source local `W^{2,2}`, and the
fixed-order `homSol_memW3` assembly.  Every exporting module had already passed
warning-free focused verification and its required named refresh.  The unified
focused audit passed without warnings; all 101 printed declarations depend only
on `propext`, `Classical.choice`, and `Quot.sound`.  These declarations verify
the local `W^{2,2} -> W^{3,2}` machinery.  They do not state the global
Cheeger--Gromoll splitting theorem, which therefore remains 0% complete.

The current 148-declaration expansion reaches the completed supplied-line
metric splitting endpoint.  It includes the smooth regular-level product
diffeomorphism, induced immersion metric, product metric, differential split,
horizontal/vertical/mixed metric blocks, and the public
`busemannMetricSplit`.  All exporting modules have warning-free focused
verification; the final metric-splitting module also has a fresh explicit
named artifact.  The unified focused audit passed without warnings, and every
printed declaration depends only on `propext`, `Classical.choice`, and
`Quot.sound`.  This makes the supplied-line splitting endpoint formally and
axiom-cleanly complete.  The independent Soul endpoint remains unstated and is
not counted as splitting progress.

The current 196-declaration expansion closes the compact-buffer P1a chain.  In
addition to the chart-independent continuation, compact minimizing-exponential,
raw segment-domain, image-measure, Jacobi, and pole-normalization producers, it
directly audits `rawSpeed_sq`, `raw_ratio_anti`, `raw_density_le`,
`rawDens_eq_trans`, `rawDens_le_zero`, and the final local absolute-volume
endpoint `ball_vol_le_eucl`.  The endpoint requires compactness only for a
strictly larger buffer ball and Ricci nonnegativity only on the compared ball;
it adds neither ambient completeness nor global Ricci assumptions.  Both
exporting modules passed warning-free focused verification and their exact
named refreshes before this downstream check.  The unified audit passed without
warnings; all 196 printed declarations depend only on `propext`,
`Classical.choice`, and `Quot.sound`.
