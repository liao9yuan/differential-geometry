# PointedRiemannian

Source used: MSM135 Chapter 3, especially Theorem 3.9 and the complete pointed Riemannian manifold hypotheses.

Introduced definitions: `PointedRiemannianManifold`, `PointedRiemannianSeq`, `PointedRiemannianSeq.basepoint`, `PointedRiemannianSeq.subseq`, `MetricComplete`, and `SeqMetricComplete`.

Design note: `MetricComplete` is no longer an axiom. It uses Mathlib's `EMetricSpace.ofRiemannianMetric` for the stored smooth Riemannian metric, then states `CompleteSpace` for that induced uniform structure.

Reason for the file split: the concrete Riemannian-emetric completeness predicate elaborates cleanly below the Ricci-flow and curvature imports. `Basic.lean` imports this file and then defines the flow-level data.

Verification: passed.
