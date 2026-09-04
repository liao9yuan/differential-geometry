# ExistenceTheory

## Weak-identity density bridge

- The existing smooth-test density engine is exposed as `weak_eq_of_smooth`.
  Its hypotheses and proof are unchanged.
- `IsSolution.to_homogeneous` combines the signed smooth-test bridge with that
  density engine, producing the equality-form weak solution on any open
  domain.
- This closes the first interface gap before witness-native difference-quotient
  regularity. The local `W^{2,2}` theorem itself remains unstated (0%); its
  dedicated difference-quotient machinery is approximately 80% complete.
- Focused verification and the required named refresh passed without warnings.
