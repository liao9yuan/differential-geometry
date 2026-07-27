# SmoothEmbedInj

## Status

The injectivity proof is verified.  After applying injectivity of the
eigenbasis representation, the representation target is a structured sequence
rather than a bare function, so its extensionality theorem (`ext i`) is the
stable proof step; `funext i` no longer matches the live API.  The coefficient
normal form also lives in the canonical `TensorHeatEquation` namespace, which
must be open at this layer.
