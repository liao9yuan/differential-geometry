# HyperbolicModel

## Pole normalization

`hypDensity_pole` records that the model density divided by the Euclidean
radial factor tends to one at the pole.  The existing canonical
`hypSnRatio_tendsto` supplies the one-dimensional slope limit; taking its
`d`-th power and unfolding `hypDensity` gives the result for every natural
dimension, including zero.

The theorem has no geometric or sign hypotheses.  It replaces the duplicated
private model-limit helpers formerly needed by higher volume-comparison
consumers without changing those claimed files.

Focused verification passed without warnings.  This model producer is complete
(100%); its use in the raw local Bishop endpoint is a separate downstream step
and remains unstated (0%), so it is only a small piece of the broader Bishop
comparison program.
