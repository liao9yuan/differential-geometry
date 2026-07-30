# H6 Step-B1 metric carrier

`H6NormalData.preapprox_tail` combines provider-native forward and inverse
intrinsic norm tails, local diffeomorphism, and injectivity with the generic
`preapprox_pair` constructor. Both `PreApproxIsoDataOn` carriers use the same
stage map built from `d.chart`.

Focused and exact verification pass (`4234/4234`), with no local warnings.
The H6 metric carrier is complete and feeds the raw-B1 producer.
