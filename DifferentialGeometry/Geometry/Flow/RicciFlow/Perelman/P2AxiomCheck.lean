import DifferentialGeometry.Analysis.Integration.Measure.Tight
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Fields.ScalarConvergence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.CostChartLip
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.CompleteFlowBound
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.RedMinTime
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.RedLengthFence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.LateVolumeLow
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.NLCBallUpper
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.NLCBallUnif
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.SmoothNLC
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Defs
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Naturality
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.CrossingCost
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.PointedAction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.Distance.ChangingDistance
import DifferentialGeometry.Geometry.Metric.Convergence.RicciFromJetsCompact

set_option autoImplicit false

#print axioms DifferentialGeometry.PDE.RicciFlow.Perelman.lCost_le_ray_bdd
#print axioms DifferentialGeometry.PDE.RicciFlow.Perelman.lRegPot_upper_rm
#print axioms DifferentialGeometry.PDE.RicciFlow.Perelman.exists_redMin_vec
#print axioms DifferentialGeometry.PDE.RicciFlow.Perelman.redMinAct_lip
#print axioms DifferentialGeometry.PDE.RicciFlow.Perelman.redMinVal_cont
#print axioms DifferentialGeometry.PDE.RicciFlow.Perelman.exists_redWeak_sup
#print axioms DifferentialGeometry.PDE.RicciFlow.Perelman.exists_redLen_le
#print axioms DifferentialGeometry.PDE.RicciFlow.Perelman.redVolume_late_low
#print axioms DifferentialGeometry.PDE.RicciFlow.Perelman.redVolume_ball_eta
#print axioms DifferentialGeometry.PDE.RicciFlow.Perelman.redVolume_ball_le
#print axioms DifferentialGeometry.PDE.RicciFlow.Perelman.redVolume_ball_unif
#print axioms DifferentialGeometry.PDE.RicciFlow.Perelman.redVolume_anti
#print axioms DifferentialGeometry.PDE.RicciFlow.Perelman.smooth_nlc
#print axioms DifferentialGeometry.PDE.RicciFlow.Perelman.lLength_join
#print axioms DifferentialGeometry.PDE.RicciFlow.Perelman.lDensity_pull
#print axioms DifferentialGeometry.PDE.RicciFlow.Perelman.lLength_pull
#print axioms DifferentialGeometry.PDE.RicciFlow.Perelman.lLength_cross
#print axioms DifferentialGeometry.HCGCompactness.lVelocity_src_map
#print axioms DifferentialGeometry.HCGCompactness.lKinetic_src_pull
#print axioms DifferentialGeometry.HCGCompactness.lLength_tendsto
#print axioms DifferentialGeometry.PDE.RicciFlow.dist_short_support
#print axioms DifferentialGeometry.Analysis.Measure.mass_tendsto_of_cc
#print axioms DifferentialGeometry.HCGCompactness.scalarSub_le_dNormOn
#print axioms DifferentialGeometry.HCGCompactness.ConvOut.scalar_convOn
