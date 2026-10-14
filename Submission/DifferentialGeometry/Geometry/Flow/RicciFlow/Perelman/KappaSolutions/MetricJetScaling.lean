import Submission.DifferentialGeometry.Geometry.Metric.Convergence.Scaling

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

alias metricCovDeriv_scale_all := CheegerGromovCompactness.metricCovDeriv_scale_all

alias metricDiffCovDerivAt_scale_all := CheegerGromovCompactness.metricDiffCovDerivAt_scale_all

alias metricDerivNorm_scale_all := CheegerGromovCompactness.metricDerivNorm_scale_all

noncomputable abbrev metricJetScaleLoss := CheegerGromovCompactness.metricJetScaleLoss

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.metricJetScaleLoss then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.metricJetScaleLoss"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.metricJetScaleLoss ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.metricJetScaleLoss

alias metricJetScaleLoss_pos := CheegerGromovCompactness.metricJetScaleLoss_pos

alias metricDerivNormSupOn_scale_all_le := CheegerGromovCompactness.metricDerivNormSupOn_scale_all_le

alias metricCPConvOn_scale_all := CheegerGromovCompactness.metricCPConvOn_scale_all

alias metricCInfConvOnCompacts_scale_all := CheegerGromovCompactness.metricCInfConvOnCompacts_scale_all

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
