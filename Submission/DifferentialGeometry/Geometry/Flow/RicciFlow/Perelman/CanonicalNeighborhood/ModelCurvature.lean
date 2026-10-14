import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.GoodPointDerivatives
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientKappaModelCurvatureWindow

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]

theorem modelCurvatureBoundNearBase
    (hdim : Module.finrank ℝ E = 3) {kappa : ℝ} (hkappa : 0 < kappa) :
    ModelCurvatureBoundNearBase.{u, uE, uH} I kappa := by
  exact DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientKappa_modelCurvatureBoundNearBase
    hdim hkappa

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.modelCurvatureBoundNearBase then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.modelCurvatureBoundNearBase"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.modelCurvatureBoundNearBase ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.modelCurvatureBoundNearBase

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood

end
