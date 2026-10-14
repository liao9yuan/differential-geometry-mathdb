import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CanonicalNeighborhoodInduction
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HamiltonIveyPinching

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

theorem pinchingThroughSurgery (P₀ : OrientedThreeStage.{u}) (g₀ : P₀.Metric) :
    PinchingThroughSurgery P₀ g₀ := by
  obtain ⟨phi, hphi, hslab⟩ :=
    Perelman.exists_admissiblePinchingFunction_for_identified_incomingSlabs P₀ g₀
  intro B _
  refine ⟨phi, 1, 1, 1, hphi, one_pos, one_pos, one_pos, ?_⟩
  intro p₀ δbound ρbound _ _ _ H hH k s G hG
  obtain ⟨initial⟩ := hH.1
  obtain ⟨p, -, -, -, -, -, records, -, -, -⟩ := hH.2.2.2.1
  exact hslab H.toHistory initial p records k s G hG.2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.pinchingThroughSurgery then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.pinchingThroughSurgery"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.pinchingThroughSurgery ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.pinchingThroughSurgery

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

end
