import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.Ancestry
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CanonicalNeighborhoodInduction
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Width.SurgeryWidthEvolution

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

theorem OrientedThreeStage.simplyConnectedSpace_connectedComponent (P : OrientedThreeStage.{u})
    (x : P.Carrier) [SimplyConnectedSpace (P.component (ConnectedComponents.mk x)).Carrier] :
    SimplyConnectedSpace (connectedComponent x) := by
  have hs : ((P.componentOpen (ConnectedComponents.mk x) : Set P.Carrier)) =
      connectedComponent x := by
    ext y
    exact ConnectedComponents.coe_eq_coe'
  let e : (P.component (ConnectedComponents.mk x)).Carrier ≃ₜ connectedComponent x :=
    Homeomorph.setCongr hs
  exact e.symm.toHomotopyEquiv.simplyConnectedSpace

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.simplyConnectedSpace_connectedComponent then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.simplyConnectedSpace_connectedComponent"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.simplyConnectedSpace_connectedComponent ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.simplyConnectedSpace_connectedComponent

theorem RetainedCoreHistory.simplyConnectedSpace_connectedComponent_stage
    {P₀ : OrientedThreeStage.{u}} [SimplyConnectedSpace P₀.Carrier] {g₀ : P₀.Metric}
    {B : ℝ} {p₀ : CutoffParameters} {δbound ρbound : ℝ} (H : RetainedCoreHistory P₀)
    (hH : H.InCutoffClass g₀ B p₀ δbound ρbound) (j : Fin (H.eventCount + 1))
    (x : (H.stage j).Carrier) : SimplyConnectedSpace (connectedComponent x) := by
  let h0 := Extinction.Width.initialIdentification_components_simplyConnected P₀ g₀
    H.toHistory hH.1.some
  have := rfs_simply_connected_history H.toHistory h0 j (ConnectedComponents.mk x)
  exact (H.stage j).simplyConnectedSpace_connectedComponent x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory.simplyConnectedSpace_connectedComponent_stage then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory.simplyConnectedSpace_connectedComponent_stage"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory.simplyConnectedSpace_connectedComponent_stage ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory.simplyConnectedSpace_connectedComponent_stage

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
