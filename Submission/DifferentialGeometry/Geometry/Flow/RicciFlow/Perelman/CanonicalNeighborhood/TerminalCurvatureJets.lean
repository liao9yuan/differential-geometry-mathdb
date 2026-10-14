import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Curvature.TerminalRegularity
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.TerminalRegularity
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHornGeometry

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology _root_.Submission.Topology

section Ancient

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle

theorem terminalJetContinuous_of_ancientFlow
    (F : PointedFlowData.{u, 0, 0} I3 ancientTimeInterval) :
    TerminalJetContinuous (I := I3) F 0 := by
  intro k x v
  exact solution_nablaKRm04_eval_continuousWithinAt_terminal F.S F.isSolution
    (a := (-1 : ℝ)) (b := 0) (by norm_num) (fun _ ht => ht.2)
    (fun _ ht => ht.2) k x v

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.terminalJetContinuous_of_ancientFlow then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.terminalJetContinuous_of_ancientFlow"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.terminalJetContinuous_of_ancientFlow ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.terminalJetContinuous_of_ancientFlow

theorem isAncientKappaSolutionTerminal_of_ancient {kappa : ℝ} {D : RealTimeInterval}
    {F : PointedFlowData.{u, 0, 0} I3 D}
    (hF : IsAncientKappaSolution (I := I3) kappa F) :
    IsAncientKappaSolutionTerminal (I := I3) kappa F := by
  refine ⟨hF, ?_⟩
  intro k x v
  apply solution_nablaKRm04_eval_continuousWithinAt_terminal F.S F.isSolution
    (a := (-1 : ℝ)) (b := 0) (by norm_num) _ _ k x v
  · intro t ht
    rw [hF.carrier_eq]
    exact ht.2
  · intro t ht
    rw [hF.regular_eq]
    exact ht.2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.isAncientKappaSolutionTerminal_of_ancient then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.isAncientKappaSolutionTerminal_of_ancient"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.isAncientKappaSolutionTerminal_of_ancient ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.isAncientKappaSolutionTerminal_of_ancient

end Ancient

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
