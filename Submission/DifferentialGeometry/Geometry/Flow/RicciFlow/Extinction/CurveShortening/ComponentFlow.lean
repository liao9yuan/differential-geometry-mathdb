import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.History
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.ChildParent
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Solutions.OpenRestriction

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section
open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.Set
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology
open _root_.Submission.DifferentialGeometry
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening
universe u
variable {P : OrientedThreeStage.{u}} {a b : ℝ}

theorem incoming_component_native_solution (G : P.IncomingSlab a b)
    (c : ConnectedComponents P.Carrier) :
    ∃ F : SolutionOn (I := ThreeModel) (M := (P.component c).Carrier)
        (RealTimeInterval.closedOpen a b G.lt),
      DifferentialGeometry.PDE.RicciFlow.IsSolutionOn F ∧
      (∀ t ∈ _root_.Set.Ico a b, F.base.metric t = P.componentMetric (G.flow.base.metric t) c) ∧
      (∀ t ∈ _root_.Set.Ico a b, ∀ x : (P.component c).Carrier,
        F.base.scalar t x = G.flow.base.scalar t x.1) := by
  let : CompactSpace (P.componentOpen c) := P.component_compact c
  let : T2Space (P.componentOpen c) := (P.component c).hausdorff
  let : IsManifold ThreeModel ∞ (P.componentOpen c) := (P.component c).smooth
  let : SigmaCompactSpace (P.componentOpen c) := inferInstance
  let F : SolutionOn (I := ThreeModel) (M := (P.component c).Carrier)
      (RealTimeInterval.closedOpen a b G.lt) :=
    CheegerGromovCompactness.solutionOnRestrictOpen (I := ThreeModel) (M := P.Carrier)
      (D := RealTimeInterval.closedOpen a b G.lt) G.flow (P.componentOpen c)
  have hF : DifferentialGeometry.PDE.RicciFlow.IsSolutionOn F :=
    CheegerGromovCompactness.isSolutionOn_restrictOpen (I := ThreeModel) (M := P.Carrier)
      (D := RealTimeInterval.closedOpen a b G.lt) G.flow G.equation (P.componentOpen c)
  refine ⟨F, hF, ?_, ?_⟩
  · intro t _
    rfl
  · intro t _ x
    dsimp only [F, CheegerGromovCompactness.solutionOnRestrictOpen, SolutionFamily.scalar]
    exact CheegerGromovCompactness.metricScalarAt_restrictOpen
      (I := ThreeModel) (M := P.Carrier) (G.flow.base.metric t) (P.componentOpen c) x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.incoming_component_native_solution then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.incoming_component_native_solution"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.incoming_component_native_solution ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.incoming_component_native_solution

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening
