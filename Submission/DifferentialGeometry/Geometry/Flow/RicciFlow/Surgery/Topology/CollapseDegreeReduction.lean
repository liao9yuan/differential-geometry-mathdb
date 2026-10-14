import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CollapseDegreeInputs

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology
universe u

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

variable {H : ObservedHistory.{u}} {i : Fin H.eventCount} {parameters : CutoffParameters}
  {G : GeometricCutoffRecord H i parameters}
  {c : ConnectedComponents (H.stage i.succ).Carrier}

namespace GeometricCutoffRecord

namespace ComparisonSupport

theorem rfs_collapse_degree_of_localTerminalEDistComparison
    (Kc : (c' : ConnectedComponents (H.stage i.succ).Carrier) → G.ComparisonSupport c')
    (a : IntegralHomology (G.Parent c).Carrier 3) (b : IntegralHomology (G.Child c).Carrier 3)
    {k : ℤ} (hcollapse : G.LocalTerminalEDistComparison Kc)
    (hmap : integralHomologyMap 3 (Kc c).rfs_whole_parent_map a = k • b)
    (hgen : ∃ φ : IntegralHomology (G.Child c).Carrier 3 →ₗ[ℤ] ℤ,
      φ (integralHomologyMap 3 (Kc c).rfs_whole_parent_map a) = 1)
    (hk : 0 < k) :
    (Kc c).LocalTerminalLengthControl (Kc c).rfs_whole_parent_map ∧
    (∀ x ∉ (Kc c).support.region, ∃ U ∈ 𝓝 x, ∀ y ∈ U,
      (Kc c).rfs_whole_parent_map y = (Kc c).rfs_whole_parent_map x) ∧
    (∀ x : G.transition.ChildCore c,
      (Kc c).rfs_whole_parent_map (G.transition.childCoreIntoParent c x) =
        G.transition.childCoreInclusion c x) ∧
    integralHomologyMap 3 (Kc c).rfs_whole_parent_map a = b ∧
    Function.Surjective (Kc c).rfs_whole_parent_map :=
  (Kc c).rfs_collapse_degree_of_localTerminalDistanceControl_and_class_generator a b
    (localTerminalDistanceControl_of_localTerminalEDistComparison Kc hcollapse) hmap hgen hk

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport.rfs_collapse_degree_of_localTerminalEDistComparison then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport.rfs_collapse_degree_of_localTerminalEDistComparison"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport.rfs_collapse_degree_of_localTerminalEDistComparison ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport.rfs_collapse_degree_of_localTerminalEDistComparison

end ComparisonSupport

end GeometricCutoffRecord

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
