import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CollapseDegreeReduction

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Set _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

namespace GeometricCutoffRecord

variable {H : ObservedHistory.{u}} {i : Fin H.eventCount} {parameters : CutoffParameters}
  {G : GeometricCutoffRecord H i parameters}

noncomputable def canonicalComparisonSupport
    (hSC : ∀ p : ConnectedComponents (H.stage i.castSucc).Carrier,
      SimplyConnectedSpace ((H.stage i.castSucc).component p).Carrier)
    (c : ConnectedComponents (H.stage i.succ).Carrier) : G.ComparisonSupport c :=
  letI : SimplyConnectedSpace (G.Parent c).Carrier := hSC (G.transition.childParent c)
  Classical.choice (G.rfs_comparison_support c)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.canonicalComparisonSupport then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.canonicalComparisonSupport"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.canonicalComparisonSupport ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.canonicalComparisonSupport

namespace ComparisonSupport

theorem rfs_collapse_degree_of_canonicalComparisonSupport
    (hSC : ∀ p : ConnectedComponents (H.stage i.castSucc).Carrier,
      SimplyConnectedSpace ((H.stage i.castSucc).component p).Carrier)
    (c : ConnectedComponents (H.stage i.succ).Carrier)
    (a : IntegralHomology (G.Parent c).Carrier 3) (b : IntegralHomology (G.Child c).Carrier 3)
    {k : ℤ}
    (hcollapse : G.LocalTerminalEDistComparison (G.canonicalComparisonSupport hSC))
    (hmap : integralHomologyMap 3 (G.canonicalComparisonSupport hSC c).rfs_whole_parent_map a
      = k • b)
    (hgen : ∃ φ : IntegralHomology (G.Child c).Carrier 3 →ₗ[ℤ] ℤ,
      φ (integralHomologyMap 3 (G.canonicalComparisonSupport hSC c).rfs_whole_parent_map a)
        = 1)
    (hk : 0 < k) :
    (G.canonicalComparisonSupport hSC c).LocalTerminalLengthControl
        (G.canonicalComparisonSupport hSC c).rfs_whole_parent_map ∧
    (∀ x ∉ (G.canonicalComparisonSupport hSC c).support.region, ∃ U ∈ 𝓝 x, ∀ y ∈ U,
      (G.canonicalComparisonSupport hSC c).rfs_whole_parent_map y =
        (G.canonicalComparisonSupport hSC c).rfs_whole_parent_map x) ∧
    (∀ x : G.transition.ChildCore c,
      (G.canonicalComparisonSupport hSC c).rfs_whole_parent_map
          (G.transition.childCoreIntoParent c x) =
        G.transition.childCoreInclusion c x) ∧
    integralHomologyMap 3 (G.canonicalComparisonSupport hSC c).rfs_whole_parent_map a = b ∧
    Function.Surjective (G.canonicalComparisonSupport hSC c).rfs_whole_parent_map :=
  rfs_collapse_degree_of_localTerminalEDistComparison
    (G.canonicalComparisonSupport hSC) a b hcollapse hmap hgen hk

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport.rfs_collapse_degree_of_canonicalComparisonSupport then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport.rfs_collapse_degree_of_canonicalComparisonSupport"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport.rfs_collapse_degree_of_canonicalComparisonSupport ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport.rfs_collapse_degree_of_canonicalComparisonSupport

theorem canonicalComparisonSupport_map_eq
    (hSC : ∀ p : ConnectedComponents (H.stage i.castSucc).Carrier,
      SimplyConnectedSpace ((H.stage i.castSucc).component p).Carrier)
    (c : ConnectedComponents (H.stage i.succ).Carrier)
    (a : IntegralHomology (G.Parent c).Carrier 3) (b : IntegralHomology (G.Child c).Carrier 3)
    {k : ℤ}
    (hcollapse : G.LocalTerminalEDistComparison (G.canonicalComparisonSupport hSC))
    (hmap : integralHomologyMap 3 (G.canonicalComparisonSupport hSC c).rfs_whole_parent_map a
      = k • b)
    (hgen : ∃ φ : IntegralHomology (G.Child c).Carrier 3 →ₗ[ℤ] ℤ,
      φ (integralHomologyMap 3 (G.canonicalComparisonSupport hSC c).rfs_whole_parent_map a)
        = 1)
    (hk : 0 < k) :
    integralHomologyMap 3 (G.canonicalComparisonSupport hSC c).rfs_whole_parent_map a = b :=
  (rfs_collapse_degree_of_canonicalComparisonSupport hSC c a b hcollapse hmap hgen hk).2.2.2.1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport.canonicalComparisonSupport_map_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport.canonicalComparisonSupport_map_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport.canonicalComparisonSupport_map_eq ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport.canonicalComparisonSupport_map_eq

end ComparisonSupport

end GeometricCutoffRecord

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

end
