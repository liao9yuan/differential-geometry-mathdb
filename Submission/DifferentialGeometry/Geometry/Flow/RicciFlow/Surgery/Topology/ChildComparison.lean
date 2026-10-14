import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.ChildLengthComparison
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CollapseFundamentalClass

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Set _root_.Submission.Set _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

namespace GeometricCutoffRecord

variable {H : ObservedHistory.{u}} {i : Fin H.eventCount} {parameters : CutoffParameters}
    (G : GeometricCutoffRecord H i parameters)

namespace ComparisonSupport

variable {G} {c : ConnectedComponents (H.stage i.succ).Carrier} (K : G.ComparisonSupport c)

theorem rfs_collapse_degree :
    K.LocalTerminalLengthControl K.rfs_whole_parent_map ∧
    (∀ x ∉ K.support.region, ∃ U ∈ 𝓝 x, ∀ y ∈ U,
      K.rfs_whole_parent_map y = K.rfs_whole_parent_map x) ∧
    (∀ x : G.transition.ChildCore c,
      K.rfs_whole_parent_map (G.transition.childCoreIntoParent c x) =
        G.transition.childCoreInclusion c x) ∧
    integralHomologyMap 3 K.rfs_whole_parent_map (fundamentalClass (G.Parent c).orientation) =
      fundamentalClass (G.Child c).orientation ∧
    Function.Surjective K.rfs_whole_parent_map := by
  exact ⟨K.rfs_whole_parent_map_localTerminalLengthControl_of_localTerminalDistanceControl
    (rfs_whole_parent_map_localTerminalDistanceControl G K),
    fun _ hx => K.rfs_whole_parent_map_locallyConstant_of_notMem hx,
    K.rfs_whole_parent_map_childCore, K.rfs_whole_parent_map_fundamentalClass,
    K.rfs_whole_parent_map_surjective_of_cover K.rfs_collapse_cover⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport.rfs_collapse_degree then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport.rfs_collapse_degree"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport.rfs_collapse_degree ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport.rfs_collapse_degree


end ComparisonSupport

theorem rfs_child_comparison
    (hSC : ∀ p : ConnectedComponents (H.stage i.castSucc).Carrier,
      SimplyConnectedSpace ((H.stage i.castSucc).component p).Carrier) :
    ∃ f : (c : ConnectedComponents (H.stage i.succ).Carrier) →
      C((G.Parent c).Carrier, (G.Child c).Carrier),
    (∀ c, ∃ K : G.ComparisonSupport c, f c = K.rfs_whole_parent_map) ∧
    (∀ c, integralHomologyMap 3 (f c) (fundamentalClass (G.Parent c).orientation) =
      fundamentalClass (G.Child c).orientation) ∧
    ∃ s₀ ∈ _root_.Set.Ico (H.time i.castSucc) (H.time i.succ), ∃ ell : ℝ → ℝ,
      (∀ s ∈ _root_.Set.Ioo s₀ (H.time i.succ), 1 ≤ ell s) ∧
      Filter.Tendsto ell (𝓝[<] (H.time i.succ)) (𝓝 1) ∧
      ∀ c, ∀ s ∈ _root_.Set.Ioo s₀ (H.time i.succ), ∀ x y : (G.Parent c).Carrier,
        riemannianEDistOf ((H.stage i.succ).componentMetric (H.event i).outputMetric c)
          (f c x) (f c y) ≤ ENNReal.ofReal (ell s) *
            riemannianEDistOf ((H.stage i.castSucc).componentMetric
              ((H.event i).incoming.flow.base.metric s) (G.transition.childParent c)) x y := by
  let Kc : (c : ConnectedComponents (H.stage i.succ).Carrier) → G.ComparisonSupport c :=
    fun c => by
      letI := hSC (G.transition.childParent c)
      exact Classical.choice (G.rfs_comparison_support c)
  exact G.rfs_child_comparison_of_local_length_comparison Kc
    (fun c => (Kc c).rfs_whole_parent_map_fundamentalClass)
    (G.local_length_comparison Kc)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.rfs_child_comparison then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.rfs_child_comparison"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.rfs_child_comparison ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.rfs_child_comparison


end GeometricCutoffRecord

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
