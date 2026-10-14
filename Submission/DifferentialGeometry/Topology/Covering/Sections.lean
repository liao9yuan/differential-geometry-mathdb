import Mathlib.Topology.Homotopy.Lifting

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

namespace DifferentialGeometry.Topology.Covering

theorem exists_unique_section {E B : Type*} [TopologicalSpace E] [TopologicalSpace B]
    [SimplyConnectedSpace B] [LocallyPathConnectedSpace B] {p : E → B}
    (hp : IsCoveringMap p) (b : B) (e : E) (he : p e = b) :
    ∃! s : C(B, E), s b = e ∧ Function.RightInverse s p := by
  obtain ⟨s, ⟨hs, hproj⟩, huniq⟩ :=
    hp.existsUnique_continuousMap_lifts (ContinuousMap.id B) b e he
  refine ⟨s, ⟨hs, congrFun hproj⟩, ?_⟩
  intro t ht
  exact huniq t ⟨ht.1, funext ht.2⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Covering.exists_unique_section then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Covering.exists_unique_section"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Covering.exists_unique_section ``Submission.DifferentialGeometry.Topology.Covering.exists_unique_section

end DifferentialGeometry.Topology.Covering
