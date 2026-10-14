import Submission.DifferentialGeometry.Topology.Homotopy.CubeSphereProjection
import Submission.DifferentialGeometry.Topology.LoopSpace.FamilySphere

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission



noncomputable section

open _root_.Set _root_.Function _root_.ContinuousMap
open scoped _root_.Topology

namespace DifferentialGeometry.Topology

variable {X : Type*} [TopologicalSpace X]



theorem sphereMap_homotopicRel_constant_of_subsingleton (n : ℕ) (x : X)
    [Subsingleton (HomotopyGroup (Fin (n + 1)) X x)]
    (f : basedMappingSpace (cubeSphereBasepoint n) x) :
    f.val.HomotopicRel (ContinuousMap.const _ x) {cubeSphereBasepoint n} := by
  let p := (genLoopSphereHomeomorph n x).symm f
  have heq := @Subsingleton.elim (HomotopyGroup (Fin (n + 1)) X x) inferInstance
    ⟦p⟧ ⟦GenLoop.const⟧
  have hp : GenLoop.Homotopic p GenLoop.const := Quotient.exact heq
  have hf := (genLoopSphereHomeomorph_homotopic_iff n x p GenLoop.const).mpr hp
  simpa only [p, Homeomorph.apply_symm_apply, genLoopSphereHomeomorph_const] using hf

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.sphereMap_homotopicRel_constant_of_subsingleton then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.sphereMap_homotopicRel_constant_of_subsingleton"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.sphereMap_homotopicRel_constant_of_subsingleton ``Submission.DifferentialGeometry.Topology.sphereMap_homotopicRel_constant_of_subsingleton



theorem sphereMap_nullhomotopic_of_subsingleton (n : ℕ)
    (f : C(Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1, X))
    [Subsingleton (HomotopyGroup (Fin (n + 1)) X (f (cubeSphereBasepoint n)))] :
    f.Nullhomotopic := by
  refine ⟨f (cubeSphereBasepoint n), ?_⟩
  obtain ⟨H⟩ := sphereMap_homotopicRel_constant_of_subsingleton n
    (f (cubeSphereBasepoint n)) ⟨f, rfl⟩
  exact ⟨H.toHomotopy⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.sphereMap_nullhomotopic_of_subsingleton then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.sphereMap_nullhomotopic_of_subsingleton"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.sphereMap_nullhomotopic_of_subsingleton ``Submission.DifferentialGeometry.Topology.sphereMap_nullhomotopic_of_subsingleton



theorem familySphereMap_nullhomotopic_of_piTwo
    (h : ∀ x : X, Subsingleton (HomotopyGroup (Fin 2) X x)) (f : C(familySphere, X)) :
    f.Nullhomotopic := by
  let := h (f (cubeSphereBasepoint 1))
  exact sphereMap_nullhomotopic_of_subsingleton 1 f

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.familySphereMap_nullhomotopic_of_piTwo then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.familySphereMap_nullhomotopic_of_piTwo"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.familySphereMap_nullhomotopic_of_piTwo ``Submission.DifferentialGeometry.Topology.familySphereMap_nullhomotopic_of_piTwo

end DifferentialGeometry.Topology
