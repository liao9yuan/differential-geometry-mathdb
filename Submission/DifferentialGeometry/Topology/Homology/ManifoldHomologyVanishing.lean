import Submission.DifferentialGeometry.Topology.Homology.ManifoldCapDuality
import Submission.DifferentialGeometry.External.CanonicalTopology.Topology.Homology.ManifoldHomologyGenerator
import Submission.DifferentialGeometry.External.CanonicalTopology.Topology.Homology.CochainCones

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Set
open scoped _root_.Manifold

namespace DifferentialGeometry.Topology

variable {E X : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace X] [T2Space X] [CompactSpace X] [ChartedSpace E X]
  [IsManifold 𝓘(ℝ, E) 1 X] [SimplyConnectedSpace X]

theorem integralSingularHomology_subsingleton_of_simplyConnected_of_one_add_eq_finrank
    (m : ℕ) (hm : 1 + m = Module.finrank ℝ E) :
    Subsingleton (integralSingularHomology m X) := by
  let _ : FiniteDimensional ℝ E := Module.finite_of_finrank_pos (by omega)
  obtain ⟨a, _, ha⟩ := exists_integralSingularHomology_generator_of_simplyConnected (E := E) (M := X)
  have hex : ∃ a : integralSingularHomology (1 + m) X,
      ∀ p : X, Function.Bijective (fun z : ℤ =>
        z • integralAbsoluteToRelative (1 + m) ({p}ᶜ : Set X) a) := by
    rw [hm]
    exact ⟨a, ha⟩
  obtain ⟨a, ha⟩ := hex
  let _ := integralSingularCohomology_one_subsingleton (X := X)
  exact (integralSingularCohomologyCapProduct_bijective_of_chartedSpace_of_local_generators
    1 m hm a ha).surjective.subsingleton

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralSingularHomology_subsingleton_of_simplyConnected_of_one_add_eq_finrank then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralSingularHomology_subsingleton_of_simplyConnected_of_one_add_eq_finrank"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralSingularHomology_subsingleton_of_simplyConnected_of_one_add_eq_finrank ``Submission.DifferentialGeometry.Topology.integralSingularHomology_subsingleton_of_simplyConnected_of_one_add_eq_finrank

theorem integralSingularHomology_two_subsingleton_of_simplyConnected_of_finrank_eq_three
    (hE : Module.finrank ℝ E = 3) : Subsingleton (integralSingularHomology 2 X) :=
  integralSingularHomology_subsingleton_of_simplyConnected_of_one_add_eq_finrank 2 hE.symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralSingularHomology_two_subsingleton_of_simplyConnected_of_finrank_eq_three then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralSingularHomology_two_subsingleton_of_simplyConnected_of_finrank_eq_three"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralSingularHomology_two_subsingleton_of_simplyConnected_of_finrank_eq_three ``Submission.DifferentialGeometry.Topology.integralSingularHomology_two_subsingleton_of_simplyConnected_of_finrank_eq_three

end DifferentialGeometry.Topology

end
