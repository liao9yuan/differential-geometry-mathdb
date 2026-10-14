import Submission.DifferentialGeometry.External.CanonicalTopology.Topology.Homology.RadialHomotopy
import Submission.DifferentialGeometry.External.CanonicalTopology.Topology.Homology.RelativeComparison
import Submission.DifferentialGeometry.External.CanonicalTopology.Topology.Homology.CochainHomotopy

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

universe v

namespace DifferentialGeometry.Topology

open _root_.Set _root_.Metric

theorem exists_integralRelativeCohomologyMap_sphere_puncture_bijective
    (E : Type v) [NormedAddCommGroup E] [NormedSpace ℝ E] (n : ℕ) :
    ∃ h : _root_.Set.MapsTo (ContinuousMap.id E) (_root_.Metric.sphere (0 : E) 1) ({0}ᶜ : Set E),
      Function.Bijective (integralRelativeCohomologyMap n (ContinuousMap.id E) h) := by
  have hf : _root_.Set.MapsTo (ContinuousMap.id E) (_root_.Metric.sphere (0 : E) 1) ({0}ᶜ : Set E) := by
    intro x hx
    change x ∉ ({0} : Set E)
    intro h
    have he : x = 0 := mem_singleton_iff.mp h
    subst x
    simp at hx
  let e := (puncturedSpaceSphereHomotopyEquiv E).symm
  have he : singularPairRestriction (ContinuousMap.id E) hf = e.toFun := by
    apply ContinuousMap.ext
    intro x
    apply Subtype.ext
    exact (puncturedSpaceSphereHomotopyEquiv_inv_apply E x).symm
  refine ⟨hf, ?_⟩
  · apply integralRelativeCohomologyMap_bijective_of_absolute_and_subspace
    · intro k
      rw [integralSingularCohomologyMap_id]
      exact Function.bijective_id
    · intro k
      rw [he]
      exact integralSingularCohomologyMap_bijective_of_homotopyEquiv e k

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.exists_integralRelativeCohomologyMap_sphere_puncture_bijective then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.exists_integralRelativeCohomologyMap_sphere_puncture_bijective"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.exists_integralRelativeCohomologyMap_sphere_puncture_bijective ``Submission.DifferentialGeometry.Topology.exists_integralRelativeCohomologyMap_sphere_puncture_bijective

end DifferentialGeometry.Topology
