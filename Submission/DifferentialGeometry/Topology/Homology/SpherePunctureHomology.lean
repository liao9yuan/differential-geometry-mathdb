import Submission.DifferentialGeometry.Topology.Homology.SpherePuncture
import Submission.DifferentialGeometry.External.CanonicalTopology.Topology.Homology.ContractiblePair
import Submission.DifferentialGeometry.Topology.Homology.LiftedSphere

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

namespace DifferentialGeometry.Topology

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem integralAbsoluteToRelative_sphere_puncture_bijective
    (n : ℕ) (p : Metric.sphere (0 : E) 1) :
    Function.Bijective (integralAbsoluteToRelative (n + 2)
      ({p}ᶜ : Set (Metric.sphere (0 : E) 1))) := by
  let := spherePuncture_contractible p
  exact (integralAbsoluteToRelativeIsoOfContractible n ({p}ᶜ)).toLinearEquiv.bijective

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralAbsoluteToRelative_sphere_puncture_bijective then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralAbsoluteToRelative_sphere_puncture_bijective"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralAbsoluteToRelative_sphere_puncture_bijective ``Submission.DifferentialGeometry.Topology.integralAbsoluteToRelative_sphere_puncture_bijective

theorem liftedSpherePuncture_contractible (n : ℕ) (p : liftedHomotopySphere.{u} n) :
    ContractibleSpace ({p}ᶜ : Set (liftedHomotopySphere.{u} n)) := by
  let e : ({p}ᶜ : Set (liftedHomotopySphere.{u} n)) ≃ₜ
      ({liftedSphereHomeomorph n p}ᶜ : Set (Metric.sphere (0 : liftedSphereSpace.{u} n) 1)) :=
    (liftedSphereHomeomorph n).subtype (fun x => by
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      exact not_congr (liftedSphereHomeomorph n).injective.eq_iff.symm)
  let := spherePuncture_contractible (liftedSphereHomeomorph n p)
  exact e.contractibleSpace

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.liftedSpherePuncture_contractible then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.liftedSpherePuncture_contractible"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.liftedSpherePuncture_contractible ``Submission.DifferentialGeometry.Topology.liftedSpherePuncture_contractible

theorem integralAbsoluteToRelative_liftedSphere_puncture_bijective
    (n k : ℕ) (p : liftedHomotopySphere.{u} n) :
    Function.Bijective (integralAbsoluteToRelative (k + 2)
      ({p}ᶜ : Set (liftedHomotopySphere.{u} n))) := by
  let := liftedSpherePuncture_contractible n p
  exact (integralAbsoluteToRelativeIsoOfContractible k ({p}ᶜ)).toLinearEquiv.bijective

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralAbsoluteToRelative_liftedSphere_puncture_bijective then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralAbsoluteToRelative_liftedSphere_puncture_bijective"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralAbsoluteToRelative_liftedSphere_puncture_bijective ``Submission.DifferentialGeometry.Topology.integralAbsoluteToRelative_liftedSphere_puncture_bijective

end DifferentialGeometry.Topology
