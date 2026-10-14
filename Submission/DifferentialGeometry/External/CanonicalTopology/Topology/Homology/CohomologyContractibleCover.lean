import Submission.DifferentialGeometry.External.CanonicalTopology.Topology.Homology.RelativeCohomologyVanishing
import Submission.DifferentialGeometry.External.CanonicalTopology.Topology.Homology.CochainExcision

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

universe u

namespace DifferentialGeometry.Topology

def integralCohomologyContractibleCoverEquiv
    {X : Type u} [TopologicalSpace X] (n : ℕ) (A B : Set X)
    [ContractibleSpace A] [ContractibleSpace B]
    (hA : IsOpen A) (hB : IsOpen B) (hcover : A ∪ B = Set.univ) :
    integralSingularCohomology (n + 2) X ≃ₗ[ℤ]
      integralSingularCohomology (n + 1) (subspaceIntersection A B) :=
  ((LinearEquiv.ofBijective (integralRelativeToAbsoluteCohomology (n + 2) A)
    (integralRelativeToAbsoluteCohomology_bijective_of_contractibleSpace (n + 1) A)).symm.trans
      (LinearEquiv.ofBijective
        (integralRelativeCohomologyMap (n + 2) (singularSubspaceInclusion B)
          (subspaceIntersection_mapsTo A B))
        (integralRelativeCohomologyMap_openExcision (n + 2) A B hA hB hcover))).trans
          (LinearEquiv.ofBijective
            (integralRelativeCohomologyConnecting (n + 1) (subspaceIntersection A B))
            (integralRelativeCohomologyConnecting_bijective_of_contractibleSpace
              (n + 1) (Nat.succ_ne_zero n) (subspaceIntersection A B))).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralCohomologyContractibleCoverEquiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralCohomologyContractibleCoverEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralCohomologyContractibleCoverEquiv ``Submission.DifferentialGeometry.Topology.integralCohomologyContractibleCoverEquiv

theorem integralCohomologyContractibleCoverEquiv_connecting
    {X : Type u} [TopologicalSpace X] (n : ℕ) (A B : Set X)
    [ContractibleSpace A] [ContractibleSpace B]
    (hA : IsOpen A) (hB : IsOpen B) (hcover : A ∪ B = Set.univ)
    (α : integralRelativeCohomology (n + 2) A) :
    integralRelativeCohomologyConnecting (n + 1) (subspaceIntersection A B)
      (integralCohomologyContractibleCoverEquiv n A B hA hB hcover
        (integralRelativeToAbsoluteCohomology (n + 2) A α)) =
      integralRelativeCohomologyMap (n + 2) (singularSubspaceInclusion B)
        (subspaceIntersection_mapsTo A B) α := by
  let eA := LinearEquiv.ofBijective (integralRelativeToAbsoluteCohomology (n + 2) A)
    (integralRelativeToAbsoluteCohomology_bijective_of_contractibleSpace (n + 1) A)
  let eδ := LinearEquiv.ofBijective
    (integralRelativeCohomologyConnecting (n + 1) (subspaceIntersection A B))
    (integralRelativeCohomologyConnecting_bijective_of_contractibleSpace
      (n + 1) (Nat.succ_ne_zero n) (subspaceIntersection A B))
  change eδ (eδ.symm
    (integralRelativeCohomologyMap (n + 2) (singularSubspaceInclusion B)
      (subspaceIntersection_mapsTo A B) (eA.symm (eA α)))) = _
  rw [LinearEquiv.symm_apply_apply, LinearEquiv.apply_symm_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralCohomologyContractibleCoverEquiv_connecting then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralCohomologyContractibleCoverEquiv_connecting"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralCohomologyContractibleCoverEquiv_connecting ``Submission.DifferentialGeometry.Topology.integralCohomologyContractibleCoverEquiv_connecting

theorem integralCohomologyContractibleCoverEquiv_symm_apply
    {X : Type u} [TopologicalSpace X] (n : ℕ) (A B : Set X)
    [ContractibleSpace A] [ContractibleSpace B]
    (hA : IsOpen A) (hB : IsOpen B) (hcover : A ∪ B = Set.univ)
    (β : integralSingularCohomology (n + 1) (subspaceIntersection A B)) :
    (integralCohomologyContractibleCoverEquiv n A B hA hB hcover).symm β =
      integralRelativeToAbsoluteCohomology (n + 2) A
        ((LinearEquiv.ofBijective
          (integralRelativeCohomologyMap (n + 2) (singularSubspaceInclusion B)
            (subspaceIntersection_mapsTo A B))
          (integralRelativeCohomologyMap_openExcision (n + 2) A B hA hB hcover)).symm
            (integralRelativeCohomologyConnecting (n + 1) (subspaceIntersection A B) β)) := by
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralCohomologyContractibleCoverEquiv_symm_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralCohomologyContractibleCoverEquiv_symm_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralCohomologyContractibleCoverEquiv_symm_apply ``Submission.DifferentialGeometry.Topology.integralCohomologyContractibleCoverEquiv_symm_apply

end DifferentialGeometry.Topology

end
