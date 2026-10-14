import Submission.DifferentialGeometry.External.CanonicalTopology.Topology.Homology.OpenExcision

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

/-! # The original pair sequence with a contractible subspace -/

noncomputable section

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicTopology _root_.ContinuousMap _root_.Set _root_.Module

universe u

namespace DifferentialGeometry.Topology

variable {X : Type u} [TopologicalSpace X]

/-- For a contractible original subspace, the actual absolute-to-relative
map is an isomorphism in degrees at least two. -/
theorem integralAbsoluteToRelative_isIso_of_contractible (n : ℕ) (A : Set X) [ContractibleSpace A] :
    IsIso (HomologicalComplex.homologyMap (integralRelativeChainSequence A).g (n + 2)) := by
  let := integralSingularHomology_subsingleton_of_contractible (n + 2) (by omega) A
  let := integralSingularHomology_subsingleton_of_contractible (n + 1) (by omega) A
  have hz₂ := ModuleCat.isZero_of_subsingleton (integralSingularHomology (n + 2) A)
  have hz₁ := ModuleCat.isZero_of_subsingleton (integralSingularHomology (n + 1) A)
  have hm := ((integralRelativeChainSequence_shortExact A).homology_exact₂ (n + 2)).mono_g
    (hz₂.eq_of_src _ _)
  have he := ((integralRelativeChainSequence_shortExact A).homology_exact₃ (n + 2) (n + 1) (by simp)).epi_f
    (hz₁.eq_of_tgt _ _)
  exact _root_.CategoryTheory.isIso_of_mono_of_epi _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralAbsoluteToRelative_isIso_of_contractible then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralAbsoluteToRelative_isIso_of_contractible"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralAbsoluteToRelative_isIso_of_contractible ``Submission.DifferentialGeometry.Topology.integralAbsoluteToRelative_isIso_of_contractible

/-- The isomorphism uses the SAME actual quotient projection on homology. -/
def integralAbsoluteToRelativeIsoOfContractible (n : ℕ) (A : Set X) [ContractibleSpace A] :
    integralSingularHomology (n + 2) X ≅ integralRelativeHomology (n + 2) A := by
  exact @_root_.CategoryTheory.asIso _ _ _ _ (HomologicalComplex.homologyMap (integralRelativeChainSequence A).g (n + 2))
    (integralAbsoluteToRelative_isIso_of_contractible n A)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralAbsoluteToRelativeIsoOfContractible then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralAbsoluteToRelativeIsoOfContractible"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralAbsoluteToRelativeIsoOfContractible ``Submission.DifferentialGeometry.Topology.integralAbsoluteToRelativeIsoOfContractible

/-- A cover by two actual contractible open subspaces identifies original
homology in degree n+2 with original intersection homology in degree n+1,
using the SAME original pair maps and connecting homomorphism. -/
def integralHomologyContractibleCoverEquiv (n : ℕ) (A B : Set X)
    [ContractibleSpace A] [ContractibleSpace B]
    (hA : IsOpen A) (hB : IsOpen B) (hcover : A ∪ B = _root_.Set.univ) :
    integralSingularHomology (n + 2) X ≃ₗ[ℤ] integralSingularHomology (n + 1) (subspaceIntersection A B) :=
  ((integralAbsoluteToRelativeIsoOfContractible n A).toLinearEquiv.trans
    (integralRelativeOpenExcisionIso (n + 2) A B hA hB hcover).symm.toLinearEquiv).trans
      (integralRelativeConnectingEquivOfContractible (n + 1) (by omega) (subspaceIntersection A B))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralHomologyContractibleCoverEquiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralHomologyContractibleCoverEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralHomologyContractibleCoverEquiv ``Submission.DifferentialGeometry.Topology.integralHomologyContractibleCoverEquiv

end DifferentialGeometry.Topology
