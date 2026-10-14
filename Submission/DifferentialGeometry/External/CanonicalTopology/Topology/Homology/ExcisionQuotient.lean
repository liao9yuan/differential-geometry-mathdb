import Submission.DifferentialGeometry.External.CanonicalTopology.Topology.Homology.TwoSetSmallChains
import Submission.DifferentialGeometry.External.CanonicalTopology.Topology.Homology.ChainCokernelElements

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

/-! # The exact original relative-quotient identification for a pair of subspaces -/

noncomputable section

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicTopology _root_.ContinuousMap _root_.Set _root_.Module

universe u

namespace DifferentialGeometry.Topology

variable {X : Type u} [TopologicalSpace X]

/-- The original relative complex of B modulo B ∩ A maps to the SAME
two-set small complex modulo the original chains on A. -/
def integralExcisionSmallMap (A B : Set X) :
    integralRelativeChains (subspaceIntersection A B) ⟶ integralSmallRelativeChains (twoSetCover A B) false :=
  cokernel.map _ _
    (integralSingularChainMap (singularPairRestriction (singularSubspaceInclusion B)
      (subspaceIntersection_mapsTo A B)))
    (integralSingularChainToSmall (twoSetCover A B) _root_.Bool.true)
    (integralSingularTwoSetSmall_square A B)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralExcisionSmallMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralExcisionSmallMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralExcisionSmallMap ``Submission.DifferentialGeometry.Topology.integralExcisionSmallMap

/-- This map of ORIGINAL quotient complexes is an actual isomorphism.
The proof uses exact carrier intersection and decomposition of actual small
chains. No openness or excision conclusion is assumed. -/
instance integralExcisionSmallMap_isIso (A B : Set X) :
    IsIso (integralExcisionSmallMap A B) := by
  unfold integralExcisionSmallMap
  apply isIso_chainCokernelMap_of_representatives _ _
    (integralSingularChainMap (singularPairRestriction (singularSubspaceInclusion B)
      (subspaceIntersection_mapsTo A B))) _ (integralSingularTwoSetSmall_square A B)
  · intro n c b hb
    have he := congrArg Subtype.val hb
    change (integralSingularChainMap (singularSubspaceInclusion A)).f n b =
      (integralSingularChainMap (singularSubspaceInclusion B)).f n c at he
    have hcA : (integralSingularChainMap (singularSubspaceInclusion B)).f n c ∈
        integralSingularChainsIn n A := by
      rw [← he, integralSingularChainsIn_eq_range]
      exact ⟨b, rfl⟩
    have hc := (integralSingularChainsIn_subspace_iff n A B c).mpr hcA
    rw [integralSingularChainsIn_eq_range] at hc
    exact hc
  · intro n d
    obtain ⟨a, b, hab⟩ := integralSingularTwoSetSmallChains_decompose n A B d
    refine ⟨b, a, ?_⟩
    apply Subtype.ext
    change (integralSingularChainMap (singularSubspaceInclusion A)).f n a =
      d.val - (integralSingularChainMap (singularSubspaceInclusion B)).f n b
    rw [← hab]
    abel

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralExcisionSmallMap_isIso then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralExcisionSmallMap_isIso"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralExcisionSmallMap_isIso ``Submission.DifferentialGeometry.Topology.integralExcisionSmallMap_isIso

set_option backward.isDefEq.respectTransparency false in
/-- Composing with the small-relative comparison recovers the SAME
original relative pair map (B,B ∩ A) → (X,A), exactly. -/
theorem integralExcisionSmallMap_comparison (A B : Set X) :
    integralExcisionSmallMap A B ≫ integralSmallRelativeComparison (twoSetCover A B) _root_.Bool.false =
      integralRelativeChainMap (singularSubspaceInclusion B) (subspaceIntersection_mapsTo A B) := by
  apply (_root_.CategoryTheory.cancel_epi (cokernel.π (integralSingularChainMap
    (singularSubspaceInclusion (subspaceIntersection A B))))).mp
  simp only [Category.assoc, integralExcisionSmallMap, integralSmallRelativeComparison,
    integralRelativeChainMap, cokernel.π_desc_assoc, cokernel.π_desc]
  rw [← Category.assoc, integralSingularChainToSmall_inclusion]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralExcisionSmallMap_comparison then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralExcisionSmallMap_comparison"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralExcisionSmallMap_comparison ``Submission.DifferentialGeometry.Topology.integralExcisionSmallMap_comparison

end DifferentialGeometry.Topology
