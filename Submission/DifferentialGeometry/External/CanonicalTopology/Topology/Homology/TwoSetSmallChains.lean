import Submission.DifferentialGeometry.External.CanonicalTopology.Topology.Homology.SmallRelative
import Submission.DifferentialGeometry.External.CanonicalTopology.Topology.Homology.SubspaceCarriers

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

/-! # The actual two-set small complex and its quotient square -/

noncomputable section

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicTopology _root_.ContinuousMap _root_.Set _root_.Module

universe u

namespace DifferentialGeometry.Topology

variable {X : Type u} [TopologicalSpace X]

/-- The specified two original subspaces, in the order A, B. -/
abbrev twoSetCover (A B : Set X) : Bool → Set X := fun b => if b then B else A

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.twoSetCover then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.twoSetCover"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.twoSetCover ``Submission.DifferentialGeometry.Topology.twoSetCover

/-- Small chains for this pair are exactly sums of original A- and B-carried chains. -/
theorem integralSingularTwoSetSmallChains_eq (n : ℕ) (A B : Set X) :
    integralSingularSmallChains n (twoSetCover A B) =
      integralSingularChainsIn n A ⊔ integralSingularChainsIn n B := by
  simp [integralSingularSmallChains, twoSetCover, iSup_bool_eq, sup_comm]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralSingularTwoSetSmallChains_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralSingularTwoSetSmallChains_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralSingularTwoSetSmallChains_eq ``Submission.DifferentialGeometry.Topology.integralSingularTwoSetSmallChains_eq

/-- Every actual small chain for the pair decomposes into actual chains
on A and B through their SAME original inclusions. -/
theorem integralSingularTwoSetSmallChains_decompose (n : ℕ) (A B : Set X)
    (c : integralSingularSmallChains n (twoSetCover A B)) :
    ∃ a : (integralSingularChains A).X n, ∃ b : (integralSingularChains B).X n,
      (integralSingularChainMap (singularSubspaceInclusion A)).f n a +
        (integralSingularChainMap (singularSubspaceInclusion B)).f n b = c.val := by
  have hc := (integralSingularTwoSetSmallChains_eq n A B).le c.property
  rw [Submodule.mem_sup] at hc
  obtain ⟨a, ha, b, hb, hab⟩ := hc
  rw [integralSingularChainsIn_eq_range] at ha hb
  obtain ⟨a', rfl⟩ := ha
  obtain ⟨b', rfl⟩ := hb
  exact ⟨a', b', hab⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralSingularTwoSetSmallChains_decompose then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralSingularTwoSetSmallChains_decompose"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralSingularTwoSetSmallChains_decompose ``Submission.DifferentialGeometry.Topology.integralSingularTwoSetSmallChains_decompose

/-- The original map of pairs (B, B ∩ A) → (X,A). -/
theorem subspaceIntersection_mapsTo (A B : Set X) :
    MapsTo (singularSubspaceInclusion B) (subspaceIntersection A B) A := fun _ h => h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.subspaceIntersection_mapsTo then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.subspaceIntersection_mapsTo"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.subspaceIntersection_mapsTo ``Submission.DifferentialGeometry.Topology.subspaceIntersection_mapsTo

/-- The SAME original pair square factors through the two-set small complex. -/
theorem integralSingularTwoSetSmall_square (A B : Set X) :
    integralSingularChainMap (singularSubspaceInclusion (subspaceIntersection A B)) ≫
      integralSingularChainToSmall (twoSetCover A B) _root_.Bool.true =
        integralSingularChainMap (singularPairRestriction (singularSubspaceInclusion B)
          (subspaceIntersection_mapsTo A B)) ≫ integralSingularChainToSmall (twoSetCover A B) false := by
  apply (_root_.CategoryTheory.cancel_mono (integralSingularSmallInclusion (twoSetCover A B))).mp
  exact integralSingularChainMap_pair_square (singularSubspaceInclusion B) (subspaceIntersection_mapsTo A B)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralSingularTwoSetSmall_square then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralSingularTwoSetSmall_square"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralSingularTwoSetSmall_square ``Submission.DifferentialGeometry.Topology.integralSingularTwoSetSmall_square

end DifferentialGeometry.Topology
