import Submission.DifferentialGeometry.External.CanonicalTopology.Topology.Homology.CarrierMaps
import Submission.DifferentialGeometry.External.CanonicalTopology.Topology.Homology.ChainSupport

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

/-! # Exact carriers of chains in an original subspace -/

noncomputable section

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicTopology _root_.ContinuousMap _root_.Set _root_.Module

universe u

namespace DifferentialGeometry.Topology

variable {X : Type u} [TopologicalSpace X]

/-- The SAME intersection, viewed as a subset of the original subspace B. -/
def subspaceIntersection (A B : Set X) : Set B := {b | b.val ∈ A}

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.subspaceIntersection then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.subspaceIntersection"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.subspaceIntersection ``Submission.DifferentialGeometry.Topology.subspaceIntersection

/-- An original chain on B is carried by A inside B exactly when its
SAME original ambient inclusion is carried by A. -/
theorem integralSingularChainsIn_subspace_iff (n : ℕ) (A B : Set X)
    (c : (integralSingularChains B).X n) :
    c ∈ integralSingularChainsIn n (subspaceIntersection A B) ↔
      (integralSingularChainMap (singularSubspaceInclusion B)).f n c ∈ integralSingularChainsIn n A := by
  constructor
  · intro hc
    exact integralSingularChainsIn_map n (singularSubspaceInclusion B) (fun _ h => h) hc
  · intro hc
    have hB : (integralSingularChainMap (singularSubspaceInclusion B)).f n c ∈
        integralSingularChainsIn n B := by
      rw [integralSingularChainsIn_eq_range]
      exact ⟨c, rfl⟩
    have hAB : (integralSingularChainMap (singularSubspaceInclusion B)).f n c ∈
        integralSingularChainsIn n (A ∩ B) := by
      rw [integralSingularChainsIn_inter]
      exact ⟨hc, hB⟩
    let b := integralSingularChainRestriction n (A ∩ B)
      ⟨(integralSingularChainMap (singularSubspaceInclusion B)).f n c, hAB⟩
    let f : C(↥(A ∩ B), subspaceIntersection A B) :=
      ⟨fun x => ⟨⟨x.val, x.property.2⟩, x.property.1⟩,
        (continuous_subtype_val.subtype_mk _).subtype_mk _⟩
    rw [integralSingularChainsIn_eq_range]
    refine ⟨(integralSingularChainMap f).f n b, ?_⟩
    apply integralSingularChainInclusion_injective n B
    have he : integralSingularChainMap f ≫
        integralSingularChainMap (singularSubspaceInclusion (subspaceIntersection A B)) ≫
          integralSingularChainMap (singularSubspaceInclusion B) =
            integralSingularChainMap (singularSubspaceInclusion (A ∩ B)) := by
      rw [← integralSingularChainMap_comp, ← integralSingularChainMap_comp]
      rfl
    have h := congrArg (fun k : integralSingularChains ↥(A ∩ B) ⟶ integralSingularChains X => k.f n b) he
    exact h.trans (integralSingularChainRestriction_inclusion n (A ∩ B) _)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralSingularChainsIn_subspace_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralSingularChainsIn_subspace_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralSingularChainsIn_subspace_iff ``Submission.DifferentialGeometry.Topology.integralSingularChainsIn_subspace_iff

end DifferentialGeometry.Topology
