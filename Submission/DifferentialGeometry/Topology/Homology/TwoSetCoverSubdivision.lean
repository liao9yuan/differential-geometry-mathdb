import Submission.DifferentialGeometry.Topology.Homology.ContractibleCoverChainEvaluation
import Submission.DifferentialGeometry.External.CanonicalTopology.Topology.Homology.TwoSetSmallChains
import Submission.DifferentialGeometry.External.CanonicalTopology.Topology.Homology.SubdivisionSmallness
import Submission.DifferentialGeometry.External.CanonicalTopology.Topology.Homology.CarrierRestriction
import Submission.DifferentialGeometry.External.CanonicalTopology.Topology.Homology.SubspaceCarriers

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicTopology _root_.ContinuousMap _root_.Set _root_.Module

universe u

namespace DifferentialGeometry.Topology

variable {X : Type u} [TopologicalSpace X]

theorem twoSetCover_isOpen (A B : Set X) (hA : IsOpen A) (hB : IsOpen B) :
    ∀ i : Bool, IsOpen (twoSetCover A B i) := by
  intro i
  cases i with
  | false => simpa [twoSetCover] using hA
  | true => simpa [twoSetCover] using hB

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.twoSetCover_isOpen then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.twoSetCover_isOpen"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.twoSetCover_isOpen ``Submission.DifferentialGeometry.Topology.twoSetCover_isOpen

omit [TopologicalSpace X] in
theorem twoSetCover_cover (A B : Set X) (hcover : A ∪ B = Set.univ) :
    ∀ x : X, ∃ i : Bool, x ∈ twoSetCover A B i := by
  intro x
  have hx : x ∈ A ∪ B := by rw [hcover]; exact _root_.Set.mem_univ x
  rcases hx with hx | hx
  · exact ⟨false, by simpa [twoSetCover] using hx⟩
  · exact ⟨true, by simpa [twoSetCover] using hx⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.twoSetCover_cover then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.twoSetCover_cover"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.twoSetCover_cover ``Submission.DifferentialGeometry.Topology.twoSetCover_cover

theorem integralSingularChainOfElement_add {M : ModuleCat.{u} ℤ} (c d : M) :
    integralSingularChainOfElement (c + d) =
      integralSingularChainOfElement c + integralSingularChainOfElement d := by
  apply integralSingularCoefficients_hom_ext
  simp [integralSingularChainOfElement]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralSingularChainOfElement_add then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralSingularChainOfElement_add"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralSingularChainOfElement_add ``Submission.DifferentialGeometry.Topology.integralSingularChainOfElement_add

theorem integralSingularChainOfElement_zero {M : ModuleCat.{u} ℤ} :
    integralSingularChainOfElement (0 : M) = 0 := by
  apply integralSingularCoefficients_hom_ext
  simp [integralSingularChainOfElement]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralSingularChainOfElement_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralSingularChainOfElement_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralSingularChainOfElement_zero ``Submission.DifferentialGeometry.Topology.integralSingularChainOfElement_zero

theorem integralSingularSubdivisionIterateChain_apply_one (n k : ℕ)
    (z : integralSingularCoefficients ⟶ (integralSingularChains X).X (n + 1)) :
    integralSingularSubdivisionIterateChain n k z (ULift.up (1 : ℤ)) =
      integralSingularSubdivisionIterate (n + 1) k (z (ULift.up (1 : ℤ))) := by
  rw [integralSingularSubdivisionIterateChain]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralSingularSubdivisionIterateChain_apply_one then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralSingularSubdivisionIterateChain_apply_one"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralSingularSubdivisionIterateChain_apply_one ``Submission.DifferentialGeometry.Topology.integralSingularSubdivisionIterateChain_apply_one

theorem exists_integralSingularSubdivisionIterate_split (n : ℕ) (A B : Set X)
    (hA : IsOpen A) (hB : IsOpen B) (hcover : A ∪ B = Set.univ)
    (z : integralSingularCoefficients ⟶ (integralSingularChains X).X (n + 2))
    (hz : z ≫ (integralSingularChains X).d (n + 2) (n + 1) = 0) :
    ∃ (k : ℕ) (zA : integralSingularCoefficients ⟶ (integralSingularChains A).X (n + 2))
      (zB : integralSingularCoefficients ⟶ (integralSingularChains B).X (n + 2))
      (a : integralSingularCoefficients ⟶
        (integralSingularChains (subspaceIntersection A B)).X (n + 1)),
      zA ≫ (integralSingularChainMap (singularSubspaceInclusion A)).f (n + 2) +
        zB ≫ (integralSingularChainMap (singularSubspaceInclusion B)).f (n + 2) =
          integralSingularSubdivisionIterateChain (n + 1) k z ∧
      a ≫ (integralSingularChainMap
          (singularSubspaceInclusion (subspaceIntersection A B))).f (n + 1) =
        zB ≫ (integralSingularChains B).d (n + 2) (n + 1) ∧
      a ≫ (integralSingularChains (subspaceIntersection A B)).d (n + 1) n = 0 := by
  obtain ⟨k, hk⟩ := exists_integralSingularSubdivisionIterate_small (n + 2) (twoSetCover A B)
    (twoSetCover_isOpen A B hA hB) (twoSetCover_cover A B hcover) (z (ULift.up 1))
  obtain ⟨a', b', hab⟩ := integralSingularTwoSetSmallChains_decompose (n + 2) A B
    ⟨integralSingularSubdivisionIterate (n + 2) k (z (ULift.up 1)), hk k le_rfl⟩
  have hz1 : (integralSingularChains X).d (n + 2) (n + 1) (z (ULift.up (1 : ℤ))) = 0 := by
    have h := congrArg (fun f : integralSingularCoefficients ⟶ (integralSingularChains X).X (n + 1) =>
      f (ULift.up (1 : ℤ))) hz
    simpa using h
  have hS : (integralSingularChains X).d (n + 2) (n + 1)
      (integralSingularSubdivisionIterate (n + 2) k (z (ULift.up (1 : ℤ)))) = 0 := by
    rw [integralSingularSubdivisionIterate_boundary (n + 1) k (z (ULift.up (1 : ℤ))), hz1]
    exact map_zero _
  have hbdy :
      (integralSingularChainMap (singularSubspaceInclusion A)).f (n + 1)
          ((integralSingularChains A).d (n + 2) (n + 1) a') +
        (integralSingularChainMap (singularSubspaceInclusion B)).f (n + 1)
          ((integralSingularChains B).d (n + 2) (n + 1) b') = 0 := by
    have h := congrArg (fun c => (integralSingularChains X).d (n + 2) (n + 1) c) hab
    rw [map_add, ← integralSingularChainMap_boundary, ← integralSingularChainMap_boundary,
      hS] at h
    exact h
  have hW : (integralSingularChainMap (singularSubspaceInclusion B)).f (n + 1)
      ((integralSingularChains B).d (n + 2) (n + 1) b') ∈ integralSingularChainsIn (n + 1) A := by
    have hneg : (integralSingularChainMap (singularSubspaceInclusion B)).f (n + 1)
        ((integralSingularChains B).d (n + 2) (n + 1) b') =
        - (integralSingularChainMap (singularSubspaceInclusion A)).f (n + 1)
          ((integralSingularChains A).d (n + 2) (n + 1) a') :=
      eq_neg_of_add_eq_zero_right hbdy
    rw [hneg]
    exact Submodule.neg_mem _ (by
      rw [integralSingularChainsIn_eq_range]
      exact ⟨_, rfl⟩)
  have hW' : (integralSingularChains B).d (n + 2) (n + 1) b' ∈
      integralSingularChainsIn (n + 1) (subspaceIntersection A B) :=
    (integralSingularChainsIn_subspace_iff (n + 1) A B _).mpr hW
  have hac_inclusion : (integralSingularChainMap
      (singularSubspaceInclusion (subspaceIntersection A B))).f (n + 1)
      (integralSingularChainRestriction (n + 1) (subspaceIntersection A B)
        ⟨(integralSingularChains B).d (n + 2) (n + 1) b', hW'⟩) =
      (integralSingularChains B).d (n + 2) (n + 1) b' :=
    integralSingularChainRestriction_inclusion (n + 1) (subspaceIntersection A B) _
  have hac_cycle : (integralSingularChains (subspaceIntersection A B)).d (n + 1) n
      (integralSingularChainRestriction (n + 1) (subspaceIntersection A B)
        ⟨(integralSingularChains B).d (n + 2) (n + 1) b', hW'⟩) = 0 := by
    have hW0 : (integralSingularChains B).d (n + 1) n
        ((integralSingularChains B).d (n + 2) (n + 1) b') = 0 := by
      have h := congrArg (fun f : (integralSingularChains B).X (n + 2) ⟶
        (integralSingularChains B).X n => f b')
        ((integralSingularChains B).d_comp_d (n + 2) (n + 1) n)
      simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero,
        LinearMap.zero_apply] using h
    have h := integralSingularChainRestriction_boundary (n) (subspaceIntersection A B)
      ⟨(integralSingularChains B).d (n + 2) (n + 1) b', hW'⟩
    simp only [hW0] at h
    have hz : integralSingularChainRestriction n (subspaceIntersection A B)
        (0 : integralSingularChainsIn n (subspaceIntersection A B)) = 0 := map_zero _
    rw [← h]
    exact hz
  refine ⟨k, integralSingularChainOfElement a', integralSingularChainOfElement b',
    integralSingularChainOfElement (integralSingularChainRestriction (n + 1)
      (subspaceIntersection A B)
      ⟨(integralSingularChains B).d (n + 2) (n + 1) b', hW'⟩), ?_, ?_, ?_⟩
  · rw [integralSingularChainOfElement_comp, integralSingularChainOfElement_comp,
      ← integralSingularChainOfElement_add, hab]
    apply integralSingularCoefficients_hom_ext
    rw [integralSingularChainOfElement_apply_one, integralSingularSubdivisionIterateChain_apply_one]
  · rw [integralSingularChainOfElement_comp, integralSingularChainOfElement_comp, hac_inclusion]
  · rw [integralSingularChainOfElement_comp, hac_cycle, integralSingularChainOfElement_zero]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.exists_integralSingularSubdivisionIterate_split then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.exists_integralSingularSubdivisionIterate_split"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.exists_integralSingularSubdivisionIterate_split ``Submission.DifferentialGeometry.Topology.exists_integralSingularSubdivisionIterate_split

theorem exists_integralHomologyContractibleCoverEquiv_liftCycles_eq
    (n : ℕ) (A B : Set X) [ContractibleSpace A] [ContractibleSpace B]
    (hA : IsOpen A) (hB : IsOpen B) (hcover : A ∪ B = Set.univ)
    (z : integralSingularCoefficients ⟶ (integralSingularChains X).X (n + 2))
    (hz : z ≫ (integralSingularChains X).d (n + 2) (n + 1) = 0) :
    ∃ (a : integralSingularCoefficients ⟶
        (integralSingularChains (subspaceIntersection A B)).X (n + 1))
      (ha : a ≫ (integralSingularChains (subspaceIntersection A B)).d (n + 1) n = 0),
      integralHomologyContractibleCoverEquiv n A B hA hB hcover
        (((integralSingularChains X).liftCycles z (n + 1)
          ((ComplexShape.down ℕ).next_eq' (by rfl)) hz ≫
          (integralSingularChains X).homologyπ (n + 2)) (ULift.up 1)) =
        (((integralSingularChains (subspaceIntersection A B)).liftCycles a n
          ((ComplexShape.down ℕ).next_eq' (by rfl)) ha ≫
          (integralSingularChains (subspaceIntersection A B)).homologyπ (n + 1))
          (ULift.up 1)) := by
  obtain ⟨k, zA, zB, a, hsplit, ha, hac⟩ :=
    exists_integralSingularSubdivisionIterate_split n A B hA hB hcover z hz
  exact ⟨a, hac, integralHomologyContractibleCoverEquiv_liftCycles_apply_of_subdivision
    n k A B hA hB hcover z hz zA zB hsplit a hac ha⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.exists_integralHomologyContractibleCoverEquiv_liftCycles_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.exists_integralHomologyContractibleCoverEquiv_liftCycles_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.exists_integralHomologyContractibleCoverEquiv_liftCycles_eq ``Submission.DifferentialGeometry.Topology.exists_integralHomologyContractibleCoverEquiv_liftCycles_eq

end DifferentialGeometry.Topology
