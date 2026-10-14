import Mathlib.Topology.Compactification.OnePoint.Basic
import Submission.DifferentialGeometry.Topology.Homology.CohomologyHomeomorphInvariance
import Submission.DifferentialGeometry.Topology.Homology.HomologyTwoFrontier
import Submission.DifferentialGeometry.Topology.Homology.SpherePuncture
import Submission.DifferentialGeometry.External.CanonicalTopology.Topology.Homology.SphereHomologyVanishing
import Submission.DifferentialGeometry.External.CanonicalTopology.Topology.Homology.SphereTopHomology
import Submission.DifferentialGeometry.Topology.FundamentalGroup.Sphere

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicTopology _root_.ContinuousMap _root_.Set
open scoped _root_.Topology

universe u

namespace DifferentialGeometry.Topology

abbrev integralCompactSupportCohomologyOne (X : Type u) [TopologicalSpace X] :
    ModuleCat.{u} ℤ :=
  integralSingularCohomology 1 (OnePoint X)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralCompactSupportCohomologyOne then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralCompactSupportCohomologyOne"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralCompactSupportCohomologyOne ``Submission.DifferentialGeometry.Topology.integralCompactSupportCohomologyOne

def noncompactPoincareDualityTwoOne (X : Type u) [TopologicalSpace X] : Prop :=
  Nonempty (integralSingularHomology 2 X ≅ integralCompactSupportCohomologyOne X)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.noncompactPoincareDualityTwoOne then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.noncompactPoincareDualityTwoOne"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.noncompactPoincareDualityTwoOne ``Submission.DifferentialGeometry.Topology.noncompactPoincareDualityTwoOne

variable {X : Type u} [TopologicalSpace X]

theorem noncompactPoincareDualityTwoOne_of_subsingleton
    [Subsingleton (integralSingularHomology 2 X)]
    [Subsingleton (integralCompactSupportCohomologyOne X)] :
    noncompactPoincareDualityTwoOne X := by
  refine ⟨?_⟩
  refine ⟨ModuleCat.ofHom 0, ModuleCat.ofHom 0, ?_, ?_⟩
  · apply ModuleCat.hom_ext
    ext x
    exact Subsingleton.elim _ _
  · apply ModuleCat.hom_ext
    ext x
    exact Subsingleton.elim _ _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.noncompactPoincareDualityTwoOne_of_subsingleton then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.noncompactPoincareDualityTwoOne_of_subsingleton"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.noncompactPoincareDualityTwoOne_of_subsingleton ``Submission.DifferentialGeometry.Topology.noncompactPoincareDualityTwoOne_of_subsingleton

theorem subsingleton_integralSingularHomology_two_of_noncompactPoincareDualityTwoOne
    (h : noncompactPoincareDualityTwoOne X)
    [Subsingleton (integralCompactSupportCohomologyOne X)] :
    Subsingleton (integralSingularHomology 2 X) := by
  refine ⟨fun a b => ?_⟩
  obtain ⟨e⟩ := h
  have hb : Function.Bijective
      (e.hom.hom : integralSingularHomology 2 X → integralCompactSupportCohomologyOne X) :=
    (ConcreteCategory.isIso_iff_bijective e.hom).mp inferInstance
  exact hb.1 (Subsingleton.elim _ _)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.subsingleton_integralSingularHomology_two_of_noncompactPoincareDualityTwoOne then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.subsingleton_integralSingularHomology_two_of_noncompactPoincareDualityTwoOne"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.subsingleton_integralSingularHomology_two_of_noncompactPoincareDualityTwoOne ``Submission.DifferentialGeometry.Topology.subsingleton_integralSingularHomology_two_of_noncompactPoincareDualityTwoOne

variable [T2Space X] [CompactSpace X]

noncomputable def compactSupportCohomologyComplSingletonHomeomorph (x : X) :
    OnePoint ({x}ᶜ : Set X) ≃ₜ X :=
  OnePoint.equivOfIsEmbeddingOfRangeEq x Subtype.val Topology.IsEmbedding.subtypeVal (by
    ext y
    simp only [Set.mem_range, Set.mem_compl_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨z, rfl⟩
      exact z.2
    · intro hy
      exact ⟨⟨y, hy⟩, rfl⟩)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.compactSupportCohomologyComplSingletonHomeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.compactSupportCohomologyComplSingletonHomeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.compactSupportCohomologyComplSingletonHomeomorph ``Submission.DifferentialGeometry.Topology.compactSupportCohomologyComplSingletonHomeomorph

theorem nonempty_linearEquiv_compactSupportCohomologyOne_compl_singleton (x : X) :
    Nonempty (integralCompactSupportCohomologyOne ({x}ᶜ : Set X) ≃ₗ[ℤ]
      integralSingularCohomology 1 X) :=
  ⟨integralSingularCohomologyEquivOfHomeomorph
    (compactSupportCohomologyComplSingletonHomeomorph x) 1⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.nonempty_linearEquiv_compactSupportCohomologyOne_compl_singleton then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.nonempty_linearEquiv_compactSupportCohomologyOne_compl_singleton"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.nonempty_linearEquiv_compactSupportCohomologyOne_compl_singleton ``Submission.DifferentialGeometry.Topology.nonempty_linearEquiv_compactSupportCohomologyOne_compl_singleton

theorem subsingleton_integralCompactSupportCohomologyOne_compl_singleton (x : X)
    [Subsingleton (integralSingularCohomology 1 X)] :
    Subsingleton (integralCompactSupportCohomologyOne ({x}ᶜ : Set X)) :=
  subsingleton_integralSingularCohomology_of_homeomorph
    (compactSupportCohomologyComplSingletonHomeomorph x).symm 1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.subsingleton_integralCompactSupportCohomologyOne_compl_singleton then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.subsingleton_integralCompactSupportCohomologyOne_compl_singleton"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.subsingleton_integralCompactSupportCohomologyOne_compl_singleton ``Submission.DifferentialGeometry.Topology.subsingleton_integralCompactSupportCohomologyOne_compl_singleton

theorem subsingleton_integralSingularHomology_two_compl_singleton_of_noncompactPoincareDuality
    (x : X) (h : noncompactPoincareDualityTwoOne ({x}ᶜ : Set X))
    [Subsingleton (integralSingularCohomology 1 X)] :
    Subsingleton (integralSingularHomology 2 ({x}ᶜ : Set X)) :=
  @subsingleton_integralSingularHomology_two_of_noncompactPoincareDualityTwoOne
    ({x}ᶜ : Set X) inferInstance h
    (subsingleton_integralCompactSupportCohomologyOne_compl_singleton x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.subsingleton_integralSingularHomology_two_compl_singleton_of_noncompactPoincareDuality then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.subsingleton_integralSingularHomology_two_compl_singleton_of_noncompactPoincareDuality"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.subsingleton_integralSingularHomology_two_compl_singleton_of_noncompactPoincareDuality ``Submission.DifferentialGeometry.Topology.subsingleton_integralSingularHomology_two_compl_singleton_of_noncompactPoincareDuality

theorem subsingleton_integralSingularHomology_two_sphereThree_compl_singleton
    (v : SphereThree) :
    Subsingleton (integralSingularHomology 2 ({v}ᶜ : Set SphereThree)) := by
  exact @integralSingularHomology_subsingleton_of_contractible 2 (by norm_num)
    ({v}ᶜ : Set SphereThree) inferInstance (spherePuncture_contractible v)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.subsingleton_integralSingularHomology_two_sphereThree_compl_singleton then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.subsingleton_integralSingularHomology_two_sphereThree_compl_singleton"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.subsingleton_integralSingularHomology_two_sphereThree_compl_singleton ``Submission.DifferentialGeometry.Topology.subsingleton_integralSingularHomology_two_sphereThree_compl_singleton

theorem noncompactPoincareDualityTwoOne_sphereThree_compl_singleton (v : SphereThree) :
    noncompactPoincareDualityTwoOne ({v}ᶜ : Set SphereThree) :=
  @noncompactPoincareDualityTwoOne_of_subsingleton
    ({v}ᶜ : Set SphereThree) inferInstance
    (subsingleton_integralSingularHomology_two_sphereThree_compl_singleton v)
    (@subsingleton_integralCompactSupportCohomologyOne_compl_singleton SphereThree _ _ _ v
      (integralSingularCohomology_one_subsingleton (X := SphereThree)))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.noncompactPoincareDualityTwoOne_sphereThree_compl_singleton then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.noncompactPoincareDualityTwoOne_sphereThree_compl_singleton"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.noncompactPoincareDualityTwoOne_sphereThree_compl_singleton ``Submission.DifferentialGeometry.Topology.noncompactPoincareDualityTwoOne_sphereThree_compl_singleton

end DifferentialGeometry.Topology
