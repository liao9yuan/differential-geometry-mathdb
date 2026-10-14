import Submission.DifferentialGeometry.Topology.Homology.Relative.Basic
import Submission.DifferentialGeometry.Topology.Homology.LiftedSquareBoundaryDegree
import Submission.DifferentialGeometry.Topology.Homology.SphereGeneratorCriterion

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicTopology _root_.ContinuousMap _root_.Set _root_.Module
open scoped _root_.Topology

universe u

namespace DifferentialGeometry.Topology

variable {X : Type u} [TopologicalSpace X]

theorem integralAbsoluteToRelative_singleton_injective (b : X) (n : ℕ) (hn : n ≠ 0) :
    Function.Injective (integralAbsoluteToRelative n ({b} : Set X)) :=
  integralAbsoluteToRelative_injective_of_subsingleton n {b}
    (integralSingularHomology_subsingleton_of_contractible n hn ({b} : Set X))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralAbsoluteToRelative_singleton_injective then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralAbsoluteToRelative_singleton_injective"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralAbsoluteToRelative_singleton_injective ``Submission.DifferentialGeometry.Topology.integralAbsoluteToRelative_singleton_injective

theorem integralAbsoluteToRelative_singleton_surjective (b : X) {n : ℕ} (hn : 1 < n) :
    Function.Surjective (integralAbsoluteToRelative n ({b} : Set X)) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hspec : LinearMap.range (integralAbsoluteToRelative (m + 1) ({b} : Set X)) =
      LinearMap.ker (integralRelativeConnecting m ({b} : Set X)) :=
    (LinearMap.exact_iff.mp (integralRelative_exact_relative m ({b} : Set X))).symm
  have hzero : integralRelativeConnecting m ({b} : Set X) = 0 := by
    refine LinearMap.ext fun y => ?_
    let hsub : Subsingleton (integralSingularHomology m ({b} : Set X)) :=
      integralSingularHomology_subsingleton_of_contractible m (by omega) ({b} : Set X)
    exact @Subsingleton.elim _ hsub _ _
  exact LinearMap.range_eq_top.mp (by rw [hspec, hzero, LinearMap.ker_zero])

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralAbsoluteToRelative_singleton_surjective then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralAbsoluteToRelative_singleton_surjective"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralAbsoluteToRelative_singleton_surjective ``Submission.DifferentialGeometry.Topology.integralAbsoluteToRelative_singleton_surjective

theorem integralAbsoluteToRelative_singleton_bijective (b : X) {n : ℕ} (hn : 1 < n) :
    Function.Bijective (integralAbsoluteToRelative n ({b} : Set X)) :=
  ⟨integralAbsoluteToRelative_singleton_injective b n (by omega),
    integralAbsoluteToRelative_singleton_surjective b hn⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralAbsoluteToRelative_singleton_bijective then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralAbsoluteToRelative_singleton_bijective"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralAbsoluteToRelative_singleton_bijective ``Submission.DifferentialGeometry.Topology.integralAbsoluteToRelative_singleton_bijective

theorem linearEquiv_symm_toLinearMap_apply {M N : Type u} [AddCommGroup M] [Module ℤ M]
    [AddCommGroup N] [Module ℤ N] (e : M ≃ₗ[ℤ] N) (y : M) :
    e.symm.toLinearMap (e y) = y :=
  LinearEquiv.symm_apply_apply e y

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.linearEquiv_symm_toLinearMap_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.linearEquiv_symm_toLinearMap_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.linearEquiv_symm_toLinearMap_apply ``Submission.DifferentialGeometry.Topology.linearEquiv_symm_toLinearMap_apply

theorem linearEquiv_toLinearMap_apply {M N : Type u} [AddCommGroup M] [Module ℤ M]
    [AddCommGroup N] [Module ℤ N] (e : M ≃ₗ[ℤ] N) (y : M) :
    e.toLinearMap y = e y := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.linearEquiv_toLinearMap_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.linearEquiv_toLinearMap_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.linearEquiv_toLinearMap_apply ``Submission.DifferentialGeometry.Topology.linearEquiv_toLinearMap_apply

theorem exists_linearMap_eq_one_iff_of_linearEquiv {M N : Type u} [AddCommGroup M] [Module ℤ M]
    [AddCommGroup N] [Module ℤ N] (e : M ≃ₗ[ℤ] N) (x : M) :
    (∃ φ : M →ₗ[ℤ] ℤ, φ x = 1) ↔ ∃ ψ : N →ₗ[ℤ] ℤ, ψ (e x) = 1 := by
  refine ⟨?_, ?_⟩
  · rintro ⟨φ, hφ⟩
    refine ⟨φ.comp e.symm.toLinearMap, ?_⟩
    rw [LinearMap.comp_apply, linearEquiv_symm_toLinearMap_apply, hφ]
  · rintro ⟨ψ, hψ⟩
    refine ⟨ψ.comp e.toLinearMap, ?_⟩
    rw [LinearMap.comp_apply, linearEquiv_toLinearMap_apply, hψ]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.exists_linearMap_eq_one_iff_of_linearEquiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.exists_linearMap_eq_one_iff_of_linearEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.exists_linearMap_eq_one_iff_of_linearEquiv ``Submission.DifferentialGeometry.Topology.exists_linearMap_eq_one_iff_of_linearEquiv

theorem isSphereHomologyGenerator_iff_exists_relative_functional (n : ℕ) (hn : 0 < n)
    (b : liftedHomotopySphere.{u} n)
    (c : integralSingularHomology (n + 1) (liftedHomotopySphere.{u} n)) :
    IsSphereHomologyGenerator n c ↔
      ∃ ψ : integralRelativeHomology (n + 1)
          ({b} : Set (liftedHomotopySphere.{u} n)) →ₗ[ℤ] ℤ,
        ψ (integralAbsoluteToRelative (n + 1)
          ({b} : Set (liftedHomotopySphere.{u} n)) c) = 1 := by
  rw [isSphereHomologyGenerator_iff_exists_functional n c]
  exact exists_linearMap_eq_one_iff_of_linearEquiv
    (LinearEquiv.ofBijective
      (integralAbsoluteToRelative (n + 1) ({b} : Set (liftedHomotopySphere.{u} n)))
      (integralAbsoluteToRelative_singleton_bijective b (X := liftedHomotopySphere.{u} n)
        (by omega))) c

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.isSphereHomologyGenerator_iff_exists_relative_functional then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.isSphereHomologyGenerator_iff_exists_relative_functional"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.isSphereHomologyGenerator_iff_exists_relative_functional ``Submission.DifferentialGeometry.Topology.isSphereHomologyGenerator_iff_exists_relative_functional

theorem exists_relative_functional_integralLiftedSphereGenerator (n : ℕ) (hn : 0 < n)
    (b : liftedHomotopySphere.{u} n) :
    ∃ ψ : integralRelativeHomology (n + 1)
        ({b} : Set (liftedHomotopySphere.{u} n)) →ₗ[ℤ] ℤ,
      ψ (integralAbsoluteToRelative (n + 1)
        ({b} : Set (liftedHomotopySphere.{u} n))
        (integralLiftedSphereGenerator.{u} n)) = 1 :=
  (isSphereHomologyGenerator_iff_exists_relative_functional n hn b
    (integralLiftedSphereGenerator.{u} n)).mp (integralLiftedSphereGenerator_isGenerator n)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.exists_relative_functional_integralLiftedSphereGenerator then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.exists_relative_functional_integralLiftedSphereGenerator"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.exists_relative_functional_integralLiftedSphereGenerator ``Submission.DifferentialGeometry.Topology.exists_relative_functional_integralLiftedSphereGenerator

theorem squareSphereFundamentalClass_isSphereHomologyGenerator_iff_exists_relative_functional :
    IsSphereHomologyGenerator.{u} 1 squareSphereFundamentalClass.{u} ↔
      ∃ ψ : integralRelativeHomology 2 (liftedSphereBasepoint.{u}) →ₗ[ℤ] ℤ,
        ψ (integralAbsoluteToRelative 2 (liftedSphereBasepoint.{u})
          squareSphereFundamentalClass) = 1 :=
  isSphereHomologyGenerator_iff_exists_relative_functional 1 (by norm_num)
    (ULift.up (cubeSphereBasepoint 1)) squareSphereFundamentalClass

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.squareSphereFundamentalClass_isSphereHomologyGenerator_iff_exists_relative_functional then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.squareSphereFundamentalClass_isSphereHomologyGenerator_iff_exists_relative_functional"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.squareSphereFundamentalClass_isSphereHomologyGenerator_iff_exists_relative_functional ``Submission.DifferentialGeometry.Topology.squareSphereFundamentalClass_isSphereHomologyGenerator_iff_exists_relative_functional

theorem squareSphereFundamentalClass_isSphereHomologyGenerator_iff_exists_collapse_functional :
    IsSphereHomologyGenerator.{u} 1 squareSphereFundamentalClass.{u} ↔
      ∃ ψ : integralRelativeHomology 2 (liftedSphereBasepoint.{u}) →ₗ[ℤ] ℤ,
        ψ (integralRelativeHomologyMap 2 liftedSquareCollapse.{u} liftedSquareCollapse_mapsTo
          liftedSquareRelativeFundamentalClass.{u}) = 1 := by
  rw [squareSphereFundamentalClass_isSphereHomologyGenerator_iff_exists_relative_functional,
    ← integralRelativeHomologyMap_liftedSquareCollapse_liftedSquareRelativeFundamentalClass]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.squareSphereFundamentalClass_isSphereHomologyGenerator_iff_exists_collapse_functional then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.squareSphereFundamentalClass_isSphereHomologyGenerator_iff_exists_collapse_functional"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.squareSphereFundamentalClass_isSphereHomologyGenerator_iff_exists_collapse_functional ``Submission.DifferentialGeometry.Topology.squareSphereFundamentalClass_isSphereHomologyGenerator_iff_exists_collapse_functional

theorem squareSphereFundamentalClass_isSphereHomologyGenerator_of_collapse_bijective
    (hT : Function.Bijective (integralRelativeHomologyMap 2 liftedSquareCollapse.{u}
      liftedSquareCollapse_mapsTo))
    (hrel : ∃ φ : integralRelativeHomology 2 (liftedSquareBoundary.{u}) →ₗ[ℤ] ℤ,
      φ liftedSquareRelativeFundamentalClass.{u} = 1) :
    IsSphereHomologyGenerator.{u} 1 squareSphereFundamentalClass.{u} := by
  obtain ⟨φ, hφ⟩ := hrel
  let e := LinearEquiv.ofBijective (integralRelativeHomologyMap 2 liftedSquareCollapse.{u}
    liftedSquareCollapse_mapsTo) hT
  refine (squareSphereFundamentalClass_isSphereHomologyGenerator_iff_exists_collapse_functional).mpr
    ⟨φ.comp e.symm.toLinearMap, ?_⟩
  have hx : e liftedSquareRelativeFundamentalClass.{u} =
      integralRelativeHomologyMap 2 liftedSquareCollapse.{u} liftedSquareCollapse_mapsTo
        liftedSquareRelativeFundamentalClass.{u} := rfl
  rw [← hx, LinearMap.comp_apply, linearEquiv_symm_toLinearMap_apply, hφ]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.squareSphereFundamentalClass_isSphereHomologyGenerator_of_collapse_bijective then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.squareSphereFundamentalClass_isSphereHomologyGenerator_of_collapse_bijective"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.squareSphereFundamentalClass_isSphereHomologyGenerator_of_collapse_bijective ``Submission.DifferentialGeometry.Topology.squareSphereFundamentalClass_isSphereHomologyGenerator_of_collapse_bijective

theorem hurewicz_two_mul_of_liftedSquareCollapse_bijective
    (hT : Function.Bijective (integralRelativeHomologyMap 2 liftedSquareCollapse.{u}
      liftedSquareCollapse_mapsTo))
    (hrel : ∃ φ : integralRelativeHomology 2 (liftedSquareBoundary.{u}) →ₗ[ℤ] ℤ,
      φ liftedSquareRelativeFundamentalClass.{u} = 1)
    (x : X) (c : integralSingularHomology 2 (liftedHomotopySphere.{u} 1))
    (hc : IsSphereHomologyGenerator 1 c) :
    ∀ a b : HomotopyGroup (Fin 2) X x,
      sphereHurewicz 1 x c (a * b) = sphereHurewicz 1 x c a + sphereHurewicz 1 x c b :=
  hurewicz_two_mul x
    (squareSphereFundamentalClass_isSphereHomologyGenerator_of_collapse_bijective hT hrel) c hc

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.hurewicz_two_mul_of_liftedSquareCollapse_bijective then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.hurewicz_two_mul_of_liftedSquareCollapse_bijective"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.hurewicz_two_mul_of_liftedSquareCollapse_bijective ``Submission.DifferentialGeometry.Topology.hurewicz_two_mul_of_liftedSquareCollapse_bijective

theorem not_exists_linearMap_eq_one_of_subsingleton {M : Type u} [AddCommGroup M] [Module ℤ M]
    (hsub : Subsingleton M) (x : M) : ¬ ∃ φ : M →ₗ[ℤ] ℤ, φ x = 1 := by
  rintro ⟨φ, hφ⟩
  rw [@Subsingleton.elim _ hsub x 0, map_zero] at hφ
  exact zero_ne_one hφ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.not_exists_linearMap_eq_one_of_subsingleton then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.not_exists_linearMap_eq_one_of_subsingleton"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.not_exists_linearMap_eq_one_of_subsingleton ``Submission.DifferentialGeometry.Topology.not_exists_linearMap_eq_one_of_subsingleton

theorem subsingleton_integralRelativeHomology_singleton_of_subsingleton_homology (b : X)
    {n : ℕ} (hn : 1 < n) (h : Subsingleton (integralSingularHomology n X)) :
    Subsingleton (integralRelativeHomology n ({b} : Set X)) := by
  have hbij := integralAbsoluteToRelative_singleton_bijective b hn
  refine ⟨fun y₁ y₂ => ?_⟩
  obtain ⟨z₁, rfl⟩ := hbij.2 y₁
  obtain ⟨z₂, rfl⟩ := hbij.2 y₂
  rw [@Subsingleton.elim _ h z₁ z₂]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.subsingleton_integralRelativeHomology_singleton_of_subsingleton_homology then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.subsingleton_integralRelativeHomology_singleton_of_subsingleton_homology"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.subsingleton_integralRelativeHomology_singleton_of_subsingleton_homology ``Submission.DifferentialGeometry.Topology.subsingleton_integralRelativeHomology_singleton_of_subsingleton_homology

theorem pi_unitInterval_nullhomotopic (n : ℕ) :
    (ContinuousMap.id (Fin n → unitInterval)).Nullhomotopic := by
  refine ⟨fun _ => (0 : unitInterval), ⟨ContinuousMap.Homotopy.mk
    ⟨fun p => fun i => ⟨(1 - (p.1 : ℝ)) * (p.2 i : ℝ), ?_, ?_⟩, ?_⟩
    ?_ ?_⟩⟩
  · exact mul_nonneg (by linarith [(p.1).property.1, (p.1).property.2]) (p.2 i).property.1
  · nlinarith [(p.1).property.1, (p.1).property.2, (p.2 i).property.1, (p.2 i).property.2]
  · apply continuous_pi
    intro i
    apply Continuous.subtype_mk
    have h1 : Continuous fun p : unitInterval × (Fin n → unitInterval) =>
        (1 - (p.1 : ℝ)) :=
      continuous_const.sub (continuous_subtype_val.comp continuous_fst)
    have h2 : Continuous fun p : unitInterval × (Fin n → unitInterval) =>
        ((p.2 i : unitInterval) : ℝ) :=
      continuous_subtype_val.comp ((continuous_apply i).comp continuous_snd)
    exact h1.mul h2
  · intro v
    funext i
    apply Subtype.ext
    simp
  · intro v
    funext i
    apply Subtype.ext
    simp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.pi_unitInterval_nullhomotopic then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.pi_unitInterval_nullhomotopic"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.pi_unitInterval_nullhomotopic ``Submission.DifferentialGeometry.Topology.pi_unitInterval_nullhomotopic

theorem pi_unitInterval_contractible (n : ℕ) : ContractibleSpace (Fin n → unitInterval) :=
  (contractible_iff_id_nullhomotopic (Fin n → unitInterval)).mpr
    (pi_unitInterval_nullhomotopic n)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.pi_unitInterval_contractible then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.pi_unitInterval_contractible"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.pi_unitInterval_contractible ``Submission.DifferentialGeometry.Topology.pi_unitInterval_contractible

theorem integralRelativeConnecting_cubeBoundary_bijective :
    Function.Bijective (integralRelativeConnecting 2 (Cube.boundary (Fin 3))) := by
  have h3 : Subsingleton (integralSingularHomology 3 (Fin 3 → unitInterval)) :=
    @integralSingularHomology_subsingleton_of_contractible 3 (by omega) _
      _ (pi_unitInterval_contractible 3)
  have h2 : Subsingleton (integralSingularHomology 2 (Fin 3 → unitInterval)) :=
    @integralSingularHomology_subsingleton_of_contractible 2 (by omega) _
      _ (pi_unitInterval_contractible 3)
  exact ⟨integralRelativeConnecting_injective_of_subsingleton 2 (Cube.boundary (Fin 3)) h3,
    integralRelativeConnecting_surjective_of_subsingleton 2 (Cube.boundary (Fin 3)) h2⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralRelativeConnecting_cubeBoundary_bijective then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralRelativeConnecting_cubeBoundary_bijective"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralRelativeConnecting_cubeBoundary_bijective ``Submission.DifferentialGeometry.Topology.integralRelativeConnecting_cubeBoundary_bijective

noncomputable def cubeBoundaryConnectingEquiv :
    integralRelativeHomology 3 (Cube.boundary (Fin 3)) ≃ₗ[ℤ]
      integralSingularHomology 2 (Cube.boundary (Fin 3)) :=
  letI := pi_unitInterval_contractible 3
  integralRelativeConnectingEquivOfContractible 2 (by omega) (Cube.boundary (Fin 3))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.cubeBoundaryConnectingEquiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.cubeBoundaryConnectingEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.cubeBoundaryConnectingEquiv ``Submission.DifferentialGeometry.Topology.cubeBoundaryConnectingEquiv

theorem subsingleton_integralRelativeHomology_two_singleton_square (b : Square) :
    Subsingleton (integralRelativeHomology 2 ({b} : Set Square)) :=
  subsingleton_integralRelativeHomology_singleton_of_subsingleton_homology (X := Square) b
    (n := 2) (by norm_num)
    (@integralSingularHomology_subsingleton_of_contractible 2 (by omega) Square _
      square_contractible)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.subsingleton_integralRelativeHomology_two_singleton_square then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.subsingleton_integralRelativeHomology_two_singleton_square"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.subsingleton_integralRelativeHomology_two_singleton_square ``Submission.DifferentialGeometry.Topology.subsingleton_integralRelativeHomology_two_singleton_square

theorem subsingleton_integralRelativeHomology_three_singleton_cube (b : Fin 3 → unitInterval) :
    Subsingleton (integralRelativeHomology 3 ({b} : Set (Fin 3 → unitInterval))) :=
  subsingleton_integralRelativeHomology_singleton_of_subsingleton_homology b (n := 3)
    (by norm_num)
    (@integralSingularHomology_subsingleton_of_contractible 3 (by omega) _ _
      (pi_unitInterval_contractible 3))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.subsingleton_integralRelativeHomology_three_singleton_cube then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.subsingleton_integralRelativeHomology_three_singleton_cube"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.subsingleton_integralRelativeHomology_three_singleton_cube ``Submission.DifferentialGeometry.Topology.subsingleton_integralRelativeHomology_three_singleton_cube

theorem not_exists_linearMap_eq_one_integralRelativeHomology_two_singleton_square (b : Square)
    (z : integralRelativeHomology 2 ({b} : Set Square)) :
    ¬ ∃ φ : integralRelativeHomology 2 ({b} : Set Square) →ₗ[ℤ] ℤ, φ z = 1 :=
  not_exists_linearMap_eq_one_of_subsingleton
    (subsingleton_integralRelativeHomology_two_singleton_square b) z

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.not_exists_linearMap_eq_one_integralRelativeHomology_two_singleton_square then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.not_exists_linearMap_eq_one_integralRelativeHomology_two_singleton_square"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.not_exists_linearMap_eq_one_integralRelativeHomology_two_singleton_square ``Submission.DifferentialGeometry.Topology.not_exists_linearMap_eq_one_integralRelativeHomology_two_singleton_square

end DifferentialGeometry.Topology
