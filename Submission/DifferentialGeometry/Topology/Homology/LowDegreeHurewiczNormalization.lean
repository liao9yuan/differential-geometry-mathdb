import Submission.DifferentialGeometry.Topology.Homology.HurewiczLowDegreeCriterion
import Submission.DifferentialGeometry.Topology.Homology.HurewiczTwoMultiplication
import Submission.DifferentialGeometry.Topology.Homology.NoncompactPoincareDualityFrontier
import Submission.DifferentialGeometry.Topology.Homology.NoncompactTopHomologyVanishing
import Submission.DifferentialGeometry.Topology.Homology.PoincareDualityThreeFrontier
import Submission.DifferentialGeometry.Topology.Homology.Relative.Basic
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.LowDegreeHurewiczCubeBridge
import Submission.DifferentialGeometry.Topology.Homology.CubeSphereDegreeUnit

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

universe u

namespace DifferentialGeometry.Topology

variable {X : Type u} [TopologicalSpace X]

theorem hurewiczTwoMultiplicative_of_squareSphereFundamentalClass
    (hgen : IsSphereHomologyGenerator.{u} 1 squareSphereFundamentalClass.{u}) :
    HurewiczTwoMultiplicative X :=
  fun x c hc a b => hurewicz_two_mul x hgen c hc a b

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.hurewiczTwoMultiplicative_of_squareSphereFundamentalClass then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.hurewiczTwoMultiplicative_of_squareSphereFundamentalClass"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.hurewiczTwoMultiplicative_of_squareSphereFundamentalClass ``Submission.DifferentialGeometry.Topology.hurewiczTwoMultiplicative_of_squareSphereFundamentalClass

theorem sphereHurewiczTwoCanonical_iff_sphereCriterion_of_squareSphereFundamentalClass
    [SimplyConnectedSpace X]
    (hgen : IsSphereHomologyGenerator.{u} 1 squareSphereFundamentalClass.{u}) (x₀ : X) :
    SphereHurewiczTwoCanonical X ↔
      HurewiczTwoSphereGeneration X ∧ HurewiczTwoSphereNullhomotopic X := by
  rw [sphereHurewiczTwoCanonical_iff_sphereCriterion x₀]
  exact ⟨fun h => ⟨h.2.1, h.2.2⟩,
    fun h => ⟨hurewiczTwoMultiplicative_of_squareSphereFundamentalClass (X := X) hgen,
      h.1, h.2⟩⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.sphereHurewiczTwoCanonical_iff_sphereCriterion_of_squareSphereFundamentalClass then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.sphereHurewiczTwoCanonical_iff_sphereCriterion_of_squareSphereFundamentalClass"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.sphereHurewiczTwoCanonical_iff_sphereCriterion_of_squareSphereFundamentalClass ``Submission.DifferentialGeometry.Topology.sphereHurewiczTwoCanonical_iff_sphereCriterion_of_squareSphereFundamentalClass

theorem sphereHurewiczThreeCanonical_iff_sphereCriterion_of_cubeSphereFundamentalClass
    [SimplyConnectedSpace X]
    (hgen : IsSphereHomologyGenerator.{u} 2 cubeSphereFundamentalClass)
    (x₀ : X) (hπ₀ : Subsingleton (HomotopyGroup (Fin 2) X x₀)) :
    SphereHurewiczThreeCanonical X ↔
      HurewiczThreeSphereGeneration X ∧ HurewiczThreeSphereNullhomotopic X := by
  rw [sphereHurewiczThreeCanonical_iff_sphereCriterion x₀ hπ₀]
  exact ⟨fun h => ⟨h.2.1, h.2.2⟩,
    fun h => ⟨hurewiczThreeMultiplicative_of_cubeSphereFundamentalClass_isSphereHomologyGenerator
      hgen, h.1, h.2⟩⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.sphereHurewiczThreeCanonical_iff_sphereCriterion_of_cubeSphereFundamentalClass then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.sphereHurewiczThreeCanonical_iff_sphereCriterion_of_cubeSphereFundamentalClass"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.sphereHurewiczThreeCanonical_iff_sphereCriterion_of_cubeSphereFundamentalClass ``Submission.DifferentialGeometry.Topology.sphereHurewiczThreeCanonical_iff_sphereCriterion_of_cubeSphereFundamentalClass

theorem poincareDualityTwoOne_iff_subsingleton_integralSingularHomology_two
    [SimplyConnectedSpace X] :
    poincareDualityTwoOne X ↔ Subsingleton (integralSingularHomology 2 X) := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · exact subsingleton_integralSingularHomology_two_of_poincareDualityTwoOne_of_simplyConnected h
  · have : Subsingleton (integralSingularHomology 2 X) := h
    have : Subsingleton (integralSingularCohomology 1 X) :=
      integralSingularCohomology_one_subsingleton (X := X)
    exact poincareDualityTwoOne_of_subsingleton

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.poincareDualityTwoOne_iff_subsingleton_integralSingularHomology_two then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.poincareDualityTwoOne_iff_subsingleton_integralSingularHomology_two"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.poincareDualityTwoOne_iff_subsingleton_integralSingularHomology_two ``Submission.DifferentialGeometry.Topology.poincareDualityTwoOne_iff_subsingleton_integralSingularHomology_two

theorem subsingleton_integralRelativeHomology_of_subsingleton_absolute_of_subsingleton_subspace
    (A : Set X) (hX : Subsingleton (integralSingularHomology 2 X))
    (hA : Subsingleton (integralSingularHomology 1 A)) :
    Subsingleton (integralRelativeHomology 2 A) := by
  have hzero : integralAbsoluteToRelative 2 A = 0 := by
    ext a
    have ha : a = 0 := hX.allEq a 0
    simp [ha]
  have hinj : Function.Injective (integralRelativeConnecting 1 A) :=
    (LinearMap.injective_iff_eq_zero_of_exact (integralRelative_exact_relative 1 A)).mpr hzero
  exact hinj.subsingleton

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.subsingleton_integralRelativeHomology_of_subsingleton_absolute_of_subsingleton_subspace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.subsingleton_integralRelativeHomology_of_subsingleton_absolute_of_subsingleton_subspace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.subsingleton_integralRelativeHomology_of_subsingleton_absolute_of_subsingleton_subspace ``Submission.DifferentialGeometry.Topology.subsingleton_integralRelativeHomology_of_subsingleton_absolute_of_subsingleton_subspace

theorem subsingleton_integralSingularHomology_two_of_subsingleton_compl_and_relative
    (x : X) (hcompl : Subsingleton (integralSingularHomology 2 ({x}ᶜ : Set X)))
    (hrel : Subsingleton (integralRelativeHomology 2 ({x}ᶜ : Set X))) :
    Subsingleton (integralSingularHomology 2 X) := by
  have hzero : integralSingularHomologyMap 2 (singularSubspaceInclusion ({x}ᶜ : Set X)) = 0 := by
    ext a
    have ha : a = 0 := hcompl.allEq a 0
    simp [ha]
  have hinj : Function.Injective (integralAbsoluteToRelative 2 ({x}ᶜ : Set X)) :=
    (LinearMap.injective_iff_eq_zero_of_exact
      (integralRelative_exact_absolute 2 ({x}ᶜ : Set X))).mpr hzero
  exact hinj.subsingleton

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.subsingleton_integralSingularHomology_two_of_subsingleton_compl_and_relative then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.subsingleton_integralSingularHomology_two_of_subsingleton_compl_and_relative"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.subsingleton_integralSingularHomology_two_of_subsingleton_compl_and_relative ``Submission.DifferentialGeometry.Topology.subsingleton_integralSingularHomology_two_of_subsingleton_compl_and_relative

theorem subsingleton_integralSingularHomology_two_and_three_compl_singleton_of_noncompactPoincareDuality
    (x : X) [T2Space X] [CompactSpace X] [SimplyConnectedSpace X]
    [ConnectedSpace ↥({x}ᶜ : Set X)] [NoncompactSpace ↥({x}ᶜ : Set X)]
    (hpd2 : noncompactPoincareDualityTwoOne ({x}ᶜ : Set X))
    (hpd3 : noncompactPoincareDualityThreeZero ({x}ᶜ : Set X)) :
    Subsingleton (integralSingularHomology 2 ({x}ᶜ : Set X)) ∧
      Subsingleton (integralSingularHomology 3 ({x}ᶜ : Set X)) := by
  have : Subsingleton (integralSingularCohomology 1 X) :=
    integralSingularCohomology_one_subsingleton (X := X)
  exact ⟨subsingleton_integralSingularHomology_two_compl_singleton_of_noncompactPoincareDuality
      x hpd2,
    subsingleton_integralSingularHomology_three_of_noncompactPoincareDualityThreeZero
      (X := ↥({x}ᶜ : Set X)) hpd3⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.subsingleton_integralSingularHomology_two_and_three_compl_singleton_of_noncompactPoincareDuality then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.subsingleton_integralSingularHomology_two_and_three_compl_singleton_of_noncompactPoincareDuality"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.subsingleton_integralSingularHomology_two_and_three_compl_singleton_of_noncompactPoincareDuality ``Submission.DifferentialGeometry.Topology.subsingleton_integralSingularHomology_two_and_three_compl_singleton_of_noncompactPoincareDuality

theorem subsingleton_integralSingularHomology_two_iff_subsingleton_compl_and_relative
    (x : X) (h₁ : Subsingleton (integralSingularHomology 1 ({x}ᶜ : Set X)))
    (hcompl : Subsingleton (integralSingularHomology 2 ({x}ᶜ : Set X))) :
    Subsingleton (integralSingularHomology 2 X) ↔
      Subsingleton (integralRelativeHomology 2 ({x}ᶜ : Set X)) :=
  ⟨fun h =>
      subsingleton_integralRelativeHomology_of_subsingleton_absolute_of_subsingleton_subspace
        ({x}ᶜ : Set X) h h₁,
    fun h => subsingleton_integralSingularHomology_two_of_subsingleton_compl_and_relative x hcompl h⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.subsingleton_integralSingularHomology_two_iff_subsingleton_compl_and_relative then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.subsingleton_integralSingularHomology_two_iff_subsingleton_compl_and_relative"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.subsingleton_integralSingularHomology_two_iff_subsingleton_compl_and_relative ``Submission.DifferentialGeometry.Topology.subsingleton_integralSingularHomology_two_iff_subsingleton_compl_and_relative

theorem subsingleton_integralSingularHomology_two_of_noncompactPoincareDuality_punctured_and_relative
    [T2Space X] [CompactSpace X] [SimplyConnectedSpace X]
    (x : X) (hpd : noncompactPoincareDualityTwoOne ({x}ᶜ : Set X))
    (hrel : Subsingleton (integralRelativeHomology 2 ({x}ᶜ : Set X))) :
    Subsingleton (integralSingularHomology 2 X) := by
  have hcohom : Subsingleton (integralSingularCohomology 1 X) :=
    integralSingularCohomology_one_subsingleton (X := X)
  exact subsingleton_integralSingularHomology_two_of_subsingleton_compl_and_relative x
    (subsingleton_integralSingularHomology_two_compl_singleton_of_noncompactPoincareDuality
      x hpd) hrel

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.subsingleton_integralSingularHomology_two_of_noncompactPoincareDuality_punctured_and_relative then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.subsingleton_integralSingularHomology_two_of_noncompactPoincareDuality_punctured_and_relative"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.subsingleton_integralSingularHomology_two_of_noncompactPoincareDuality_punctured_and_relative ``Submission.DifferentialGeometry.Topology.subsingleton_integralSingularHomology_two_of_noncompactPoincareDuality_punctured_and_relative

end DifferentialGeometry.Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

open _root_.Submission.DifferentialGeometry.Topology

variable {M : Type u} [TopologicalSpace M] [SimplyConnectedSpace M]

theorem rfs_homotopy_groups_of_lowDegreeHurewiczFrontier (q : M)
    (hH₂ : Subsingleton (integralSingularHomology 2 M))
    (hgenSquare : DifferentialGeometry.Topology.IsSphereHomologyGenerator.{u} 1
      DifferentialGeometry.Topology.squareSphereFundamentalClass.{u})
    (hgenCube : DifferentialGeometry.Topology.IsSphereHomologyGenerator.{u} 2
      DifferentialGeometry.Topology.cubeSphereFundamentalClass)
    (hgenTwo : DifferentialGeometry.Topology.HurewiczTwoSphereGeneration M)
    (hnullTwo : DifferentialGeometry.Topology.HurewiczTwoSphereNullhomotopic M)
    (hgenThree : DifferentialGeometry.Topology.HurewiczThreeSphereGeneration M)
    (hnullThree : DifferentialGeometry.Topology.HurewiczThreeSphereNullhomotopic M) :
    Subsingleton (HomotopyGroup (Fin 2) M q) ∧ Function.Bijective (hurewiczThree q) := by
  obtain ⟨x₀⟩ := DifferentialGeometry.Topology.nonempty_of_hurewiczTwoSphereGeneration hgenTwo
  have hcanonTwo : DifferentialGeometry.Topology.SphereHurewiczTwoCanonical M :=
    (DifferentialGeometry.Topology.sphereHurewiczTwoCanonical_iff_sphereCriterion_of_squareSphereFundamentalClass
      hgenSquare x₀).mpr ⟨hgenTwo, hnullTwo⟩
  have hπ₀ : Subsingleton (HomotopyGroup (Fin 2) M x₀) :=
    DifferentialGeometry.Topology.homotopyTwo_subsingleton_of_sphereHurewiczTwoCanonical
      hcanonTwo hH₂ x₀
  have hcanonThree : DifferentialGeometry.Topology.SphereHurewiczThreeCanonical M :=
    (DifferentialGeometry.Topology.sphereHurewiczThreeCanonical_iff_sphereCriterion_of_cubeSphereFundamentalClass
      hgenCube x₀ hπ₀).mpr ⟨hgenThree, hnullThree⟩
  exact DifferentialGeometry.Topology.rfs_homotopy_groups_of_sphereHurewiczCanonical
    q hH₂ hgenCube hcanonTwo hcanonThree

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.rfs_homotopy_groups_of_lowDegreeHurewiczFrontier then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.rfs_homotopy_groups_of_lowDegreeHurewiczFrontier"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.rfs_homotopy_groups_of_lowDegreeHurewiczFrontier ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.rfs_homotopy_groups_of_lowDegreeHurewiczFrontier

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
