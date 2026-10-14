import Submission.DifferentialGeometry.Topology.Homology.HurewiczLowDegrees
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.LowDegreeHurewiczCubeBridge
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HomotopyGroupsAssembly
import Submission.DifferentialGeometry.Topology.Homology.HurewiczLowDegreeCriterion
import Submission.DifferentialGeometry.Topology.Homology.HurewiczLowDegreeTransport
import Submission.DifferentialGeometry.Topology.Homology.HurewiczThreeWitness
import Submission.DifferentialGeometry.Topology.Homology.SecondHomologyVanishingClosedThreeManifold

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Set
open scoped _root_.ContDiff _root_.Manifold _root_.Submission.Manifold

universe u

namespace DifferentialGeometry.Topology

variable {X : Type u} [TopologicalSpace X]

theorem hurewicz_three_isomorphism_of_cubeSphereFundamentalClass_of_sphereCriterion
    [SimplyConnectedSpace X] (hgen : IsSphereHomologyGenerator.{u} 2 cubeSphereFundamentalClass)
    (hgenThree : HurewiczThreeSphereGeneration X)
    (hnullThree : HurewiczThreeSphereNullhomotopic X)
    (x : X) (hπ₂ : Subsingleton (HomotopyGroup (Fin 2) X x))
    (c : integralSingularHomology 3 (liftedHomotopySphere.{u} 2))
    (hc : IsSphereHomologyGenerator 2 c) :
    Function.Bijective (sphereHurewicz 2 x c) ∧
      ∀ a b : HomotopyGroup (Fin 3) X x,
        sphereHurewicz 2 x c (a * b) = sphereHurewicz 2 x c a + sphereHurewicz 2 x c b :=
  sphereHurewicz_three_isomorphism_of_canonical_generator
    ((sphereHurewiczThreeCanonical_iff_sphereCriterion_of_cubeSphereFundamentalClass
      hgen x hπ₂).mpr ⟨hgenThree, hnullThree⟩) x hπ₂ c hc

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.hurewicz_three_isomorphism_of_cubeSphereFundamentalClass_of_sphereCriterion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.hurewicz_three_isomorphism_of_cubeSphereFundamentalClass_of_sphereCriterion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.hurewicz_three_isomorphism_of_cubeSphereFundamentalClass_of_sphereCriterion ``Submission.DifferentialGeometry.Topology.hurewicz_three_isomorphism_of_cubeSphereFundamentalClass_of_sphereCriterion

theorem
    hurewicz_three_isomorphism_liftedHomotopySphere_of_cubeSphereFundamentalClass_of_nullhomotopic
    (hgen : IsSphereHomologyGenerator.{u} 2 cubeSphereFundamentalClass)
    (hnull : HurewiczThreeSphereNullhomotopic (liftedHomotopySphere.{u} 2))
    (x : liftedHomotopySphere.{u} 2)
    (hπ₂ : Subsingleton (HomotopyGroup (Fin 2) (liftedHomotopySphere.{u} 2) x))
    (c : integralSingularHomology 3 (liftedHomotopySphere.{u} 2))
    (hc : IsSphereHomologyGenerator 2 c) :
    Function.Bijective (sphereHurewicz 2 x c) ∧
      ∀ a b : HomotopyGroup (Fin 3) (liftedHomotopySphere.{u} 2) x,
        sphereHurewicz 2 x c (a * b) = sphereHurewicz 2 x c a + sphereHurewicz 2 x c b :=
  hurewicz_three_isomorphism_of_cubeSphereFundamentalClass_of_sphereCriterion hgen
    (hurewiczThreeSphereGeneration_liftedHomotopySphere_of_cubeSphereFundamentalClass hgen)
    hnull x hπ₂ c hc

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.hurewicz_three_isomorphism_liftedHomotopySphere_of_cubeSphereFundamentalClass_of_nullhomotopic then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.hurewicz_three_isomorphism_liftedHomotopySphere_of_cubeSphereFundamentalClass_of_nullhomotopic"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.hurewicz_three_isomorphism_liftedHomotopySphere_of_cubeSphereFundamentalClass_of_nullhomotopic ``Submission.DifferentialGeometry.Topology.hurewicz_three_isomorphism_liftedHomotopySphere_of_cubeSphereFundamentalClass_of_nullhomotopic

theorem
    homotopyTwo_subsingleton_of_sphereHurewiczTwoCanonical_of_noncompactPoincareDuality
    {M : Type u} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M] [T2Space M] [CompactSpace M] [SimplyConnectedSpace M]
    (hTwo : SphereHurewiczTwoCanonical M) (x q : M)
    (hpd : noncompactPoincareDualityTwoOne ({x}ᶜ : Set M)) :
    Subsingleton (HomotopyGroup (Fin 2) M q) :=
  homotopyTwo_subsingleton_of_sphereHurewiczTwoCanonical hTwo
    (subsingleton_integralSingularHomology_two_of_noncompactPoincareDuality_punctured x hpd) q

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.homotopyTwo_subsingleton_of_sphereHurewiczTwoCanonical_of_noncompactPoincareDuality then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.homotopyTwo_subsingleton_of_sphereHurewiczTwoCanonical_of_noncompactPoincareDuality"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.homotopyTwo_subsingleton_of_sphereHurewiczTwoCanonical_of_noncompactPoincareDuality ``Submission.DifferentialGeometry.Topology.homotopyTwo_subsingleton_of_sphereHurewiczTwoCanonical_of_noncompactPoincareDuality

theorem
    homotopyTwo_subsingleton_of_hurewiczTwoSphereNullhomotopic_of_noncompactPoincareDuality
    {M : Type u} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M] [T2Space M] [CompactSpace M] [SimplyConnectedSpace M]
    (hnull : HurewiczTwoSphereNullhomotopic M) (x q : M)
    (hpd : noncompactPoincareDualityTwoOne ({x}ᶜ : Set M)) :
    Subsingleton (HomotopyGroup (Fin 2) M q) :=
  @homotopyTwo_subsingleton_of_homologyTwo_of_sphereNullhomotopic M _ _ hnull
    (subsingleton_integralSingularHomology_two_of_noncompactPoincareDuality_punctured x hpd) q

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.homotopyTwo_subsingleton_of_hurewiczTwoSphereNullhomotopic_of_noncompactPoincareDuality then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.homotopyTwo_subsingleton_of_hurewiczTwoSphereNullhomotopic_of_noncompactPoincareDuality"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.homotopyTwo_subsingleton_of_hurewiczTwoSphereNullhomotopic_of_noncompactPoincareDuality ``Submission.DifferentialGeometry.Topology.homotopyTwo_subsingleton_of_hurewiczTwoSphereNullhomotopic_of_noncompactPoincareDuality

open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology in
theorem
    sphereHurewiczTwoCanonical_iff_forall_subsingleton_homotopyGroup_of_noncompactPoincareDuality
    {M : Type u} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M] [T2Space M] [CompactSpace M] [SimplyConnectedSpace M]
    (x : M) (hpd : noncompactPoincareDualityTwoOne ({x}ᶜ : Set M)) :
    SphereHurewiczTwoCanonical M ↔ ∀ q : M, Subsingleton (HomotopyGroup (Fin 2) M q) :=
  sphereHurewiczTwoCanonical_iff_forall_subsingleton_homotopyGroup
    (subsingleton_integralSingularHomology_two_of_noncompactPoincareDuality_punctured x hpd)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.sphereHurewiczTwoCanonical_iff_forall_subsingleton_homotopyGroup_of_noncompactPoincareDuality then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.sphereHurewiczTwoCanonical_iff_forall_subsingleton_homotopyGroup_of_noncompactPoincareDuality"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.sphereHurewiczTwoCanonical_iff_forall_subsingleton_homotopyGroup_of_noncompactPoincareDuality ``Submission.DifferentialGeometry.Topology.sphereHurewiczTwoCanonical_iff_forall_subsingleton_homotopyGroup_of_noncompactPoincareDuality

theorem hurewicz_two_and_three_isomorphism_of_lowDegreeAssembly
    {M : Type u} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M] [T2Space M] [CompactSpace M] [SimplyConnectedSpace M]
    (x : M) (hpd : noncompactPoincareDualityTwoOne ({x}ᶜ : Set M))
    (hTwo : SphereHurewiczTwoCanonical M)
    (hgen : IsSphereHomologyGenerator.{u} 2 cubeSphereFundamentalClass)
    (hgenThree : HurewiczThreeSphereGeneration M)
    (hnullThree : HurewiczThreeSphereNullhomotopic M)
    (q : M) (c₂ : integralSingularHomology 2 (liftedHomotopySphere.{u} 1))
    (hc₂ : IsSphereHomologyGenerator 1 c₂)
    (c₃ : integralSingularHomology 3 (liftedHomotopySphere.{u} 2))
    (hc₃ : IsSphereHomologyGenerator 2 c₃) :
    (Function.Bijective (sphereHurewicz 1 q c₂) ∧
      ∀ a b : HomotopyGroup (Fin 2) M q,
        sphereHurewicz 1 q c₂ (a * b) = sphereHurewicz 1 q c₂ a + sphereHurewicz 1 q c₂ b) ∧
    (Function.Bijective (sphereHurewicz 2 q c₃) ∧
      ∀ a b : HomotopyGroup (Fin 3) M q,
        sphereHurewicz 2 q c₃ (a * b) = sphereHurewicz 2 q c₃ a + sphereHurewicz 2 q c₃ b) :=
  ⟨sphereHurewicz_two_isomorphism_of_canonical_generator hTwo q c₂ hc₂,
    hurewicz_three_isomorphism_of_cubeSphereFundamentalClass_of_sphereCriterion hgen hgenThree
      hnullThree q
      (homotopyTwo_subsingleton_of_sphereHurewiczTwoCanonical_of_noncompactPoincareDuality
        hTwo x q hpd) c₃ hc₃⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.hurewicz_two_and_three_isomorphism_of_lowDegreeAssembly then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.hurewicz_two_and_three_isomorphism_of_lowDegreeAssembly"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.hurewicz_two_and_three_isomorphism_of_lowDegreeAssembly ``Submission.DifferentialGeometry.Topology.hurewicz_two_and_three_isomorphism_of_lowDegreeAssembly

theorem homotopyTwo_subsingleton_sphereThree_of_hurewiczTwoSphereNullhomotopic
    (hnull : HurewiczTwoSphereNullhomotopic SphereThree) (q : SphereThree) :
    Subsingleton (HomotopyGroup (Fin 2) SphereThree q) :=
  homotopyTwo_subsingleton_of_hurewiczTwoSphereNullhomotopic_of_noncompactPoincareDuality
    hnull (Classical.choice (inferInstance : Nonempty SphereThree)) q
    (noncompactPoincareDualityTwoOne_sphereThree_compl_singleton _)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.homotopyTwo_subsingleton_sphereThree_of_hurewiczTwoSphereNullhomotopic then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.homotopyTwo_subsingleton_sphereThree_of_hurewiczTwoSphereNullhomotopic"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.homotopyTwo_subsingleton_sphereThree_of_hurewiczTwoSphereNullhomotopic ``Submission.DifferentialGeometry.Topology.homotopyTwo_subsingleton_sphereThree_of_hurewiczTwoSphereNullhomotopic

end DifferentialGeometry.Topology

namespace DifferentialGeometry.Topology

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.ContinuousMap _root_.Submission.ContinuousMap _root_.Metric _root_.Submission.Metric
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

variable {X : Type u} [TopologicalSpace X]
variable {Y : Type u} [TopologicalSpace Y]
variable {M : Type u} [TopologicalSpace M] [SimplyConnectedSpace M]

theorem sphereHurewiczTwoCanonical_of_hurewicz_two_isomorphism :
    SphereHurewiczTwoCanonical M :=
  (sphereHurewicz_two_isomorphism_iff_canonical_generator (X := M)).mp
    (fun x c hc => hurewicz_two_isomorphism x c hc)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.sphereHurewiczTwoCanonical_of_hurewicz_two_isomorphism then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.sphereHurewiczTwoCanonical_of_hurewicz_two_isomorphism"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.sphereHurewiczTwoCanonical_of_hurewicz_two_isomorphism ``Submission.DifferentialGeometry.Topology.sphereHurewiczTwoCanonical_of_hurewicz_two_isomorphism

theorem sphereHurewiczThreeCanonical_of_hurewicz_three_isomorphism :
    SphereHurewiczThreeCanonical M :=
  (sphereHurewicz_three_isomorphism_iff_canonical_generator (X := M)).mp
    (fun x hπ₂ c hc => hurewicz_three_isomorphism x hπ₂ c hc)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.sphereHurewiczThreeCanonical_of_hurewicz_three_isomorphism then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.sphereHurewiczThreeCanonical_of_hurewicz_three_isomorphism"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.sphereHurewiczThreeCanonical_of_hurewicz_three_isomorphism ``Submission.DifferentialGeometry.Topology.sphereHurewiczThreeCanonical_of_hurewicz_three_isomorphism

theorem rfs_homotopy_groups_of_subsingleton_homology_two (q : M)
    (hH₂ : Subsingleton (integralSingularHomology 2 M))
    (hgen : IsSphereHomologyGenerator.{u} 2 cubeSphereFundamentalClass) :
    Subsingleton (HomotopyGroup (Fin 2) M q) ∧ Function.Bijective (hurewiczThree q) :=
  rfs_homotopy_groups_of_sphereHurewiczCanonical q hH₂ hgen
    sphereHurewiczTwoCanonical_of_hurewicz_two_isomorphism
    sphereHurewiczThreeCanonical_of_hurewicz_three_isomorphism

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.rfs_homotopy_groups_of_subsingleton_homology_two then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.rfs_homotopy_groups_of_subsingleton_homology_two"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.rfs_homotopy_groups_of_subsingleton_homology_two ``Submission.DifferentialGeometry.Topology.rfs_homotopy_groups_of_subsingleton_homology_two

end DifferentialGeometry.Topology
