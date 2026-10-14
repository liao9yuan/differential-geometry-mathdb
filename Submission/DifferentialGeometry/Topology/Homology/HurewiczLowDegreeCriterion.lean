import Submission.DifferentialGeometry.Topology.Homology.HurewiczBijectionFrontier
import Submission.DifferentialGeometry.Topology.Homology.HurewiczLowDegreeBasepoint

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

universe u

namespace DifferentialGeometry.Topology

variable {X : Type u} [TopologicalSpace X]

theorem hurewicz_two_isomorphism_of_sphereCriterion [SimplyConnectedSpace X] (x₀ : X)
    (hmul : HurewiczTwoMultiplicative X) (hgen : HurewiczTwoSphereGeneration X)
    (hnull : HurewiczTwoSphereNullhomotopic X)
    (x : X) (c : integralSingularHomology 2 (liftedHomotopySphere.{u} 1))
    (hc : IsSphereHomologyGenerator 1 c) :
    Function.Bijective (sphereHurewicz 1 x c) ∧
      ∀ a b : HomotopyGroup (Fin 2) X x,
        sphereHurewicz 1 x c (a * b) = sphereHurewicz 1 x c a + sphereHurewicz 1 x c b :=
  IsSphereHurewiczIsomorphism.of_isSphereHomologyGenerator 1 x hc
    ⟨((hurewiczTwoBijective_iff_sphereCriterion_of_multiplicative hmul x₀).mpr
        ⟨hgen, hnull⟩) x,
      hmul x (integralLiftedSphereGenerator.{u} 1)
        (integralLiftedSphereGenerator_isGenerator 1)⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.hurewicz_two_isomorphism_of_sphereCriterion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.hurewicz_two_isomorphism_of_sphereCriterion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.hurewicz_two_isomorphism_of_sphereCriterion ``Submission.DifferentialGeometry.Topology.hurewicz_two_isomorphism_of_sphereCriterion

theorem hurewicz_three_isomorphism_of_sphereCriterion [SimplyConnectedSpace X] (x₀ : X)
    (hπ₀ : Subsingleton (HomotopyGroup (Fin 2) X x₀))
    (hmul : HurewiczThreeMultiplicative X) (hgen : HurewiczThreeSphereGeneration X)
    (hnull : HurewiczThreeSphereNullhomotopic X)
    (x : X) (hπ₂ : Subsingleton (HomotopyGroup (Fin 2) X x))
    (c : integralSingularHomology 3 (liftedHomotopySphere.{u} 2))
    (hc : IsSphereHomologyGenerator 2 c) :
    Function.Bijective (sphereHurewicz 2 x c) ∧
      ∀ a b : HomotopyGroup (Fin 3) X x,
        sphereHurewicz 2 x c (a * b) = sphereHurewicz 2 x c a + sphereHurewicz 2 x c b :=
  IsSphereHurewiczIsomorphism.of_isSphereHomologyGenerator 2 x hc
    ⟨((hurewiczThreeBijective_iff_sphereCriterion_of_multiplicative hmul x₀ hπ₀).mpr
        ⟨hgen, hnull⟩) x hπ₂,
      hmul x hπ₂ (integralLiftedSphereGenerator.{u} 2)
        (integralLiftedSphereGenerator_isGenerator 2)⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.hurewicz_three_isomorphism_of_sphereCriterion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.hurewicz_three_isomorphism_of_sphereCriterion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.hurewicz_three_isomorphism_of_sphereCriterion ``Submission.DifferentialGeometry.Topology.hurewicz_three_isomorphism_of_sphereCriterion

theorem hurewicz_two_isomorphism_iff_sphereCriterion [SimplyConnectedSpace X] (x₀ : X) :
    (∀ (x : X) (c : integralSingularHomology 2 (liftedHomotopySphere.{u} 1))
      (_ : IsSphereHomologyGenerator 1 c), IsSphereHurewiczIsomorphism 1 X x c) ↔
      HurewiczTwoMultiplicative X ∧ HurewiczTwoSphereGeneration X ∧
        HurewiczTwoSphereNullhomotopic X := by
  constructor
  · intro h
    have hbij : HurewiczTwoBijective X := fun x =>
      (h x (integralLiftedSphereGenerator.{u} 1)
        (integralLiftedSphereGenerator_isGenerator 1)).1
    exact ⟨fun x c hc => (h x c hc).2,
      hurewiczTwoSphereGeneration_of_hurewiczTwoBijective hbij x₀,
      hurewiczTwoSphereNullhomotopic_of_hurewiczTwoBijective hbij x₀⟩
  · rintro ⟨hmul, hgen, hnull⟩ x c hc
    exact hurewicz_two_isomorphism_of_sphereCriterion x₀ hmul hgen hnull x c hc

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.hurewicz_two_isomorphism_iff_sphereCriterion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.hurewicz_two_isomorphism_iff_sphereCriterion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.hurewicz_two_isomorphism_iff_sphereCriterion ``Submission.DifferentialGeometry.Topology.hurewicz_two_isomorphism_iff_sphereCriterion

theorem hurewicz_three_isomorphism_iff_sphereCriterion [SimplyConnectedSpace X] (x₀ : X)
    (hπ₀ : Subsingleton (HomotopyGroup (Fin 2) X x₀)) :
    (∀ (x : X) (_ : Subsingleton (HomotopyGroup (Fin 2) X x))
      (c : integralSingularHomology 3 (liftedHomotopySphere.{u} 2))
      (_ : IsSphereHomologyGenerator 2 c), IsSphereHurewiczIsomorphism 2 X x c) ↔
      HurewiczThreeMultiplicative X ∧ HurewiczThreeSphereGeneration X ∧
        HurewiczThreeSphereNullhomotopic X := by
  constructor
  · intro h
    have hbij : HurewiczThreeBijective X := fun x hπ₂ =>
      (h x hπ₂ (integralLiftedSphereGenerator.{u} 2)
        (integralLiftedSphereGenerator_isGenerator 2)).1
    exact ⟨fun x hπ₂ c hc => (h x hπ₂ c hc).2,
      hurewiczThreeSphereGeneration_of_hurewiczThreeBijective hbij x₀ hπ₀,
      hurewiczThreeSphereNullhomotopic_of_hurewiczThreeBijective hbij x₀ hπ₀⟩
  · rintro ⟨hmul, hgen, hnull⟩ x hπ₂ c hc
    exact hurewicz_three_isomorphism_of_sphereCriterion x₀ hπ₀ hmul hgen hnull x hπ₂ c hc

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.hurewicz_three_isomorphism_iff_sphereCriterion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.hurewicz_three_isomorphism_iff_sphereCriterion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.hurewicz_three_isomorphism_iff_sphereCriterion ``Submission.DifferentialGeometry.Topology.hurewicz_three_isomorphism_iff_sphereCriterion

theorem sphereHurewiczTwoCanonical_iff_sphereCriterion [SimplyConnectedSpace X] (x₀ : X) :
    SphereHurewiczTwoCanonical X ↔
      HurewiczTwoMultiplicative X ∧ HurewiczTwoSphereGeneration X ∧
        HurewiczTwoSphereNullhomotopic X :=
  (sphereHurewicz_two_isomorphism_iff_canonical_generator (X := X)).symm.trans
    (hurewicz_two_isomorphism_iff_sphereCriterion x₀)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.sphereHurewiczTwoCanonical_iff_sphereCriterion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.sphereHurewiczTwoCanonical_iff_sphereCriterion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.sphereHurewiczTwoCanonical_iff_sphereCriterion ``Submission.DifferentialGeometry.Topology.sphereHurewiczTwoCanonical_iff_sphereCriterion

theorem sphereHurewiczThreeCanonical_iff_sphereCriterion [SimplyConnectedSpace X] (x₀ : X)
    (hπ₀ : Subsingleton (HomotopyGroup (Fin 2) X x₀)) :
    SphereHurewiczThreeCanonical X ↔
      HurewiczThreeMultiplicative X ∧ HurewiczThreeSphereGeneration X ∧
        HurewiczThreeSphereNullhomotopic X :=
  (sphereHurewicz_three_isomorphism_iff_canonical_generator (X := X)).symm.trans
    (hurewicz_three_isomorphism_iff_sphereCriterion x₀ hπ₀)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.sphereHurewiczThreeCanonical_iff_sphereCriterion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.sphereHurewiczThreeCanonical_iff_sphereCriterion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.sphereHurewiczThreeCanonical_iff_sphereCriterion ``Submission.DifferentialGeometry.Topology.sphereHurewiczThreeCanonical_iff_sphereCriterion

theorem nonempty_of_hurewiczTwoSphereGeneration (h : HurewiczTwoSphereGeneration X) :
    Nonempty X :=
  (h 0).elim fun f _ => ⟨f (cubeSphereBasepoint 1)⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.nonempty_of_hurewiczTwoSphereGeneration then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.nonempty_of_hurewiczTwoSphereGeneration"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.nonempty_of_hurewiczTwoSphereGeneration ``Submission.DifferentialGeometry.Topology.nonempty_of_hurewiczTwoSphereGeneration

theorem nonempty_of_hurewiczThreeSphereGeneration (h : HurewiczThreeSphereGeneration X) :
    Nonempty X :=
  (h 0).elim fun f _ => ⟨f (cubeSphereBasepoint 2)⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.nonempty_of_hurewiczThreeSphereGeneration then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.nonempty_of_hurewiczThreeSphereGeneration"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.nonempty_of_hurewiczThreeSphereGeneration ``Submission.DifferentialGeometry.Topology.nonempty_of_hurewiczThreeSphereGeneration

theorem not_hurewiczTwoSphereGeneration_of_isEmpty [IsEmpty X] :
    ¬ HurewiczTwoSphereGeneration X :=
  fun h => (nonempty_of_hurewiczTwoSphereGeneration h).elim isEmptyElim

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.not_hurewiczTwoSphereGeneration_of_isEmpty then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.not_hurewiczTwoSphereGeneration_of_isEmpty"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.not_hurewiczTwoSphereGeneration_of_isEmpty ``Submission.DifferentialGeometry.Topology.not_hurewiczTwoSphereGeneration_of_isEmpty

theorem not_hurewiczThreeSphereGeneration_of_isEmpty [IsEmpty X] :
    ¬ HurewiczThreeSphereGeneration X :=
  fun h => (nonempty_of_hurewiczThreeSphereGeneration h).elim isEmptyElim

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.not_hurewiczThreeSphereGeneration_of_isEmpty then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.not_hurewiczThreeSphereGeneration_of_isEmpty"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.not_hurewiczThreeSphereGeneration_of_isEmpty ``Submission.DifferentialGeometry.Topology.not_hurewiczThreeSphereGeneration_of_isEmpty

theorem hurewiczTwoSphereCriterion_punit :
    HurewiczTwoSphereGeneration PUnit.{u + 1} ∧
      HurewiczTwoSphereNullhomotopic PUnit.{u + 1} := by
  obtain ⟨-, hgen, hnull⟩ :=
    (hurewicz_two_isomorphism_iff_sphereCriterion (X := PUnit.{u + 1}) PUnit.unit).mp
      fun x c hc => IsSphereHurewiczIsomorphism.of_isSphereHomologyGenerator 1 x hc
        (sphereHurewiczTwoCanonical_punit x)
  exact ⟨hgen, hnull⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.hurewiczTwoSphereCriterion_punit then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.hurewiczTwoSphereCriterion_punit"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.hurewiczTwoSphereCriterion_punit ``Submission.DifferentialGeometry.Topology.hurewiczTwoSphereCriterion_punit

theorem hurewiczThreeSphereCriterion_punit :
    HurewiczThreeSphereGeneration PUnit.{u + 1} ∧
      HurewiczThreeSphereNullhomotopic PUnit.{u + 1} := by
  obtain ⟨-, hgen, hnull⟩ :=
    (hurewicz_three_isomorphism_iff_sphereCriterion (X := PUnit.{u + 1}) PUnit.unit
      (subsingleton_homotopyGroup_of_subsingleton (Fin 2) PUnit.unit)).mp
      fun x _ c hc => IsSphereHurewiczIsomorphism.of_isSphereHomologyGenerator 2 x hc
        (sphereHurewiczThreeCanonical_punit x (subsingleton_homotopyGroup_of_subsingleton
          (Fin 2) x))
  exact ⟨hgen, hnull⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.hurewiczThreeSphereCriterion_punit then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.hurewiczThreeSphereCriterion_punit"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.hurewiczThreeSphereCriterion_punit ``Submission.DifferentialGeometry.Topology.hurewiczThreeSphereCriterion_punit

end DifferentialGeometry.Topology
