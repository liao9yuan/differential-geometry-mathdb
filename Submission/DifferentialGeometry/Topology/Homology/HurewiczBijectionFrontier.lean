import Submission.DifferentialGeometry.Topology.Homology.HurewiczFrontier
import Submission.DifferentialGeometry.Topology.Homology.HurewiczSphereCriterion
import Submission.DifferentialGeometry.Topology.Homology.HurewiczNullhomotopyCriterion
import Submission.DifferentialGeometry.Topology.Homology.LiftedSphereRelativeBridge
import Submission.DifferentialGeometry.Topology.Homology.LowDegreeHurewiczNonvacuity

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

universe u

namespace DifferentialGeometry.Topology

variable {X : Type u} [TopologicalSpace X]

theorem bijective_sphereHurewicz_iff_of_path (n : ℕ) {x y : X} (p : Path x y)
    (c : integralSingularHomology (n + 1) (liftedHomotopySphere.{u} n)) :
    Function.Bijective (sphereHurewicz n x c) ↔
      Function.Bijective (sphereHurewicz n y c) := by
  have hfun : sphereHurewicz n y c =
      (sphereHurewicz n x c) ∘ (homotopyGroupBasepointEquiv n p).symm := by
    funext a
    rw [Function.comp_apply]
    calc sphereHurewicz n y c a
        = sphereHurewicz n y c
            ((homotopyGroupBasepointEquiv n p) ((homotopyGroupBasepointEquiv n p).symm a)) := by
          rw [Equiv.apply_symm_apply]
      _ = sphereHurewicz n x c ((homotopyGroupBasepointEquiv n p).symm a) :=
          sphereHurewicz_transport n p c ((homotopyGroupBasepointEquiv n p).symm a)
  rw [hfun]
  exact (Equiv.bijective_comp (homotopyGroupBasepointEquiv n p).symm (sphereHurewicz n x c)).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.bijective_sphereHurewicz_iff_of_path then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.bijective_sphereHurewicz_iff_of_path"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.bijective_sphereHurewicz_iff_of_path ``Submission.DifferentialGeometry.Topology.bijective_sphereHurewicz_iff_of_path

theorem surjective_sphereHurewicz_iff_surjective_freeSphereHomologyImage
    [PathConnectedSpace X] (n : ℕ) (x : X)
    (c : integralSingularHomology (n + 1) (liftedHomotopySphere.{u} n)) :
    Function.Surjective (sphereHurewicz n x c) ↔
      Function.Surjective (freeSphereHomologyImage (X := X) n c) := by
  constructor
  · intro h y
    obtain ⟨a, ha⟩ := h y
    refine ⟨homotopyGroupToFreeSphere n x a, ?_⟩
    change sphereHurewicz n x c a = y
    exact ha
  · intro h y
    obtain ⟨b, hb⟩ := h y
    obtain ⟨a, ha⟩ := homotopyGroupToFreeSphere_surjective n x b
    refine ⟨a, ?_⟩
    change freeSphereHomologyImage (X := X) n c (homotopyGroupToFreeSphere n x a) = y
    rw [ha, hb]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.surjective_sphereHurewicz_iff_surjective_freeSphereHomologyImage then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.surjective_sphereHurewicz_iff_surjective_freeSphereHomologyImage"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.surjective_sphereHurewicz_iff_surjective_freeSphereHomologyImage ``Submission.DifferentialGeometry.Topology.surjective_sphereHurewicz_iff_surjective_freeSphereHomologyImage

def HurewiczTwoBijective (X : Type u) [TopologicalSpace X] : Prop :=
  ∀ x : X, Function.Bijective (sphereHurewicz 1 x (integralLiftedSphereGenerator.{u} 1))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.HurewiczTwoBijective then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.HurewiczTwoBijective"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.HurewiczTwoBijective ``Submission.DifferentialGeometry.Topology.HurewiczTwoBijective

def HurewiczThreeBijective (X : Type u) [TopologicalSpace X] : Prop :=
  ∀ x : X, Subsingleton (HomotopyGroup (Fin 2) X x) →
    Function.Bijective (sphereHurewicz 2 x (integralLiftedSphereGenerator.{u} 2))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.HurewiczThreeBijective then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.HurewiczThreeBijective"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.HurewiczThreeBijective ``Submission.DifferentialGeometry.Topology.HurewiczThreeBijective

def HurewiczTwoMultiplicative (X : Type u) [TopologicalSpace X] : Prop :=
  ∀ (x : X) (c : integralSingularHomology 2 (liftedHomotopySphere.{u} 1))
    (_ : IsSphereHomologyGenerator 1 c) (a b : HomotopyGroup (Fin 2) X x),
    sphereHurewicz 1 x c (a * b) = sphereHurewicz 1 x c a + sphereHurewicz 1 x c b

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.HurewiczTwoMultiplicative then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.HurewiczTwoMultiplicative"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.HurewiczTwoMultiplicative ``Submission.DifferentialGeometry.Topology.HurewiczTwoMultiplicative

def HurewiczThreeMultiplicative (X : Type u) [TopologicalSpace X] : Prop :=
  ∀ (x : X) (_ : Subsingleton (HomotopyGroup (Fin 2) X x))
    (c : integralSingularHomology 3 (liftedHomotopySphere.{u} 2))
    (_ : IsSphereHomologyGenerator 2 c) (a b : HomotopyGroup (Fin 3) X x),
    sphereHurewicz 2 x c (a * b) = sphereHurewicz 2 x c a + sphereHurewicz 2 x c b

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.HurewiczThreeMultiplicative then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.HurewiczThreeMultiplicative"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.HurewiczThreeMultiplicative ``Submission.DifferentialGeometry.Topology.HurewiczThreeMultiplicative

def HurewiczTwoSphereGeneration (X : Type u) [TopologicalSpace X] : Prop :=
  ∀ y : integralSingularHomology 2 X,
    ∃ f : C(Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1, X),
      freeSphereHomologyImage 1 (integralLiftedSphereGenerator.{u} 1) (ZerothHomotopy.mk f) = y

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.HurewiczTwoSphereGeneration then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.HurewiczTwoSphereGeneration"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.HurewiczTwoSphereGeneration ``Submission.DifferentialGeometry.Topology.HurewiczTwoSphereGeneration

def HurewiczTwoSphereNullhomotopic (X : Type u) [TopologicalSpace X] : Prop :=
  ∀ f : C(Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1, X),
    freeSphereHomologyImage 1 (integralLiftedSphereGenerator.{u} 1) (ZerothHomotopy.mk f) = 0 →
      f.Nullhomotopic

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.HurewiczTwoSphereNullhomotopic then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.HurewiczTwoSphereNullhomotopic"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.HurewiczTwoSphereNullhomotopic ``Submission.DifferentialGeometry.Topology.HurewiczTwoSphereNullhomotopic

def HurewiczThreeSphereGeneration (X : Type u) [TopologicalSpace X] : Prop :=
  ∀ y : integralSingularHomology 3 X,
    ∃ f : C(Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1, X),
      freeSphereHomologyImage 2 (integralLiftedSphereGenerator.{u} 2) (ZerothHomotopy.mk f) = y

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.HurewiczThreeSphereGeneration then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.HurewiczThreeSphereGeneration"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.HurewiczThreeSphereGeneration ``Submission.DifferentialGeometry.Topology.HurewiczThreeSphereGeneration

def HurewiczThreeSphereNullhomotopic (X : Type u) [TopologicalSpace X] : Prop :=
  ∀ f : C(Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1, X),
    freeSphereHomologyImage 2 (integralLiftedSphereGenerator.{u} 2) (ZerothHomotopy.mk f) = 0 →
      f.Nullhomotopic

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.HurewiczThreeSphereNullhomotopic then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.HurewiczThreeSphereNullhomotopic"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.HurewiczThreeSphereNullhomotopic ``Submission.DifferentialGeometry.Topology.HurewiczThreeSphereNullhomotopic

theorem hurewiczTwoBijective_of_sphereHurewiczTwoCanonical
    (h : SphereHurewiczTwoCanonical X) : HurewiczTwoBijective X :=
  fun x => (h x).1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.hurewiczTwoBijective_of_sphereHurewiczTwoCanonical then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.hurewiczTwoBijective_of_sphereHurewiczTwoCanonical"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.hurewiczTwoBijective_of_sphereHurewiczTwoCanonical ``Submission.DifferentialGeometry.Topology.hurewiczTwoBijective_of_sphereHurewiczTwoCanonical

theorem hurewiczThreeBijective_of_sphereHurewiczThreeCanonical
    (h : SphereHurewiczThreeCanonical X) : HurewiczThreeBijective X :=
  fun x hπ => (h x hπ).1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.hurewiczThreeBijective_of_sphereHurewiczThreeCanonical then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.hurewiczThreeBijective_of_sphereHurewiczThreeCanonical"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.hurewiczThreeBijective_of_sphereHurewiczThreeCanonical ``Submission.DifferentialGeometry.Topology.hurewiczThreeBijective_of_sphereHurewiczThreeCanonical

theorem sphereHurewiczTwoCanonical_of_hurewiczTwoFrontier
    (h : HurewiczTwoBijective X ∧ HurewiczTwoMultiplicative X) :
    SphereHurewiczTwoCanonical X :=
  fun x => ⟨h.1 x, h.2 x (integralLiftedSphereGenerator.{u} 1)
    (integralLiftedSphereGenerator_isGenerator 1)⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.sphereHurewiczTwoCanonical_of_hurewiczTwoFrontier then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.sphereHurewiczTwoCanonical_of_hurewiczTwoFrontier"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.sphereHurewiczTwoCanonical_of_hurewiczTwoFrontier ``Submission.DifferentialGeometry.Topology.sphereHurewiczTwoCanonical_of_hurewiczTwoFrontier

theorem sphereHurewiczThreeCanonical_of_hurewiczThreeFrontier
    (h : HurewiczThreeBijective X ∧ HurewiczThreeMultiplicative X) :
    SphereHurewiczThreeCanonical X :=
  fun x hπ => ⟨h.1 x hπ, h.2 x hπ (integralLiftedSphereGenerator.{u} 2)
    (integralLiftedSphereGenerator_isGenerator 2)⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.sphereHurewiczThreeCanonical_of_hurewiczThreeFrontier then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.sphereHurewiczThreeCanonical_of_hurewiczThreeFrontier"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.sphereHurewiczThreeCanonical_of_hurewiczThreeFrontier ``Submission.DifferentialGeometry.Topology.sphereHurewiczThreeCanonical_of_hurewiczThreeFrontier

theorem hurewiczTwoFrontier_iff_sphereHurewiczTwoCanonical :
    (HurewiczTwoBijective X ∧ HurewiczTwoMultiplicative X) ↔
      SphereHurewiczTwoCanonical X :=
  ⟨sphereHurewiczTwoCanonical_of_hurewiczTwoFrontier,
    fun h => ⟨hurewiczTwoBijective_of_sphereHurewiczTwoCanonical h,
      fun x c hc => (IsSphereHurewiczIsomorphism.of_isSphereHomologyGenerator 1 (c := c) x hc
        (h x)).2⟩⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.hurewiczTwoFrontier_iff_sphereHurewiczTwoCanonical then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.hurewiczTwoFrontier_iff_sphereHurewiczTwoCanonical"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.hurewiczTwoFrontier_iff_sphereHurewiczTwoCanonical ``Submission.DifferentialGeometry.Topology.hurewiczTwoFrontier_iff_sphereHurewiczTwoCanonical

theorem hurewiczThreeFrontier_iff_sphereHurewiczThreeCanonical :
    (HurewiczThreeBijective X ∧ HurewiczThreeMultiplicative X) ↔
      SphereHurewiczThreeCanonical X :=
  ⟨sphereHurewiczThreeCanonical_of_hurewiczThreeFrontier,
    fun h => ⟨hurewiczThreeBijective_of_sphereHurewiczThreeCanonical h,
      fun x hπ c hc => (IsSphereHurewiczIsomorphism.of_isSphereHomologyGenerator 2 (c := c) x hc
        (h x hπ)).2⟩⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.hurewiczThreeFrontier_iff_sphereHurewiczThreeCanonical then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.hurewiczThreeFrontier_iff_sphereHurewiczThreeCanonical"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.hurewiczThreeFrontier_iff_sphereHurewiczThreeCanonical ``Submission.DifferentialGeometry.Topology.hurewiczThreeFrontier_iff_sphereHurewiczThreeCanonical

theorem hurewicz_two_isomorphism_of_frontier
    (h : HurewiczTwoBijective X ∧ HurewiczTwoMultiplicative X)
    (x : X) (c : integralSingularHomology 2 (liftedHomotopySphere.{u} 1))
    (hc : IsSphereHomologyGenerator 1 c) :
    Function.Bijective (sphereHurewicz 1 x c) ∧
      ∀ a b : HomotopyGroup (Fin 2) X x,
        sphereHurewicz 1 x c (a * b) = sphereHurewicz 1 x c a + sphereHurewicz 1 x c b :=
  sphereHurewicz_two_isomorphism_of_canonical_generator
    (sphereHurewiczTwoCanonical_of_hurewiczTwoFrontier h) x c hc

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.hurewicz_two_isomorphism_of_frontier then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.hurewicz_two_isomorphism_of_frontier"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.hurewicz_two_isomorphism_of_frontier ``Submission.DifferentialGeometry.Topology.hurewicz_two_isomorphism_of_frontier

theorem hurewicz_three_isomorphism_of_frontier
    (h : HurewiczThreeBijective X ∧ HurewiczThreeMultiplicative X)
    (x : X) (hπ₂ : Subsingleton (HomotopyGroup (Fin 2) X x))
    (c : integralSingularHomology 3 (liftedHomotopySphere.{u} 2))
    (hc : IsSphereHomologyGenerator 2 c) :
    Function.Bijective (sphereHurewicz 2 x c) ∧
      ∀ a b : HomotopyGroup (Fin 3) X x,
        sphereHurewicz 2 x c (a * b) = sphereHurewicz 2 x c a + sphereHurewicz 2 x c b :=
  sphereHurewicz_three_isomorphism_of_canonical_generator
    (sphereHurewiczThreeCanonical_of_hurewiczThreeFrontier h) x hπ₂ c hc

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.hurewicz_three_isomorphism_of_frontier then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.hurewicz_three_isomorphism_of_frontier"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.hurewicz_three_isomorphism_of_frontier ``Submission.DifferentialGeometry.Topology.hurewicz_three_isomorphism_of_frontier

theorem hurewicz_two_isomorphism_iff_frontier :
    (∀ (x : X) (c : integralSingularHomology 2 (liftedHomotopySphere.{u} 1))
      (_ : IsSphereHomologyGenerator 1 c),
        Function.Bijective (sphereHurewicz 1 x c) ∧
          ∀ a b : HomotopyGroup (Fin 2) X x,
            sphereHurewicz 1 x c (a * b) = sphereHurewicz 1 x c a + sphereHurewicz 1 x c b) ↔
      HurewiczTwoBijective X ∧ HurewiczTwoMultiplicative X :=
  ⟨fun h => ⟨fun x => (h x (integralLiftedSphereGenerator.{u} 1)
      (integralLiftedSphereGenerator_isGenerator 1)).1,
    fun x c hc => (h x c hc).2⟩,
    fun h x c hc => hurewicz_two_isomorphism_of_frontier h x c hc⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.hurewicz_two_isomorphism_iff_frontier then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.hurewicz_two_isomorphism_iff_frontier"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.hurewicz_two_isomorphism_iff_frontier ``Submission.DifferentialGeometry.Topology.hurewicz_two_isomorphism_iff_frontier

theorem hurewicz_three_isomorphism_iff_frontier :
    (∀ (x : X) (_ : Subsingleton (HomotopyGroup (Fin 2) X x))
      (c : integralSingularHomology 3 (liftedHomotopySphere.{u} 2))
      (_ : IsSphereHomologyGenerator 2 c),
        Function.Bijective (sphereHurewicz 2 x c) ∧
          ∀ a b : HomotopyGroup (Fin 3) X x,
            sphereHurewicz 2 x c (a * b) = sphereHurewicz 2 x c a + sphereHurewicz 2 x c b) ↔
      HurewiczThreeBijective X ∧ HurewiczThreeMultiplicative X :=
  ⟨fun h => ⟨fun x hπ => (h x hπ (integralLiftedSphereGenerator.{u} 2)
      (integralLiftedSphereGenerator_isGenerator 2)).1,
    fun x hπ c hc => (h x hπ c hc).2⟩,
    fun h x hπ c hc => hurewicz_three_isomorphism_of_frontier h x hπ c hc⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.hurewicz_three_isomorphism_iff_frontier then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.hurewicz_three_isomorphism_iff_frontier"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.hurewicz_three_isomorphism_iff_frontier ``Submission.DifferentialGeometry.Topology.hurewicz_three_isomorphism_iff_frontier

theorem hurewiczTwoMultiplicative_of_liftedSquareCollapse_bijective
    (hT : Function.Bijective (integralRelativeHomologyMap 2 liftedSquareCollapse.{u}
      liftedSquareCollapse_mapsTo))
    (hrel : ∃ φ : integralRelativeHomology 2 (liftedSquareBoundary.{u}) →ₗ[ℤ] ℤ,
      φ liftedSquareRelativeFundamentalClass.{u} = 1) :
    HurewiczTwoMultiplicative X :=
  fun x c hc => hurewicz_two_mul_of_liftedSquareCollapse_bijective hT hrel x c hc

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.hurewiczTwoMultiplicative_of_liftedSquareCollapse_bijective then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.hurewiczTwoMultiplicative_of_liftedSquareCollapse_bijective"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.hurewiczTwoMultiplicative_of_liftedSquareCollapse_bijective ``Submission.DifferentialGeometry.Topology.hurewiczTwoMultiplicative_of_liftedSquareCollapse_bijective

theorem hurewiczTwoSphereGeneration_of_hurewiczTwoBijective [PathConnectedSpace X]
    (h : HurewiczTwoBijective X) (x : X) : HurewiczTwoSphereGeneration X := by
  change ∀ y : integralSingularHomology 2 X,
    ∃ f : C(Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1, X),
      freeSphereHomologyImage 1 (integralLiftedSphereGenerator.{u} 1) (ZerothHomotopy.mk f) = y
  intro y
  obtain ⟨a, ha⟩ :=
    (surjective_sphereHurewicz_iff_surjective_freeSphereHomologyImage 1 x
      (integralLiftedSphereGenerator.{u} 1)).mp (h x).2 y
  have hout : ZerothHomotopy.mk (Quotient.out a) = a := Quotient.out_eq a
  exact ⟨Quotient.out a, by rw [hout]; exact ha⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.hurewiczTwoSphereGeneration_of_hurewiczTwoBijective then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.hurewiczTwoSphereGeneration_of_hurewiczTwoBijective"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.hurewiczTwoSphereGeneration_of_hurewiczTwoBijective ``Submission.DifferentialGeometry.Topology.hurewiczTwoSphereGeneration_of_hurewiczTwoBijective

theorem hurewiczTwoSphereNullhomotopic_of_hurewiczTwoBijective [PathConnectedSpace X]
    (h : HurewiczTwoBijective X) (x : X) : HurewiczTwoSphereNullhomotopic X := by
  change ∀ f : C(Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1, X),
    freeSphereHomologyImage 1 (integralLiftedSphereGenerator.{u} 1) (ZerothHomotopy.mk f) = 0 →
      f.Nullhomotopic
  intro f hf
  obtain ⟨a, ha⟩ := homotopyGroupToFreeSphere_surjective 1 x (ZerothHomotopy.mk f)
  have hzero : sphereHurewicz 1 x (integralLiftedSphereGenerator.{u} 1) a = 0 := by
    change freeSphereHomologyImage 1 (integralLiftedSphereGenerator.{u} 1)
      (homotopyGroupToFreeSphere 1 x a) = 0
    rw [ha, hf]
  have hone := forall_sphereHurewicz_eq_zero_of_injective 1 x
    (integralLiftedSphereGenerator.{u} 1) (h x).1 a hzero
  have hmk : ZerothHomotopy.mk f = ZerothHomotopy.mk (ContinuousMap.const _ x) := by
    rw [← ha, hone, homotopyGroupToFreeSphere_one]
  exact (zerothHomotopy_mk_eq_const_iff_nullhomotopic 1 x f).mp hmk

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.hurewiczTwoSphereNullhomotopic_of_hurewiczTwoBijective then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.hurewiczTwoSphereNullhomotopic_of_hurewiczTwoBijective"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.hurewiczTwoSphereNullhomotopic_of_hurewiczTwoBijective ``Submission.DifferentialGeometry.Topology.hurewiczTwoSphereNullhomotopic_of_hurewiczTwoBijective

theorem hurewiczThreeSphereGeneration_of_hurewiczThreeBijective [PathConnectedSpace X]
    (h : HurewiczThreeBijective X) (x : X)
    (hπ : Subsingleton (HomotopyGroup (Fin 2) X x)) : HurewiczThreeSphereGeneration X := by
  change ∀ y : integralSingularHomology 3 X,
    ∃ f : C(Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1, X),
      freeSphereHomologyImage 2 (integralLiftedSphereGenerator.{u} 2) (ZerothHomotopy.mk f) = y
  intro y
  obtain ⟨a, ha⟩ :=
    (surjective_sphereHurewicz_iff_surjective_freeSphereHomologyImage 2 x
      (integralLiftedSphereGenerator.{u} 2)).mp (h x hπ).2 y
  have hout : ZerothHomotopy.mk (Quotient.out a) = a := Quotient.out_eq a
  exact ⟨Quotient.out a, by rw [hout]; exact ha⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.hurewiczThreeSphereGeneration_of_hurewiczThreeBijective then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.hurewiczThreeSphereGeneration_of_hurewiczThreeBijective"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.hurewiczThreeSphereGeneration_of_hurewiczThreeBijective ``Submission.DifferentialGeometry.Topology.hurewiczThreeSphereGeneration_of_hurewiczThreeBijective

theorem hurewiczThreeSphereNullhomotopic_of_hurewiczThreeBijective [PathConnectedSpace X]
    (h : HurewiczThreeBijective X) (x : X)
    (hπ : Subsingleton (HomotopyGroup (Fin 2) X x)) :
    HurewiczThreeSphereNullhomotopic X := by
  change ∀ f : C(Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1, X),
    freeSphereHomologyImage 2 (integralLiftedSphereGenerator.{u} 2) (ZerothHomotopy.mk f) = 0 →
      f.Nullhomotopic
  intro f hf
  obtain ⟨a, ha⟩ := homotopyGroupToFreeSphere_surjective 2 x (ZerothHomotopy.mk f)
  have hzero : sphereHurewicz 2 x (integralLiftedSphereGenerator.{u} 2) a = 0 := by
    change freeSphereHomologyImage 2 (integralLiftedSphereGenerator.{u} 2)
      (homotopyGroupToFreeSphere 2 x a) = 0
    rw [ha, hf]
  have hone := forall_sphereHurewicz_eq_zero_of_injective 2 x
    (integralLiftedSphereGenerator.{u} 2) (h x hπ).1 a hzero
  have hmk : ZerothHomotopy.mk f = ZerothHomotopy.mk (ContinuousMap.const _ x) := by
    rw [← ha, hone, homotopyGroupToFreeSphere_one]
  exact (zerothHomotopy_mk_eq_const_iff_nullhomotopic 2 x f).mp hmk

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.hurewiczThreeSphereNullhomotopic_of_hurewiczThreeBijective then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.hurewiczThreeSphereNullhomotopic_of_hurewiczThreeBijective"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.hurewiczThreeSphereNullhomotopic_of_hurewiczThreeBijective ``Submission.DifferentialGeometry.Topology.hurewiczThreeSphereNullhomotopic_of_hurewiczThreeBijective

theorem hurewiczTwoBijective_iff_sphereCriterion_of_multiplicative [SimplyConnectedSpace X]
    (hmul : HurewiczTwoMultiplicative X) (x₀ : X) :
    HurewiczTwoBijective X ↔
      HurewiczTwoSphereGeneration X ∧ HurewiczTwoSphereNullhomotopic X := by
  constructor
  · intro h
    exact ⟨hurewiczTwoSphereGeneration_of_hurewiczTwoBijective h x₀,
      hurewiczTwoSphereNullhomotopic_of_hurewiczTwoBijective h x₀⟩
  · rintro ⟨hg, hk⟩
    have hgen : ∀ y : integralSingularHomology 2 X,
        ∃ f : C(Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1, X),
          freeSphereHomologyImage 1 (integralLiftedSphereGenerator.{u} 1)
            (ZerothHomotopy.mk f) = y := hg
    have hnull' : ∀ f : C(Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1, X),
        freeSphereHomologyImage 1 (integralLiftedSphereGenerator.{u} 1)
          (ZerothHomotopy.mk f) = 0 → f.Nullhomotopic := hk
    have hnull : ∀ f : C(Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1, X),
        freeSphereHomologyImage 1 (integralLiftedSphereGenerator.{u} 1)
          (ZerothHomotopy.mk f) = 0 →
        ZerothHomotopy.mk f = ZerothHomotopy.mk (ContinuousMap.const _ x₀) :=
      fun f hf => (zerothHomotopy_mk_eq_const_iff_nullhomotopic 1 x₀ f).mpr (hnull' f hf)
    have hx₀ : Function.Bijective (sphereHurewicz 1 x₀
        (integralLiftedSphereGenerator.{u} 1)) :=
      (bijective_sphereHurewicz_iff_forall_exists_map_eq_and_nullhomotopic_of_additive 1 x₀
        (integralLiftedSphereGenerator.{u} 1)
        (hmul x₀ (integralLiftedSphereGenerator.{u} 1)
          (integralLiftedSphereGenerator_isGenerator 1))).mpr ⟨hgen, hnull⟩
    intro x
    exact (bijective_sphereHurewicz_iff_of_path 1
      (PathConnectedSpace.somePath x₀ x) (integralLiftedSphereGenerator.{u} 1)).mp hx₀

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.hurewiczTwoBijective_iff_sphereCriterion_of_multiplicative then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.hurewiczTwoBijective_iff_sphereCriterion_of_multiplicative"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.hurewiczTwoBijective_iff_sphereCriterion_of_multiplicative ``Submission.DifferentialGeometry.Topology.hurewiczTwoBijective_iff_sphereCriterion_of_multiplicative

theorem hurewiczThreeBijective_iff_sphereCriterion_of_multiplicative [SimplyConnectedSpace X]
    (hmul : HurewiczThreeMultiplicative X) (x₀ : X)
    (hπ₀ : Subsingleton (HomotopyGroup (Fin 2) X x₀)) :
    HurewiczThreeBijective X ↔
      HurewiczThreeSphereGeneration X ∧ HurewiczThreeSphereNullhomotopic X := by
  constructor
  · intro h
    exact ⟨hurewiczThreeSphereGeneration_of_hurewiczThreeBijective h x₀ hπ₀,
      hurewiczThreeSphereNullhomotopic_of_hurewiczThreeBijective h x₀ hπ₀⟩
  · rintro ⟨hg, hk⟩
    have hgen : ∀ y : integralSingularHomology 3 X,
        ∃ f : C(Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1, X),
          freeSphereHomologyImage 2 (integralLiftedSphereGenerator.{u} 2)
            (ZerothHomotopy.mk f) = y := hg
    have hnull' : ∀ f : C(Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1, X),
        freeSphereHomologyImage 2 (integralLiftedSphereGenerator.{u} 2)
          (ZerothHomotopy.mk f) = 0 → f.Nullhomotopic := hk
    have hnull : ∀ f : C(Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1, X),
        freeSphereHomologyImage 2 (integralLiftedSphereGenerator.{u} 2)
          (ZerothHomotopy.mk f) = 0 →
        ZerothHomotopy.mk f = ZerothHomotopy.mk (ContinuousMap.const _ x₀) :=
      fun f hf => (zerothHomotopy_mk_eq_const_iff_nullhomotopic 2 x₀ f).mpr (hnull' f hf)
    have hx₀ : Function.Bijective (sphereHurewicz 2 x₀
        (integralLiftedSphereGenerator.{u} 2)) :=
      (bijective_sphereHurewicz_iff_forall_exists_map_eq_and_nullhomotopic_of_additive 2 x₀
        (integralLiftedSphereGenerator.{u} 2)
        (hmul x₀ hπ₀ (integralLiftedSphereGenerator.{u} 2)
          (integralLiftedSphereGenerator_isGenerator 2))).mpr ⟨hgen, hnull⟩
    intro x hπ
    exact (bijective_sphereHurewicz_iff_of_path 2
      (PathConnectedSpace.somePath x₀ x) (integralLiftedSphereGenerator.{u} 2)).mp hx₀

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.hurewiczThreeBijective_iff_sphereCriterion_of_multiplicative then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.hurewiczThreeBijective_iff_sphereCriterion_of_multiplicative"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.hurewiczThreeBijective_iff_sphereCriterion_of_multiplicative ``Submission.DifferentialGeometry.Topology.hurewiczThreeBijective_iff_sphereCriterion_of_multiplicative

theorem hurewiczTwoBijective_punit : HurewiczTwoBijective PUnit.{u + 1} :=
  fun x => (sphereHurewiczTwoCanonical_punit x).1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.hurewiczTwoBijective_punit then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.hurewiczTwoBijective_punit"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.hurewiczTwoBijective_punit ``Submission.DifferentialGeometry.Topology.hurewiczTwoBijective_punit

theorem hurewiczThreeBijective_punit : HurewiczThreeBijective PUnit.{u + 1} :=
  fun x hπ => (sphereHurewiczThreeCanonical_punit x hπ).1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.hurewiczThreeBijective_punit then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.hurewiczThreeBijective_punit"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.hurewiczThreeBijective_punit ``Submission.DifferentialGeometry.Topology.hurewiczThreeBijective_punit

theorem hurewiczTwoMultiplicative_punit : HurewiczTwoMultiplicative PUnit.{u + 1} :=
  fun x c hc => (IsSphereHurewiczIsomorphism.of_isSphereHomologyGenerator 1 (c := c) x hc
    (sphereHurewiczTwoCanonical_punit x)).2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.hurewiczTwoMultiplicative_punit then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.hurewiczTwoMultiplicative_punit"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.hurewiczTwoMultiplicative_punit ``Submission.DifferentialGeometry.Topology.hurewiczTwoMultiplicative_punit

theorem hurewiczThreeMultiplicative_punit : HurewiczThreeMultiplicative PUnit.{u + 1} :=
  fun x hπ c hc => (IsSphereHurewiczIsomorphism.of_isSphereHomologyGenerator 2 (c := c) x hc
    (sphereHurewiczThreeCanonical_punit x hπ)).2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.hurewiczThreeMultiplicative_punit then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.hurewiczThreeMultiplicative_punit"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.hurewiczThreeMultiplicative_punit ``Submission.DifferentialGeometry.Topology.hurewiczThreeMultiplicative_punit

theorem hurewiczTwoBijective_of_subsingleton
    (hπ : ∀ x : X, Subsingleton (HomotopyGroup (Fin 2) X x))
    (hH : Subsingleton (integralSingularHomology 2 X)) : HurewiczTwoBijective X := by
  refine fun x => ?_
  have hinst := hπ x
  have hinst' := hH
  exact (IsSphereHurewiczIsomorphism.of_subsingleton 1 x
    (integralLiftedSphereGenerator.{u} 1)).1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.hurewiczTwoBijective_of_subsingleton then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.hurewiczTwoBijective_of_subsingleton"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.hurewiczTwoBijective_of_subsingleton ``Submission.DifferentialGeometry.Topology.hurewiczTwoBijective_of_subsingleton

theorem hurewiczTwoMultiplicative_of_subsingleton
    (hπ : ∀ x : X, Subsingleton (HomotopyGroup (Fin 2) X x))
    (hH : Subsingleton (integralSingularHomology 2 X)) : HurewiczTwoMultiplicative X := by
  refine fun x c hc => ?_
  have hinst := hπ x
  have hinst' := hH
  exact (IsSphereHurewiczIsomorphism.of_subsingleton 1 x c).2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.hurewiczTwoMultiplicative_of_subsingleton then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.hurewiczTwoMultiplicative_of_subsingleton"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.hurewiczTwoMultiplicative_of_subsingleton ``Submission.DifferentialGeometry.Topology.hurewiczTwoMultiplicative_of_subsingleton

theorem not_surjective_sphereHurewicz_zero_twoSphere
    (x : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
    ¬ Function.Surjective (sphereHurewicz 1 x
      (0 : integralSingularHomology 2 (liftedHomotopySphere.{0} 1))) := by
  intro hsurj
  have hzero : sphereHurewicz 1 x
      (0 : integralSingularHomology 2 (liftedHomotopySphere.{0} 1)) = 0 :=
    funext fun a => sphereHurewicz_zero 1 x a
  have hsub : Subsingleton
      (integralSingularHomology 2 (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)) :=
    ⟨fun a b => by
      obtain ⟨p, hp⟩ := hsurj a
      obtain ⟨q, hq⟩ := hsurj b
      rw [← hp, ← hq, hzero]
      rfl⟩
  exact not_subsingleton_integralSingularHomology_two_twoSphere hsub

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.not_surjective_sphereHurewicz_zero_twoSphere then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.not_surjective_sphereHurewicz_zero_twoSphere"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.not_surjective_sphereHurewicz_zero_twoSphere ``Submission.DifferentialGeometry.Topology.not_surjective_sphereHurewicz_zero_twoSphere

end DifferentialGeometry.Topology
