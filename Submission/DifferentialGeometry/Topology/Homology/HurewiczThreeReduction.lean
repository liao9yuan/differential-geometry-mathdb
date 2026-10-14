import Submission.DifferentialGeometry.Topology.Homology.HurewiczLowDegreeCriterion

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.ContinuousMap _root_.Metric

universe u

namespace DifferentialGeometry.Topology

variable {X : Type u} [TopologicalSpace X]

theorem hurewiczThreeSphereGeneration_of_exists (x : X)
    (hmul : ∀ a b : HomotopyGroup (Fin 3) X x,
      sphereHurewicz (X := X) 2 x (integralLiftedSphereGenerator.{u} 2) (a * b) =
        sphereHurewicz (X := X) 2 x (integralLiftedSphereGenerator.{u} 2) a +
          sphereHurewicz (X := X) 2 x (integralLiftedSphereGenerator.{u} 2) b)
    (a₀ : HomotopyGroup (Fin 3) X x)
    (z₀ : integralSingularHomology 3 X)
    (ha₀ : sphereHurewicz (X := X) 2 x (integralLiftedSphereGenerator.{u} 2) a₀ = z₀)
    (hgen : ∀ y : integralSingularHomology 3 X, ∃ k : ℤ, y = k • z₀) :
    HurewiczThreeSphereGeneration X := by
  intro y
  obtain ⟨k, hk⟩ := hgen y
  refine ⟨Quotient.out (homotopyGroupToFreeSphere 2 x (a₀ ^ k)), ?_⟩
  have hout : ZerothHomotopy.mk (Quotient.out (homotopyGroupToFreeSphere 2 x (a₀ ^ k))) =
      homotopyGroupToFreeSphere 2 x (a₀ ^ k) := Quotient.out_eq _
  rw [hout]
  change sphereHurewicz (X := X) 2 x (integralLiftedSphereGenerator.{u} 2) (a₀ ^ k) = y
  rw [sphereHurewicz_zpow_of_additive (X := X) 2 x (integralLiftedSphereGenerator.{u} 2)
      hmul a₀ k,
    ha₀, hk]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.hurewiczThreeSphereGeneration_of_exists then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.hurewiczThreeSphereGeneration_of_exists"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.hurewiczThreeSphereGeneration_of_exists ``Submission.DifferentialGeometry.Topology.hurewiczThreeSphereGeneration_of_exists

def HurewiczThreeHypothesis (X : Type u) [TopologicalSpace X] : Prop :=
  ∀ x : X, Subsingleton (HomotopyGroup (Fin 2) X x) →
    Function.Bijective
      (sphereHurewicz (X := X) 2 x (integralLiftedSphereGenerator.{u} 2)) ∧
    ∀ a b : HomotopyGroup (Fin 3) X x,
      sphereHurewicz (X := X) 2 x (integralLiftedSphereGenerator.{u} 2) (a * b) =
        sphereHurewicz (X := X) 2 x (integralLiftedSphereGenerator.{u} 2) a +
          sphereHurewicz (X := X) 2 x (integralLiftedSphereGenerator.{u} 2) b

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.HurewiczThreeHypothesis then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.HurewiczThreeHypothesis"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.HurewiczThreeHypothesis ``Submission.DifferentialGeometry.Topology.HurewiczThreeHypothesis

theorem hurewiczThreeHypothesis_of_sphereHurewiczThreeCanonical
    (h : SphereHurewiczThreeCanonical X) : HurewiczThreeHypothesis X :=
  fun x hπ => h x hπ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.hurewiczThreeHypothesis_of_sphereHurewiczThreeCanonical then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.hurewiczThreeHypothesis_of_sphereHurewiczThreeCanonical"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.hurewiczThreeHypothesis_of_sphereHurewiczThreeCanonical ``Submission.DifferentialGeometry.Topology.hurewiczThreeHypothesis_of_sphereHurewiczThreeCanonical

theorem hurewiczThreeHypothesis_punit : HurewiczThreeHypothesis PUnit.{u + 1} :=
  hurewiczThreeHypothesis_of_sphereHurewiczThreeCanonical sphereHurewiczThreeCanonical_punit

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.hurewiczThreeHypothesis_punit then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.hurewiczThreeHypothesis_punit"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.hurewiczThreeHypothesis_punit ``Submission.DifferentialGeometry.Topology.hurewiczThreeHypothesis_punit

theorem sphereHurewiczThreeCanonical_of_hurewiczThreeHypothesis
    (h : HurewiczThreeHypothesis X) :
    SphereHurewiczThreeCanonical X :=
  fun x hπ => h x hπ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.sphereHurewiczThreeCanonical_of_hurewiczThreeHypothesis then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.sphereHurewiczThreeCanonical_of_hurewiczThreeHypothesis"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.sphereHurewiczThreeCanonical_of_hurewiczThreeHypothesis ``Submission.DifferentialGeometry.Topology.sphereHurewiczThreeCanonical_of_hurewiczThreeHypothesis

theorem hurewiczThreeHypothesis_iff_sphereHurewiczThreeCanonical :
    HurewiczThreeHypothesis X ↔ SphereHurewiczThreeCanonical X :=
  ⟨fun h => sphereHurewiczThreeCanonical_of_hurewiczThreeHypothesis h,
    hurewiczThreeHypothesis_of_sphereHurewiczThreeCanonical⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.hurewiczThreeHypothesis_iff_sphereHurewiczThreeCanonical then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.hurewiczThreeHypothesis_iff_sphereHurewiczThreeCanonical"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.hurewiczThreeHypothesis_iff_sphereHurewiczThreeCanonical ``Submission.DifferentialGeometry.Topology.hurewiczThreeHypothesis_iff_sphereHurewiczThreeCanonical

end DifferentialGeometry.Topology
