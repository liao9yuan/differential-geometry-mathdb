import Submission.DifferentialGeometry.Topology.Homology.HurewiczTwo
import Submission.DifferentialGeometry.Topology.Homology.HurewiczThree

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission












noncomputable section

universe u

namespace DifferentialGeometry.Topology

variable {X : Type u} [TopologicalSpace X] [SimplyConnectedSpace X]




theorem hurewicz_two_isomorphism (x : X)
    (c : integralSingularHomology 2 (liftedHomotopySphere.{u} 1))
    (hc : IsSphereHomologyGenerator 1 c) :
    Function.Bijective (sphereHurewicz 1 x c) ∧
      ∀ a b : HomotopyGroup (Fin 2) X x,
        sphereHurewicz 1 x c (a * b) = sphereHurewicz 1 x c a + sphereHurewicz 1 x c b :=
  ⟨bijective_sphereHurewicz_two x c hc, sphereHurewicz_two_mul x c⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.hurewicz_two_isomorphism then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.hurewicz_two_isomorphism"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.hurewicz_two_isomorphism ``Submission.DifferentialGeometry.Topology.hurewicz_two_isomorphism




theorem hurewicz_three_isomorphism (x : X)
    (hπ₂ : Subsingleton (HomotopyGroup (Fin 2) X x))
    (c : integralSingularHomology 3 (liftedHomotopySphere.{u} 2))
    (hc : IsSphereHomologyGenerator 2 c) :
    Function.Bijective (sphereHurewicz 2 x c) ∧
      ∀ a b : HomotopyGroup (Fin 3) X x,
        sphereHurewicz 2 x c (a * b) = sphereHurewicz 2 x c a + sphereHurewicz 2 x c b := by
  let _ := hπ₂
  exact ⟨bijective_sphereHurewicz_three x c hc, sphereHurewicz_three_mul x c⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.hurewicz_three_isomorphism then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.hurewicz_three_isomorphism"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.hurewicz_three_isomorphism ``Submission.DifferentialGeometry.Topology.hurewicz_three_isomorphism

theorem bijective_sphereHurewicz_iff_bijective_freeSphereHomologyImage (n : ℕ) (x : X)
    (c : integralSingularHomology (n + 1) (liftedHomotopySphere.{u} n)) :
    Function.Bijective (sphereHurewicz n x c) ↔
      Function.Bijective (freeSphereHomologyImage (X := X) n c) :=
  Equiv.bijective_comp (homotopyGroupFreeSphereEquiv n x)
    (freeSphereHomologyImage (X := X) n c)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.bijective_sphereHurewicz_iff_bijective_freeSphereHomologyImage then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.bijective_sphereHurewicz_iff_bijective_freeSphereHomologyImage"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.bijective_sphereHurewicz_iff_bijective_freeSphereHomologyImage ``Submission.DifferentialGeometry.Topology.bijective_sphereHurewicz_iff_bijective_freeSphereHomologyImage

end DifferentialGeometry.Topology
