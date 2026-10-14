import Submission.DifferentialGeometry.Topology.Homology.SquareSphereGenerator

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

universe u

namespace DifferentialGeometry.Topology

variable {X : Type u} [TopologicalSpace X]

theorem sphereHurewicz_two_mul (x : X)
    (c : integralSingularHomology 2 (liftedHomotopySphere.{u} 1))
    (a b : HomotopyGroup (Fin 2) X x) :
    sphereHurewicz 1 x c (a * b) = sphereHurewicz 1 x c a + sphereHurewicz 1 x c b := by
  obtain ⟨k, rfl⟩ :=
    (isSphereHomologyGenerator_iff_forall_exists_zsmul 1 squareSphereFundamentalClass).mp
      isSphereHomologyGenerator_squareSphereFundamentalClass c
  rw [sphereHurewicz_zsmul, sphereHurewicz_zsmul, sphereHurewicz_zsmul,
    hurewicz_two_mul_squareSphereFundamentalClass, zsmul_add]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.sphereHurewicz_two_mul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.sphereHurewicz_two_mul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.sphereHurewicz_two_mul ``Submission.DifferentialGeometry.Topology.sphereHurewicz_two_mul

end DifferentialGeometry.Topology
