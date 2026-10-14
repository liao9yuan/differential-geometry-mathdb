import Submission.DifferentialGeometry.Topology.Homotopy.CubeSphereLocalHomeomorph
import Submission.DifferentialGeometry.Topology.Homology.LocalGerm

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Set

universe u

namespace DifferentialGeometry.Topology

theorem integralRelativeHomologyMap_liftedCubeSphereProjection_bijective (n k : ℕ)
    (x : ULift.{u} (Fin (n + 1) → unitInterval))
    (hx : x.down ∈ cubeInterior (Fin (n + 1))) :
    Function.Bijective (integralRelativeHomologyMap k (liftedCubeSphereProjection n)
      (liftedCubeSphereProjection_mapsTo n x hx)) := by
  let e := liftedCubeSphereProjectionOpenPartialHomeomorph.{u} n
  have hmap := integralRelativeHomologyMap_eq_of_eqOn_openPartialHomeomorph k
    (liftedCubeSphereProjection n) e x e.source e.open_source hx Subset.rfl
    (fun _ _ => rfl) (liftedCubeSphereProjection_mapsTo n x hx)
  have hbij : Function.Bijective
      (integralLocalHomologyOpenPartialHomeomorphIso k e x hx).hom.hom :=
    (CategoryTheory.ConcreteCategory.isIso_iff_bijective _).mp inferInstance
  exact hmap.symm ▸ hbij

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralRelativeHomologyMap_liftedCubeSphereProjection_bijective then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralRelativeHomologyMap_liftedCubeSphereProjection_bijective"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralRelativeHomologyMap_liftedCubeSphereProjection_bijective ``Submission.DifferentialGeometry.Topology.integralRelativeHomologyMap_liftedCubeSphereProjection_bijective

end DifferentialGeometry.Topology
