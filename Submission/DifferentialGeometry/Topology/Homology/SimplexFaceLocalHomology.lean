import Submission.DifferentialGeometry.Topology.Simplex.FaceLocalHomeomorph
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

theorem integralRelativeHomologyMap_liftedFaceToBoundary_bijective
    {n : ℕ} (k : ℕ) (i : Fin (n + 2))
    (p : ULift.{u} (stdSimplex ℝ (Fin (n + 1))))
    (hp : p.down ∉ Simplex.boundary (Fin (n + 1))) :
    Function.Bijective (integralRelativeHomologyMap k (Simplex.liftedFaceToBoundary i)
      (Simplex.liftedFaceToBoundary_mapsTo i p)) := by
  let e := Simplex.liftedFaceOpenPartialHomeomorph.{u} i
  have hmap := integralRelativeHomologyMap_eq_of_eqOn_openPartialHomeomorph k
    (Simplex.liftedFaceToBoundary i) e p e.source e.open_source hp Subset.rfl
    (fun _ _ => rfl) (Simplex.liftedFaceToBoundary_mapsTo i p)
  have hbij : Function.Bijective
      (integralLocalHomologyOpenPartialHomeomorphIso k e p hp).hom.hom :=
    (CategoryTheory.ConcreteCategory.isIso_iff_bijective _).mp inferInstance
  exact hmap.symm ▸ hbij

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralRelativeHomologyMap_liftedFaceToBoundary_bijective then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralRelativeHomologyMap_liftedFaceToBoundary_bijective"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralRelativeHomologyMap_liftedFaceToBoundary_bijective ``Submission.DifferentialGeometry.Topology.integralRelativeHomologyMap_liftedFaceToBoundary_bijective

theorem integralRelativeHomologyMap_liftedFaceToBoundary_barycenter_bijective
    {n : ℕ} (k : ℕ) (i : Fin (n + 2)) :
    Function.Bijective (integralRelativeHomologyMap k (Simplex.liftedFaceToBoundary.{u} i)
      (Simplex.liftedFaceToBoundary_mapsTo i (ULift.up stdSimplex.barycenter))) := by
  apply integralRelativeHomologyMap_liftedFaceToBoundary_bijective
  exact fun h => Simplex.boundary_ne_barycenter h rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralRelativeHomologyMap_liftedFaceToBoundary_barycenter_bijective then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralRelativeHomologyMap_liftedFaceToBoundary_barycenter_bijective"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralRelativeHomologyMap_liftedFaceToBoundary_barycenter_bijective ``Submission.DifferentialGeometry.Topology.integralRelativeHomologyMap_liftedFaceToBoundary_barycenter_bijective

end DifferentialGeometry.Topology
