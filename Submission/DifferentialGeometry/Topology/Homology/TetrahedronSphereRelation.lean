import Submission.DifferentialGeometry.Topology.Homology.TetrahedronSpherePairing
import Submission.DifferentialGeometry.Topology.Homology.FourSimplexTerminalFaces
import Submission.DifferentialGeometry.Topology.Simplex.FourSimplexHomotopyRelation

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

namespace DifferentialGeometry.Topology

open _root_.CategoryTheory _root_.AlgebraicTopology
open scoped _root_.Simplicial

universe u

variable {X : Type u} [TopologicalSpace X] [SimplyConnectedSpace X]

theorem integralSingularTetrahedronSphereClass_face_relation
    (x : X) [Subsingleton (HomotopyGroup (Fin 2) X x)]
    (τ : integralSingularSimplex 4 X) :
    integralSingularTetrahedronSphereClass x ((TopCat.toSSet.obj (TopCat.of X)).δ 0 τ) *
      integralSingularTetrahedronSphereClass x ((TopCat.toSSet.obj (TopCat.of X)).δ 2 τ) *
      integralSingularTetrahedronSphereClass x ((TopCat.toSSet.obj (TopCat.of X)).δ 4 τ) =
    integralSingularTetrahedronSphereClass x ((TopCat.toSSet.obj (TopCat.of X)).δ 1 τ) *
      integralSingularTetrahedronSphereClass x ((TopCat.toSSet.obj (TopCat.of X)).δ 3 τ) := by
  obtain ⟨g, _, hskel, hfaces⟩ := exists_fourSimplex_cone_terminal_faces x τ
  have hg : ∀ p ∈ Simplex.skeleton (Fin 5) 2, g p = x := fun p hp => hskel ⟨p, hp⟩
  have heq (i : Fin 5) := integralSingularTetrahedronSphereClass_eq_tetrahedronGenLoop x
    ((TopCat.toSSet.obj (TopCat.of X)).δ i τ)
    (g.comp ⟨stdSimplex.map i.succAbove, stdSimplex.continuous_map i.succAbove⟩)
    (fun p hp => hg _ (Simplex.map_succAbove_mem_skeleton_of_mem_boundary i hp))
    (hfaces i).choose_spec
  rw [heq 0, heq 2, heq 4, heq 1, heq 3]
  exact tetrahedronGenLoop_fourSimplex_face_relation g hg

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralSingularTetrahedronSphereClass_face_relation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralSingularTetrahedronSphereClass_face_relation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralSingularTetrahedronSphereClass_face_relation ``Submission.DifferentialGeometry.Topology.integralSingularTetrahedronSphereClass_face_relation

end DifferentialGeometry.Topology
