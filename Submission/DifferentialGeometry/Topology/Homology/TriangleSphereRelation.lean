import Submission.DifferentialGeometry.Topology.Homology.TriangleSpherePairing
import Submission.DifferentialGeometry.Topology.Homology.TerminalTetrahedronFaces
import Submission.DifferentialGeometry.Topology.Simplex.TetrahedronHomotopyRelation

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

theorem integralSingularTriangleSphereClass_face_relation
    (x : X) (tau : integralSingularSimplex 3 X) :
    integralSingularTriangleSphereClass x ((TopCat.toSSet.obj (TopCat.of X)).δ 0 tau) *
      integralSingularTriangleSphereClass x ((TopCat.toSSet.obj (TopCat.of X)).δ 2 tau) =
    integralSingularTriangleSphereClass x ((TopCat.toSSet.obj (TopCat.of X)).δ 1 tau) *
      integralSingularTriangleSphereClass x ((TopCat.toSSet.obj (TopCat.of X)).δ 3 tau) := by
  obtain ⟨G, hG, hfaces⟩ := exists_terminal_tetrahedron_faces x tau
  have heq (i : Fin 4) := integralSingularTriangleSphereClass_eq_triangleGenLoop x
    ((TopCat.toSSet.obj (TopCat.of X)).δ i tau)
    (G.comp ⟨stdSimplex.map i.succAbove, stdSimplex.continuous_map i.succAbove⟩)
    (fun p hp => hG (Simplex.faceBoundaryIntoTetrahedronOneSkeleton i ⟨p, hp⟩))
    (hfaces i)
  rw [heq 0, heq 2, heq 1, heq 3]
  exact triangleGenLoop_tetrahedron_face_relation G hG

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralSingularTriangleSphereClass_face_relation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralSingularTriangleSphereClass_face_relation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralSingularTriangleSphereClass_face_relation ``Submission.DifferentialGeometry.Topology.integralSingularTriangleSphereClass_face_relation

end DifferentialGeometry.Topology
