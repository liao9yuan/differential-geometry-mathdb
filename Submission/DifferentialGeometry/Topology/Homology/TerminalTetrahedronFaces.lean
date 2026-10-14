import Submission.DifferentialGeometry.Topology.Homology.TetrahedronConeHomotopy
import Submission.DifferentialGeometry.Topology.Homology.ConeSphereHomotopy
import Submission.DifferentialGeometry.Topology.Simplex.FaceCompatibility

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section
namespace DifferentialGeometry.Topology
open _root_.CategoryTheory _root_.AlgebraicTopology _root_.ContinuousMap _root_.Submission.ContinuousMap
open scoped _root_.Simplicial
universe u
variable {X : Type u} [TopologicalSpace X] [SimplyConnectedSpace X]

theorem exists_terminal_tetrahedron_faces
    (x : X) (tau : integralSingularSimplex 3 X) :
    ∃ G : C(stdSimplex ℝ (Fin 4), X),
      ∃ hG : ∀ p : Simplex.tetrahedronOneSkeleton, G p.val = x,
      ∀ i : Fin 4,
        (integralSingularConeSphereMap x
          ((TopCat.toSSet.obj (TopCat.of X)).δ i tau)).Homotopic
          (Simplex.triangleSphereMap
            (G.comp ⟨stdSimplex.map i.succAbove, stdSimplex.continuous_map i.succAbove⟩)
            x
            (fun p hp => hG (Simplex.faceBoundaryIntoTetrahedronOneSkeleton i ⟨p, hp⟩))) := by
  obtain ⟨F, hF0, hFtrace, hF1⟩ := exists_tetrahedron_cone_edge_homotopy x tau
  let G : C(stdSimplex ℝ (Fin 4), X) :=
    ⟨fun p => F (1, p), F.continuous.comp (continuous_const.prodMk continuous_id)⟩
  have hG : ∀ p : Simplex.tetrahedronOneSkeleton, G p.val = x := by
    intro p
    exact hF1 p
  refine ⟨G, hG, ?_⟩
  intro i
  let g : C(stdSimplex ℝ (Fin 3), X) :=
    G.comp ⟨stdSimplex.map i.succAbove, stdSimplex.continuous_map i.succAbove⟩
  let H : (integralSingularSimplexEquiv 2 X
      ((TopCat.toSSet.obj (TopCat.of X)).δ i tau)).Homotopy g := by
    let K : C(unitInterval × stdSimplex ℝ (Fin 3), X) := F.comp ⟨fun z => (z.1, stdSimplex.map i.succAbove z.2), continuous_fst.prodMk ((stdSimplex.continuous_map i.succAbove).comp continuous_snd)⟩
    refine { toContinuousMap := K, map_zero_left := ?_, map_one_left := ?_ }
    · intro p
      change F (0, stdSimplex.map i.succAbove p) = _
      rw [hF0]
      rfl
    · intro p
      change F (1, stdSimplex.map i.succAbove p) = _
      rfl
  have hH : ∀ (t : unitInterval) (j : Fin 3) (p : stdSimplex ℝ (Fin 2)),
      H (t, stdSimplex.map j.succAbove p) =
        integralSingularConeEdgeHomotopy x
          ((TopCat.toSSet.obj (TopCat.of X)).δ j
            ((TopCat.toSSet.obj (TopCat.of X)).δ i tau))
          (t, stdSimplexHomeomorphUnitInterval p) := by
    intro t j p
    change F (t, stdSimplex.map i.succAbove (stdSimplex.map j.succAbove p)) = _
    exact hFtrace i j t p
  exact integralSingularConeSphereMap_homotopic_triangleSphereMap x
    ((TopCat.toSSet.obj (TopCat.of X)).δ i tau) g
    (fun p hp => hG (Simplex.faceBoundaryIntoTetrahedronOneSkeleton i ⟨p, hp⟩)) H hH

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.exists_terminal_tetrahedron_faces then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.exists_terminal_tetrahedron_faces"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.exists_terminal_tetrahedron_faces ``Submission.DifferentialGeometry.Topology.exists_terminal_tetrahedron_faces

end DifferentialGeometry.Topology
