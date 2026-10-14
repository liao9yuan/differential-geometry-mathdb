/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.Section34SplitDiskIntersection
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.Section34IncidentEdges

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

variable {Ea : Type} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea]
  {M : Type u} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  {U : Set M} {𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M U}
  {src srcBd : Section34CutLabelOf 𝒦 𝒦' → Set M}

theorem exists_section34Edge_of_vertex_inter_nonempty
    (hframe : Section34CutFrame U 𝒦 𝒦' src srcBd)
    (ends : Section34EdgeIndex 𝒦 𝒦' → Section34VertexIndex 𝒦 𝒦' × Section34VertexIndex 𝒦 𝒦')
    (hends : ∀ e, (e.1 : Set Ea) = ((ends e).1.1 : Set Ea) ∪ ((ends e).2.1 : Set Ea))
    {w w' : Section34VertexIndex 𝒦 𝒦'} (hne : w ≠ w')
    (hmeet : (src (.vertexBall w) ∩ src (.vertexBall w')).Nonempty) :
    ∃ e : Section34EdgeIndex 𝒦 𝒦',
      src (.splitDisk e) = src (.vertexBall w) ∩ src (.vertexBall w') ∧
      ((w = (ends e).1 ∧ w' = (ends e).2) ∨ (w = (ends e).2 ∧ w' = (ends e).1)) := by
  obtain ⟨e, he⟩ := exists_splitDisk_src_eq_inter_vertexBall hframe hne hmeet
  obtain ⟨x, hxw, hxw'⟩ := hmeet
  have hxe : x ∈ src (.splitDisk e) := he.symm ▸ ⟨hxw, hxw'⟩
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hve, -⟩ := id hframe
  have hw := eq_or_eq_of_section34VertexIndex_subset e (hends e) (hve w e ⟨x, hxw, hxe⟩)
  have hw' := eq_or_eq_of_section34VertexIndex_subset e (hends e) (hve w' e ⟨x, hxw', hxe⟩)
  refine ⟨e, he, ?_⟩
  rcases hw with hw | hw <;> rcases hw' with hw' | hw'
  · exact (hne (hw.trans hw'.symm)).elim
  · exact Or.inl ⟨hw, hw'⟩
  · exact Or.inr ⟨hw, hw'⟩
  · exact (hne (hw.trans hw'.symm)).elim

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.exists_section34Edge_of_vertex_inter_nonempty then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.exists_section34Edge_of_vertex_inter_nonempty"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.exists_section34Edge_of_vertex_inter_nonempty ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.exists_section34Edge_of_vertex_inter_nonempty

end DifferentialGeometry.Topology.PiecewiseLinear
