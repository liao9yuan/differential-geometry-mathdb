import Submission.DifferentialGeometry.Topology.PiecewiseLinear.PLPath
import Submission.DifferentialGeometry.Topology.SimplicialComplex.EdgeGraph
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

open _root_.Classical in
theorem space_eq_iUnion_closedStar (K : Geometry.SimplicialComplex ℝ E) :
    K.space = ⋃ v : K.vertices, closedStar K v := by
  apply Subset.antisymm
  · intro x hx
    obtain ⟨s, hs, hxs⟩ := K.mem_space_iff.mp hx
    obtain ⟨v, hvs⟩ := K.nonempty_of_mem_faces hs
    have hv : v ∈ K.vertices :=
      K.down_closed hs (Finset.singleton_subset_iff.mpr hvs) (Finset.singleton_nonempty v)
    apply mem_iUnion.mpr
    refine ⟨⟨v, hv⟩, ?_⟩
    exact _root_.Set.mem_biUnion ⟨hs, subset_convexHull ℝ (s : Set E) hvs⟩ hxs
  · apply _root_.Set.iUnion_subset
    intro v
    exact closedStar_subset_space K v

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.space_eq_iUnion_closedStar then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.space_eq_iUnion_closedStar"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.space_eq_iUnion_closedStar ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.space_eq_iUnion_closedStar

theorem isConnected_closedStar (K : Geometry.SimplicialComplex ℝ E) {v : E}
    (hv : {v} ∈ K.faces) : IsConnected (closedStar K v) :=
  ((starConvex_closedStar K).isPathConnected (mem_closedStar_of_singleton_mem K hv)).isConnected

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.isConnected_closedStar then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.isConnected_closedStar"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.isConnected_closedStar ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.isConnected_closedStar

open _root_.Classical in
theorem closedStar_inter_closedStar_nonempty_of_edgeGraph_adj
    (K : Geometry.SimplicialComplex ℝ E) {u v : K.vertices}
    (huv : (SimplicialComplex.edgeGraph K).Adj u v) :
    (closedStar K u ∩ closedStar K v).Nonempty := by
  refine ⟨u, mem_closedStar_of_singleton_mem K u.2, ?_⟩
  exact _root_.Set.mem_biUnion
    ⟨huv.2, subset_convexHull ℝ (({(u : E), (v : E)} : Finset E) : Set E) (by simp)⟩
    (subset_convexHull ℝ (({(u : E), (v : E)} : Finset E) : Set E) (by simp))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.closedStar_inter_closedStar_nonempty_of_edgeGraph_adj then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.closedStar_inter_closedStar_nonempty_of_edgeGraph_adj"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.closedStar_inter_closedStar_nonempty_of_edgeGraph_adj ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.closedStar_inter_closedStar_nonempty_of_edgeGraph_adj

open _root_.Classical in
theorem isConnected_space_of_edgeGraph_connected
    (K : Geometry.SimplicialComplex ℝ E)
    (hK : (SimplicialComplex.edgeGraph K).Connected) : IsConnected K.space := by
  rw [space_eq_iUnion_closedStar]
  let _ : Nonempty K.vertices := hK.nonempty
  apply IsConnected.iUnion_of_reflTransGen
  · intro v
    exact isConnected_closedStar K v.2
  · intro u v
    apply Relation.ReflTransGen.mono
      (fun a b hab => closedStar_inter_closedStar_nonempty_of_edgeGraph_adj K hab)
    exact ((SimplicialComplex.edgeGraph K).reachable_iff_reflTransGen u v).mp
      (hK.preconnected u v)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.isConnected_space_of_edgeGraph_connected then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.isConnected_space_of_edgeGraph_connected"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.isConnected_space_of_edgeGraph_connected ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.isConnected_space_of_edgeGraph_connected

end DifferentialGeometry.Topology.PiecewiseLinear
