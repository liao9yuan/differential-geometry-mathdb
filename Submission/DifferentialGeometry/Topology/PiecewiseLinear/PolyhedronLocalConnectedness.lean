import Submission.DifferentialGeometry.Topology.PiecewiseLinear.PLPath
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.Triangulation
import Mathlib.Topology.Connected.LocallyConnected

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem locallyConnectedSpace_space (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] :
    LocallyConnectedSpace K.space := by
  apply locallyConnectedSpace_iff_connected_subsets.mpr
  intro p U hU
  obtain ⟨V, hV, hVU⟩ := (mem_nhds_subtype K.space p U).mp hU
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hV
  let C := closedStar K p ∩ Metric.ball (p : E) ε
  have hpball : (p : E) ∈ Metric.ball (p : E) ε := Metric.mem_ball_self hε
  have hpstar : (p : E) ∈ closedStar K p :=
    mem_of_mem_nhdsWithin p.property (closedStar_mem_nhdsWithin K p)
  have hCconn : IsPreconnected C :=
    ((starConvex_closedStar K).inter ((convex_ball (p : E) ε).starConvex hpball)).isPathConnected
      ⟨hpstar, hpball⟩ |>.isConnected.isPreconnected
  have hCsub : C ⊆ K.space := inter_subset_left.trans (closedStar_subset_space K p)
  have hCnhds : C ∈ 𝓝[K.space] (p : E) :=
    Filter.inter_mem (closedStar_mem_nhdsWithin K p)
      (mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds (p : E) hε))
  refine ⟨((↑) : K.space → E) ⁻¹' C, preimage_coe_mem_nhds_subtype.mpr hCnhds, ?_, ?_⟩
  · apply Topology.IsInducing.subtypeVal.isPreconnected_image.mp
    rwa [Subtype.image_preimage_coe, inter_eq_right.mpr hCsub]
  · intro q hq
    exact hVU (hball hq.2)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.locallyConnectedSpace_space then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.locallyConnectedSpace_space"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.locallyConnectedSpace_space ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.locallyConnectedSpace_space

theorem IsPolyhedron.locallyConnectedSpace [FiniteDimensional ℝ E] {P : Set E}
    (hP : IsPolyhedron P) : LocallyConnectedSpace P := by
  obtain ⟨K, hKfin, hK⟩ := hP.exists_simplicialComplex
  let : Finite K.faces := hKfin.to_subtype
  rw [← hK]
  exact locallyConnectedSpace_space K

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsPolyhedron.locallyConnectedSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsPolyhedron.locallyConnectedSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsPolyhedron.locallyConnectedSpace ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsPolyhedron.locallyConnectedSpace

end DifferentialGeometry.Topology.PiecewiseLinear
