import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.SpatialFiniteCapFrontier
import Submission.DifferentialGeometry.Topology.Connected.InteriorUnion
import Submission.DifferentialGeometry.Topology.Manifold.SphereBoundaryDomain

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Set _root_.Submission.Set _root_.Manifold _root_.Submission.Manifold
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Submission.ContDiff _root_.Topology _root_.Submission.Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M] [PreconnectedSpace M]
  {g : SmoothRiemannianMetric I3 M} {eps : ℝ} {p : M}

theorem isConnected_interior_of_compact_regular_neck_boundary
    (nk : SpatialNeck g eps p) {level : ℝ} (hlevel : |level| ≤ 4)
    {K : Set M} (hK : IsCompact K) (hKr : closure (interior K) = K)
    (hfront : frontier K = _root_.Set.range (fun z : Sphere 2 => nk.map (z, level))) :
    IsConnected (interior K) := by
  have hnonempty : (interior K).Nonempty := by
    by_contra h
    have hi : interior K = ∅ := not_nonempty_iff_eq_empty.mp h
    have hKe : K = ∅ := by simpa only [hi, closure_empty] using hKr.symm
    have hf := hfront.symm ▸ (_root_.Set.mem_range_self nk.center :
      nk.map (nk.center, level) ∈ _root_.Set.range (fun z : Sphere 2 => nk.map (z, level)))
    simp only [hKe, frontier_empty, _root_.Set.notMem_empty] at hf
  have he := nk.isSmoothEmbedding_level (hlevel.trans_lt
    ((lt_inv_comm₀ (by norm_num) nk.eps_pos).mpr (by linarith [nk.eps_small])))
  exact (DifferentialGeometry.Topology.Manifold.isConnected_interior_and_compl_of_sphere_boundary
    hK.isClosed hnonempty _ he hfront).1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.isConnected_interior_of_compact_regular_neck_boundary then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.isConnected_interior_of_compact_regular_neck_boundary"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.isConnected_interior_of_compact_regular_neck_boundary ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.isConnected_interior_of_compact_regular_neck_boundary

theorem isConnected_interior_union_of_neck_cap_filling
    (nk : SpatialNeck g eps p) {level : ℝ} (hlevel : |level| ≤ 4)
    {W K : Set M} (hW : closure (interior W) = W)
    (hconn : IsPreconnected (interior W)) (hK : IsCompact K)
    (hKr : closure (interior K) = K)
    (hfront : frontier K = _root_.Set.range (fun z : Sphere 2 => nk.map (z, level)))
    (hinter : K ∩ W = _root_.Set.range (fun z : Sphere 2 => nk.map (z, level)))
    (hfill : _root_.Set.range (fun z : Sphere 2 => nk.map (z, level)) ⊆ interior (W ∪ K)) :
    IsConnected (interior (W ∪ K)) := by
  have hkc := isConnected_interior_of_compact_regular_neck_boundary nk hlevel hK hKr hfront
  have hx : nk.map (nk.center, level) ∈ _root_.Set.range (fun z : Sphere 2 => nk.map (z, level)) :=
    _root_.Set.mem_range_self _
  have hxm := hinter.symm ▸ hx
  exact DifferentialGeometry.Topology.isConnected_interior_union
    (S := W) (T := K) hW.symm.subset hKr.symm.subset hconn hkc.isPreconnected
    ⟨_, ⟨hW.symm ▸ hxm.2, hKr.symm ▸ hxm.1⟩, hfill hx⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.isConnected_interior_union_of_neck_cap_filling then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.isConnected_interior_union_of_neck_cap_filling"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.isConnected_interior_union_of_neck_cap_filling ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.isConnected_interior_union_of_neck_cap_filling

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
