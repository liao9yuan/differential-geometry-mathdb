import Submission.DifferentialGeometry.Topology.PiecewiseLinear.ArcSubset
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.BallDensity
import Submission.DifferentialGeometry.Topology.Connected.FiniteComponents

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem IsPLSphere.eq_or_exists_disjoint_arc_cover {ι : Type*} {S : Set E}
    (hS : IsPLSphere 1 S) (d : Finset ι) (A : ι → Set E)
    (hA : ∀ i ∈ d, IsPLBall 1 (A i)) (hAS : ∀ i ∈ d, A i ⊆ S) :
    (⋃ i ∈ d, A i) = S ∨ ∃ c : Finset (Set E),
      (∀ B ∈ c, IsPLBall 1 B) ∧ (∀ B ∈ c, B ⊆ S) ∧
      (∀ B ∈ c, ∀ C ∈ c, B ≠ C → Disjoint B C) ∧
      (⋃ B ∈ c, B) = ⋃ i ∈ d, A i := by
  classical
  by_cases heq : (⋃ i ∈ d, A i) = S
  · exact Or.inl heq
  have hUS : (⋃ i ∈ d, A i) ⊆ S := _root_.Set.iUnion₂_subset hAS
  have hUcompact : IsCompact (⋃ i ∈ d, A i) :=
    d.finite_toSet.isCompact_biUnion (fun i hi => (hA i hi).isPolyhedron.isCompact)
  obtain ⟨D, hD, hUD, -⟩ := hS.exists_isPLBall_one_superset_of_ssubset hUcompact.isClosed
    ⟨hUS, fun hSU => heq (Subset.antisymm hUS hSU)⟩
  obtain ⟨C, hCfin, hCdis, hC, hCU⟩ := Topology.exists_finite_isConnected_partition d A
    (fun i hi => (hA i hi).isPolyhedron.isCompact) (fun i hi => (hA i hi).isConnected)
  have hBU : ∀ B ∈ C, B ⊆ ⋃ i ∈ d, A i := by
    intro B hBC x hx
    exact hCU.subset (mem_sUnion.mpr ⟨B, hBC, hx⟩)
  refine Or.inr ⟨hCfin.toFinset, ?_, ?_, ?_, ?_⟩
  · intro B hB
    have hBC := hCfin.mem_toFinset.mp hB
    obtain ⟨hcompact, hconn, i, hi, hAiB⟩ := hC B hBC
    exact hD.isPLBall_one_of_isCompact_of_isConnected hcompact hconn
      ((hA i hi).nontrivial.mono hAiB) ((hBU B hBC).trans hUD)
  · intro B hB
    exact (hBU B (hCfin.mem_toFinset.mp hB)).trans hUS
  · intro B hB D hD hBD
    exact hCdis (hCfin.mem_toFinset.mp hB) (hCfin.mem_toFinset.mp hD) hBD
  · calc
      (⋃ B ∈ hCfin.toFinset, B) = ⋃₀ C := by
        ext x
        simp only [_root_.Set.mem_iUnion, hCfin.mem_toFinset, _root_.Set.mem_sUnion, exists_prop]
      _ = ⋃ i ∈ d, A i := hCU

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsPLSphere.eq_or_exists_disjoint_arc_cover then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsPLSphere.eq_or_exists_disjoint_arc_cover"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsPLSphere.eq_or_exists_disjoint_arc_cover ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsPLSphere.eq_or_exists_disjoint_arc_cover

end DifferentialGeometry.Topology.PiecewiseLinear
