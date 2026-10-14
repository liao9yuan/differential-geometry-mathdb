import Mathlib.Topology.Connected.LocallyPathConnected
import Mathlib.Topology.Connected.PathConnected
import Mathlib.Topology.Homotopy.Path
import Mathlib.Topology.Homotopy.Contractible
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Geometry.Manifold.IsManifold.ExtChartAt
import Mathlib.Topology.OpenPartialHomeomorph.Constructions

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission


open _root_.Set _root_.Function _root_.Filter _root_.Metric _root_.Bundle _root_.Manifold
open scoped _root_.Topology _root_.Manifold _root_.ContDiff

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace Topology

class SemilocallySimplyConnectedSpace (X : Type*) [TopologicalSpace X] :
    Prop where
  out : ∀ x : X, ∃ U ∈ nhds x, ∀ γ : _root_.Path x x,
          Set.range γ.toContinuousMap ⊆ U →
            (⟦γ⟧ : _root_.Path.Homotopic.Quotient x x) = ⟦_root_.Path.refl x⟧

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.Topology.SemilocallySimplyConnectedSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.Topology.SemilocallySimplyConnectedSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.Topology.SemilocallySimplyConnectedSpace ``Submission.DifferentialGeometry.Geometry.Riemannian.Topology.SemilocallySimplyConnectedSpace

theorem contractible_loops_nullhomotopic_in_subset
    {X : Type*} [TopologicalSpace X]
    {U : Set X} [ContractibleSpace U]
    {x : X}
    (γ : _root_.Path x x)
    (hγU : Set.range γ.toContinuousMap ⊆ U) :
    (⟦γ⟧ : _root_.Path.Homotopic.Quotient x x) = ⟦_root_.Path.refl x⟧ := by
  have hSC : IsSimplyConnected U := (inferInstance : SimplyConnectedSpace U)
  have hmem : ∀ t, γ t ∈ U := by
    intro t
    have ht : γ t ∈ Set.range γ.toContinuousMap := by
      refine ⟨t, ?_⟩
      simp [Path.coe_toContinuousMap]
    exact hγU ht
  obtain ⟨F, _⟩ :=
    (isSimplyConnected_iff_exists_homotopy_refl_forall_mem.mp hSC).2 x γ hmem
  exact Quotient.sound ⟨F⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.Topology.contractible_loops_nullhomotopic_in_subset then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.Topology.contractible_loops_nullhomotopic_in_subset"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.Topology.contractible_loops_nullhomotopic_in_subset ``Submission.DifferentialGeometry.Geometry.Riemannian.Topology.contractible_loops_nullhomotopic_in_subset

section ChartContractible

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

include I in
omit [InnerProductSpace ℝ E] [IsManifold I ∞ M] in
theorem exists_contractible_open_nhd (x : M) :
    ∃ U : Set M, IsOpen U ∧ x ∈ U ∧ ContractibleSpace U := by
  set e : OpenPartialHomeomorph M E :=
    (chartAt H x).transHomeomorph I.toHomeomorph with he_def
  have he_source : e.source = (chartAt H x).source := rfl
  set c : E := e x with hc_def
  have hxsrc : x ∈ e.source := by
    rw [he_source]; exact mem_chart_source H x
  have hc_target : c ∈ e.target := e.map_source hxsrc
  have h_target_open : IsOpen e.target := e.open_target
  obtain ⟨r, hr_pos, hr_sub⟩ :=
    Metric.isOpen_iff.mp h_target_open c hc_target
  set B : Set E := Metric.ball c r with hB_def
  set U : Set M := e.source ∩ e ⁻¹' B with hU_def
  have hU_open : IsOpen U := e.isOpen_inter_preimage Metric.isOpen_ball
  have hxU : x ∈ U := by
    refine ⟨hxsrc, ?_⟩
    change e x ∈ B
    simp [hB_def, ← hc_def, Metric.mem_ball, dist_self, hr_pos]
  have heImage : e '' U = B := by
    ext b
    refine ⟨?_, ?_⟩
    · rintro ⟨m, ⟨_, hmB⟩, rfl⟩
      exact hmB
    · intro hb
      have hbT : b ∈ e.target := hr_sub hb
      refine ⟨e.symm b, ⟨e.map_target hbT, ?_⟩, e.right_inv hbT⟩
      change e (e.symm b) ∈ B
      rw [e.right_inv hbT]
      exact hb
  have hU_sub : U ⊆ e.source := Set.inter_subset_left
  let φ : U ≃ₜ B := e.homeomorphOfImageSubsetSource hU_sub heImage
  have hB_contr : ContractibleSpace B := Metric.contractibleSpace_ball hr_pos
  have hU_contr : ContractibleSpace U := φ.contractibleSpace
  exact ⟨U, hU_open, hxU, hU_contr⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.Topology.exists_contractible_open_nhd then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.Topology.exists_contractible_open_nhd"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.Topology.exists_contractible_open_nhd ``Submission.DifferentialGeometry.Geometry.Riemannian.Topology.exists_contractible_open_nhd

include I in
omit [InnerProductSpace ℝ E] [IsManifold I ∞ M] in
theorem manifold_semilocallySimplyConnectedSpace :
    SemilocallySimplyConnectedSpace M := ⟨by
  intro x
  obtain ⟨U, hU_open, hxU, hU_contr⟩ := exists_contractible_open_nhd (I := I) x
  refine ⟨U, hU_open.mem_nhds hxU, fun γ hγU => ?_⟩
  exact contractible_loops_nullhomotopic_in_subset γ hγU⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.Topology.manifold_semilocallySimplyConnectedSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.Topology.manifold_semilocallySimplyConnectedSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.Topology.manifold_semilocallySimplyConnectedSpace ``Submission.DifferentialGeometry.Geometry.Riemannian.Topology.manifold_semilocallySimplyConnectedSpace

end ChartContractible

end Topology
end Riemannian
end Geometry
end DifferentialGeometry
