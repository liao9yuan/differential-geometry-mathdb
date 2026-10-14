import Submission.DifferentialGeometry.Geometry.Neck.ScalarControl
import Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.CutCoreSelection

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section

open _root_.Set _root_.Submission.Set _root_.Function _root_.TopologicalSpace _root_.Manifold _root_.Submission.Manifold
open _root_.Submission.DifferentialGeometry.Geometry.Neck _root_.Submission.DifferentialGeometry.Geometry.Curvature
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff

namespace DifferentialGeometry.Topology.ThreeManifold.Surgery

variable {M : Type*} [TopologicalSpace M] {ι : Type*} {δ : ι → ℝ}

theorem interior_cutCore_eq_compl_closedSlabs [Finite ι] [T2Space M]
    (hδ : ∀ i, 0 < δ i) (f : ∀ i, bufferedCylinder (δ i) → M)
    (hf : ∀ i, Continuous (f i)) :
    interior (cutCore f) = (⋃ i, closedSlab (f i))ᶜ := by
  rw [cutCore, interior_compl, closure_iUnion_of_finite]
  simp_rw [closure_removedSlab (hδ _) _ (hf _)]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.interior_cutCore_eq_compl_closedSlabs then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.interior_cutCore_eq_compl_closedSlabs"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.interior_cutCore_eq_compl_closedSlabs ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.interior_cutCore_eq_compl_closedSlabs

section Riemannian

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Fact (Module.finrank ℝ E = 3)]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

theorem scalar_lower_bound_of_closedCentralDomain
    (U : _root_.TopologicalSpace.Opens M) {g : SmoothRiemannianMetric I U} {x₀ : U} {ε : ℝ} {k : ℕ}
    (d : normalizedDatum g x₀ ε k) (hk : 2 ≤ k) (hε : ε ≤ 1 / 2)
    (q : bufferedCylinder ε) (hq : q ∈ closedCentralDomain ε) :
    (1 - 4323 * ε) * metricScalarAt g x₀ ≤ metricScalarAt g (d.map q) := by
  have hi : 1 < ε⁻¹ := (one_lt_inv₀ d.precision_pos).mpr d.precision_lt_one
  have hcontrol : q ∈ controlledCylinder ε := by
    change q.val.2 ∈ _root_.Set.Icc (-ε⁻¹) ε⁻¹
    change -1 ≤ q.val.2 ∧ q.val.2 ≤ 1 at hq
    exact ⟨by linarith [hq.1], by linarith [hq.2]⟩
  have hr := (abs_le.mp (d.abs_scalar_ratio_sub_one_le hk hε q hcontrol)).1
  have hh : 1 - 4323 * ε ≤ metricScalarAt g (d.map q) / metricScalarAt g x₀ := by linarith
  exact (le_div_iff₀ d.scalar_pos).mp hh

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.scalar_lower_bound_of_closedCentralDomain then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.scalar_lower_bound_of_closedCentralDomain"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.scalar_lower_bound_of_closedCentralDomain ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.scalar_lower_bound_of_closedCentralDomain

theorem scalar_sublevel_mem_interior_cutCore [Finite ι]
    (U : _root_.TopologicalSpace.Opens M) (g : SmoothRiemannianMetric I U)
    (x₀ : ι → U) (order : ι → ℕ)
    (d : ∀ i, normalizedDatum g (x₀ i) (δ i) (order i))
    (horder : ∀ i, 2 ≤ order i) (hδ : ∀ i, δ i ≤ 1 / 2)
    (K : ℝ) (hhigh : ∀ i, K < (1 - 4323 * δ i) * metricScalarAt g (x₀ i))
    (x : U) (hx : metricScalarAt g x ≤ K) :
    x.val ∈ interior (cutCore (fun i => neckAmbientMap U (d i))) := by
  rw [interior_cutCore_eq_compl_closedSlabs (fun i => (d i).precision_pos) _
    (fun i => (isOpenEmbedding_neckAmbientMap U (d i)).continuous)]
  intro hmem
  obtain ⟨i, q, hq, heq⟩ := mem_iUnion.mp hmem
  have hqx : (d i).map q = x := Subtype.ext heq
  have hl := scalar_lower_bound_of_closedCentralDomain U (d i) (horder i) (hδ i) q hq
  rw [hqx] at hl
  exact (not_lt_of_ge (hl.trans hx)) (hhigh i)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.scalar_sublevel_mem_interior_cutCore then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.scalar_sublevel_mem_interior_cutCore"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.scalar_sublevel_mem_interior_cutCore ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.scalar_sublevel_mem_interior_cutCore

end Riemannian

end DifferentialGeometry.Topology.ThreeManifold.Surgery
