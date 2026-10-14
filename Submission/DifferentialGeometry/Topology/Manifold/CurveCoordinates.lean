import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Tactic.Linarith

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section

open _root_.Set _root_.Filter
open scoped _root_.Manifold _root_.ContDiff _root_.Topology

namespace DifferentialGeometry.Topology.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

theorem exists_endpoint_chart_displacement_bound
    (α : ℝ → M) (b : ℝ)
    (hα : ContMDiffAt 𝓘(ℝ, ℝ) I 1 α b) :
    let p := α b
    let e := extChartAt I p
    ∃ R : ℝ, 0 < R ∧
      ∃ δ : ℝ, 0 < δ ∧
        ∃ V : ℝ, 0 ≤ V ∧
          Metric.closedBall (e p) R ⊆ interior e.target ∧
          ∀ s ∈ _root_.Set.Icc (b - δ) b,
            α s ∈ e.source ∧
            e (α s) ∈ Metric.ball (e p) (R / 2) ∧
            ‖e (α s) - e p‖ ≤ V * |s - b| := by
  let p := α b
  let e := extChartAt I p
  let z := e p
  let F : ℝ → E := e ∘ α
  have hF : ContDiffAt ℝ 1 F b :=
    ((contMDiffAt_extChartAt (I := I) (x := p) (n := 1)).comp b hα).contDiffAt
  have hF0 : F b = z := rfl
  have htarget : interior e.target ∈ 𝓝 z :=
    interior_mem_nhds.mpr (extChartAt_target_mem_nhds (I := I) p)
  obtain ⟨R, hR, hRsub⟩ :=
    (Metric.nhds_basis_closedBall (x := z)).mem_iff.mp htarget
  obtain ⟨K, W, hW, hLip⟩ := hF.exists_lipschitzOnWith
  have hsource : α ⁻¹' e.source ∈ 𝓝 b :=
    hα.continuousAt.preimage_mem_nhds
      (extChartAt_source_mem_nhds (I := I) p)
  have hhalf : F ⁻¹' Metric.ball z (R / 2) ∈ 𝓝 b := by
    apply hF.continuousAt.preimage_mem_nhds
    simpa only [hF0] using Metric.ball_mem_nhds z (half_pos hR)
  have hneighborhood :
      ((W ∩ (α ⁻¹' e.source)) ∩
        (F ⁻¹' Metric.ball z (R / 2))) ∈ 𝓝 b :=
    _root_.Filter.inter_mem (_root_.Filter.inter_mem hW hsource) hhalf
  obtain ⟨δ, hδ, hδsub⟩ :=
    (Metric.nhds_basis_closedBall (x := b)).mem_iff.mp hneighborhood
  refine ⟨R, hR, δ, hδ, (K : ℝ), K.2, hRsub, ?_⟩
  intro s hs
  have hsball : s ∈ Metric.closedBall b δ := by
    rw [Metric.mem_closedBall, Real.dist_eq]
    apply abs_le.mpr
    constructor
    · linarith only [hs.1]
    · linarith only [hs.2, hδ]
  have hsneighborhood := hδsub hsball
  refine ⟨hsneighborhood.1.2, hsneighborhood.2, ?_⟩
  have hdist :=
    hLip.dist_le_mul s hsneighborhood.1.1 b (mem_of_mem_nhds hW)
  change ‖F s - z‖ ≤ (K : ℝ) * |s - b|
  simpa only [dist_eq_norm, Real.norm_eq_abs, hF0] using hdist

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.exists_endpoint_chart_displacement_bound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.exists_endpoint_chart_displacement_bound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.exists_endpoint_chart_displacement_bound ``Submission.DifferentialGeometry.Topology.Manifold.exists_endpoint_chart_displacement_bound

end DifferentialGeometry.Topology.Manifold
