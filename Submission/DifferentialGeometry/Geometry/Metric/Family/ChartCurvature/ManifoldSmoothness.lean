import Submission.DifferentialGeometry.Geometry.Metric.Family.ChartCurvature.MetricFamilySmoothOn
import Submission.DifferentialGeometry.Geometry.Metric.Family.ChartCurvature.JointSmoothness
import Submission.DifferentialGeometry.Geometry.Metric.Family.JointSmoothness
import Submission.DifferentialGeometry.Analysis.Calculus.Inverse.MatrixSmoothness

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Submission.DifferentialGeometry.Geometry.Connection
open _root_.Submission.DifferentialGeometry.Geometry.Operator


noncomputable section


open _root_.Set _root_.Function _root_.Bundle _root_.Submission.Bundle
open scoped _root_.Topology _root_.Manifold _root_.BigOperators _root_.ContDiff _root_.Matrix _root_.Submission.Matrix

namespace DifferentialGeometry.Geometry.Curvature

open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.DivergenceTheorem

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

namespace MetricFamilySmoothOn

theorem chartGramFamilyJointSmoothOn
    {D : RealTimeInterval}
    (g_fam : ℝ → SmoothRiemannianMetric I M)
    (hG : MetricFamilySmoothOn (I := I) (M := M) D g_fam)
    (α : M) :
    chartGramFamilyJointSmoothOn (I := I) (fun t => g_fam t) α D.regular := by
  intro i j s₀ y₀ hs hy
  exact (MetricFamilySmoothOn.chartGramOnE_contDiffOn
    (I := I) hG (J := D.regular) Subset.rfl α i j).contDiffAt
    (prod_mem_nhds (D.regular_isOpen.mem_nhds hs) (isOpen_interior.mem_nhds hy))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.MetricFamilySmoothOn.chartGramFamilyJointSmoothOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.MetricFamilySmoothOn.chartGramFamilyJointSmoothOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.MetricFamilySmoothOn.chartGramFamilyJointSmoothOn ``Submission.DifferentialGeometry.Geometry.Curvature.MetricFamilySmoothOn.chartGramFamilyJointSmoothOn

variable [I.Boundaryless]

omit [I.Boundaryless] in
open scoped _root_.Matrix.Norms.Elementwise in
theorem chartInvGramMatrix_jointContMDiffOn
    {D : RealTimeInterval}
    (g_fam : ℝ → SmoothRiemannianMetric I M)
    (hG : MetricFamilySmoothOn (I := I) (M := M) D g_fam)
    (α : M) (i j : Fin (Module.finrank ℝ E)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ) ∞
      (fun p : M × ℝ => chartInvGramMatrix (I := I) (g_fam p.2) α p.1 i j)
      ((chartAt H α).source ×ˢ D.regular) := by
  let A := fun (p : M × ℝ) (k l : Fin (Module.finrank ℝ E)) =>
    DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) (g_fam p.2) α p.1 k l
  have hA : ContMDiffOn (I.prod 𝓘(ℝ))
      𝓘(ℝ, (Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ)) ∞ A
      ((chartAt H α).source ×ˢ D.regular) := by
    apply contMDiffOn_pi_space.mpr
    intro k
    apply contMDiffOn_pi_space.mpr
    intro l
    exact (chartGramMatrix_joint_contMDiffOn g_fam D.regular
      (hG.metricCLMSection_contMDiffOn Subset.rfl) α k l).comp
      (contMDiffOn_snd.prodMk contMDiffOn_fst) (fun p hp => ⟨hp.2, hp.1⟩)
  intro p hp
  have hdet : Matrix.det (A p) ≠ 0 := ne_of_gt
    (DifferentialGeometry.Tensor.Coordinates.chartGramMatrix_det_pos (g_fam p.2) α hp.1)
  have hinv := DifferentialGeometry.Analysis.contDiffAt_inv_of_entries
    (fun B : (Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ) => B)
    (fun k l => (contDiff_pi.mp (contDiff_pi.mp contDiff_id k) l)) hdet i j
  exact hinv.contMDiffAt.comp_contMDiffWithinAt p (hA p hp)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.MetricFamilySmoothOn.chartInvGramMatrix_jointContMDiffOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.MetricFamilySmoothOn.chartInvGramMatrix_jointContMDiffOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.MetricFamilySmoothOn.chartInvGramMatrix_jointContMDiffOn ``Submission.DifferentialGeometry.Geometry.Curvature.MetricFamilySmoothOn.chartInvGramMatrix_jointContMDiffOn

theorem chartChristoffel_comp_extChartAt_jointContMDiffOn
    {D : RealTimeInterval}
    (g_fam : ℝ → SmoothRiemannianMetric I M)
    (hG : MetricFamilySmoothOn (I := I) (M := M) D g_fam)
    (α : M) (i j k : Fin (Module.finrank ℝ E)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ) ∞
      (fun p : M × ℝ =>
        chartChristoffel (I := I) (g_fam p.2) α i j k (extChartAt I α p.1))
      ((chartAt H α).source ×ˢ D.regular) := by
  have hGram := chartGramFamilyJointSmoothOn (I := I) g_fam hG α
  have hmove : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) ∞
      (fun p : M × ℝ => (p.2, extChartAt I α p.1))
      ((chartAt H α).source ×ˢ D.regular) := by
    refine ContMDiffOn.prodMk contMDiffOn_snd ?_
    exact (contMDiffOn_extChartAt (I := I) (x := α)).comp contMDiffOn_fst
      (fun p hp => hp.1)
  intro p hp
  obtain ⟨hx, ht⟩ := hp
  have hxsrc : p.1 ∈ (extChartAt I α).source := by
    rw [extChartAt_source (I := I)]
    exact hx
  have hy : extChartAt I α p.1 ∈ interior (extChartAt I α).target :=
    extChartAt_target_subset_interior_of_boundaryless (I := I) α
      ((extChartAt I α).map_source hxsrc)
  have hentry := chartChristoffel_joint_contDiffAt (I := I) (fun t => g_fam t) α hGram i j k ht hy
  have hentryM : ContMDiffAt 𝓘(ℝ, ℝ × E) 𝓘(ℝ) ∞
      (fun r : ℝ × E => chartChristoffel (I := I) (g_fam r.1) α i j k r.2)
      (p.2, extChartAt I α p.1) :=
    hentry.contMDiffAt
  have hmoveAt : ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ × E) ∞
      (fun q : M × ℝ => (q.2, extChartAt I α q.1))
      ((chartAt H α).source ×ˢ D.regular) p := by
    have hm := hmove p ⟨hx, ht⟩
    rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod] at hm
    exact hm
  have hcomp := hentryM.comp_contMDiffWithinAt p hmoveAt
  change ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ) ∞
    (fun q : M × ℝ =>
      chartChristoffel (I := I) (g_fam q.2) α i j k (extChartAt I α q.1))
    ((chartAt H α).source ×ˢ D.regular) p at hcomp
  exact hcomp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.MetricFamilySmoothOn.chartChristoffel_comp_extChartAt_jointContMDiffOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.MetricFamilySmoothOn.chartChristoffel_comp_extChartAt_jointContMDiffOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.MetricFamilySmoothOn.chartChristoffel_comp_extChartAt_jointContMDiffOn ``Submission.DifferentialGeometry.Geometry.Curvature.MetricFamilySmoothOn.chartChristoffel_comp_extChartAt_jointContMDiffOn

end MetricFamilySmoothOn

end DifferentialGeometry.Geometry.Curvature
