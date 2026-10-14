import Submission.DifferentialGeometry.Analysis.Elliptic.Regularity.ChartBilinear.H1ComplFromDom
import Submission.DifferentialGeometry.Analysis.Elliptic.Regularity.H1Compl.ToLpChartBridge
import Submission.DifferentialGeometry.Analysis.Sobolev.Chart.Defs
import Submission.DifferentialGeometry.Geometry.Operator.Gradient.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Complete

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission


noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Set _root_.MeasureTheory _root_.Filter _root_.Topology _root_.Function
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.Matrix _root_.InnerProductSpace _root_.BigOperators
  RealInnerProductSpace ENNReal NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace H1ComplGradientChartBridge

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.DivergenceTheorem
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.MetricExtension
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1Compl
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1ComplFromDom
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.H1ComplToLpChartBridge

private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.H1ComplGradientChartBridge.instMeasurableSpace_differentialGeometry : MeasurableSpace E := borel E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.H1ComplGradientChartBridge.instMeasurableSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.H1ComplGradientChartBridge.instMeasurableSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.H1ComplGradientChartBridge.instBorelSpace_differentialGeometry : BorelSpace E := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.H1ComplGradientChartBridge.instBorelSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.H1ComplGradientChartBridge.instBorelSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.H1ComplGradientChartBridge.instMeasurableSpace_differentialGeometry_1 : MeasurableSpace M := borel M

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.H1ComplGradientChartBridge.instMeasurableSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.H1ComplGradientChartBridge.instMeasurableSpace_differentialGeometry_1 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.H1ComplGradientChartBridge.instBorelSpace_differentialGeometry_1 : BorelSpace M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.H1ComplGradientChartBridge.instBorelSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.H1ComplGradientChartBridge.instBorelSpace_differentialGeometry_1 target :: scope.openDecls } }

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

variable [I.Boundaryless] [T2Space M] [CompactSpace M]

noncomputable def chartPushedPartial
    (g : SmoothRiemannianMetric I M) (α : M)
    (j : Fin (Module.finrank ℝ E)) (v : SmoothScalar g) : EuclN → ℝ :=
  fun y =>
    (fderiv ℝ (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed (I := I) (M := M)
      (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α v.toFun) y)
      (EuclideanSpace.single j 1)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.H1ComplGradientChartBridge.chartPushedPartial then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.H1ComplGradientChartBridge.chartPushedPartial"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.H1ComplGradientChartBridge.chartPushedPartial ``Submission.DifferentialGeometry.Analysis.Laplacian.H1ComplGradientChartBridge.chartPushedPartial

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
@[simp] lemma chartPushedPartial_def
    (g : SmoothRiemannianMetric I M) (α : M)
    (j : Fin (Module.finrank ℝ E)) (v : SmoothScalar g) (y : EuclN) :
    chartPushedPartial (I := I) (M := M) g α j v y =
      (fderiv ℝ (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed (I := I) (M := M)
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α v.toFun) y)
        (EuclideanSpace.single j 1) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.H1ComplGradientChartBridge.chartPushedPartial_def then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.H1ComplGradientChartBridge.chartPushedPartial_def"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.H1ComplGradientChartBridge.chartPushedPartial_def ``Submission.DifferentialGeometry.Analysis.Laplacian.H1ComplGradientChartBridge.chartPushedPartial_def

noncomputable def chartPushedPartialLp
    (g : SmoothRiemannianMetric I M) (α : M)
    (j : Fin (Module.finrank ℝ E)) (v : SmoothScalar g)
    (h : _root_.MeasureTheory.MemLp (chartPushedPartial (I := I) (M := M) g α j v) 2
      ((chartPulledWeightedMeasure (I := I) g α).restrict
        (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid (I := I) (M := M) α))) :
    Lp ℝ 2 ((chartPulledWeightedMeasure (I := I) g α).restrict
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid (I := I) (M := M) α)) :=
  h.toLp _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.H1ComplGradientChartBridge.chartPushedPartialLp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.H1ComplGradientChartBridge.chartPushedPartialLp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.H1ComplGradientChartBridge.chartPushedPartialLp ``Submission.DifferentialGeometry.Analysis.Laplacian.H1ComplGradientChartBridge.chartPushedPartialLp

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
lemma norm_chartPushedPartialLp
    (g : SmoothRiemannianMetric I M) (α : M)
    (j : Fin (Module.finrank ℝ E)) (v : SmoothScalar g)
    (h : _root_.MeasureTheory.MemLp (chartPushedPartial (I := I) (M := M) g α j v) 2
      ((chartPulledWeightedMeasure (I := I) g α).restrict
        (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid (I := I) (M := M) α))) :
    ‖chartPushedPartialLp (I := I) (M := M) g α j v h‖ =
      ENNReal.toReal (_root_.MeasureTheory.eLpNorm (chartPushedPartial (I := I) (M := M) g α j v) 2
        ((chartPulledWeightedMeasure (I := I) g α).restrict
          (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid (I := I) (M := M)
            α))) := by
  unfold chartPushedPartialLp
  exact MeasureTheory.Lp.norm_toLp _ _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.H1ComplGradientChartBridge.norm_chartPushedPartialLp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.H1ComplGradientChartBridge.norm_chartPushedPartialLp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.H1ComplGradientChartBridge.norm_chartPushedPartialLp ``Submission.DifferentialGeometry.Analysis.Laplacian.H1ComplGradientChartBridge.norm_chartPushedPartialLp

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
lemma eLpNorm_chartPushedPartial_eq_ofReal_norm
    (g : SmoothRiemannianMetric I M) (α : M)
    (j : Fin (Module.finrank ℝ E)) (v : SmoothScalar g)
    (h : _root_.MeasureTheory.MemLp (chartPushedPartial (I := I) (M := M) g α j v) 2
      ((chartPulledWeightedMeasure (I := I) g α).restrict
        (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid (I := I) (M := M) α))) :
    eLpNorm (chartPushedPartial (I := I) (M := M) g α j v) 2
        ((chartPulledWeightedMeasure (I := I) g α).restrict
          (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid (I := I) (M := M) α)) =
      ENNReal.ofReal ‖chartPushedPartialLp (I := I) (M := M) g α j v h‖ := by
  rw [norm_chartPushedPartialLp (I := I) (M := M) g α j v h]
  rw [ENNReal.ofReal_toReal]
  exact h.2.ne

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.H1ComplGradientChartBridge.eLpNorm_chartPushedPartial_eq_ofReal_norm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.H1ComplGradientChartBridge.eLpNorm_chartPushedPartial_eq_ofReal_norm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.H1ComplGradientChartBridge.eLpNorm_chartPushedPartial_eq_ofReal_norm ``Submission.DifferentialGeometry.Analysis.Laplacian.H1ComplGradientChartBridge.eLpNorm_chartPushedPartial_eq_ofReal_norm

omit [NeZero (Module.finrank ℝ E)] in
theorem cauchy_in_Lp_of_h1Compl_cauchy_with_extension
    (g : SmoothRiemannianMetric I M) (α : M)
    (T : SmoothScalar g →L[ℝ] _root_.MeasureTheory.Lp ℝ 2
      ((chartPulledWeightedMeasure (I := I) g α).restrict
        (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid (I := I) (M := M) α)))
    {v : ℕ → SmoothScalar g}
    (h_cauchy_h1 : Cauchy (atTop.map fun n =>
      smoothToH1Compl (I := I) (M := M) g (v n))) :
    Cauchy (atTop.map fun n => T (v n)) := by
  classical
  have h_inducing : IsUniformInducing (UniformSpace.Completion.toComplL :
      SmoothScalar g →L[ℝ] H1Compl g) := by
    rw [show (UniformSpace.Completion.toComplL : SmoothScalar g → H1Compl g) =
        ((↑) : SmoothScalar g → UniformSpace.Completion (SmoothScalar g)) from
        UniformSpace.Completion.coe_toComplL]
    exact UniformSpace.Completion.isUniformInducing_coe (SmoothScalar g)
  have h_cauchy_smooth : Cauchy (atTop.map v) := by
    rw [(h_inducing.cauchy_map_iff).symm]
    exact h_cauchy_h1
  have hT_uc : UniformContinuous T := T.uniformContinuous
  exact h_cauchy_smooth.map hT_uc

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.H1ComplGradientChartBridge.cauchy_in_Lp_of_h1Compl_cauchy_with_extension then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.H1ComplGradientChartBridge.cauchy_in_Lp_of_h1Compl_cauchy_with_extension"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.H1ComplGradientChartBridge.cauchy_in_Lp_of_h1Compl_cauchy_with_extension ``Submission.DifferentialGeometry.Analysis.Laplacian.H1ComplGradientChartBridge.cauchy_in_Lp_of_h1Compl_cauchy_with_extension

omit [NeZero (Module.finrank ℝ E)] in
theorem cauchy_in_Lp_of_chartPushed_partial_smoothApprox_with_extension
    (g : SmoothRiemannianMetric I M) (α : M)
    (T : SmoothScalar g →L[ℝ] _root_.MeasureTheory.Lp ℝ 2
      ((chartPulledWeightedMeasure (I := I) g α).restrict
        (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid (I := I) (M := M) α)))
    {u_h : H1Compl g}
    {v : ℕ → SmoothScalar g}
    (h_tendsto : _root_.Filter.Tendsto (fun n =>
      smoothToH1Compl (I := I) (M := M) g (v n)) _root_.Filter.atTop (𝓝 u_h)) :
    ∃ g_j_α : _root_.MeasureTheory.Lp ℝ 2 ((chartPulledWeightedMeasure (I := I) g α).restrict
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid (I := I) (M := M) α)),
      Tendsto (fun n => ‖T (v n) - g_j_α‖) _root_.Filter.atTop (𝓝 0) := by
  classical
  have h_cauchy_h1 : Cauchy (atTop.map fun n =>
      smoothToH1Compl (I := I) (M := M) g (v n)) := h_tendsto.cauchy_map
  have h_lp_cauchy : Cauchy (atTop.map fun n => T (v n)) :=
    cauchy_in_Lp_of_h1Compl_cauchy_with_extension (I := I) (M := M) g α T h_cauchy_h1
  have h_seq_cauchy : CauchySeq (fun n => T (v n)) := h_lp_cauchy
  obtain ⟨g_j_α, h_tendsto_lim⟩ := cauchySeq_tendsto_of_complete h_seq_cauchy
  refine ⟨g_j_α, ?_⟩
  have h_dist : _root_.Filter.Tendsto (fun n => _root_.Dist.dist (T (v n)) g_j_α) _root_.Filter.atTop (𝓝 0) :=
    tendsto_iff_dist_tendsto_zero.mp h_tendsto_lim
  have h_funext : (fun n => _root_.Dist.dist (T (v n)) g_j_α) =
      (fun n => ‖T (v n) - g_j_α‖) := by
    funext n; exact dist_eq_norm _ _
  rw [h_funext] at h_dist
  exact h_dist

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.H1ComplGradientChartBridge.cauchy_in_Lp_of_chartPushed_partial_smoothApprox_with_extension then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.H1ComplGradientChartBridge.cauchy_in_Lp_of_chartPushed_partial_smoothApprox_with_extension"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.H1ComplGradientChartBridge.cauchy_in_Lp_of_chartPushed_partial_smoothApprox_with_extension ``Submission.DifferentialGeometry.Analysis.Laplacian.H1ComplGradientChartBridge.cauchy_in_Lp_of_chartPushed_partial_smoothApprox_with_extension

omit [NeZero (Module.finrank ℝ E)] in
theorem cauchy_eLpNorm_diff_chartPushedPartial_with_extension
    (g : SmoothRiemannianMetric I M) (α : M)
    (j : Fin (Module.finrank ℝ E))
    (T : SmoothScalar g →L[ℝ] _root_.MeasureTheory.Lp ℝ 2
      ((chartPulledWeightedMeasure (I := I) g α).restrict
        (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid (I := I) (M := M) α)))
    (h_T_partial_normEq : ∀ v w : SmoothScalar g,
      ‖T v - T w‖ = ENNReal.toReal (_root_.MeasureTheory.eLpNorm
        (fun y => chartPushedPartial (I := I) (M := M) g α j v y -
          chartPushedPartial (I := I) (M := M) g α j w y) 2
        ((chartPulledWeightedMeasure (I := I) g α).restrict
          (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid (I := I) (M := M) α))))
    (h_partial_diff_memLp : ∀ v w : SmoothScalar g,
      MemLp (fun y => chartPushedPartial (I := I) (M := M) g α j v y -
          chartPushedPartial (I := I) (M := M) g α j w y) 2
        ((chartPulledWeightedMeasure (I := I) g α).restrict
          (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid (I := I) (M := M) α)))
    {v : ℕ → SmoothScalar g}
    (h_cauchy_h1 : Cauchy (atTop.map fun n =>
      smoothToH1Compl (I := I) (M := M) g (v n))) :
    ∀ ε : ℝ≥0∞, 0 < ε → ε ≠ ⊤ → ∃ N : ℕ, ∀ n m : ℕ, N ≤ n → N ≤ m →
      eLpNorm (fun y => chartPushedPartial (I := I) (M := M) g α j (v n) y -
          chartPushedPartial (I := I) (M := M) g α j (v m) y) 2
          ((chartPulledWeightedMeasure (I := I) g α).restrict
            (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid (I := I) (M := M) α))
        < ε := by
  classical
  intro ε hε_pos hε_top
  have h_lp_cauchy : Cauchy (atTop.map fun n => T (v n)) :=
    cauchy_in_Lp_of_h1Compl_cauchy_with_extension (I := I) (M := M) g α T h_cauchy_h1
  have h_seq_cauchy : CauchySeq (fun n => T (v n)) := h_lp_cauchy
  have hε_real_pos : 0 < ε.toReal := ENNReal.toReal_pos (ne_of_gt hε_pos) hε_top
  rw [Metric.cauchySeq_iff] at h_seq_cauchy
  obtain ⟨N, hN⟩ := h_seq_cauchy ε.toReal hε_real_pos
  refine ⟨N, fun n m hn hm => ?_⟩
  have h_dist : _root_.Dist.dist (T (v n)) (T (v m)) < ε.toReal := hN n hn m hm
  have h_norm : ‖T (v n) - T (v m)‖ < ε.toReal := by
    rw [← dist_eq_norm]; exact h_dist
  rw [h_T_partial_normEq] at h_norm
  have hLeR : _root_.MeasureTheory.eLpNorm
      (fun y => chartPushedPartial (I := I) (M := M) g α j (v n) y -
        chartPushedPartial (I := I) (M := M) g α j (v m) y) 2
      ((chartPulledWeightedMeasure (I := I) g α).restrict
        (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
          (I := I) (M := M) α)) =
    ENNReal.ofReal (ENNReal.toReal (_root_.MeasureTheory.eLpNorm
      (fun y => chartPushedPartial (I := I) (M := M) g α j (v n) y -
        chartPushedPartial (I := I) (M := M) g α j (v m) y) 2
      ((chartPulledWeightedMeasure (I := I) g α).restrict
        (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
          (I := I) (M := M) α)))) :=
    (ENNReal.ofReal_toReal (h_partial_diff_memLp (v n) (v m)).2.ne).symm
  rw [hLeR]
  have hε_eq : ε = ENNReal.ofReal ε.toReal := (ENNReal.ofReal_toReal hε_top).symm
  rw [hε_eq]
  exact (ENNReal.ofReal_lt_ofReal_iff hε_real_pos).mpr h_norm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.H1ComplGradientChartBridge.cauchy_eLpNorm_diff_chartPushedPartial_with_extension then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.H1ComplGradientChartBridge.cauchy_eLpNorm_diff_chartPushedPartial_with_extension"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.H1ComplGradientChartBridge.cauchy_eLpNorm_diff_chartPushedPartial_with_extension ``Submission.DifferentialGeometry.Analysis.Laplacian.H1ComplGradientChartBridge.cauchy_eLpNorm_diff_chartPushedPartial_with_extension

end H1ComplGradientChartBridge
end Laplacian
end Analysis
end DifferentialGeometry

end
