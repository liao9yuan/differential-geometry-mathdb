import Submission.DifferentialGeometry.Analysis.Integration.Measure.Family.CompactSupportContinuity
import Submission.DifferentialGeometry.Analysis.Parabolic.ScalarHeat.TimeDependent
import Submission.DifferentialGeometry.Geometry.Metric.Family.JointSmoothness
import Submission.DifferentialGeometry.Geometry.Metric.Family.Regularity.Pair
import Submission.DifferentialGeometry.Geometry.Operator.Gradient.NormSquared
import Submission.DifferentialGeometry.Geometry.Operator.Gradient.NormSquaredTime

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.MeasureTheory _root_.Set
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Operator
open _root_.Submission.DifferentialGeometry.Integral.Measure
open scoped _root_.Manifold _root_.ContDiff

namespace DifferentialGeometry.Analysis.Parabolic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [CompactSpace M]

private local instance _root_.Submission.DifferentialGeometry.Analysis.Parabolic.instMeasurableSpace_differentialGeometry : MeasurableSpace M := borel M

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.instMeasurableSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.instMeasurableSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Parabolic.instBorelSpace_differentialGeometry : BorelSpace M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.instBorelSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.instBorelSpace_differentialGeometry target :: scope.openDecls } }

theorem continuousOn_integral_sq_of_metricFamilySmoothOn
    {D : RealTimeInterval} {g : ℝ → SmoothRiemannianMetric I M}
    (hg : MetricFamilySmoothOn D g) {u : ℝ → M → ℝ}
    (hu : ContinuousOn (fun p : ℝ × M => u p.1 p.2) (D.carrier ×ˢ _root_.Set.univ)) :
    ContinuousOn
      (fun t => ∫ x, u t x ^ 2 ∂riemannianVolumeMeasure I M (g t)) D.carrier := by
  exact continuousOn_integral_riemannianVolumeMeasure_of_compact_support
    g hg.chartGramMatrix_continuousOn_carrier (fun t x => u t x ^ 2)
    (hu.pow 2) isCompact_univ (fun _ _ _ hx => (hx (_root_.Set.mem_univ _)).elim)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.continuousOn_integral_sq_of_metricFamilySmoothOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.continuousOn_integral_sq_of_metricFamilySmoothOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.continuousOn_integral_sq_of_metricFamilySmoothOn ``Submission.DifferentialGeometry.Analysis.Parabolic.continuousOn_integral_sq_of_metricFamilySmoothOn

theorem continuousOn_integral_normGradSqFun_of_metricFamilySmoothOn
    {D : RealTimeInterval} {g : ℝ → SmoothRiemannianMetric I M}
    (hg : MetricFamilySmoothOn D g) {u : ℝ → M → ℝ}
    (hu : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => u p.1 p.2) (D.regular ×ˢ _root_.Set.univ)) :
    ContinuousOn
      (fun t => ∫ x, normGradSqFun (g t) (u t) x
        ∂riemannianVolumeMeasure I M (g t)) D.regular := by
  have hmetric : ContMDiffOn (𝓘(ℝ, ℝ).prod I)
      (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun p : ℝ × M => (⟨p.2, (g p.1).inner p.2⟩ :
        _root_.Bundle.TotalSpace (E →L[ℝ] E →L[ℝ] ℝ)
          (fun x => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)))
      (D.regular ×ˢ (_root_.Set.univ : Set M)) := by
    intro p hp
    exact (hg.metricCLMSmoothAt
      (D.regular_isOpen.mem_nhds hp.1)).contMDiffWithinAt
  have hgrad : ContinuousOn
      (fun p : ℝ × M => normGradSqFun (g p.1) (u p.1) p.2)
      (D.regular ×ˢ _root_.Set.univ) :=
    (gradSq_joint g D.regular_isOpen
      (chartGramMatrix_joint_contMDiffOn g D.regular hmetric) u hu).continuousOn
  exact continuousOn_integral_riemannianVolumeMeasure_of_compact_support
    g (fun α i j => (hg.chartGramMatrix_continuousOn_carrier α i j).mono
      (_root_.Set.prod_mono D.regular_subset Subset.rfl))
    (fun t x => normGradSqFun (g t) (u t) x) hgrad isCompact_univ
    (fun _ _ _ hx => (hx (_root_.Set.mem_univ _)).elim)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.continuousOn_integral_normGradSqFun_of_metricFamilySmoothOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.continuousOn_integral_normGradSqFun_of_metricFamilySmoothOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.continuousOn_integral_normGradSqFun_of_metricFamilySmoothOn ``Submission.DifferentialGeometry.Analysis.Parabolic.continuousOn_integral_normGradSqFun_of_metricFamilySmoothOn

namespace IsHeatPotOn

theorem continuousOn_integral_sq
    {D : RealTimeInterval} {G : MetricConnectionFamily (I := I) (M := M) ℝ}
    {V u : ℝ → M → ℝ} (hu : IsHeatPotOn D G V u)
    (hG : MetricFamilySmoothOn D G.metric) :
    ContinuousOn
      (fun t => ∫ x, u t x ^ 2 ∂riemannianVolumeMeasure I M (G.metric t))
      D.carrier :=
  continuousOn_integral_sq_of_metricFamilySmoothOn hG hu.jointCont

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.IsHeatPotOn.continuousOn_integral_sq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.IsHeatPotOn.continuousOn_integral_sq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.IsHeatPotOn.continuousOn_integral_sq ``Submission.DifferentialGeometry.Analysis.Parabolic.IsHeatPotOn.continuousOn_integral_sq

theorem continuousOn_integral_normGradSqFun
    {D : RealTimeInterval} {G : MetricConnectionFamily (I := I) (M := M) ℝ}
    {V u : ℝ → M → ℝ} (hu : IsHeatPotOn D G V u)
    (hG : MetricFamilySmoothOn D G.metric) :
    ContinuousOn
      (fun t => ∫ x, normGradSqFun (G.metric t) (u t) x
        ∂riemannianVolumeMeasure I M (G.metric t)) D.regular :=
  continuousOn_integral_normGradSqFun_of_metricFamilySmoothOn hG hu.jointSmooth

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.IsHeatPotOn.continuousOn_integral_normGradSqFun then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.IsHeatPotOn.continuousOn_integral_normGradSqFun"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.IsHeatPotOn.continuousOn_integral_normGradSqFun ``Submission.DifferentialGeometry.Analysis.Parabolic.IsHeatPotOn.continuousOn_integral_normGradSqFun

end IsHeatPotOn

end DifferentialGeometry.Analysis.Parabolic
