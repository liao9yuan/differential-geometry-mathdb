import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Fields.GradientCoefficients
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Fields.Open.HalfLineRegularity
import Submission.DifferentialGeometry.Analysis.Integration.Measure.VolumeDensityFamily

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission


noncomputable section

namespace DifferentialGeometry.CheegerGromovCompactness

open _root_.Bundle _root_.Submission.Bundle _root_.Set
open _root_.Submission.DifferentialGeometry.Geometry.Curvature _root_.Submission.DifferentialGeometry.Geometry.Operator _root_.Submission.DifferentialGeometry.Integral.Measure
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology _root_.Submission.Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {X : PointedFlowSeq (I := I)} {P : PointedRiemannianManifold (I := I)}
  {subseq : ℕ → ℕ} (Φ : PointedCGHMaps X P subseq)

private local instance covectorNormedAddCommGroup : NormedAddCommGroup (E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

run_cmd do
  let target := ``Submission.DifferentialGeometry.CheegerGromovCompactness.covectorNormedAddCommGroup
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.CheegerGromovCompactness.covectorNormedAddCommGroup target :: scope.openDecls } }

private local instance covectorNormedSpace : NormedSpace ℝ (E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

run_cmd do
  let target := ``Submission.DifferentialGeometry.CheegerGromovCompactness.covectorNormedSpace
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.CheegerGromovCompactness.covectorNormedSpace target :: scope.openDecls } }

private local instance covectorDualNormedAddCommGroup : NormedAddCommGroup ((E →L[ℝ] ℝ) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

run_cmd do
  let target := ``Submission.DifferentialGeometry.CheegerGromovCompactness.covectorDualNormedAddCommGroup
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.CheegerGromovCompactness.covectorDualNormedAddCommGroup target :: scope.openDecls } }

private local instance covectorDualNormedSpace : NormedSpace ℝ ((E →L[ℝ] ℝ) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

run_cmd do
  let target := ``Submission.DifferentialGeometry.CheegerGromovCompactness.covectorDualNormedSpace
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.CheegerGromovCompactness.covectorDualNormedSpace target :: scope.openDecls } }

private local instance covectorBilinNormedAddCommGroup :
    NormedAddCommGroup ((E →L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] ℝ) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

run_cmd do
  let target := ``Submission.DifferentialGeometry.CheegerGromovCompactness.covectorBilinNormedAddCommGroup
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.CheegerGromovCompactness.covectorBilinNormedAddCommGroup target :: scope.openDecls } }

private local instance covectorBilinNormedSpace :
    NormedSpace ℝ ((E →L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] ℝ) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

run_cmd do
  let target := ``Submission.DifferentialGeometry.CheegerGromovCompactness.covectorBilinNormedSpace
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.CheegerGromovCompactness.covectorBilinNormedSpace target :: scope.openDecls } }

attribute [local instance] PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact

omit [FiniteDimensional ℝ E] [CompleteSpace E] [I.Boundaryless] in
private theorem continuousOn_chart_pullback
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    {F : Type*} [TopologicalSpace F] {J : Set ℝ} (α : M)
    (f : ℝ × M → F)
    (hf : ContinuousOn f (J ×ˢ (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet)) :
    ContinuousOn (fun z : ℝ × E => f (z.1, (extChartAt I α).symm z.2))
      (J ×ˢ (extChartAt I α).target) := by
  have hchart : ContinuousOn (fun z : ℝ × E => (extChartAt I α).symm z.2)
      (J ×ˢ (extChartAt I α).target) :=
    (continuousOn_extChartAt_symm (I := I) α).comp
      (continuous_snd.continuousOn : ContinuousOn (fun z : ℝ × E => z.2)
        (J ×ˢ (extChartAt I α).target)) (fun _ hz => hz.2)
  have hpair : ContinuousOn (fun z : ℝ × E => (z.1, (extChartAt I α).symm z.2))
      (J ×ˢ (extChartAt I α).target) :=
    continuous_fst.continuousOn.prodMk hchart
  exact hf.comp hpair
    (fun z hz => ⟨hz.1,
      Tensor.Coordinates.extChartAt_symm_mem_trivializationAt_baseSet (I := I) α hz.2⟩)

run_cmd do
  let target := ``Submission.DifferentialGeometry.CheegerGromovCompactness.continuousOn_chart_pullback
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.CheegerGromovCompactness.continuousOn_chart_pullback target :: scope.openDecls } }

namespace HalfLineMetricConvergenceData

variable {R : SmoothRiemannianMetric I P.M}
  {bf : BumpFamily Φ} {hsrc : SourceIsSigmaCompact Φ} {htgt : TargetIsSigmaCompact Φ}
  (co : HalfLineMetricConvergenceData Φ R bf hsrc htgt)

theorem continuousOn_chartDensity
    (hreg : _root_.Set.Iio 0 ⊆ X.D.regular) (α : P.M) :
    ContinuousOn (fun z : ℝ × E =>
      chartDensity (co.gInf z.1) α ((extChartAt I α).symm z.2))
      (_root_.Set.Iio 0 ×ˢ (extChartAt I α).target) := by
  have hc : ContinuousOn
      (fun p : ℝ × P.M => chartDensity (I := I) (co.gInf p.1) α p.2)
      (_root_.Set.Iio 0 ×ˢ (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet) :=
    (chartDensity_family_contMDiffOn (I := I) (M := P.M) co.gInf α
      (gramSmooth (I := I) (Φ := Φ) co hreg α)).continuousOn
  exact continuousOn_chart_pullback (I := I) α _ hc

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.continuousOn_chartDensity then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.continuousOn_chartDensity"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.continuousOn_chartDensity ``Submission.DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.continuousOn_chartDensity

theorem continuousOn_chartGradientBilin
    (hreg : _root_.Set.Iio 0 ⊆ X.D.regular) (α : P.M) :
    ContinuousOn (fun z : ℝ × E =>
      chartGradientBilin (co.gInf z.1) α ((extChartAt I α).symm z.2))
      (_root_.Set.Iio 0 ×ˢ (extChartAt I α).target) := by
  let G : MetricConnectionFamilyOn (I := I) (M := P.M) X.D :=
    (lcMetricFamily (I := I) co.gInf).restrict X.D
  have hgram : ContinuousOn (chartGramOp G α) (_root_.Set.Iio 0 ×ˢ (extChartAt I α).target) := by
    apply Geometry.Curvature.continuousOn_chartGramOp
    intro i j
    exact continuousOn_chart_pullback (I := I) α _
      ((gramSmooth (I := I) (Φ := Φ) co hreg α i j).continuousOn)
  have hc := Geometry.Curvature.continuousOn_smul_chartGradientBilin G α
    (fun z hz => hz.2) hgram (fun _ => (1 : ℝ)) continuousOn_const
  simpa only [one_smul, G, MetricConnectionFamily.restrict_metric, lcMetricFamily] using hc

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.continuousOn_chartGradientBilin then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.continuousOn_chartGradientBilin"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.continuousOn_chartGradientBilin ``Submission.DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.continuousOn_chartGradientBilin

end HalfLineMetricConvergenceData

end DifferentialGeometry.CheegerGromovCompactness
