import Submission.DifferentialGeometry.Geometry.Metric.Family.GradientCoefficients
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Fields.GramConvergence

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Set _root_.Filter _root_.Bundle _root_.Submission.Bundle
open scoped _root_.Manifold _root_.Submission.Manifold _root_.Topology _root_.Submission.Topology _root_.ContDiff

namespace DifferentialGeometry.CheegerGromovCompactness

open _root_.Submission.DifferentialGeometry.Geometry.Curvature _root_.Submission.DifferentialGeometry.Geometry.Operator _root_.Submission.DifferentialGeometry.Integral.Measure

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {X : PointedFlowSeq.{u, uE, uH} (I := I)}
variable {P : PointedRiemannianManifold.{u, uE, uH} (I := I)}
variable {subseq : ℕ → ℕ}
variable (Φ : PointedCGHMaps (I := I) X P subseq)

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

theorem continuousOn_chartDensity_smul_chartGradientBilin_gSeqExt [I.Boundaryless]
    (R : let : TopologicalSpace P.M := P.topology
      let : ChartedSpace H P.M := P.charted
      let : IsManifold I ∞ P.M := P.smooth
      SmoothRiemannianMetric I P.M)
    (bf : BumpFamily (I := I) Φ) (hsrc : SourceIsSigmaCompact Φ)
    (htgt : TargetIsSigmaCompact Φ)
    (k : ℕ)
    (alpha : P.M) {K : Set E}
    (hKchart : let : TopologicalSpace P.M := P.topology
      let : ChartedSpace H P.M := P.charted
      K ⊆ (extChartAt I alpha).target)
    (w : ℝ × E → ℝ) (hw : ContinuousOn w (X.D.carrier ×ˢ K)) :
    let : TopologicalSpace P.M := P.topology
    let : ChartedSpace H P.M := P.charted
    let : T2Space P.M := P.t2
    let : IsManifold I ∞ P.M := P.smooth
    let : SigmaCompactSpace P.M := P.sigmaCompact
    ContinuousOn
      (fun q : ℝ × E =>
        (w q * chartDensity (gSeqExt (I := I) Φ R bf hsrc htgt k q.1)
          alpha ((extChartAt I alpha).symm q.2)) •
        chartGradientBilin (gSeqExt (I := I) Φ R bf hsrc htgt k q.1)
          alpha ((extChartAt I alpha).symm q.2))
      (X.D.carrier ×ˢ K) := by
  let : TopologicalSpace P.M := P.topology
  let : ChartedSpace H P.M := P.charted
  let : T2Space P.M := P.t2
  let : IsManifold I ∞ P.M := P.smooth
  let : SigmaCompactSpace P.M := P.sigmaCompact
  let G : MetricConnectionFamilyOn (I := I) (M := P.M) X.D :=
    (lcMetricFamily (I := I) (M := P.M)
      (fun t => gSeqExt (I := I) Φ R bf hsrc htgt k t)).restrict X.D
  exact continuousOn_chartDensity_smul_chartGradientBilin G alpha
    (fun q hq => hKchart hq.2)
    (continuousOn_chartGramOp_gSeqExt Φ R bf hsrc htgt k alpha hKchart) w hw

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.continuousOn_chartDensity_smul_chartGradientBilin_gSeqExt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.continuousOn_chartDensity_smul_chartGradientBilin_gSeqExt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.continuousOn_chartDensity_smul_chartGradientBilin_gSeqExt ``Submission.DifferentialGeometry.CheegerGromovCompactness.continuousOn_chartDensity_smul_chartGradientBilin_gSeqExt

theorem FlowMetricConvergenceData.continuousOn_chartDensity_smul_chartGradientBilin [I.Boundaryless]
    (R : let : TopologicalSpace P.M := P.topology
      let : ChartedSpace H P.M := P.charted
      let : IsManifold I ∞ P.M := P.smooth
      SmoothRiemannianMetric I P.M)
    (bf : BumpFamily (I := I) Φ) (hsrc : SourceIsSigmaCompact Φ)
    (htgt : TargetIsSigmaCompact Φ)
    (beta psi : ℝ) (co : FlowMetricConvergenceData (I := I) Φ R bf hsrc htgt beta psi)
    (alpha : P.M) {K : Set E}
    (hKchart : let : TopologicalSpace P.M := P.topology
      let : ChartedSpace H P.M := P.charted
      K ⊆ (extChartAt I alpha).target) (hKc : IsCompact K)
    (hcarrier : _root_.Set.Icc beta psi ⊆ X.D.carrier)
    (w : ℝ × E → ℝ) (hw : ContinuousOn w (_root_.Set.Icc beta psi ×ˢ K)) :
    let : TopologicalSpace P.M := P.topology
    let : ChartedSpace H P.M := P.charted
    let : T2Space P.M := P.t2
    let : IsManifold I ∞ P.M := P.smooth
    let : SigmaCompactSpace P.M := P.sigmaCompact
    ContinuousOn
      (fun q : ℝ × E =>
        (w q * chartDensity (co.gInf q.1) alpha ((extChartAt I alpha).symm q.2)) •
        chartGradientBilin (co.gInf q.1) alpha ((extChartAt I alpha).symm q.2))
      (_root_.Set.Icc beta psi ×ˢ K) := by
  let : TopologicalSpace P.M := P.topology
  let : ChartedSpace H P.M := P.charted
  let : T2Space P.M := P.t2
  let : IsManifold I ∞ P.M := P.smooth
  let : SigmaCompactSpace P.M := P.sigmaCompact
  let G : MetricConnectionFamilyOn (I := I) (M := P.M) X.D :=
    (lcMetricFamily (I := I) (M := P.M) co.gInf).restrict X.D
  exact Geometry.Curvature.continuousOn_chartDensity_smul_chartGradientBilin G alpha
    (fun q hq => hKchart hq.2)
    (co.continuousOn_chartGramOp Φ R bf hsrc htgt beta psi alpha hKchart hKc hcarrier) w hw

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.FlowMetricConvergenceData.continuousOn_chartDensity_smul_chartGradientBilin then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.FlowMetricConvergenceData.continuousOn_chartDensity_smul_chartGradientBilin"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.FlowMetricConvergenceData.continuousOn_chartDensity_smul_chartGradientBilin ``Submission.DifferentialGeometry.CheegerGromovCompactness.FlowMetricConvergenceData.continuousOn_chartDensity_smul_chartGradientBilin

theorem FlowMetricConvergenceData.tendstoUniformlyOn_chartDensity_smul_chartGradientBilin
    [I.Boundaryless]
    (R : let : TopologicalSpace P.M := P.topology
      let : ChartedSpace H P.M := P.charted
      let : IsManifold I ∞ P.M := P.smooth
      SmoothRiemannianMetric I P.M)
    (bf : BumpFamily (I := I) Φ) (hsrc : SourceIsSigmaCompact Φ)
    (htgt : TargetIsSigmaCompact Φ)
    (beta psi : ℝ) (co : FlowMetricConvergenceData (I := I) Φ R bf hsrc htgt beta psi)
    (alpha : P.M) {K : Set E}
    (hKchart : let : TopologicalSpace P.M := P.topology
      let : ChartedSpace H P.M := P.charted
      K ⊆ (extChartAt I alpha).target) (hKc : IsCompact K)
    (hcarrier : _root_.Set.Icc beta psi ⊆ X.D.carrier)
    (w : ℝ × E → ℝ) (hw : ContinuousOn w (_root_.Set.Icc beta psi ×ˢ K)) :
    let : TopologicalSpace P.M := P.topology
    let : ChartedSpace H P.M := P.charted
    let : T2Space P.M := P.t2
    let : IsManifold I ∞ P.M := P.smooth
    let : SigmaCompactSpace P.M := P.sigmaCompact
    TendstoUniformlyOn
      (fun k (q : ℝ × E) =>
        (w q * chartDensity (gSeqExt (I := I) Φ R bf hsrc htgt (co.φ k) q.1)
          alpha ((extChartAt I alpha).symm q.2)) •
        chartGradientBilin (gSeqExt (I := I) Φ R bf hsrc htgt (co.φ k) q.1)
          alpha ((extChartAt I alpha).symm q.2))
      (fun q =>
        (w q * chartDensity (co.gInf q.1) alpha ((extChartAt I alpha).symm q.2)) •
        chartGradientBilin (co.gInf q.1) alpha ((extChartAt I alpha).symm q.2))
      atTop (_root_.Set.Icc beta psi ×ˢ K) := by
  let : TopologicalSpace P.M := P.topology
  let : ChartedSpace H P.M := P.charted
  let : T2Space P.M := P.t2
  let : IsManifold I ∞ P.M := P.smooth
  let : SigmaCompactSpace P.M := P.sigmaCompact
  let GSeq : ℕ → MetricConnectionFamilyOn (I := I) (M := P.M) X.D := fun k =>
    (lcMetricFamily (I := I) (M := P.M)
      (fun t => gSeqExt (I := I) Φ R bf hsrc htgt (co.φ k) t)).restrict X.D
  let GInf : MetricConnectionFamilyOn (I := I) (M := P.M) X.D :=
    (lcMetricFamily (I := I) (M := P.M) co.gInf).restrict X.D
  exact Geometry.Curvature.tendstoUniformlyOn_chartDensity_smul_chartGradientBilin
    GSeq GInf alpha (isCompact_Icc.prod hKc) (fun q hq => hKchart hq.2)
    (co.continuousOn_chartGramOp Φ R bf hsrc htgt beta psi alpha hKchart hKc hcarrier)
    (co.tendstoUniformlyOn_chartGramOp Φ R bf hsrc htgt beta psi alpha hKchart hKc)
    w hw

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.FlowMetricConvergenceData.tendstoUniformlyOn_chartDensity_smul_chartGradientBilin then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.FlowMetricConvergenceData.tendstoUniformlyOn_chartDensity_smul_chartGradientBilin"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.FlowMetricConvergenceData.tendstoUniformlyOn_chartDensity_smul_chartGradientBilin ``Submission.DifferentialGeometry.CheegerGromovCompactness.FlowMetricConvergenceData.tendstoUniformlyOn_chartDensity_smul_chartGradientBilin

end DifferentialGeometry.CheegerGromovCompactness
