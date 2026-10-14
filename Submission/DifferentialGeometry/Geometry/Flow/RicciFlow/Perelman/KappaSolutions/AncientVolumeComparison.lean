import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.ModelWitness
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientTerminalBounds
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.MetricComparison
import Submission.DifferentialGeometry.Analysis.Integration.Measure.Riemannian.MetricComparison
import Submission.DifferentialGeometry.Geometry.Curvature.Bounds.RicciUpper

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section

section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open _root_.Filter _root_.Set _root_.MeasureTheory _root_.Submission.MeasureTheory
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Integral.Measure
open scoped _root_.ContDiff _root_.Manifold _root_.Submission.Manifold _root_.Topology _root_.Submission.Topology _root_.ENNReal

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)

private local instance terminalFatouTopology : TopologicalSpace F.M := F.topology

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.terminalFatouTopology
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.terminalFatouTopology target :: scope.openDecls } }
private local instance terminalFatouCharted : ChartedSpace H F.M := F.charted

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.terminalFatouCharted
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.terminalFatouCharted target :: scope.openDecls } }
private local instance terminalFatouSmooth : IsManifold I ∞ F.M := F.smooth

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.terminalFatouSmooth
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.terminalFatouSmooth target :: scope.openDecls } }
private local instance terminalFatouC1 : IsManifold I 1 F.M :=
  IsManifold.of_le (n := ∞) (by decide)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.terminalFatouC1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.terminalFatouC1 target :: scope.openDecls } }
private local instance terminalFatouT2 : T2Space F.M := F.t2

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.terminalFatouT2
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.terminalFatouT2 target :: scope.openDecls } }
private local instance terminalFatouSigma : SigmaCompactSpace F.M := F.sigmaCompact

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.terminalFatouSigma
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.terminalFatouSigma target :: scope.openDecls } }
private local instance terminalFatouMeasurable : MeasurableSpace F.M := borel F.M

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.terminalFatouMeasurable
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.terminalFatouMeasurable target :: scope.openDecls } }
private local instance terminalFatouBorel : BorelSpace F.M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.terminalFatouBorel
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.terminalFatouBorel target :: scope.openDecls } }

theorem ancient_volumeMeasure_le_of_time_le
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
    {s t : ℝ} (hst : s ≤ t) (ht : t ≤ 0) :
    riemannianVolumeMeasure (I := I) (M := F.M) (F.S.base.metric t) ≤
      riemannianVolumeMeasure (I := I) (M := F.M) (F.S.base.metric s) := by
  have hRic : ∀ q ∈ _root_.Set.Ioo s t, ∀ y : F.M, ∀ w : TangentSpace I y,
      0 ≤ F.S.ricciAt q y (vec2 w w) := by
    intro q hq y w
    have hqmem : q ∈ ancientTimeInterval.carrier := hq.2.le.trans ht
    apply metricRicciAt_nonnegative_of_curvatureOperator_nonnegative
    apply (metricAlgebraicCurvatureTensorAt_mem_curvatureOperatorNonnegativeCone_iff
      (I := I) (F.S.base.metric q) y).mpr
    intro n c a b
    simpa only [SolutionFamily.rm04, metricRm04StandardAt_apply, metricRm04_apply] using
      hF.nonnegativeCurvatureOperator q hqmem y n c a b
  have hmetric (x : F.M) (v : TangentSpace I x) :
      (F.S.base.metric t).inner x v v ≤ (F.S.base.metric s).inner x v v := by
    have hanti := CanonicalNeighborhood.metric_inner_antitoneOn_of_ricci_nonnegative_interior F.S F.isSolution
      (a := s) (b := t) (fun _ hq => hq.2.trans ht)
      (fun _ hq => hq.2.trans_le ht) hRic x v
    exact hanti ⟨le_rfl, hst⟩ ⟨hst, le_rfl⟩ hst
  simpa only [one_pow, Real.sqrt_one, ENNReal.ofReal_one, one_smul] using
    volumeMeasure_le (F.S.base.metric s) (F.S.base.metric t) one_pos
      (fun x v => by simpa only [one_mul] using hmetric x v)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancient_volumeMeasure_le_of_time_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancient_volumeMeasure_le_of_time_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancient_volumeMeasure_le_of_time_le ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancient_volumeMeasure_le_of_time_le


end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end

section

open _root_.Set _root_.MeasureTheory _root_.Submission.MeasureTheory
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open _root_.Submission.DifferentialGeometry.Integral.Measure
open scoped _root_.ContDiff _root_.Manifold _root_.Submission.Manifold _root_.ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)

local instance terminalVolumeTopology : TopologicalSpace F.M := F.topology

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.terminalVolumeTopology then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.terminalVolumeTopology"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.terminalVolumeTopology ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.terminalVolumeTopology
local instance terminalVolumeCharted : ChartedSpace H F.M := F.charted

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.terminalVolumeCharted then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.terminalVolumeCharted"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.terminalVolumeCharted ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.terminalVolumeCharted
local instance terminalVolumeSmooth : IsManifold I ∞ F.M := F.smooth

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.terminalVolumeSmooth then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.terminalVolumeSmooth"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.terminalVolumeSmooth ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.terminalVolumeSmooth
local instance terminalVolumeT2 : T2Space F.M := F.t2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.terminalVolumeT2 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.terminalVolumeT2"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.terminalVolumeT2 ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.terminalVolumeT2
local instance terminalVolumeSigma : SigmaCompactSpace F.M := F.sigmaCompact

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.terminalVolumeSigma then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.terminalVolumeSigma"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.terminalVolumeSigma ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.terminalVolumeSigma
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.instMeasurableSpaceM : MeasurableSpace F.M := borel F.M

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.instMeasurableSpaceM
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.instMeasurableSpaceM target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.instBorelSpaceM : BorelSpace F.M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.instBorelSpaceM
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.instBorelSpaceM target :: scope.openDecls } }

theorem exists_ancientKappa_metric_inner_le_exp
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ s t : ℝ, s ≤ t → t ≤ 0 →
      ∀ x : F.M, ∀ v : TangentSpace I x,
      (F.S.base.metric s).inner x v v ≤
        Real.exp (2 * K * (t - s)) * (F.S.base.metric t).inner x v v := by
  obtain ⟨B, hB⟩ := ancientKappa_rmNormSqBounded_finrank F hF
  let K : ℝ := (Module.finrank ℝ E : ℝ) ^ 2 * Real.sqrt B
  refine ⟨K, mul_nonneg (sq_nonneg _) (Real.sqrt_nonneg _), ?_⟩
  intro s t hst ht x v
  have hslab : _root_.Set.Icc s t ⊆ ancientTimeInterval.carrier := fun r hr => hr.2.trans ht
  have hreg : _root_.Set.Ioo s t ⊆ ancientTimeInterval.regular := fun r hr => hr.2.trans_le ht
  have hpde := metricPDE_Icc F.S F.isSolution hslab hreg
  have hric : ∀ r ∈ _root_.Set.Icc s t, ∀ y : F.M, ∀ w : TangentSpace I y,
      |ricciTensor (F.S.base.metric r) y w w| ≤
        K * (F.S.base.metric r).inner y w w :=
    fun r hr y w => ricci_quadratic_form_bound_of_solution_curvature_bound F.S y w
      (hB r (hslab hr) y)
  have hpair := (metricEquiv_Icc F.S.base.metric hpde hric t ⟨hst, le_rfl⟩ x v).1
  calc
    (F.S.base.metric s).inner x v v =
        Real.exp (2 * K * (t - s)) *
          (Real.exp (-(2 * K * (t - s))) * (F.S.base.metric s).inner x v v) := by
      rw [← mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul]
    _ ≤ Real.exp (2 * K * (t - s)) * (F.S.base.metric t).inner x v v :=
      mul_le_mul_of_nonneg_left hpair (Real.exp_pos _).le

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_ancientKappa_metric_inner_le_exp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_ancientKappa_metric_inner_le_exp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_ancientKappa_metric_inner_le_exp ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_ancientKappa_metric_inner_le_exp

theorem exists_ancientKappa_volumeMeasure_le_exp
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ s t : ℝ, s ≤ t → t ≤ 0 →
      riemannianVolumeMeasure (I := I) (M := F.M) (F.S.base.metric s) ≤
        ENNReal.ofReal (Real.sqrt (Real.exp (2 * K * (t - s)) ^ Module.finrank ℝ E)) •
          riemannianVolumeMeasure (I := I) (M := F.M) (F.S.base.metric t) := by
  obtain ⟨K, hK, hmetric⟩ := exists_ancientKappa_metric_inner_le_exp F hF
  exact ⟨K, hK, fun s t hst ht =>
    volumeMeasure_le _ _ (Real.exp_pos _) (hmetric s t hst ht)⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_ancientKappa_volumeMeasure_le_exp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_ancientKappa_volumeMeasure_le_exp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_ancientKappa_volumeMeasure_le_exp ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_ancientKappa_volumeMeasure_le_exp

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
