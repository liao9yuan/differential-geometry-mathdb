import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientReducedVolumeConvergence
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AsymptoticShrinkerNormalizationReduction
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientReducedVolumeLowerBound
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.ReducedVolume.UpperBound
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.ReducedVolume.Asymptotic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
open _root_.Filter _root_.Set _root_.Submission.Set
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open scoped _root_.ContDiff _root_.Topology _root_.Submission.Topology
universe u uE uH
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.instTopologicalSpaceM : TopologicalSpace F.M := F.topology

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.instTopologicalSpaceM
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.instTopologicalSpaceM target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.instChartedSpaceM : ChartedSpace H F.M := F.charted

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.instChartedSpaceM
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.instChartedSpaceM target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.instIsManifoldRealSomeENatTopM : IsManifold I ∞ F.M := F.smooth

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.instIsManifoldRealSomeENatTopM
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.instIsManifoldRealSomeENatTopM target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.instT2SpaceM : T2Space F.M := F.t2

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.instT2SpaceM
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.instT2SpaceM target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.instSigmaCompactSpaceM : SigmaCompactSpace F.M := F.sigmaCompact

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.instSigmaCompactSpaceM
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.instSigmaCompactSpaceM target :: scope.openDecls } }

private theorem ancient_reducedVolume_le_one_of_regular_base
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
    {T : ℝ} (hT : T < 0) (p : F.M) {tau : ℝ} (htau : 0 < tau) :
    intrinsicReducedVolume F.S T p tau ≤ 1 := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  let _ : ConnectedSpace F.M := hF.connected
  let _ : NeZero (Module.finrank ℝ E) := neZero_finrank_of_isAncientKappaSolution F hF
  have hcomplete : RiemannianMetricComplete (I := I) (F.S.base.metric T) :=
    ⟨hF.complete T hT.le⟩
  apply Perelman.redVolume_le_one_of_rm F.S F.isSolution T hcomplete p
    (fun sigma _ hreg => ancientKappa_regularSlabBound_finrank F hF (T - sigma) T hreg) htau
  exact fun t ht => ht.2.trans_lt hT

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancient_reducedVolume_le_one_of_regular_base
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancient_reducedVolume_le_one_of_regular_base target :: scope.openDecls } }

theorem ancient_reducedVolume_le_one
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
    {T : ℝ} (hT : T ≤ 0) (p : F.M) {tau : ℝ} (htau : 0 < tau) :
    intrinsicReducedVolume F.S T p tau ≤ 1 := by
  rcases hT.lt_or_eq with hT | rfl
  · exact ancient_reducedVolume_le_one_of_regular_base F hF hT p htau
  · let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
    apply le_of_tendsto (ancient_reducedVolume_tendsto_terminal F hF htau p)
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact ancient_reducedVolume_le_one_of_regular_base F hF ht p htau

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancient_reducedVolume_le_one then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancient_reducedVolume_le_one"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancient_reducedVolume_le_one ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancient_reducedVolume_le_one

theorem ancient_reducedVolume_tendsto_atTop
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F) (p : F.M) :
    _root_.Filter.Tendsto (intrinsicReducedVolume F.S 0 p) _root_.Filter.atTop
      (𝓝 (asymptoticReducedVolume F.S 0 p)) := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  exact redVolume_tendsto_atTop_of_antitone F.S 0 p (ancient_reducedVolume_antitone F hF p)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancient_reducedVolume_tendsto_atTop then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancient_reducedVolume_tendsto_atTop"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancient_reducedVolume_tendsto_atTop ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancient_reducedVolume_tendsto_atTop

theorem ancient_reducedVolume_tendsto_rescaled
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F) (p : F.M)
    {α : Type*} {l : Filter α} {tau : α → ℝ} (hescape : _root_.Filter.Tendsto tau l _root_.Filter.atTop)
    {theta : ℝ} (htheta : 0 < theta) :
    _root_.Filter.Tendsto (fun i => intrinsicReducedVolume F.S 0 p (tau i * theta)) l
      (𝓝 (asymptoticReducedVolume F.S 0 p)) :=
  (ancient_reducedVolume_tendsto_atTop F hF p).comp (hescape.atTop_mul_const htheta)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancient_reducedVolume_tendsto_rescaled then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancient_reducedVolume_tendsto_rescaled"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancient_reducedVolume_tendsto_rescaled ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancient_reducedVolume_tendsto_rescaled

theorem ancient_asymptoticReducedVolume_le_one
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F) (p : F.M) :
    asymptoticReducedVolume F.S 0 p ≤ 1 :=
  (asymptoticReducedVolume_le_redVolume F.S 0 p one_pos).trans
    (ancient_reducedVolume_le_one F hF le_rfl p one_pos)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancient_asymptoticReducedVolume_le_one then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancient_asymptoticReducedVolume_le_one"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancient_asymptoticReducedVolume_le_one ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancient_asymptoticReducedVolume_le_one

theorem ancient_asymptoticReducedVolume_pos
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F) (p : F.M) :
    0 < asymptoticReducedVolume F.S 0 p := by
  obtain ⟨v, hv, hbound⟩ := exists_pos_le_ancient_reducedVolume F hF
  exact (ENNReal.ofReal_pos.mpr hv).trans_le
    (le_iInf fun tau : Set.Ioi (0 : ℝ) => hbound p tau tau.property)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancient_asymptoticReducedVolume_pos then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancient_asymptoticReducedVolume_pos"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancient_asymptoticReducedVolume_pos ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancient_asymptoticReducedVolume_pos

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
