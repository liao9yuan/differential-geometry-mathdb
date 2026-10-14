import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Cost.Continuity.BaseTimeSemicontinuity
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.AncientScalarTimeControl
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientMetricMonotonicity
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientTerminalBounds
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.TensorNormFinrankNeZero

import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Cost.Comparison
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientScalarMonotonicity
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientVolumeComparison

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open _root_.Set _root_.Submission.Set
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open scoped _root_.ContDiff _root_.Manifold _root_.Submission.Manifold

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)

private local instance terminalCostTopology : TopologicalSpace F.M := F.topology

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.terminalCostTopology
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.terminalCostTopology target :: scope.openDecls } }
private local instance terminalCostCharted : ChartedSpace H F.M := F.charted

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.terminalCostCharted
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.terminalCostCharted target :: scope.openDecls } }
private local instance terminalCostSmooth : IsManifold I ∞ F.M := F.smooth

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.terminalCostSmooth
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.terminalCostSmooth target :: scope.openDecls } }
private local instance terminalCostC1 : IsManifold I 1 F.M :=
  IsManifold.of_le (n := ∞) (by decide)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.terminalCostC1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.terminalCostC1 target :: scope.openDecls } }
private local instance terminalCostT2 : T2Space F.M := F.t2

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.terminalCostT2
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.terminalCostT2 target :: scope.openDecls } }
private local instance terminalCostSigma : SigmaCompactSpace F.M := F.sigmaCompact

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.terminalCostSigma
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.terminalCostSigma target :: scope.openDecls } }

theorem exists_lCost_base_time_bound_of_ancient
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {R T tau : ℝ}, R ≤ T → T ≤ 0 → 0 < tau →
      ∀ p q : F.M, lCost F.S T p q tau ≤ lCost F.S R p q tau +
        2 * Real.sqrt tau ^ 3 * C * (T - R) := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  let _ : ConnectedSpace F.M := hF.connected
  let _ : NeZero (Module.finrank ℝ E) := by
    obtain ⟨t, _ht, x, hx⟩ := hF.notFlat
    exact ⟨Tensor0SBundle.finrank_ne_zero_of_normSq0S_ne_zero
      (F.S.base.metric t) x (by decide : 0 < 4) (F.S.base.rm04 t x) hx⟩
  obtain ⟨B, hB⟩ := ancientKappa_rmNormSqBounded_finrank F hF
  let K := |B| + 1
  have hK : 0 < K := by dsimp only [K]; positivity
  have hBK : B ≤ K ^ 2 := by
    dsimp only [K]
    nlinarith [le_abs_self B, abs_nonneg B, sq_nonneg (|B|)]
  obtain ⟨C, hC, hscalarTime⟩ :=
    DifferentialGeometry.PDE.RicciFlow.exists_scalar_time_lipschitz_bound_of_complete_ancient_bounded_curvature
      F.S F.isSolution hF.carrier_eq hF.regular_eq hK
      (fun t ht => ⟨hF.complete t ht⟩) (fun t ht x => (hB t ht x).trans hBK)
  have hmetric (x : F.M) (v : TangentSpace I x) :
      AntitoneOn (fun t => (F.S.base.metric t).inner x v v) (_root_.Set.Iic 0) :=
    ancientModel_metric_inner_antitoneOn F hF x v
  obtain ⟨Bscalar, hBscalar⟩ := hF.globalScalarBound
  refine ⟨C, hC, ?_⟩
  intro R T tau hRT hT htau p q
  exact lCost_le_add_of_metric_antitone_of_scalar_time_lipschitz F.S F.isSolution
    hF.carrier_eq hC hmetric hscalarTime (fun t ht x => (hBscalar t ht x).1)
    hRT hT htau p q

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_lCost_base_time_bound_of_ancient then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_lCost_base_time_bound_of_ancient"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_lCost_base_time_bound_of_ancient ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_lCost_base_time_bound_of_ancient

theorem exists_lCost_base_time_exp_bound_of_ancient
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {R T tau : ℝ}, R ≤ T → T ≤ 0 → 0 < tau →
      ∀ p q : F.M, lCost F.S R p q tau ≤
        Real.exp (K * (T - R)) * lCost F.S T p q tau := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  let _ : ConnectedSpace F.M := hF.connected
  obtain ⟨K, hK, hm⟩ := exists_ancientKappa_metric_inner_le_exp F hF
  obtain ⟨C, hC⟩ := hF.globalScalarBound
  refine ⟨2 * K, mul_nonneg (by norm_num) hK, ?_⟩
  intro R T tau hRT hT htau p q
  apply lCost_le_mul_of_metric_le_of_scalar_le F.S F.S F.isSolution F.isSolution
    htau (Real.exp_pos _).le
    (fun s hs => hs.2.trans (hRT.trans hT)) (fun s hs => hs.2.trans hT)
    (fun s hs x => (hC (R - s) ((sub_le_self _ hs.1).trans (hRT.trans hT)) x).1)
  · intro s hs x v
    have h := hm (R - s) (T - s) (sub_le_sub_right hRT _) ((sub_le_self _ hs.1).trans hT) x v
    simpa only [sub_sub_sub_cancel_right] using h
  · intro s hs x
    have hRs : R - s ≤ 0 := (sub_le_self _ hs.1).trans (hRT.trans hT)
    have hTs : T - s ≤ 0 := (sub_le_self _ hs.1).trans hT
    have hsc := ancientKappa_scalar_monotoneOn F hF x hRs hTs (sub_le_sub_right hRT _)
    have he : 1 ≤ Real.exp (2 * K * (T - R)) := Real.one_le_exp (mul_nonneg
      (mul_nonneg (by norm_num) hK) (sub_nonneg.mpr hRT))
    exact hsc.trans (le_mul_of_one_le_left (hC (T - s) hTs x).1 he)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_lCost_base_time_exp_bound_of_ancient then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_lCost_base_time_exp_bound_of_ancient"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_lCost_base_time_exp_bound_of_ancient ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_lCost_base_time_exp_bound_of_ancient


end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
