import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientCostBaseTime
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.ReducedVolume.Defs

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open _root_.Set _root_.Submission.Set _root_.Filter
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open scoped _root_.ContDiff _root_.Manifold _root_.Submission.Manifold _root_.Topology _root_.Submission.Topology

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
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

theorem ancient_lCost_lowerSemicontinuousWithinAt_terminal
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
    {tau : ℝ} (htau : 0 < tau) (p q : F.M) :
    LowerSemicontinuousWithinAt (fun T => lCost F.S T p q tau) (_root_.Set.Iic 0) 0 := by
  obtain ⟨C, _hC, hbound⟩ := exists_lCost_base_time_bound_of_ancient F hF
  intro A hA
  have hcont : Continuous (fun R : ℝ =>
      lCost F.S 0 p q tau - 2 * Real.sqrt tau ^ 3 * C * (0 - R)) := by fun_prop
  have hevent : ∀ᶠ R in nhdsWithin 0 (_root_.Set.Iic 0),
      A < lCost F.S 0 p q tau - 2 * Real.sqrt tau ^ 3 * C * (0 - R) :=
    (hcont.continuousAt.eventually (Ioi_mem_nhds (by simpa using hA))).filter_mono
      nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin, hevent] with R hR hRA
  have hle := hbound hR le_rfl htau p q
  linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancient_lCost_lowerSemicontinuousWithinAt_terminal then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancient_lCost_lowerSemicontinuousWithinAt_terminal"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancient_lCost_lowerSemicontinuousWithinAt_terminal ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancient_lCost_lowerSemicontinuousWithinAt_terminal

theorem ancient_lCost_continuousWithinAt_terminal
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
    {tau : ℝ} (htau : 0 < tau) (p q : F.M) :
    ContinuousWithinAt (fun T => lCost F.S T p q tau) (_root_.Set.Iic 0) 0 := by
  let _ : ConnectedSpace F.M := hF.connected
  obtain ⟨B, hB⟩ := hF.globalScalarBound
  refine continuousWithinAt_iff_lower_upperSemicontinuousWithinAt.mpr ⟨?_, ?_⟩
  · exact ancient_lCost_lowerSemicontinuousWithinAt_terminal F hF htau p q
  · exact lCost_upperSemicontinuousWithinAt_of_scalar_nonneg F.S F.isSolution
      (fun {_ _} hb hab => hab.trans hb) (fun t ht x => (hB t ht x).1)
      (T := 0) (by simp only [ancientTimeInterval_carrier, _root_.Set.mem_Iic, le_refl]) htau p q

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancient_lCost_continuousWithinAt_terminal then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancient_lCost_continuousWithinAt_terminal"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancient_lCost_continuousWithinAt_terminal ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancient_lCost_continuousWithinAt_terminal

theorem ancient_redDensity_continuousWithinAt_terminal
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
    {tau : ℝ} (htau : 0 < tau) (p q : F.M) :
    ContinuousWithinAt (fun T => redDensity F.S T p q tau) (_root_.Set.Iic 0) 0 := by
  have hcost := ancient_lCost_continuousWithinAt_terminal F hF htau p q
  have harg := (((hcost.div_const (2 * Real.sqrt tau)).neg.sub_const
    ((Module.finrank ℝ E : ℝ) / 2 * Real.log tau)).sub_const
    ((Module.finrank ℝ E : ℝ) / 2 * Real.log (4 * Real.pi)))
  change ContinuousWithinAt (fun T => Real.exp
    (-(lCost F.S T p q tau / (2 * Real.sqrt tau)) -
      ((Module.finrank ℝ E : ℝ) / 2) * Real.log tau -
      ((Module.finrank ℝ E : ℝ) / 2) * Real.log (4 * Real.pi))) (_root_.Set.Iic 0) 0
  exact Real.continuous_exp.continuousAt.comp_continuousWithinAt harg

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancient_redDensity_continuousWithinAt_terminal then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancient_redDensity_continuousWithinAt_terminal"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancient_redDensity_continuousWithinAt_terminal ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancient_redDensity_continuousWithinAt_terminal

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
