import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Cost.Continuity.EndpointSemicontinuity
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientTerminalBounds
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.ReducedVolume.Defs
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open _root_.Set
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open scoped _root_.ContDiff _root_.Manifold _root_.Submission.Manifold

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)

private local instance terminalMeasurableTopology : TopologicalSpace F.M := F.topology

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.terminalMeasurableTopology
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.terminalMeasurableTopology target :: scope.openDecls } }
private local instance terminalMeasurableCharted : ChartedSpace H F.M := F.charted

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.terminalMeasurableCharted
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.terminalMeasurableCharted target :: scope.openDecls } }
private local instance terminalMeasurableSmooth : IsManifold I ∞ F.M := F.smooth

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.terminalMeasurableSmooth
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.terminalMeasurableSmooth target :: scope.openDecls } }
private local instance terminalMeasurableT2 : T2Space F.M := F.t2

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.terminalMeasurableT2
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.terminalMeasurableT2 target :: scope.openDecls } }
private local instance terminalMeasurableSpace : MeasurableSpace F.M := borel F.M

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.terminalMeasurableSpace
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.terminalMeasurableSpace target :: scope.openDecls } }
private local instance terminalMeasurableBorel : BorelSpace F.M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.terminalMeasurableBorel
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.terminalMeasurableBorel target :: scope.openDecls } }

theorem ancient_measurable_redDensity
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
    {T tau : ℝ} (hT : T ≤ 0) (htau : 0 < tau) (p : F.M) :
    Measurable (fun q : F.M => redDensity F.S T p q tau) := by
  let : ConnectedSpace F.M := hF.connected
  obtain ⟨B, hB⟩ := hF.globalScalarBound
  have hcost : UpperSemicontinuous (fun q : F.M => lCost F.S T p q tau) :=
    upperSemicontinuous_lCost_of_scalar_nonneg F.S F.isSolution htau p
      isOpen_univ (_root_.Set.subset_univ _)
      (fun s _ => by change T - s ^ 2 ≤ 0; nlinarith [sq_nonneg s])
      (fun s hs z => (hB (T - s) ((sub_le_self _ hs.1).trans hT) z).1)
  let phi : ℝ → ℝ := fun r => Real.exp
    (-r / (2 * Real.sqrt tau) -
      ((Module.finrank ℝ E : ℝ) / 2) * Real.log tau -
      ((Module.finrank ℝ E : ℝ) / 2) * Real.log (4 * Real.pi))
  have hphi : Continuous phi := by dsimp only [phi]; fun_prop
  have hphiAnti : Antitone phi := by
    intro a b hab
    apply Real.exp_le_exp.mpr
    gcongr
  have hdensity : LowerSemicontinuous (fun q : F.M => redDensity F.S T p q tau) := by
    simpa only [Function.comp_def, phi, redDensity, redLength, neg_div] using
      hphi.comp_upperSemicontinuous_antitone hcost hphiAnti
  exact hdensity.measurable

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancient_measurable_redDensity then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancient_measurable_redDensity"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancient_measurable_redDensity ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancient_measurable_redDensity

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
