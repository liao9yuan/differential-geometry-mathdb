import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Cost.LowerBound
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientMetricMonotonicity
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.ReducedVolume.Measure

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Set
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open scoped _root_.ContDiff _root_.Manifold _root_.Submission.Manifold

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)

local instance terminalGaussianTopology : TopologicalSpace F.M := F.topology

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.terminalGaussianTopology then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.terminalGaussianTopology"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.terminalGaussianTopology ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.terminalGaussianTopology
local instance terminalGaussianCharted : ChartedSpace H F.M := F.charted

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.terminalGaussianCharted then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.terminalGaussianCharted"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.terminalGaussianCharted ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.terminalGaussianCharted
local instance terminalGaussianSmooth : IsManifold I ∞ F.M := F.smooth

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.terminalGaussianSmooth then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.terminalGaussianSmooth"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.terminalGaussianSmooth ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.terminalGaussianSmooth
local instance terminalGaussianT2 : T2Space F.M := F.t2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.terminalGaussianT2 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.terminalGaussianT2"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.terminalGaussianT2 ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.terminalGaussianT2
local instance terminalGaussianSigma : SigmaCompactSpace F.M := F.sigmaCompact

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.terminalGaussianSigma then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.terminalGaussianSigma"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.terminalGaussianSigma ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.terminalGaussianSigma

theorem ancient_lCost_ge_terminal_distance_sq
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
    {T : ℝ} (hT : T ≤ 0) (p q : F.M) {tau : ℝ} (htau : 0 < tau) :
    (riemannianEDistOf (F.S.base.metric 0) p q).toReal ^ 2 / (2 * Real.sqrt tau) ≤
      lCost F.S T p q tau := by
  let : ConnectedSpace F.M := hF.connected
  let : TopologicalSpace.MetrizableSpace F.M := Manifold.metrizableSpace I F.M
  let : PseudoMetricSpace F.M := TopologicalSpace.pseudoMetrizableSpacePseudoMetric F.M
  have htime (s : ℝ) : T - s ^ 2 ∈ ancientTimeInterval.carrier := by
    change T - s ^ 2 ≤ 0
    nlinarith [sq_nonneg s]
  obtain ⟨C, hC⟩ := hF.globalScalarBound
  exact Perelman.lCost_ge_riemannianEDistOf_sq_div F.S F.isSolution T p q htau
    (F.S.base.metric 0) (fun s _ => htime s)
    (fun s _ => CanonicalNeighborhood.ancientModel_metric_zero_le F hF (htime s))
    (fun s _ z => (hC (T - s ^ 2) (htime s) z).1)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancient_lCost_ge_terminal_distance_sq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancient_lCost_ge_terminal_distance_sq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancient_lCost_ge_terminal_distance_sq ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancient_lCost_ge_terminal_distance_sq

theorem ancient_redLength_ge_terminal_distance_sq
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
    {T : ℝ} (hT : T ≤ 0) (p q : F.M) {tau : ℝ} (htau : 0 < tau) :
    (riemannianEDistOf (F.S.base.metric 0) p q).toReal ^ 2 / (4 * tau) ≤
      redLength F.S T p q tau := by
  have hcost := ancient_lCost_ge_terminal_distance_sq F hF hT p q htau
  have hquot := div_le_div_of_nonneg_right hcost
    (show 0 ≤ 2 * Real.sqrt tau by positivity)
  rw [div_div, show (2 * Real.sqrt tau) * (2 * Real.sqrt tau) = 4 * tau by
    nlinarith [Real.sq_sqrt htau.le]] at hquot
  exact hquot

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancient_redLength_ge_terminal_distance_sq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancient_redLength_ge_terminal_distance_sq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancient_redLength_ge_terminal_distance_sq ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancient_redLength_ge_terminal_distance_sq

theorem ancient_redDensity_le_terminal_gaussian
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
    {T : ℝ} (hT : T ≤ 0) (p q : F.M) {tau : ℝ} (htau : 0 < tau) :
    redDensity F.S T p q tau ≤
      Real.exp (-((Module.finrank ℝ E : ℝ) / 2) * Real.log tau -
        ((Module.finrank ℝ E : ℝ) / 2) * Real.log (4 * Real.pi)) *
      Real.exp (-(1 / (4 * tau)) * (riemannianEDistOf (F.S.base.metric 0) p q).toReal ^ 2) := by
  have hlength := ancient_redLength_ge_terminal_distance_sq F hF hT p q htau
  rw [redDensity, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have heq : -(1 / (4 * tau)) * (riemannianEDistOf (F.S.base.metric 0) p q).toReal ^ 2 =
      -(riemannianEDistOf (F.S.base.metric 0) p q).toReal ^ 2 / (4 * tau) := by ring
  rw [heq, neg_div]
  simp only [neg_mul]
  linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancient_redDensity_le_terminal_gaussian then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancient_redDensity_le_terminal_gaussian"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancient_redDensity_le_terminal_gaussian ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancient_redDensity_le_terminal_gaussian

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
