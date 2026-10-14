import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.ReducedLength.PrefixBound
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientReducedVolumeMonotonicity
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientEndpoint
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Cost.Continuity.CarrierBaseTime

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood _root_.Set _root_.Submission.Set _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Bundle _root_.Submission.Bundle _root_.Filter _root_.Function
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)

local instance ancientPrefixTopology : TopologicalSpace F.M := F.topology

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientPrefixTopology then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientPrefixTopology"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientPrefixTopology ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientPrefixTopology
local instance ancientPrefixCharted : ChartedSpace H F.M := F.charted

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientPrefixCharted then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientPrefixCharted"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientPrefixCharted ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientPrefixCharted
local instance ancientPrefixSmooth : IsManifold I ∞ F.M := F.smooth

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientPrefixSmooth then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientPrefixSmooth"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientPrefixSmooth ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientPrefixSmooth
local instance ancientPrefixT2 : T2Space F.M := F.t2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientPrefixT2 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientPrefixT2"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientPrefixT2 ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientPrefixT2
local instance ancientPrefixSigma : SigmaCompactSpace F.M := F.sigmaCompact

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientPrefixSigma then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientPrefixSigma"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientPrefixSigma ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientPrefixSigma

theorem redLength_prefix_le_of_ancient_action_eq_lCost
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
    (alpha : ℝ → F.M) (halpha : ContMDiff 𝓘(ℝ, ℝ) I 1 alpha)
    (x y : F.M) {s tau : ℝ} (hs : 0 < s) (hst : s ≤ tau)
    (hstart : alpha 0 = x) (hend : alpha (Real.sqrt tau) = y)
    (hcost : lRegularizedAction F.S 0 alpha 0 (Real.sqrt tau) =
      lCost F.S 0 x (alpha (Real.sqrt tau)) tau) :
    redLength F.S 0 x (alpha (Real.sqrt s)) s ≤
      (Real.sqrt tau / Real.sqrt s) * redLength F.S 0 x y tau := by
  have hLag := lRegularizedLagrangian_continuousOn_carrier F.S F.isSolution alpha halpha
  have hcont : ContinuousOn (lRegularizedLagrangian F.S 0 alpha)
      (_root_.Set.uIcc 0 (Real.sqrt tau)) := by
    apply hLag.comp (continuous_const.prodMk continuous_id).continuousOn
    intro r hr
    change (0 : ℝ) - r ^ 2 ∈ ancientTimeInterval.carrier
    simpa only [ancientTimeInterval_carrier, Set.mem_Iic, zero_sub] using
      neg_nonpos.mpr (sq_nonneg r)
  apply redLength_squareRootReparametrization_le_of_action_eq_lCost F.S 0 alpha halpha x y
    hs hst hstart hend _ hcont.intervalIntegrable hcost
  obtain ⟨C, hC⟩ := hF.globalScalarBound
  intro r hr z
  exact (hC (0-r) (by simpa only [ancientTimeInterval_carrier, Set.mem_Iic, zero_sub] using neg_nonpos.mpr hr.1) z).1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.redLength_prefix_le_of_ancient_action_eq_lCost then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.redLength_prefix_le_of_ancient_action_eq_lCost"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.redLength_prefix_le_of_ancient_action_eq_lCost ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.redLength_prefix_le_of_ancient_action_eq_lCost

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
