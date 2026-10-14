import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientSpeed

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood _root_.Set _root_.Submission.Set _root_.MeasureTheory _root_.Submission.MeasureTheory
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)

local instance tailSpeedTopology : TopologicalSpace F.M := F.topology

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.tailSpeedTopology then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.tailSpeedTopology"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.tailSpeedTopology ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.tailSpeedTopology
local instance tailSpeedCharted : ChartedSpace H F.M := F.charted

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.tailSpeedCharted then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.tailSpeedCharted"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.tailSpeedCharted ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.tailSpeedCharted
local instance tailSpeedSmooth : IsManifold I ∞ F.M := F.smooth

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.tailSpeedSmooth then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.tailSpeedSmooth"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.tailSpeedSmooth ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.tailSpeedSmooth
local instance tailSpeedT2 : T2Space F.M := F.t2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.tailSpeedT2 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.tailSpeedT2"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.tailSpeedT2 ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.tailSpeedT2
local instance tailSpeedSigma : SigmaCompactSpace F.M := F.sigmaCompact

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.tailSpeedSigma then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.tailSpeedSigma"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.tailSpeedSigma ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.tailSpeedSigma

theorem lRegularizedSpeedSq_le_six_action_div_on_tail_of_ancient
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
    (alpha : ℝ → F.M) (halpha : ContMDiff 𝓘(ℝ, ℝ) I 1 alpha)
    {c s b : ℝ} (hc : 0 < c) (hcs : c ≤ s) (hsb : s ≤ b)
    (hgeo : IsLRegularizedGeodesicOn F.S 0 alpha (_root_.Set.Ioo 0 b)) :
    lRegularizedSpeedSq F.S 0 alpha s ≤
      6 * lRegularizedAction F.S 0 alpha 0 b / c := by
  have hs : 0 < s := hc.trans_le hcs
  have hspeed := lRegularizedSpeedSq_le_six_action_div_of_ancient F hF alpha halpha hs
    (fun r hr ↦ hgeo r ⟨hr.1, hr.2.trans_le hsb⟩)
  have hscalar (r : ℝ) : 0 ≤ F.S.scalar (0 - r ^ 2) (alpha r) := by
    obtain ⟨C, hC⟩ := hF.globalScalarBound
    exact (hC (0 - r ^ 2) (by
      simpa only [ancientTimeInterval_carrier, _root_.Set.mem_Iic, zero_sub] using
        neg_nonpos.mpr (sq_nonneg r)) (alpha r)).1
  have hlag (r : ℝ) : 0 ≤ lRegularizedLagrangian F.S 0 alpha r := by
    change 0 ≤ (1 / 2 : ℝ) * lRegularizedSpeedSq F.S 0 alpha r +
      2 * r ^ 2 * F.S.scalar (0 - r ^ 2) (alpha r)
    exact add_nonneg (mul_nonneg (by norm_num) (lRegularizedSpeedSq_nonneg F.S 0 alpha r))
      (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg r)) (hscalar r))
  have hcont : ContinuousOn (lRegularizedLagrangian F.S 0 alpha) (_root_.Set.Icc 0 b) := by
    apply (lRegularizedLagrangian_continuousOn_carrier F.S F.isSolution alpha halpha).comp
      (continuous_const.prodMk continuous_id).continuousOn
    intro r _hr
    change (0 : ℝ) - r ^ 2 ∈ ancientTimeInterval.carrier
    simpa only [ancientTimeInterval_carrier, _root_.Set.mem_Iic, zero_sub] using
      neg_nonpos.mpr (sq_nonneg r)
  have hint : IntervalIntegrable (lRegularizedLagrangian F.S 0 alpha) _root_.MeasureTheory.MeasureSpace.volume 0 b :=
    hcont.intervalIntegrable_of_Icc (hs.le.trans hsb)
  have haction : lRegularizedAction F.S 0 alpha 0 s ≤
      lRegularizedAction F.S 0 alpha 0 b :=
    intervalIntegral.integral_mono_interval le_rfl hs.le hsb
      (Filter.Eventually.of_forall hlag) hint
  have hkin := (le_div_iff₀ hs).mp hspeed
  have hnonneg := lRegularizedSpeedSq_nonneg F.S 0 alpha s
  apply (le_div_iff₀ hc).mpr
  calc
    lRegularizedSpeedSq F.S 0 alpha s * c ≤
        lRegularizedSpeedSq F.S 0 alpha s * s := mul_le_mul_of_nonneg_left hcs hnonneg
    _ ≤ 6 * lRegularizedAction F.S 0 alpha 0 s := hkin
    _ ≤ 6 * lRegularizedAction F.S 0 alpha 0 b :=
      mul_le_mul_of_nonneg_left haction (by norm_num)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.lRegularizedSpeedSq_le_six_action_div_on_tail_of_ancient then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.lRegularizedSpeedSq_le_six_action_div_on_tail_of_ancient"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.lRegularizedSpeedSq_le_six_action_div_on_tail_of_ancient ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.lRegularizedSpeedSq_le_six_action_div_on_tail_of_ancient

theorem lRegularizedSpeedSq_le_twenty_four_mul_redLength_on_half_tail_of_ancient
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
    (alpha : ℝ → F.M) (halpha : ContMDiff 𝓘(ℝ, ℝ) I 1 alpha)
    (p : F.M) {tau s : ℝ} (htau : 0 < tau)
    (hs : s ∈ _root_.Set.Icc (Real.sqrt tau / 2) (Real.sqrt tau))
    (hgeo : IsLRegularizedGeodesicOn F.S 0 alpha (_root_.Set.Ioo 0 (Real.sqrt tau)))
    (hcost : lRegularizedAction F.S 0 alpha 0 (Real.sqrt tau) =
      lCost F.S 0 p (alpha (Real.sqrt tau)) tau) :
    lRegularizedSpeedSq F.S 0 alpha s ≤
      24 * redLength F.S 0 p (alpha (Real.sqrt tau)) tau := by
  have hb : 0 < Real.sqrt tau := Real.sqrt_pos.mpr htau
  have h := lRegularizedSpeedSq_le_six_action_div_on_tail_of_ancient F hF alpha halpha
    (half_pos hb) hs.1 hs.2 hgeo
  rw [hcost] at h
  convert h using 1
  unfold redLength
  field_simp
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.lRegularizedSpeedSq_le_twenty_four_mul_redLength_on_half_tail_of_ancient then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.lRegularizedSpeedSq_le_twenty_four_mul_redLength_on_half_tail_of_ancient"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.lRegularizedSpeedSq_le_twenty_four_mul_redLength_on_half_tail_of_ancient ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.lRegularizedSpeedSq_le_twenty_four_mul_redLength_on_half_tail_of_ancient

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
