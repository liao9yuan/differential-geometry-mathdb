import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientTerminalMinimizer
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Hamilton.Ancient
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientTerminalBounds
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.TensorNormFinrankNeZero
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Cost.Continuity.CarrierBaseTime

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open _root_.Bundle _root_.Submission.Bundle _root_.Set _root_.Submission.Set _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Filter _root_.Function
open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open _root_.Submission.DifferentialGeometry.Tensor0SBundle
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff


universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)

local instance ancientEndpointTopology : TopologicalSpace F.M := F.topology

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientEndpointTopology then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientEndpointTopology"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientEndpointTopology ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientEndpointTopology
local instance ancientEndpointCharted : ChartedSpace H F.M := F.charted

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientEndpointCharted then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientEndpointCharted"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientEndpointCharted ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientEndpointCharted
local instance ancientEndpointSmooth : IsManifold I ∞ F.M := F.smooth

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientEndpointSmooth then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientEndpointSmooth"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientEndpointSmooth ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientEndpointSmooth
local instance ancientEndpointC1 : IsManifold I 1 F.M := IsManifold.of_le (n := ∞) (by decide)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientEndpointC1 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientEndpointC1"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientEndpointC1 ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientEndpointC1
local instance ancientEndpointT2 : T2Space F.M := F.t2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientEndpointT2 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientEndpointT2"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientEndpointT2 ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientEndpointT2
local instance ancientEndpointSigma : SigmaCompactSpace F.M := F.sigmaCompact

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientEndpointSigma then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientEndpointSigma"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientEndpointSigma ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientEndpointSigma

theorem lRegularizedLagrangian_mul_le_three_mul_action_of_ancientKappa
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
    (alpha : ℝ → F.M) (halpha : ContMDiff 𝓘(ℝ, ℝ) I 1 alpha)
    {b : ℝ} (hb : 0 ≤ b)
    (hgeo : IsLRegularizedGeodesicOn F.S 0 alpha (_root_.Set.Ioo 0 b)) :
    b * lRegularizedLagrangian F.S 0 alpha b ≤ 3 * lRegularizedAction F.S 0 alpha 0 b := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  let _ : NeZero (Module.finrank ℝ E) := ⟨by
    obtain ⟨t, ht, x, hx⟩ := hF.notFlat
    exact finrank_ne_zero_of_normSq0S_ne_zero (F.S.base.metric t) x (by norm_num : 0 < 4)
      (F.S.base.rm04 t x) hx⟩
  have hcomplete : ∀ t ∈ ancientTimeInterval.regular,
      RiemannianMetricComplete (I := I) (F.S.base.metric t) :=
    fun t ht => ⟨hF.complete t (ancientTimeInterval.regular_subset ht)⟩
  have hR : ∀ t ∈ ancientTimeInterval.regular, ∀ x : F.M,
      metricAlgebraicCurvatureTensorAt (I := I) (F.S.base.metric t) x ∈
        algebraicCurvatureOperatorNonnegativeCone (I := I) (M := F.M) := by
    intro t ht x
    apply mem_algebraicCurvatureOperatorNonnegativeCone.mpr
    intro n c v w
    have h := hF.nonnegativeCurvatureOperator t (ancientTimeInterval.regular_subset ht) x n c v w
    simpa only [algebraicCurvatureOperatorQuadraticEval, metricAlgebraicCurvatureTensorAt,
      tensor04StandardAt, SolutionFamily.rm04, metricRm04_apply] using h
  have hregular : ∀ s ∈ _root_.Set.Ioo 0 b, _root_.Set.Iic ((0 : ℝ) - s ^ 2) ⊆ ancientTimeInterval.regular := by
    intro s hs t ht
    rw [ancientTimeInterval_regular]
    exact lt_of_le_of_lt (mem_Iic.mp ht) (by nlinarith [sq_pos_of_pos hs.1])
  have hLag := lRegularizedLagrangian_continuousOn_carrier F.S F.isSolution alpha halpha
  have hcont : ContinuousOn (lRegularizedLagrangian F.S 0 alpha) (_root_.Set.Icc 0 b) := by
    apply hLag.comp (continuous_const.prodMk continuous_id).continuousOn
    intro r hr
    change (0 : ℝ) - r ^ 2 ∈ ancientTimeInterval.carrier
    simpa only [ancientTimeInterval_carrier, _root_.Set.mem_Iic, zero_sub] using neg_nonpos.mpr (sq_nonneg r)
  exact lRegularizedLagrangian_mul_le_three_mul_action_of_ancient F.S F.isSolution hcomplete
    (ancientKappa_regularSlabBound_finrank F hF) hR 0 alpha hb hregular hgeo hcont

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.lRegularizedLagrangian_mul_le_three_mul_action_of_ancientKappa then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.lRegularizedLagrangian_mul_le_three_mul_action_of_ancientKappa"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.lRegularizedLagrangian_mul_le_three_mul_action_of_ancientKappa ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.lRegularizedLagrangian_mul_le_three_mul_action_of_ancientKappa

theorem scalar_le_three_mul_redLength_div_of_ancient
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
    (p q : F.M) {tau : ℝ} (htau : 0 < tau) :
    F.S.scalar (-tau) q ≤ 3 * redLength F.S 0 p q tau / tau := by
  obtain ⟨alpha, halpha, _hstart, hend, hgeo, hcost⟩ :=
    exists_lRegularized_minimizer_of_ancient F hF p q htau
  rw [← hend]
  have hsqrt : 0 < Real.sqrt tau := Real.sqrt_pos.mpr htau
  have henergy := lRegularizedLagrangian_mul_le_three_mul_action_of_ancientKappa F hF alpha
    halpha hsqrt.le (fun s hs => hgeo s ⟨hs.1, hs.2.le⟩)
  have hspeed := metric_inner_self_nonneg (F.S.base.metric (-tau)) (alpha (Real.sqrt tau))
    (lVelocity (I := I) alpha (Real.sqrt tau))
  rw [hcost] at henergy
  dsimp only [lRegularizedLagrangian] at henergy
  rw [Real.sq_sqrt htau.le, zero_sub] at henergy
  have hbound : 2 * Real.sqrt tau * tau * F.S.scalar (-tau) (alpha (Real.sqrt tau)) ≤
      3 * lCost F.S 0 p (alpha (Real.sqrt tau)) tau := by
    nlinarith [mul_nonneg hsqrt.le hspeed]
  unfold redLength
  apply (le_div_iff₀ htau).mpr
  rw [← mul_div_assoc]
  apply (le_div_iff₀ (mul_pos (by norm_num) hsqrt)).mpr
  nlinarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.scalar_le_three_mul_redLength_div_of_ancient then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.scalar_le_three_mul_redLength_div_of_ancient"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.scalar_le_three_mul_redLength_div_of_ancient ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.scalar_le_three_mul_redLength_div_of_ancient

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood _root_.Set _root_.Submission.Set _root_.MeasureTheory _root_.Submission.MeasureTheory
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)

private local instance tailScalarTopology : TopologicalSpace F.M := F.topology

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.tailScalarTopology
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.tailScalarTopology target :: scope.openDecls } }
private local instance tailScalarCharted : ChartedSpace H F.M := F.charted

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.tailScalarCharted
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.tailScalarCharted target :: scope.openDecls } }
private local instance tailScalarSmooth : IsManifold I ∞ F.M := F.smooth

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.tailScalarSmooth
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.tailScalarSmooth target :: scope.openDecls } }
private local instance tailScalarT2 : T2Space F.M := F.t2

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.tailScalarT2
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.tailScalarT2 target :: scope.openDecls } }
private local instance tailScalarSigma : SigmaCompactSpace F.M := F.sigmaCompact

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.tailScalarSigma
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.tailScalarSigma target :: scope.openDecls } }

theorem scalar_le_three_mul_action_div_cube_on_tail_of_ancient
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
    (alpha : ℝ → F.M) (halpha : ContMDiff 𝓘(ℝ, ℝ) I 1 alpha)
    {c s b : ℝ} (hc : 0 < c) (hcs : c ≤ s) (hsb : s ≤ b)
    (hgeo : IsLRegularizedGeodesicOn F.S 0 alpha (_root_.Set.Ioo 0 b)) :
    F.S.scalar (-(s ^ 2)) (alpha s) ≤
      3 * lRegularizedAction F.S 0 alpha 0 b / (2 * c ^ 3) := by
  have hs : 0 < s := hc.trans_le hcs
  have henergy := lRegularizedLagrangian_mul_le_three_mul_action_of_ancientKappa
    F hF alpha halpha hs.le (fun r hr => hgeo r ⟨hr.1, hr.2.trans_le hsb⟩)
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
    intro r _
    change (0 : ℝ) - r ^ 2 ∈ ancientTimeInterval.carrier
    simpa only [ancientTimeInterval_carrier, _root_.Set.mem_Iic, zero_sub] using
      neg_nonpos.mpr (sq_nonneg r)
  have hint : IntervalIntegrable (lRegularizedLagrangian F.S 0 alpha) _root_.MeasureTheory.MeasureSpace.volume 0 b :=
    hcont.intervalIntegrable_of_Icc (hs.le.trans hsb)
  have haction : lRegularizedAction F.S 0 alpha 0 s ≤
      lRegularizedAction F.S 0 alpha 0 b :=
    intervalIntegral.integral_mono_interval le_rfl hs.le hsb
      (Filter.Eventually.of_forall hlag) hint
  change s * ((1 / 2 : ℝ) * lRegularizedSpeedSq F.S 0 alpha s +
      2 * s ^ 2 * F.S.scalar (0 - s ^ 2) (alpha s)) ≤
    3 * lRegularizedAction F.S 0 alpha 0 s at henergy
  have hspeed := lRegularizedSpeedSq_nonneg F.S 0 alpha s
  have hpotential : F.S.scalar (0 - s ^ 2) (alpha s) * (2 * s ^ 3) ≤
      3 * lRegularizedAction F.S 0 alpha 0 s := by
    nlinarith [mul_nonneg hs.le hspeed]
  have hcube : c ^ 3 ≤ s ^ 3 := pow_le_pow_left₀ hc.le hcs 3
  rw [← zero_sub (s ^ 2)]
  apply (le_div_iff₀ (by positivity : 0 < 2 * c ^ 3)).mpr
  calc
    F.S.scalar (0 - s ^ 2) (alpha s) * (2 * c ^ 3) ≤
        F.S.scalar (0 - s ^ 2) (alpha s) * (2 * s ^ 3) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hcube (by norm_num)) (hscalar s)
    _ ≤ 3 * lRegularizedAction F.S 0 alpha 0 s := hpotential
    _ ≤ 3 * lRegularizedAction F.S 0 alpha 0 b :=
      mul_le_mul_of_nonneg_left haction (by norm_num)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.scalar_le_three_mul_action_div_cube_on_tail_of_ancient then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.scalar_le_three_mul_action_div_cube_on_tail_of_ancient"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.scalar_le_three_mul_action_div_cube_on_tail_of_ancient ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.scalar_le_three_mul_action_div_cube_on_tail_of_ancient

theorem scalar_le_twenty_four_mul_redLength_div_on_half_tail_of_ancient
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
    (alpha : ℝ → F.M) (halpha : ContMDiff 𝓘(ℝ, ℝ) I 1 alpha)
    (p : F.M) {tau s : ℝ} (htau : 0 < tau)
    (hs : s ∈ _root_.Set.Icc (Real.sqrt tau / 2) (Real.sqrt tau))
    (hgeo : IsLRegularizedGeodesicOn F.S 0 alpha (_root_.Set.Ioo 0 (Real.sqrt tau)))
    (hcost : lRegularizedAction F.S 0 alpha 0 (Real.sqrt tau) =
      lCost F.S 0 p (alpha (Real.sqrt tau)) tau) :
    F.S.scalar (-(s ^ 2)) (alpha s) ≤
      24 * redLength F.S 0 p (alpha (Real.sqrt tau)) tau / tau := by
  have hb : 0 < Real.sqrt tau := Real.sqrt_pos.mpr htau
  have h := scalar_le_three_mul_action_div_cube_on_tail_of_ancient F hF alpha halpha
    (half_pos hb) hs.1 hs.2 hgeo
  rw [hcost] at h
  convert h using 1
  unfold redLength
  have hden : 2 * (Real.sqrt tau / 2) ^ 3 = Real.sqrt tau * tau / 4 := by
    calc
      2 * (Real.sqrt tau / 2) ^ 3 = Real.sqrt tau * (Real.sqrt tau) ^ 2 / 4 := by ring
      _ = Real.sqrt tau * tau / 4 := by rw [Real.sq_sqrt htau.le]
  rw [hden]
  field_simp
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.scalar_le_twenty_four_mul_redLength_div_on_half_tail_of_ancient then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.scalar_le_twenty_four_mul_redLength_div_on_half_tail_of_ancient"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.scalar_le_twenty_four_mul_redLength_div_on_half_tail_of_ancient ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.scalar_le_twenty_four_mul_redLength_div_on_half_tail_of_ancient

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
