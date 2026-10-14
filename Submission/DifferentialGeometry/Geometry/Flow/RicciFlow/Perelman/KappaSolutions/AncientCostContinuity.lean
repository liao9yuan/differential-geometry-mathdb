import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.TerminalEnergy
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Compactness.CarrierLowerSemicontinuity
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Compactness.CarrierDensity
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Cost.Continuity.CarrierEndpoint
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Minimizer.Existence
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientPullback
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Naturality
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Submission.DifferentialGeometry.Topology.Manifold.ModelWithCorners
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.ReducedLength.Defs

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open _root_.Filter _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Set
open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open scoped _root_.ContDiff _root_.Manifold _root_.Submission.Manifold _root_.Topology _root_.Submission.Topology

universe u uE uH
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)
local instance endpointTopology : TopologicalSpace F.M := F.topology

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.endpointTopology then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.endpointTopology"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.endpointTopology ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.endpointTopology
local instance endpointCharted : ChartedSpace H F.M := F.charted

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.endpointCharted then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.endpointCharted"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.endpointCharted ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.endpointCharted
local instance endpointSmooth : IsManifold I ∞ F.M := F.smooth

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.endpointSmooth then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.endpointSmooth"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.endpointSmooth ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.endpointSmooth
local instance endpointT2 : T2Space F.M := F.t2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.endpointT2 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.endpointT2"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.endpointT2 ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.endpointT2
local instance endpointSigma : SigmaCompactSpace F.M := F.sigmaCompact

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.endpointSigma then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.endpointSigma"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.endpointSigma ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.endpointSigma

private theorem lowerSemicontinuous_lCost_of_ancient
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
    (x : F.M) {tau : ℝ} (htau : 0 < tau) :
    LowerSemicontinuous (fun y : F.M => lCost F.S 0 x y tau) := by
  classical
  let : TopologicalSpace.MetrizableSpace F.M := Manifold.metrizableSpace I F.M
  let : PseudoMetricSpace F.M := TopologicalSpace.pseudoMetrizableSpacePseudoMetric F.M
  let : ConnectedSpace F.M := hF.connected
  have hcarrier : ∀ s ∈ _root_.Set.Icc 0 (Real.sqrt tau), 0 - s ^ 2 ∈ ancientTimeInterval.carrier := by
    intro s hs
    simpa only [ancientTimeInterval_carrier, _root_.Set.mem_Iic, zero_sub] using neg_nonpos.mpr (sq_nonneg s)
  have hscalar : ∀ s ∈ _root_.Set.Icc 0 (Real.sqrt tau), ∀ z : F.M, 0 ≤ F.S.scalar (0 - s ^ 2) z := by
    obtain ⟨C, hC⟩ := hF.globalScalarBound
    exact fun s hs z => (hC _ (hcarrier s hs) z).1
  have hnonneg (alpha : ℝ → F.M) : 0 ≤ lRegularizedAction F.S 0 alpha 0 (Real.sqrt tau) := by
    apply intervalIntegral.integral_nonneg (Real.sqrt_nonneg tau)
    intro s hs
    change 0 ≤ (1 / 2 : ℝ) * (F.S.base.metric (0 - s ^ 2)).inner (alpha s)
      (lVelocity (I := I) alpha s) (lVelocity (I := I) alpha s) +
      2 * s ^ 2 * F.S.scalar (0 - s ^ 2) (alpha s)
    exact add_nonneg (mul_nonneg (by norm_num) (lRegularizedSpeedSq_nonneg F.S 0 alpha s))
      (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg s)) (hscalar s hs (alpha s)))
  intro y
  change LowerSemicontinuousAt (fun y : F.M => lCost F.S 0 x y tau) y
  rw [lowerSemicontinuousAt_iff]
  intro A hA
  by_contra hev
  have hfreq : ∃ᶠ z in nhds y, lCost F.S 0 x z tau ≤ A := by
    simpa only [not_lt] using (not_eventually.mp hev)
  have hycl : y ∈ closure {z | lCost F.S 0 x z tau ≤ A} :=
    mem_closure_iff_frequently.mpr hfreq
  obtain ⟨q, hqmem, hq⟩ := mem_closure_iff_seq_limit.mp hycl
  obtain ⟨C, hAC, hCy⟩ := exists_between hA
  have hpaths (n : ℕ) : ∃ alpha : ℝ → F.M, ContMDiff 𝓘(ℝ, ℝ) I 1 alpha ∧
      alpha 0 = x ∧ alpha (Real.sqrt tau) = q n ∧
      lRegularizedAction F.S 0 alpha 0 (Real.sqrt tau) < C :=
    exists_lRegularizedAction_lt_of_lCost_lt_of_preconnected F.S 0 x (q n) tau htau C
      ((hqmem n).trans_lt hAC)
  choose alpha halpha hstart hend hact using hpaths
  obtain ⟨K, phi, g, hK, hphi, hKalpha, hconv, _hKg, hga, hgb⟩ :=
    exists_uniform_subseq_of_ancient_action_le_of_tendsto_endpoint F hF alpha halpha x y
      (Real.sqrt_nonneg tau) hstart (by simpa only [hend] using hq)
      (fun n => (hact n).le)
  let gamma : ℝ → F.M := _root_.Set.IccExtend (Real.sqrt_nonneg tau) g
  have heq (s : _root_.Set.Icc 0 (Real.sqrt tau)) : gamma s.1 = g s :=
    _root_.Set.IccExtend_of_mem (Real.sqrt_nonneg tau) g s.2
  have hga' : gamma 0 = x := (heq ⟨0, le_rfl, Real.sqrt_nonneg tau⟩).trans hga
  have hgb' : gamma (Real.sqrt tau) = y :=
    (heq ⟨Real.sqrt tau, Real.sqrt_nonneg tau, le_rfl⟩).trans hgb
  have hconv' : TendstoUniformly
      (fun n (s : _root_.Set.Icc 0 (Real.sqrt tau)) => alpha (phi n) s.1)
      (fun s => gamma s.1) atTop := by
    convert hconv using 1
    funext s
    exact heq s
  obtain ⟨m, t, p, u, htmono, ht0, htlast, hsrc, hrep, _hint, chi, _hchi, hlsc⟩ :=
    exists_chartH1_representation_of_tendstoUniformly_of_lRegularizedAction_le_on_carrier
      F.S F.isSolution.smoothMetric ⟨F.isSolution.scalarCont⟩
      0 0 (Real.sqrt tau) C (Real.sqrt_nonneg tau) (fun n => alpha (phi n))
      (fun n => (halpha (phi n)).contMDiffOn) K hK
      (fun n s hs => hKalpha n ⟨s, hs, rfl⟩) (fun n => (hact (phi n)).le)
      gamma hconv' hcarrier
  have hbounded : (_root_.Filter.atTop : Filter ℕ).IsBoundedUnder (· ≥ ·)
      (fun n => lRegularizedAction F.S 0 (alpha (phi (chi n))) 0 (Real.sqrt tau)) :=
    _root_.Filter.isBoundedUnder_of_eventually_ge (Eventually.of_forall fun n => hnonneg (alpha (phi (chi n))))
  have hlimle : _root_.Filter.liminf
      (fun n => lRegularizedAction F.S 0 (alpha (phi (chi n))) 0 (Real.sqrt tau)) _root_.Filter.atTop ≤ C :=
    _root_.Filter.liminf_le_of_frequently_le (Frequently.of_forall fun n => (hact (phi (chi n))).le)
      hbounded
  have hlower : lCost F.S 0 x y tau ≤ lRegularizedAction F.S 0 gamma 0 (Real.sqrt tau) := by
    rw [lCost_eq_regularity F.S 0 x y tau htau.le, ← hga', ← hgb']
    exact lRegularizedCostC1_le_action_of_chartH1_of_carrier F.S
      F.isSolution.smoothMetric ⟨F.isSolution.scalarCont⟩ 0 0 (Real.sqrt tau)
      t htmono ht0 htlast p gamma u hsrc hrep hcarrier hscalar
  exact (not_le_of_gt hCy) (hlower.trans (hlsc.trans hlimle))

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.lowerSemicontinuous_lCost_of_ancient
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.lowerSemicontinuous_lCost_of_ancient target :: scope.openDecls } }

private theorem continuous_lCost_of_ancient_of_innerProductSpace
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
    (x : F.M) {tau : ℝ} (htau : 0 < tau) :
    Continuous (fun y : F.M => lCost F.S 0 x y tau) := by
  let : TopologicalSpace.MetrizableSpace F.M := Manifold.metrizableSpace I F.M
  let : PseudoMetricSpace F.M := TopologicalSpace.pseudoMetrizableSpacePseudoMetric F.M
  let : ConnectedSpace F.M := hF.connected
  refine continuous_iff_lower_upperSemicontinuous.mpr
    ⟨lowerSemicontinuous_lCost_of_ancient F hF x htau, ?_⟩
  apply upperSemicontinuous_lCost_of_carrier_of_scalar_nonneg F.S F.isSolution 0 tau htau x
  · intro s hs
    simpa only [ancientTimeInterval_carrier, _root_.Set.mem_Iic, zero_sub] using neg_nonpos.mpr (sq_nonneg s)
  · obtain ⟨C, hC⟩ := hF.globalScalarBound
    intro s hs z
    exact (hC (0 - s ^ 2) (by
      simpa only [ancientTimeInterval_carrier, _root_.Set.mem_Iic, zero_sub] using neg_nonpos.mpr (sq_nonneg s)) z).1

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.continuous_lCost_of_ancient_of_innerProductSpace
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.continuous_lCost_of_ancient_of_innerProductSpace target :: scope.openDecls } }

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)

local instance ancientEndpointContinuityTopology : TopologicalSpace F.M := F.topology

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientEndpointContinuityTopology then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientEndpointContinuityTopology"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientEndpointContinuityTopology ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientEndpointContinuityTopology
local instance ancientEndpointContinuityCharted : ChartedSpace H F.M := F.charted

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientEndpointContinuityCharted then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientEndpointContinuityCharted"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientEndpointContinuityCharted ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientEndpointContinuityCharted
local instance ancientEndpointContinuitySmooth : IsManifold I ∞ F.M := F.smooth

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientEndpointContinuitySmooth then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientEndpointContinuitySmooth"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientEndpointContinuitySmooth ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientEndpointContinuitySmooth
local instance ancientEndpointContinuityT2 : T2Space F.M := F.t2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientEndpointContinuityT2 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientEndpointContinuityT2"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientEndpointContinuityT2 ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientEndpointContinuityT2
local instance ancientEndpointContinuitySigma : SigmaCompactSpace F.M := F.sigmaCompact

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientEndpointContinuitySigma then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientEndpointContinuitySigma"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientEndpointContinuitySigma ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientEndpointContinuitySigma

theorem continuous_lCost_of_ancient
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
    (x : F.M) {tau : ℝ} (htau : 0 < tau) :
    Continuous (fun y : F.M => lCost F.S 0 x y tau) := by
  let e : E ≃L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) := toEuclidean
  let J := I.transContinuousLinearEquiv e
  let Phi : F.M ≃ₘ⟮I, J⟯ F.M := ContinuousLinearEquiv.toTransContinuousLinearEquiv I F.M e
  let G := F.pullback Phi.symm
  have hG : IsAncientKappaSolution kappa G := F.pullback_isAncientKappaSolution Phi.symm hF
  have hcont := continuous_lCost_of_ancient_of_innerProductSpace G hG x htau
  change Continuous (fun y : F.M => lCost (F.S.pullback Phi.symm) 0 x y tau) at hcont
  exact hcont.congr (fun y => lCost_pullback F.S Phi.symm 0 x y tau)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.continuous_lCost_of_ancient then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.continuous_lCost_of_ancient"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.continuous_lCost_of_ancient ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.continuous_lCost_of_ancient

theorem continuous_redLength_of_ancient
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
    (x : F.M) {tau : ℝ} (htau : 0 < tau) :
    Continuous (fun y : F.M => redLength F.S 0 x y tau) := by
  exact (continuous_lCost_of_ancient F hF x htau).div_const (2 * Real.sqrt tau)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.continuous_redLength_of_ancient then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.continuous_redLength_of_ancient"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.continuous_redLength_of_ancient ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.continuous_redLength_of_ancient

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
