import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.TerminalMinimizingSequence
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Compactness.CarrierLowerSemicontinuity
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Compactness.CarrierDensity
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Minimizer.Existence

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
local instance terminalAttainmentTopology : TopologicalSpace F.M := F.topology

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.terminalAttainmentTopology then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.terminalAttainmentTopology"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.terminalAttainmentTopology ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.terminalAttainmentTopology
local instance terminalAttainmentCharted : ChartedSpace H F.M := F.charted

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.terminalAttainmentCharted then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.terminalAttainmentCharted"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.terminalAttainmentCharted ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.terminalAttainmentCharted
local instance terminalAttainmentSmooth : IsManifold I ∞ F.M := F.smooth

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.terminalAttainmentSmooth then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.terminalAttainmentSmooth"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.terminalAttainmentSmooth ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.terminalAttainmentSmooth
local instance terminalAttainmentT2 : T2Space F.M := F.t2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.terminalAttainmentT2 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.terminalAttainmentT2"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.terminalAttainmentT2 ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.terminalAttainmentT2
local instance terminalAttainmentSigma : SigmaCompactSpace F.M := F.sigmaCompact

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.terminalAttainmentSigma then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.terminalAttainmentSigma"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.terminalAttainmentSigma ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.terminalAttainmentSigma

theorem exists_lRegularizedMin_of_ancient
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
    (x y : F.M) {tau : ℝ} (htau : 0 < tau) :
    ∃ (gamma : ℝ → F.M) (m : ℕ) (t : Fin (m + 1) → ℝ) (p : Fin m → F.M)
      (u : (i : Fin m) → timeH1 E (partitionIntervalLength t i)),
      Continuous gamma ∧ gamma 0 = x ∧ gamma (Real.sqrt tau) = y ∧
      Monotone t ∧ t 0 = 0 ∧ t (Fin.last m) = Real.sqrt tau ∧
      (∀ i, _root_.Set.MapsTo gamma (_root_.Set.Icc (t i.castSucc) (t i.succ)) (chartAt H (p i)).source) ∧
      (∀ i, _root_.Set.EqOn (u i).toFun
        (fun r => extChartAt I (p i) (gamma (t i.castSucc + r)))
        (_root_.Set.Icc (0 : ℝ) (partitionIntervalLength t i))) ∧
      IntervalIntegrable (lRegularizedLagrangian F.S 0 gamma) _root_.MeasureTheory.MeasureSpace.volume 0 (Real.sqrt tau) ∧
      lRegularizedAction F.S 0 gamma 0 (Real.sqrt tau) = lCost F.S 0 x y tau ∧
      ∀ delta : ℝ → F.M, ContMDiff 𝓘(ℝ, ℝ) I 1 delta →
        delta 0 = x → delta (Real.sqrt tau) = y →
        lRegularizedAction F.S 0 gamma 0 (Real.sqrt tau) ≤
          lRegularizedAction F.S 0 delta 0 (Real.sqrt tau) := by
  let : TopologicalSpace.MetrizableSpace F.M := Manifold.metrizableSpace I F.M
  let : PseudoMetricSpace F.M := TopologicalSpace.pseudoMetrizableSpacePseudoMetric F.M
  obtain ⟨beta, gamma, K, hbeta, hstart, hend, hanti, hlim, hgamma, hga, hgb,
    hK, hKbeta, _hKgamma, hconv⟩ :=
    exists_tendstoUniformly_minimizing_sequence_of_ancient F hF x y htau
  have hcarrier : ∀ s ∈ _root_.Set.Icc 0 (Real.sqrt tau), 0 - s ^ 2 ∈ ancientTimeInterval.carrier := by
    intro s hs
    simpa only [ancientTimeInterval_carrier, _root_.Set.mem_Iic, zero_sub] using neg_nonpos.mpr (sq_nonneg s)
  have hscalar : ∀ s ∈ _root_.Set.Icc 0 (Real.sqrt tau), ∀ z : F.M, 0 ≤ F.S.scalar (0 - s ^ 2) z := by
    obtain ⟨C, hC⟩ := hF.globalScalarBound
    exact fun s hs z => (hC _ (hcarrier s hs) z).1
  have hbound (n : ℕ) : lRegularizedAction F.S 0 (beta n) 0 (Real.sqrt tau) ≤
      lRegularizedAction F.S 0 (beta 0) 0 (Real.sqrt tau) := hanti (Nat.zero_le n)
  obtain ⟨m, t, p, u, htmono, ht0, htlast, hsrc, hrep, hint, chi, hchi, hlsc⟩ :=
    exists_chartH1_representation_of_tendstoUniformly_of_lRegularizedAction_le_on_carrier
      F.S F.isSolution.smoothMetric ⟨F.isSolution.scalarCont⟩
      0 0 (Real.sqrt tau) (lRegularizedAction F.S 0 (beta 0) 0 (Real.sqrt tau))
      (Real.sqrt_nonneg tau) beta (fun n => (hbeta n).contMDiffOn)
      K hK (fun n s hs => hKbeta n ⟨s, hs, rfl⟩) hbound gamma hconv hcarrier
  have hupper : lRegularizedAction F.S 0 gamma 0 (Real.sqrt tau) ≤ lCost F.S 0 x y tau := by
    have hsub := hlim.comp hchi.tendsto_atTop
    exact hlsc.trans_eq hsub.liminf_eq
  have hlower : lCost F.S 0 x y tau ≤ lRegularizedAction F.S 0 gamma 0 (Real.sqrt tau) := by
    rw [lCost_eq_regularity F.S 0 x y tau htau.le, ← hga, ← hgb]
    exact lRegularizedCostC1_le_action_of_chartH1_of_carrier F.S
      F.isSolution.smoothMetric ⟨F.isSolution.scalarCont⟩ 0 0 (Real.sqrt tau)
      t htmono ht0 htlast p gamma u hsrc hrep hcarrier hscalar
  have heq := le_antisymm hupper hlower
  refine ⟨gamma, m, t, p, u, hgamma, hga, hgb, htmono, ht0, htlast,
    hsrc, hrep, hint, heq, ?_⟩
  intro delta hdelta hda hdb
  rw [heq, lCost_eq_regularity F.S 0 x y tau htau.le]
  apply lRegularizedCostC1_le_bdd F.S 0 0 (Real.sqrt tau) x y _ delta hdelta hda hdb
  refine ⟨0, ?_⟩
  rintro r ⟨alpha, _, _, _, rfl⟩
  apply intervalIntegral.integral_nonneg (Real.sqrt_nonneg tau)
  intro s hs
  change 0 ≤ (1 / 2 : ℝ) * (F.S.base.metric (0 - s ^ 2)).inner (alpha s)
    (lVelocity (I := I) alpha s) (lVelocity (I := I) alpha s) +
    2 * s ^ 2 * F.S.scalar (0 - s ^ 2) (alpha s)
  exact add_nonneg (mul_nonneg (by norm_num) (lRegularizedSpeedSq_nonneg F.S 0 alpha s))
    (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg s)) (hscalar s hs (alpha s)))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_lRegularizedMin_of_ancient then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_lRegularizedMin_of_ancient"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_lRegularizedMin_of_ancient ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_lRegularizedMin_of_ancient

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
