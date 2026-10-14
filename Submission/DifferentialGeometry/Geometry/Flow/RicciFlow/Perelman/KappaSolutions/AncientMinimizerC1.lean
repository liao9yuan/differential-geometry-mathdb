import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.TerminalAttainment
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Minimizer.CarrierC1Regularity
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Metric.CarrierRegularity
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Scalar.CarrierRegularity
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
local instance ancientMinimizerC1Topology : TopologicalSpace F.M := F.topology

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientMinimizerC1Topology then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientMinimizerC1Topology"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientMinimizerC1Topology ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientMinimizerC1Topology
local instance ancientMinimizerC1Charted : ChartedSpace H F.M := F.charted

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientMinimizerC1Charted then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientMinimizerC1Charted"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientMinimizerC1Charted ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientMinimizerC1Charted
local instance ancientMinimizerC1Smooth : IsManifold I ∞ F.M := F.smooth

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientMinimizerC1Smooth then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientMinimizerC1Smooth"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientMinimizerC1Smooth ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientMinimizerC1Smooth
local instance ancientMinimizerC1T2 : T2Space F.M := F.t2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientMinimizerC1T2 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientMinimizerC1T2"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientMinimizerC1T2 ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientMinimizerC1T2
local instance ancientMinimizerC1Sigma : SigmaCompactSpace F.M := F.sigmaCompact

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientMinimizerC1Sigma then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientMinimizerC1Sigma"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientMinimizerC1Sigma ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientMinimizerC1Sigma

theorem exists_lRegularizedMin_contMDiffOn_one_of_ancient
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
    (x y : F.M) {tau : ℝ} (htau : 0 < tau) :
    ∃ (gamma : ℝ → F.M) (m : ℕ) (t : Fin (m + 1) → ℝ) (p : Fin m → F.M)
      (u : (i : Fin m) → timeH1 E (partitionIntervalLength t i)),
      ContMDiffOn 𝓘(ℝ, ℝ) I 1 gamma (_root_.Set.Icc 0 (Real.sqrt tau)) ∧
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
  let _ : NeZero (Module.finrank ℝ E) := by
    obtain ⟨t, ht, z, hz⟩ := hF.notFlat
    exact ⟨Tensor0SBundle.finrank_ne_zero_of_normSq0S_ne_zero
      (F.S.base.metric t) z (by norm_num : 0 < 4) _ hz⟩
  let : TopologicalSpace.MetrizableSpace F.M := Manifold.metrizableSpace I F.M
  let : PseudoMetricSpace F.M := TopologicalSpace.pseudoMetrizableSpacePseudoMetric F.M
  obtain ⟨gamma, m, t, p, u, hgamma, hga, hgb, ht, ht0, htl, hsrc, hrep,
    hint, heq, hmin⟩ := exists_lRegularizedMin_of_ancient F hF x y htau
  have hmin' : ∀ delta : ℝ → F.M, ContMDiff 𝓘(ℝ, ℝ) I 1 delta →
      delta 0 = gamma 0 → delta (Real.sqrt tau) = gamma (Real.sqrt tau) →
      lRegularizedAction F.S 0 gamma 0 (Real.sqrt tau) ≤
        lRegularizedAction F.S 0 delta 0 (Real.sqrt tau) := by
    intro delta hd hda hdb
    exact hmin delta hd (hda.trans hga) (hdb.trans hgb)
  have hc1 : ContMDiffOn 𝓘(ℝ, ℝ) I 1 gamma (_root_.Set.Icc 0 (Real.sqrt tau)) := by
    apply lMinCurve_c1_of_spatial_derivatives F.S F.isSolution 0 0 (Real.sqrt tau)
      (Real.sqrt_pos.mpr htau) t ht ht0 htl p gamma hgamma u hsrc hrep
      (_root_.Set.Iic 0) (by simpa only [ancientTimeInterval_carrier] using (Subset.rfl : _root_.Set.Iic (0 : ℝ) ⊆ _root_.Set.Iic 0))
      ?_ ?_ ?_ ?_ hmin'
    · intro r hr
      simpa only [zero_sub, _root_.Set.mem_Iic] using neg_nonpos.mpr (sq_nonneg r)
    · intro r hr
      rw [ancientTimeInterval_regular, _root_.Set.mem_Iio, zero_sub]
      exact neg_neg_of_pos (sq_pos_of_pos hr.1)
    · intro q
      exact (solution_chartGramOp_spatial_fderiv_continuousOn_carrier F.S F.isSolution
        ancientTimeInterval_carrier ancientTimeInterval_regular q).mono
        (fun _ hz => ⟨hz.1, interior_subset hz.2⟩)
    · intro q
      exact (solution_chartScalar_fderiv_continuousOn_carrier F.S F.isSolution
        ancientTimeInterval_carrier ancientTimeInterval_regular q).mono
        (fun _ hz => ⟨hz.1, interior_subset hz.2⟩)
  exact ⟨gamma, m, t, p, u, hc1, hgamma, hga, hgb, ht, ht0, htl,
    hsrc, hrep, hint, heq, hmin⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_lRegularizedMin_contMDiffOn_one_of_ancient then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_lRegularizedMin_contMDiffOn_one_of_ancient"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_lRegularizedMin_contMDiffOn_one_of_ancient ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_lRegularizedMin_contMDiffOn_one_of_ancient

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
