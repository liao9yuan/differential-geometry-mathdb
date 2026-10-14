import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientMinimizerC1
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Minimizer.EulerLagrangeRegularity
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Geodesic.Congruence
import Submission.DifferentialGeometry.Topology.Manifold.CurveIntervalExtension

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
local instance ancientMinimizerInteriorTopology : TopologicalSpace F.M := F.topology

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientMinimizerInteriorTopology then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientMinimizerInteriorTopology"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientMinimizerInteriorTopology ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientMinimizerInteriorTopology
local instance ancientMinimizerInteriorCharted : ChartedSpace H F.M := F.charted

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientMinimizerInteriorCharted then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientMinimizerInteriorCharted"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientMinimizerInteriorCharted ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientMinimizerInteriorCharted
local instance ancientMinimizerInteriorSmooth : IsManifold I ∞ F.M := F.smooth

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientMinimizerInteriorSmooth then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientMinimizerInteriorSmooth"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientMinimizerInteriorSmooth ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientMinimizerInteriorSmooth
local instance ancientMinimizerInteriorT2 : T2Space F.M := F.t2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientMinimizerInteriorT2 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientMinimizerInteriorT2"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientMinimizerInteriorT2 ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientMinimizerInteriorT2
local instance ancientMinimizerInteriorSigma : SigmaCompactSpace F.M := F.sigmaCompact

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientMinimizerInteriorSigma then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientMinimizerInteriorSigma"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientMinimizerInteriorSigma ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientMinimizerInteriorSigma

theorem exists_lRegularizedMin_contMDiffOn_one_regularizedGeodesicOn_of_ancient
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
    (x y : F.M) {tau : ℝ} (htau : 0 < tau) :
    ∃ (gamma : ℝ → F.M) (m : ℕ) (t : Fin (m + 1) → ℝ) (p : Fin m → F.M)
      (u : (i : Fin m) → timeH1 E (partitionIntervalLength t i)),
      ContMDiffOn 𝓘(ℝ, ℝ) I 1 gamma (_root_.Set.Icc 0 (Real.sqrt tau)) ∧
      IsLRegularizedGeodesicOn F.S 0 gamma (_root_.Set.Ioo 0 (Real.sqrt tau)) ∧
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
  obtain ⟨gamma, m, t, p, u, hc1, hgamma, hga, hgb, ht, ht0, htl, hsrc, hrep,
    hint, heq, hmin⟩ := exists_lRegularizedMin_contMDiffOn_one_of_ancient F hF x y htau
  have hmin' : ∀ delta : ℝ → F.M, ContMDiff 𝓘(ℝ, ℝ) I 1 delta →
      delta 0 = gamma 0 → delta (Real.sqrt tau) = gamma (Real.sqrt tau) →
      lRegularizedAction F.S 0 gamma 0 (Real.sqrt tau) ≤
        lRegularizedAction F.S 0 delta 0 (Real.sqrt tau) := by
    intro delta hd hda hdb
    exact hmin delta hd (hda.trans hga) (hdb.trans hgb)
  have hgeo : IsLRegularizedGeodesicOn F.S 0 gamma (_root_.Set.Ioo 0 (Real.sqrt tau)) := by
    apply lMinCurve_regularizedGeodesicOn_of_spatial_derivatives F.S F.isSolution 0 0 (Real.sqrt tau)
      t ht ht0 htl p gamma hgamma u hsrc hrep
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
  exact ⟨gamma, m, t, p, u, hc1, hgeo, hgamma, hga, hgb, ht, ht0, htl,
    hsrc, hrep, hint, heq, hmin⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_lRegularizedMin_contMDiffOn_one_regularizedGeodesicOn_of_ancient then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_lRegularizedMin_contMDiffOn_one_regularizedGeodesicOn_of_ancient"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_lRegularizedMin_contMDiffOn_one_regularizedGeodesicOn_of_ancient ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_lRegularizedMin_contMDiffOn_one_regularizedGeodesicOn_of_ancient

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
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
local instance ancientGlobalMinimizerInteriorTopology : TopologicalSpace F.M := F.topology

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientGlobalMinimizerInteriorTopology then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientGlobalMinimizerInteriorTopology"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientGlobalMinimizerInteriorTopology ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientGlobalMinimizerInteriorTopology
local instance ancientGlobalMinimizerInteriorCharted : ChartedSpace H F.M := F.charted

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientGlobalMinimizerInteriorCharted then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientGlobalMinimizerInteriorCharted"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientGlobalMinimizerInteriorCharted ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientGlobalMinimizerInteriorCharted
local instance ancientGlobalMinimizerInteriorSmooth : IsManifold I ∞ F.M := F.smooth

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientGlobalMinimizerInteriorSmooth then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientGlobalMinimizerInteriorSmooth"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientGlobalMinimizerInteriorSmooth ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientGlobalMinimizerInteriorSmooth
local instance ancientGlobalMinimizerInteriorT2 : T2Space F.M := F.t2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientGlobalMinimizerInteriorT2 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientGlobalMinimizerInteriorT2"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientGlobalMinimizerInteriorT2 ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientGlobalMinimizerInteriorT2
local instance ancientGlobalMinimizerInteriorSigma : SigmaCompactSpace F.M := F.sigmaCompact

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientGlobalMinimizerInteriorSigma then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientGlobalMinimizerInteriorSigma"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientGlobalMinimizerInteriorSigma ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientGlobalMinimizerInteriorSigma

theorem exists_lRegularizedMin_contMDiff_one_regularizedGeodesicOn_of_ancient
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
    (x y : F.M) {tau : ℝ} (htau : 0 < tau) :
    ∃ alpha : ℝ → F.M,
      ContMDiff 𝓘(ℝ, ℝ) I 1 alpha ∧
      IsLRegularizedGeodesicOn F.S 0 alpha (_root_.Set.Ioo 0 (Real.sqrt tau)) ∧ alpha 0 = x ∧ alpha (Real.sqrt tau) = y ∧
      lRegularizedAction F.S 0 alpha 0 (Real.sqrt tau) = lCost F.S 0 x y tau ∧
      ∀ delta : ℝ → F.M, ContMDiff 𝓘(ℝ, ℝ) I 1 delta →
        delta 0 = x → delta (Real.sqrt tau) = y →
        lRegularizedAction F.S 0 alpha 0 (Real.sqrt tau) ≤
          lRegularizedAction F.S 0 delta 0 (Real.sqrt tau) := by
  obtain ⟨gamma, m, t, p, u, hc1, hgeo, hgamma, hga, hgb, ht, ht0, htl,
    hsrc, hrep, hint, heq, hmin⟩ := exists_lRegularizedMin_contMDiffOn_one_regularizedGeodesicOn_of_ancient F hF x y htau
  obtain ⟨alpha, halpha, heqOn⟩ :=
    DifferentialGeometry.Topology.exists_contMDiff_extension_Icc (k := 1) hc1
  have hact : lRegularizedAction F.S 0 alpha 0 (Real.sqrt tau) =
      lRegularizedAction F.S 0 gamma 0 (Real.sqrt tau) := by
    apply lRegularizedAction_congr F.S 0
    intro s hs
    rw [_root_.Set.uIoo_of_le (Real.sqrt_nonneg tau)] at hs
    exact heqOn ⟨hs.1.le, hs.2.le⟩
  have hgeoAlpha : IsLRegularizedGeodesicOn F.S 0 alpha (_root_.Set.Ioo 0 (Real.sqrt tau)) := by
    apply hgeo.congr_of_eventuallyEq
    intro r hr
    exact heqOn.eventuallyEq_of_mem (_root_.Filter.mem_of_superset (isOpen_Ioo.mem_nhds hr) _root_.Set.Ioo_subset_Icc_self)
  refine ⟨alpha, halpha, hgeoAlpha,
    (heqOn ⟨le_rfl, Real.sqrt_nonneg tau⟩).trans hga,
    (heqOn ⟨Real.sqrt_nonneg tau, le_rfl⟩).trans hgb,
    hact.trans heq, ?_⟩
  intro delta hd hda hdb
  rw [hact]
  exact hmin delta hd hda hdb

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_lRegularizedMin_contMDiff_one_regularizedGeodesicOn_of_ancient then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_lRegularizedMin_contMDiff_one_regularizedGeodesicOn_of_ancient"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_lRegularizedMin_contMDiff_one_regularizedGeodesicOn_of_ancient ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_lRegularizedMin_contMDiff_one_regularizedGeodesicOn_of_ancient

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
