import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.ReducedCostTwoPoint
import Submission.DifferentialGeometry.Analysis.Integration.Measure.Riemannian.GaussianTail

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open _root_.Bundle _root_.Submission.Bundle _root_.Filter _root_.Set _root_.Submission.Set _root_.MeasureTheory _root_.Submission.MeasureTheory
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian.BonnetMyers
open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open _root_.Submission.DifferentialGeometry.Analysis.Measure
open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open scoped _root_.ContDiff _root_.ENNReal _root_.Topology _root_.Submission.Topology

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)

private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.instTopologicalSpaceM : TopologicalSpace F.M := F.topology

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.instTopologicalSpaceM
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.instTopologicalSpaceM target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.instChartedSpaceM : ChartedSpace H F.M := F.charted

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.instChartedSpaceM
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.instChartedSpaceM target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.instIsManifoldRealSomeENatTopM : IsManifold I ∞ F.M := F.smooth

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.instIsManifoldRealSomeENatTopM
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.instIsManifoldRealSomeENatTopM target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.instT2SpaceM : T2Space F.M := F.t2

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.instT2SpaceM
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.instT2SpaceM target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.instSigmaCompactSpaceM : SigmaCompactSpace F.M := F.sigmaCompact

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.instSigmaCompactSpaceM
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.instSigmaCompactSpaceM target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.instMeasurableSpaceM : MeasurableSpace F.M := borel F.M

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.instMeasurableSpaceM
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.instMeasurableSpaceM target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.instBorelSpaceM : BorelSpace F.M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.instBorelSpaceM
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.instBorelSpaceM target :: scope.openDecls } }

theorem ancient_redLength_ge_rescaled_distance_sq
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
    (p q x : F.M) {tau A : ℝ}
    (htau : 0 < tau) (hbase : redLength F.S 0 p q tau ≤ A) :
    let g := scaleMetric tau⁻¹ (inv_pos.mpr htau) (F.S.base.metric (-tau))
    (576 * ((Module.finrank ℝ E : ℝ) + 1) ^ 2)⁻¹ * (riemannianEDistOf g q x).toReal ^ 2 - 1 - A ≤
      redLength F.S 0 p x tau := by
  have h := ancient_reducedCost_two_point_between F hF p q x htau
  simp only [one_div] at h
  change (576 * ((Module.finrank ℝ E : ℝ) + 1) ^ 2)⁻¹ *
    (riemannianEDistOf (I := I) (F.S.base.metric (-tau)) q x).toReal ^ 2 / tau - 1 -
    redLength F.S 0 p q tau ≤ redLength F.S 0 p x tau at h
  dsimp only
  rw [edistOf_scale, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (Real.sqrt_nonneg _), Real.sqrt_inv, mul_pow, inv_pow,
    Real.sq_sqrt htau.le]
  have heq : (576 * ((Module.finrank ℝ E : ℝ) + 1) ^ 2)⁻¹ *
      (tau⁻¹ * (riemannianEDistOf (F.S.base.metric (-tau)) q x).toReal ^ 2) =
      (576 * ((Module.finrank ℝ E : ℝ) + 1) ^ 2)⁻¹ * (riemannianEDistOf (F.S.base.metric (-tau)) q x).toReal ^ 2 / tau := by
    ring
  rw [heq]
  linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancient_redLength_ge_rescaled_distance_sq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancient_redLength_ge_rescaled_distance_sq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancient_redLength_ge_rescaled_distance_sq ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancient_redLength_ge_rescaled_distance_sq

private theorem rescaled_ricci_nonnegative
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
    {tau : ℝ} (htau : 0 < tau) :
    RicciBoundedBelow (I := I)
      (scaleMetric tau⁻¹ (inv_pos.mpr htau) (F.S.base.metric (-tau))) 0 := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  intro x v
  rw [_root_.MulZeroClass.zero_mul, ← metricRicciAt_apply_eq_ricciTensor]
  apply metricRicciAt_nonnegative_of_curvatureOperator_nonnegative
  rw [metricAlgebraicCurvatureTensorAt_scaleMetric]
  apply algebraicCurvatureOperatorNonnegativeCone.smul_mem ?_ (inv_pos.mpr htau).le
  apply (metricAlgebraicCurvatureTensorAt_mem_curvatureOperatorNonnegativeCone_iff
    (F.S.base.metric (-tau)) x).mpr
  intro n c a b
  simpa only [SolutionFamily.rm04, metricRm04StandardAt_apply, metricRm04_apply] using
    hF.nonnegativeCurvatureOperator (-tau) (neg_nonpos.mpr htau.le) x n c a b

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.rescaled_ricci_nonnegative
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.rescaled_ricci_nonnegative target :: scope.openDecls } }

theorem ancient_lintegral_exp_neg_redLength_tail_le
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
    (p q : F.M) {tau A : ℝ}
    (htau : 0 < tau) (hbase : redLength F.S 0 p q tau ≤ A) (N : ℕ) :
    let g := scaleMetric tau⁻¹ (inv_pos.mpr htau) (F.S.base.metric (-tau))
    ∫⁻ x in {x : F.M | (N : ℝ) ≤ (riemannianEDistOf g q x).toReal},
        ENNReal.ofReal (Real.exp (-redLength F.S 0 p x tau)) ∂riemannianVolumeMeasure (I := I) (M := F.M) g ≤
      ENNReal.ofReal (Real.exp (1 + A)) *
        (((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))).toSphere _root_.Set.univ) *
          ENNReal.ofReal ((Module.finrank ℝ E : ℝ)⁻¹)) * gaussianTail (Module.finrank ℝ E) (576 * ((Module.finrank ℝ E : ℝ) + 1) ^ 2)⁻¹ N := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  let _ : NeZero (Module.finrank ℝ E) := ⟨by
    obtain ⟨t, ht, x, hx⟩ := hF.notFlat
    exact Tensor0SBundle.finrank_ne_zero_of_normSq0S_ne_zero
      (F.S.base.metric t) x (by norm_num : 0 < 4) (F.S.base.rm04 t x) hx⟩
  let _ : ConnectedSpace F.M := hF.connected
  let g := scaleMetric tau⁻¹ (inv_pos.mpr htau) (F.S.base.metric (-tau))
  have hc : RiemannianMetricComplete (I := I) (F.S.base.metric (-tau)) :=
    ⟨hF.complete (-tau) (neg_nonpos.mpr htau.le)⟩
  have hcomplete : RiemannianMetricComplete (I := I) g :=
    hc.of_lower (inv_pos.mpr htau) (fun _ _ => le_rfl)
  have hchi : 0 < (576 * ((Module.finrank ℝ E : ℝ) + 1) ^ 2)⁻¹ := by positivity
  have hg := lintegral_gaussian_riemannianEDistOf_le g hcomplete q hchi
    (rescaled_ricci_nonnegative F hF htau) N
  calc
    _ ≤ ∫⁻ x in {x : F.M | (N : ℝ) ≤ (riemannianEDistOf g q x).toReal},
        ENNReal.ofReal (Real.exp (1 + A)) * ENNReal.ofReal
          (Real.exp (-(576 * ((Module.finrank ℝ E : ℝ) + 1) ^ 2)⁻¹ * (riemannianEDistOf g q x).toReal ^ 2))
          ∂riemannianVolumeMeasure (I := I) (M := F.M) g := by
      apply _root_.MeasureTheory.lintegral_mono
      intro x
      dsimp only
      rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
      apply ENNReal.ofReal_le_ofReal
      apply Real.exp_le_exp.mpr
      have h := ancient_redLength_ge_rescaled_distance_sq F hF p q x htau hbase
      change (576 * ((Module.finrank ℝ E : ℝ) + 1) ^ 2)⁻¹ * (riemannianEDistOf g q x).toReal ^ 2 - 1 - A ≤ _ at h
      linarith
    _ = ENNReal.ofReal (Real.exp (1 + A)) *
        ∫⁻ x in {x : F.M | (N : ℝ) ≤ (riemannianEDistOf g q x).toReal},
          ENNReal.ofReal (Real.exp (-(576 * ((Module.finrank ℝ E : ℝ) + 1) ^ 2)⁻¹ *
            (riemannianEDistOf g q x).toReal ^ 2)) ∂riemannianVolumeMeasure (I := I) (M := F.M) g :=
      _root_.MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ _ := by
      simpa only [mul_assoc, one_div] using mul_le_mul_of_nonneg_left hg
        (bot_le : (0 : ℝ≥0∞) ≤ ENNReal.ofReal (Real.exp (1 + A)))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancient_lintegral_exp_neg_redLength_tail_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancient_lintegral_exp_neg_redLength_tail_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancient_lintegral_exp_neg_redLength_tail_le ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancient_lintegral_exp_neg_redLength_tail_le

theorem ancient_exp_neg_redLength_uniform_tightness
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
    (A : ℝ) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ (p q : F.M) (tau : ℝ) (htau : 0 < tau),
      redLength F.S 0 p q tau ≤ A →
      let g := scaleMetric tau⁻¹ (inv_pos.mpr htau) (F.S.base.metric (-tau))
      ∫⁻ x in {x : F.M | (N : ℝ) ≤ (riemannianEDistOf g q x).toReal},
          ENNReal.ofReal (Real.exp (-redLength F.S 0 p x tau))
          ∂riemannianVolumeMeasure (I := I) (M := F.M) g ≤ ε := by
  let C : ℝ≥0∞ := ENNReal.ofReal (Real.exp (1 + A)) *
    (((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))).toSphere _root_.Set.univ) *
      ENNReal.ofReal ((Module.finrank ℝ E : ℝ)⁻¹))
  have hC : C ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (ENNReal.mul_ne_top (_root_.MeasureTheory.measure_ne_top volume.toSphere _root_.Set.univ) ENNReal.ofReal_ne_top)
  have htail : _root_.Filter.Tendsto (fun N => C * gaussianTail (Module.finrank ℝ E) (576 * ((Module.finrank ℝ E : ℝ) + 1) ^ 2)⁻¹ N) _root_.Filter.atTop (𝓝 0) := by
    simpa only [_root_.MulZeroClass.mul_zero] using
      ENNReal.Tendsto.const_mul
        (tendsto_gaussianTail (Module.finrank ℝ E) (by positivity)) (Or.inr hC)
  obtain ⟨N, hN⟩ := eventually_atTop.1 (htail.eventually (gt_mem_nhds hε))
  refine ⟨N, fun p q tau htau hbase => ?_⟩
  exact (ancient_lintegral_exp_neg_redLength_tail_le F hF p q htau hbase N).trans
    (hN N le_rfl).le

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancient_exp_neg_redLength_uniform_tightness then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancient_exp_neg_redLength_uniform_tightness"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancient_exp_neg_redLength_uniform_tightness ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancient_exp_neg_redLength_uniform_tightness

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
