import Submission.DifferentialGeometry.Analysis.Integration.Integral.GradientCutoff
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientReducedDensityGradient
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientReducedDensityIntegrability
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientMetricMonotonicity

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section
namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
open _root_.Filter _root_.Set _root_.Submission.Set _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Bundle _root_.Submission.Bundle
open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open _root_.Submission.DifferentialGeometry.Integral.Measure _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Entropy
open _root_.Submission.DifferentialGeometry.Geometry.Operator _root_.Submission.DifferentialGeometry.Geometry.Riemannian
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.ENNReal _root_.NNReal _root_.Topology _root_.Submission.Topology
universe u uE uH
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)
attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
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

private theorem ancient_cutoff_flux_integrable_and_tendsto
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F) (p o : F.M)
    {a b : ℝ} (ha : 0 < a)
    (μ : _root_.MeasureTheory.Measure (_root_.Set.Icc a b)) [_root_.MeasureTheory.IsFiniteMeasure μ] (ψ : C(_root_.Set.Icc a b, ℝ)) :
    let f : ℝ≥0 → _root_.Set.Icc a b × F.M → ℝ := fun r z =>
      riemannianVolumeDensity (F.S.base.metric (-a)) (F.S.base.metric (-z.1)) z.2 * ψ z.1 *
        (F.S.base.metric (-z.1)).inner z.2
          (gradFun (F.S.base.metric (-z.1))
            (perelmanDensity (Module.finrank ℝ E) z.1 (fun y => redLength F.S 0 p y z.1)) z.2)
          (gradFun (F.S.base.metric (-z.1)) (fun y => Analysis.CutoffProfile.evalue
            ((r : ℝ≥0∞) * riemannianEDistOf (F.S.base.metric (-a)) o y)) z.2)
    (∀ r, _root_.MeasureTheory.Integrable (f r)
      (μ.prod (riemannianVolumeMeasure (I := I) (M := F.M) (F.S.base.metric (-a))))) ∧
      ∀ {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
        (r : ι → ℝ≥0), _root_.Filter.Tendsto r l (𝓝 0) →
          _root_.Filter.Tendsto (fun i => ∫ z, |f (r i) z|
            ∂(μ.prod (riemannianVolumeMeasure (I := I) (M := F.M) (F.S.base.metric (-a))))) l (𝓝 0) := by
  intro f
  let _ : SecondCountableTopology H := I.secondCountableTopology
  let _ : SecondCountableTopology F.M := ChartedSpace.secondCountable_of_sigmaCompact H F.M
  let g := F.S.base.metric (-a)
  let h : _root_.Set.Icc a b → SmoothRiemannianMetric I F.M := fun t => F.S.base.metric (-t)
  let ρ : _root_.Set.Icc a b × F.M → ℝ := fun z => riemannianVolumeDensity g (h z.1) z.2
  let u : _root_.Set.Icc a b → F.M → ℝ := fun t =>
    perelmanDensity (Module.finrank ℝ E) t (fun y => redLength F.S 0 p y t)
  have hm : _root_.MeasureTheory.Integrable (fun z => ρ z * u z.1 z.2)
      (μ.prod (riemannianVolumeMeasure (I := I) (M := F.M) g)) :=
    integrable_ancient_perelmanDensity F hF p ha μ g
  have hw : _root_.MeasureTheory.Integrable (fun z => |ψ z.1| * (ρ z * u z.1 z.2))
      (μ.prod (riemannianVolumeMeasure (I := I) (M := F.M) g)) :=
    hm.bdd_mul (c := ‖ψ‖) (ψ.continuous.comp continuous_fst).abs.aestronglyMeasurable
      (Eventually.of_forall fun z => by
        simpa only [Real.norm_eq_abs, abs_abs] using ψ.norm_coe_le_norm z.1)
  have hu0 (z : _root_.Set.Icc a b × F.M) : 0 ≤ u z.1 z.2 :=
    (mul_pos (prefactor_pos _ (ha.trans_le z.1.property.1)) (Real.exp_pos _)).le
  have hρ0 (z : _root_.Set.Icc a b × F.M) : 0 ≤ ρ z := (riemannianVolumeDensity_pos _ _ _).le
  have hw' : _root_.MeasureTheory.Integrable (fun z => |ρ z * ψ z.1| * u z.1 z.2)
      (μ.prod (riemannianVolumeMeasure (I := I) (M := F.M) g)) := by
    apply hw.congr
    filter_upwards [] with z
    rw [abs_mul, abs_of_nonneg (hρ0 z)]
    ring
  have hgh (t : _root_.Set.Icc a b) (x : F.M) (v : TangentSpace I x) :
      g.inner x v v ≤ (h t).inner x v v :=
    ancientModel_metric_inner_antitoneOn F hF x v
      (neg_nonpos.mpr (ha.le.trans t.property.1)) (neg_nonpos.mpr ha.le)
      (neg_le_neg t.property.1)
  obtain ⟨C, hC⟩ := exists_ancient_perelmanDensity_gradient_le_linear_distance F hF p o (b := b) ha
  have hρc : Continuous ρ :=
    (riemannianVolumeDensity_family_continuousOn g F.S.base.metric
      F.isSolution.smoothMetric.chartGramMatrix_continuousOn_carrier).comp_continuous
      ((continuous_subtype_val.comp continuous_fst).neg.prodMk continuous_snd)
      (fun z => ⟨show -(z.1 : ℝ) ≤ 0 from neg_nonpos.mpr (ha.le.trans z.1.property.1), _root_.Set.mem_univ _⟩)
  have hl : Continuous (fun z : _root_.Set.Icc a b × F.M => redLength F.S 0 p z.2 z.1) :=
    (continuousOn_redLength_space_time_of_ancient F hF p).comp_continuous
      ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
      (fun z => ⟨ha.trans_le z.1.property.1, _root_.Set.mem_univ _⟩)
  have huc : Continuous u.uncurry := by
    unfold u perelmanDensity perelmanDensityPrefactor Function.uncurry
    apply Continuous.mul
    · apply Continuous.rpow_const (continuous_const.mul (continuous_subtype_val.comp continuous_fst))
      intro z
      exact Or.inl (mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero)
        (ne_of_gt (ha.trans_le z.1.property.1)))
    · exact Real.continuous_exp.comp hl.neg
  have hhc : Continuous (fun z : _root_.Set.Icc a b × F.M => (⟨z.2, (h z.1).inner z.2⟩ :
      _root_.Bundle.TotalSpace (E →L[ℝ] E →L[ℝ] ℝ)
        (fun x => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ))) :=
    F.isSolution.smoothMetric.metricCLMSection_continuousOn_carrier.comp_continuous
      ((continuous_subtype_val.comp continuous_fst).neg.prodMk continuous_snd)
      (fun z => ⟨show -(z.1 : ℝ) ≤ 0 from neg_nonpos.mpr (ha.le.trans z.1.property.1), _root_.Set.mem_univ _⟩)
  have hv := (hρc.mul (ψ.continuous.comp continuous_fst)).measurable
  constructor
  · intro r
    exact Analysis.integrable_mul_inner_grad_distance_cutoff
      (μ.prod (riemannianVolumeMeasure (I := I) (M := F.M) g)) r g h hhc
      (Eventually.of_forall fun z => hgh z.1) huc (Eventually.of_forall hu0) hv hw' o C
      (Eventually.of_forall fun z => hC z.1 z.1.property z.2)
  · intro ι l _ r hr
    exact Analysis.tendsto_integral_abs_mul_inner_grad_distance_cutoff
      (μ.prod (riemannianVolumeMeasure (I := I) (M := F.M) g)) r hr g h hhc
      (Eventually.of_forall fun z => hgh z.1) huc (Eventually.of_forall hu0) hv hw' o C
      (Eventually.of_forall fun z => hC z.1 z.1.property z.2)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancient_cutoff_flux_integrable_and_tendsto
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancient_cutoff_flux_integrable_and_tendsto target :: scope.openDecls } }

theorem integrable_ancient_perelmanDensity_cutoff_flux
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F) (p o : F.M)
    {a b : ℝ} (ha : 0 < a)
    (μ : MeasureTheory.Measure (_root_.Set.Icc a b)) [_root_.MeasureTheory.IsFiniteMeasure μ]
    (ψ : C(_root_.Set.Icc a b, ℝ))
    (r : NNReal) :
    _root_.MeasureTheory.Integrable (fun z : _root_.Set.Icc a b × F.M =>
      riemannianVolumeDensity (F.S.base.metric (-a)) (F.S.base.metric (-z.1)) z.2 * ψ z.1 *
        (F.S.base.metric (-z.1)).inner z.2
          (gradFun (F.S.base.metric (-z.1))
            (perelmanDensity (Module.finrank ℝ E) z.1 (fun y => redLength F.S 0 p y z.1)) z.2)
          (gradFun (F.S.base.metric (-z.1)) (fun y => Analysis.CutoffProfile.evalue
            ((r : ℝ≥0∞) * riemannianEDistOf (F.S.base.metric (-a)) o y)) z.2))
      (μ.prod (riemannianVolumeMeasure (I := I) (M := F.M) (F.S.base.metric (-a)))) := by
  exact (ancient_cutoff_flux_integrable_and_tendsto.{u, uE, uH, 0} F hF p o ha μ ψ).1 r

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.integrable_ancient_perelmanDensity_cutoff_flux then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.integrable_ancient_perelmanDensity_cutoff_flux"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.integrable_ancient_perelmanDensity_cutoff_flux ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.integrable_ancient_perelmanDensity_cutoff_flux

theorem tendsto_integral_abs_ancient_perelmanDensity_cutoff_flux
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F) (p o : F.M)
    {a b : ℝ} (ha : 0 < a)
    (μ : MeasureTheory.Measure (_root_.Set.Icc a b)) [_root_.MeasureTheory.IsFiniteMeasure μ]
    (ψ : C(_root_.Set.Icc a b, ℝ))
    {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    (r : ι → ℝ≥0) (hr : _root_.Filter.Tendsto r l (𝓝 0)) :
    _root_.Filter.Tendsto (fun i => ∫ z : _root_.Set.Icc a b × F.M,
      |riemannianVolumeDensity (F.S.base.metric (-a)) (F.S.base.metric (-z.1)) z.2 * ψ z.1 *
        (F.S.base.metric (-z.1)).inner z.2
          (gradFun (F.S.base.metric (-z.1))
            (perelmanDensity (Module.finrank ℝ E) z.1 (fun y => redLength F.S 0 p y z.1)) z.2)
          (gradFun (F.S.base.metric (-z.1)) (fun y => Analysis.CutoffProfile.evalue
            ((r i : ℝ≥0∞) * riemannianEDistOf (F.S.base.metric (-a)) o y)) z.2)|
      ∂(μ.prod (riemannianVolumeMeasure (I := I) (M := F.M) (F.S.base.metric (-a))))) l (𝓝 0) := by
  exact (ancient_cutoff_flux_integrable_and_tendsto F hF p o ha μ ψ).2 r hr

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.tendsto_integral_abs_ancient_perelmanDensity_cutoff_flux then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.tendsto_integral_abs_ancient_perelmanDensity_cutoff_flux"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.tendsto_integral_abs_ancient_perelmanDensity_cutoff_flux ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.tendsto_integral_abs_ancient_perelmanDensity_cutoff_flux

theorem tendsto_integral_ancient_perelmanDensity_cutoff_flux
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F) (p o : F.M)
    {a b : ℝ} (ha : 0 < a)
    (μ : MeasureTheory.Measure (_root_.Set.Icc a b)) [_root_.MeasureTheory.IsFiniteMeasure μ]
    (ψ : C(_root_.Set.Icc a b, ℝ))
    {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    (r : ι → ℝ≥0) (hr : _root_.Filter.Tendsto r l (𝓝 0)) :
    _root_.Filter.Tendsto (fun i => ∫ theta : _root_.Set.Icc a b, ψ theta *
      ∫ x : F.M, (F.S.base.metric (-theta)).inner x
        (gradFun (F.S.base.metric (-theta))
          (perelmanDensity (Module.finrank ℝ E) theta (fun y => redLength F.S 0 p y theta)) x)
        (gradFun (F.S.base.metric (-theta)) (fun y => Analysis.CutoffProfile.evalue
          ((r i : ℝ≥0∞) * riemannianEDistOf (F.S.base.metric (-a)) o y)) x)
        ∂riemannianVolumeMeasure (I := I) (M := F.M) (F.S.base.metric (-theta)) ∂μ)
      l (𝓝 0) := by
  let g : _root_.Set.Icc a b → SmoothRiemannianMetric I F.M := fun theta => F.S.base.metric (-theta)
  let V : ι → _root_.Set.Icc a b × F.M → ℝ := fun i z =>
    (g z.1).inner z.2
      (gradFun (g z.1) (perelmanDensity (Module.finrank ℝ E) z.1 (fun y => redLength F.S 0 p y z.1)) z.2)
      (gradFun (g z.1) (fun y => Analysis.CutoffProfile.evalue
        ((r i : ℝ≥0∞) * riemannianEDistOf (F.S.base.metric (-a)) o y)) z.2)
  let w : ι → _root_.Set.Icc a b × F.M → ℝ := fun i z =>
    riemannianVolumeDensity (F.S.base.metric (-a)) (g z.1) z.2 * ψ z.1 * V i z
  have hi (i : ι) : _root_.MeasureTheory.Integrable (w i)
      (μ.prod (riemannianVolumeMeasure (I := I) (M := F.M) (F.S.base.metric (-a)))) :=
    integrable_ancient_perelmanDensity_cutoff_flux F hF p o ha μ ψ (r i)
  have habs : _root_.Filter.Tendsto (fun i => ∫ z, |w i z|
      ∂μ.prod (riemannianVolumeMeasure (I := I) (M := F.M) (F.S.base.metric (-a)))) l (𝓝 0) :=
    tendsto_integral_abs_ancient_perelmanDensity_cutoff_flux F hF p o ha μ ψ r hr
  have hlimw : _root_.Filter.Tendsto (fun i => ∫ z, w i z
      ∂μ.prod (riemannianVolumeMeasure (I := I) (M := F.M) (F.S.base.metric (-a)))) l (𝓝 0) := by
    apply squeeze_zero_norm (fun i => ?_) habs
    simpa only [Real.norm_eq_abs] using _root_.MeasureTheory.norm_integral_le_integral_norm (w i)
  have heq (i : ι) : (∫ z, w i z
      ∂μ.prod (riemannianVolumeMeasure (I := I) (M := F.M) (F.S.base.metric (-a)))) =
      ∫ theta, ψ theta * ∫ x, V i (theta, x)
        ∂riemannianVolumeMeasure (I := I) (M := F.M) (g theta) ∂μ := by
    have hf : _root_.MeasureTheory.Integrable (fun z : _root_.Set.Icc a b × F.M =>
        riemannianVolumeDensity (F.S.base.metric (-a)) (g z.1) z.2 • (ψ z.1 * V i z))
        (μ.prod (riemannianVolumeMeasure (I := I) (M := F.M) (F.S.base.metric (-a)))) := by
      convert hi i using 1
      funext z
      simp only [w, smul_eq_mul, mul_assoc]
    calc
      _ = ∫ z, riemannianVolumeDensity (F.S.base.metric (-a)) (g z.1) z.2 • (ψ z.1 * V i z)
          ∂μ.prod (riemannianVolumeMeasure (I := I) (M := F.M) (F.S.base.metric (-a))) := by
        apply _root_.MeasureTheory.integral_congr_ae
        filter_upwards [] with z
        simp only [w, smul_eq_mul, mul_assoc]
      _ = ∫ theta, ∫ x, ψ theta * V i (theta, x)
          ∂riemannianVolumeMeasure (I := I) (M := F.M) (g theta) ∂μ :=
        integral_prod_volumeDensity_smul μ (F.S.base.metric (-a)) g (fun z => ψ z.1 * V i z) hf
      _ = _ := by simp only [_root_.MeasureTheory.integral_const_mul]
  simp_rw [heq] at hlimw
  exact hlimw

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.tendsto_integral_ancient_perelmanDensity_cutoff_flux then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.tendsto_integral_ancient_perelmanDensity_cutoff_flux"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.tendsto_integral_ancient_perelmanDensity_cutoff_flux ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.tendsto_integral_ancient_perelmanDensity_cutoff_flux
end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
