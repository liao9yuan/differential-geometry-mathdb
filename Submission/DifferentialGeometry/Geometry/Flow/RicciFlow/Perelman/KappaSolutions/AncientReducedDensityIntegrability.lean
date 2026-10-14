import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientAsymptoticReducedVolume
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientReducedLengthContinuity
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.ReducedVolume.Scaling
import Submission.DifferentialGeometry.Analysis.Integration.Measure.VolumeDensityIntegrability
import Submission.DifferentialGeometry.Analysis.Integration.Measure.VolumeDensityContinuity

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section
open _root_.Set _root_.Submission.Set _root_.Filter _root_.MeasureTheory _root_.Submission.MeasureTheory
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology _root_.Submission.Topology _root_.NNReal
namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open _root_.Submission.DifferentialGeometry.Geometry.Curvature _root_.Submission.DifferentialGeometry.Integral.Measure _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Entropy
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  (F : PointedFlowData (I := I) ancientTimeInterval)
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

theorem integrable_ancient_perelmanDensity
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F) (p : F.M)
    {a b : ℝ} (ha : 0 < a) (μ : _root_.MeasureTheory.Measure (_root_.Set.Icc a b)) [_root_.MeasureTheory.IsFiniteMeasure μ]
    (R : SmoothRiemannianMetric I F.M) :
    _root_.MeasureTheory.Integrable (fun z : _root_.Set.Icc a b × F.M =>
      riemannianVolumeDensity R (F.S.base.metric (-z.1)) z.2 *
        perelmanDensity (Module.finrank ℝ E) z.1 (fun y => redLength F.S 0 p y z.1) z.2)
      (μ.prod (riemannianVolumeMeasure (I := I) (M := F.M) R)) := by
  have hρ := riemannianVolumeDensity_family_continuousOn R F.S.base.metric
    F.isSolution.smoothMetric.chartGramMatrix_continuousOn_carrier
  have hρc : Continuous (fun z : _root_.Set.Icc a b × F.M =>
      riemannianVolumeDensity R (F.S.base.metric (-z.1)) z.2) :=
    hρ.comp_continuous ((continuous_subtype_val.comp continuous_fst).neg.prodMk continuous_snd)
      (fun z => ⟨show -(z.1 : ℝ) ≤ 0 from neg_nonpos.mpr (ha.le.trans z.1.property.1), _root_.Set.mem_univ _⟩)
  have hl : Continuous (fun z : _root_.Set.Icc a b × F.M => redLength F.S 0 p z.2 z.1) :=
    (continuousOn_redLength_space_time_of_ancient F hF p).comp_continuous
      ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
      (fun z => ⟨ha.trans_le z.1.property.1, _root_.Set.mem_univ _⟩)
  have hu : Continuous (fun z : _root_.Set.Icc a b × F.M =>
      perelmanDensity (Module.finrank ℝ E) z.1 (fun y => redLength F.S 0 p y z.1) z.2) := by
    unfold perelmanDensity perelmanDensityPrefactor
    apply Continuous.mul
    · apply Continuous.rpow_const (continuous_const.mul (continuous_subtype_val.comp continuous_fst))
      intro z
      exact Or.inl (mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero)
        (ne_of_gt (ha.trans_le z.1.property.1)))
    · exact Real.continuous_exp.comp hl.neg
  have hw := (hρc.mul hu).aestronglyMeasurable
    (μ := μ.prod (riemannianVolumeMeasure (I := I) (M := F.M) R))
  apply integrable_prod_volumeDensity_smul_of_lintegral_norm_le μ R
    (fun tau => F.S.base.metric (-tau))
    (fun z => perelmanDensity (Module.finrank ℝ E) z.1 (fun y => redLength F.S 0 p y z.1) z.2)
    hw (C := 1) ENNReal.one_ne_top
  filter_upwards [] with tau
  have htau : 0 < (tau : ℝ) := ha.trans_le tau.property.1
  have hnonneg (x : F.M) : 0 ≤ perelmanDensity (Module.finrank ℝ E) tau
      (fun y => redLength F.S 0 p y tau) x :=
    (mul_pos (prefactor_pos _ htau) (Real.exp_pos _)).le
  simp_rw [Real.norm_eq_abs, abs_of_nonneg (hnonneg _)]
  have hmass := intrinsicReducedVolume_eq_normalizedShrinkerMass F.S 0 p htau
  rw [normalizedShrinkerMass_scaleMetric_inv_eq_lintegral_perelmanDensity _ htau, zero_sub] at hmass
  rw [← hmass]
  exact ancient_reducedVolume_le_one F hF le_rfl p htau

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.integrable_ancient_perelmanDensity then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.integrable_ancient_perelmanDensity"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.integrable_ancient_perelmanDensity ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.integrable_ancient_perelmanDensity

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
