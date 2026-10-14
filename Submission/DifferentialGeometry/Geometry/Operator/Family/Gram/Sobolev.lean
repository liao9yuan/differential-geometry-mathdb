import Submission.DifferentialGeometry.Analysis.Calculus.Manifold.AbsolutelyContinuous
import Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.H1.Regularity.AbsolutelyContinuous
import Submission.DifferentialGeometry.Geometry.Operator.Family.Gram.Curve
import Submission.DifferentialGeometry.Geometry.Operator.Family.Gram.Carrier

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Filter _root_.Function _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Set
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Interval _root_.Topology

namespace DifferentialGeometry.Geometry.Curvature

open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {D : RealTimeInterval}

theorem MetricConnectionFamilyOn.exists_timeH1_extChartAt
    (G : MetricConnectionFamilyOn (I := I) (M := M) D)
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G.metric)
    (p : M) {L : ℝ} (gamma : ℝ → M) (tau : ℝ → ℝ)
    (hAC : AbsolutelyContinuousOnInterval ((extChartAt I p) ∘ gamma) 0 L)
    (hsrc : _root_.Set.MapsTo gamma (_root_.Set.uIcc 0 L) (chartAt H p).source)
    (hchart : _root_.Set.MapsTo ((extChartAt I p) ∘ gamma) (_root_.Set.Icc 0 L)
      (interior (extChartAt I p).target))
    (htau : ContinuousOn tau (_root_.Set.Icc 0 L))
    (hreg : _root_.Set.MapsTo tau (_root_.Set.Icc 0 L) D.regular)
    (hInt : _root_.MeasureTheory.Integrable (fun r ↦ (G.metric (tau r)).inner (gamma r)
      ((mfderiv 𝓘(ℝ, ℝ) I gamma r : ℝ →L[ℝ] _) (1 : ℝ))
      ((mfderiv 𝓘(ℝ, ℝ) I gamma r : ℝ →L[ℝ] _) (1 : ℝ))) (timeMeasure L)) :
    ∃ u : timeH1 E L,
      _root_.Set.EqOn u.toFun ((extChartAt I p) ∘ gamma) (_root_.Set.Icc 0 L) ∧
        u.deriv =ᵐ[timeMeasure L] deriv ((extChartAt I p) ∘ gamma) := by
  let f := (extChartAt I p) ∘ gamma
  have hmdiff : ∀ᵐ r ∂timeMeasure L, MDifferentiableAt 𝓘(ℝ, ℝ) I gamma r :=
    _root_.MeasureTheory.ae_mono (Measure.restrict_mono _root_.Set.Icc_subset_uIcc le_rfl)
      (hAC.ae_mdifferentiableAt_of_extChartAt p hsrc)
  obtain ⟨c, hc, hcLower⟩ := chartGramOp_lower hG (mapsTo_iff_image_subset.mp hreg)
    (isCompact_Icc.image_of_continuousOn htau) p (mapsTo_iff_image_subset.mp hchart)
    (isCompact_Icc.image_of_continuousOn (hAC.continuousOn.mono _root_.Set.Icc_subset_uIcc))
  have hsqBound : ∀ᵐ r ∂timeMeasure L,
      ‖deriv f r‖ ^ 2 ≤ |(G.metric (tau r)).inner (gamma r)
        ((mfderiv 𝓘(ℝ, ℝ) I gamma r : ℝ →L[ℝ] _) (1 : ℝ))
        ((mfderiv 𝓘(ℝ, ℝ) I gamma r : ℝ →L[ℝ] _) (1 : ℝ))| / c := by
    filter_upwards [hmdiff, _root_.MeasureTheory.ae_restrict_mem measurableSet_Icc] with r hmd hr
    apply (le_div_iff₀' hc).2
    have hgram := hcLower (tau r, f r) ⟨⟨r, hr, rfl⟩, ⟨r, hr, rfl⟩⟩ (deriv f r)
    dsimp only [f, Function.comp_apply] at hgram
    rw [chartGramOp_inner_deriv G p (tau r) hmd (hsrc (_root_.Set.Icc_subset_uIcc hr))] at hgram
    exact hgram.trans (le_abs_self _)
  have hdmeas := aestronglyMeasurable_deriv f (timeMeasure L)
  have hsqInt : _root_.MeasureTheory.Integrable (fun r ↦ ‖deriv f r‖ ^ 2) (timeMeasure L) :=
    (hInt.abs.div_const c).mono_nonneg (hdmeas.norm.pow 2)
      (Eventually.of_forall fun r ↦ sq_nonneg ‖deriv f r‖) hsqBound
  exact timeH1.exists_of_absolutelyContinuousOnInterval f hAC
    ((_root_.MeasureTheory.memLp_two_iff_integrable_sq_norm hdmeas).2 hsqInt)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.MetricConnectionFamilyOn.exists_timeH1_extChartAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.MetricConnectionFamilyOn.exists_timeH1_extChartAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.MetricConnectionFamilyOn.exists_timeH1_extChartAt ``Submission.DifferentialGeometry.Geometry.Curvature.MetricConnectionFamilyOn.exists_timeH1_extChartAt

end DifferentialGeometry.Geometry.Curvature

end

noncomputable section

open _root_.Filter _root_.Function _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Set
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Interval _root_.Topology

namespace DifferentialGeometry.Geometry.Curvature

open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {D : RealTimeInterval}

theorem MetricConnectionFamilyOn.exists_timeH1_extChartAt_of_carrier
    (G : MetricConnectionFamilyOn (I := I) (M := M) D)
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G.metric)
    (p : M) {L : ℝ} (gamma : ℝ → M) (tau : ℝ → ℝ)
    (hAC : AbsolutelyContinuousOnInterval ((extChartAt I p) ∘ gamma) 0 L)
    (hsrc : _root_.Set.MapsTo gamma (_root_.Set.uIcc 0 L) (chartAt H p).source)
    (htau : ContinuousOn tau (_root_.Set.Icc 0 L))
    (hreg : _root_.Set.MapsTo tau (_root_.Set.Icc 0 L) D.carrier)
    (hInt : _root_.MeasureTheory.Integrable (fun r ↦ (G.metric (tau r)).inner (gamma r)
      ((mfderiv 𝓘(ℝ, ℝ) I gamma r : ℝ →L[ℝ] _) (1 : ℝ))
      ((mfderiv 𝓘(ℝ, ℝ) I gamma r : ℝ →L[ℝ] _) (1 : ℝ))) (timeMeasure L)) :
    ∃ u : timeH1 E L,
      _root_.Set.EqOn u.toFun ((extChartAt I p) ∘ gamma) (_root_.Set.Icc 0 L) ∧
        u.deriv =ᵐ[timeMeasure L] deriv ((extChartAt I p) ∘ gamma) := by
  let f := (extChartAt I p) ∘ gamma
  have hmdiff : ∀ᵐ r ∂timeMeasure L, MDifferentiableAt 𝓘(ℝ, ℝ) I gamma r :=
    _root_.MeasureTheory.ae_mono (Measure.restrict_mono _root_.Set.Icc_subset_uIcc le_rfl)
      (hAC.ae_mdifferentiableAt_of_extChartAt p hsrc)
  have hchart : _root_.Set.MapsTo ((extChartAt I p) ∘ gamma) (_root_.Set.Icc 0 L) (extChartAt I p).target := by
    intro r hr
    exact (extChartAt I p).map_source (by
      simpa only [extChartAt_source] using hsrc (_root_.Set.Icc_subset_uIcc hr))
  obtain ⟨c, hc, hcLower⟩ := chartGramOp_lower_of_carrier hG (mapsTo_iff_image_subset.mp hreg)
    (isCompact_Icc.image_of_continuousOn htau) p (mapsTo_iff_image_subset.mp hchart)
    (isCompact_Icc.image_of_continuousOn (hAC.continuousOn.mono _root_.Set.Icc_subset_uIcc))
  have hsqBound : ∀ᵐ r ∂timeMeasure L,
      ‖deriv f r‖ ^ 2 ≤ |(G.metric (tau r)).inner (gamma r)
        ((mfderiv 𝓘(ℝ, ℝ) I gamma r : ℝ →L[ℝ] _) (1 : ℝ))
        ((mfderiv 𝓘(ℝ, ℝ) I gamma r : ℝ →L[ℝ] _) (1 : ℝ))| / c := by
    filter_upwards [hmdiff, _root_.MeasureTheory.ae_restrict_mem measurableSet_Icc] with r hmd hr
    apply (le_div_iff₀' hc).2
    have hgram := hcLower (tau r, f r) ⟨⟨r, hr, rfl⟩, ⟨r, hr, rfl⟩⟩ (deriv f r)
    dsimp only [f, Function.comp_apply] at hgram
    rw [chartGramOp_inner_deriv G p (tau r) hmd (hsrc (_root_.Set.Icc_subset_uIcc hr))] at hgram
    exact hgram.trans (le_abs_self _)
  have hdmeas := aestronglyMeasurable_deriv f (timeMeasure L)
  have hsqInt : _root_.MeasureTheory.Integrable (fun r ↦ ‖deriv f r‖ ^ 2) (timeMeasure L) :=
    (hInt.abs.div_const c).mono_nonneg (hdmeas.norm.pow 2)
      (Eventually.of_forall fun r ↦ sq_nonneg ‖deriv f r‖) hsqBound
  exact timeH1.exists_of_absolutelyContinuousOnInterval f hAC
    ((_root_.MeasureTheory.memLp_two_iff_integrable_sq_norm hdmeas).2 hsqInt)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.MetricConnectionFamilyOn.exists_timeH1_extChartAt_of_carrier then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.MetricConnectionFamilyOn.exists_timeH1_extChartAt_of_carrier"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.MetricConnectionFamilyOn.exists_timeH1_extChartAt_of_carrier ``Submission.DifferentialGeometry.Geometry.Curvature.MetricConnectionFamilyOn.exists_timeH1_extChartAt_of_carrier

end DifferentialGeometry.Geometry.Curvature
