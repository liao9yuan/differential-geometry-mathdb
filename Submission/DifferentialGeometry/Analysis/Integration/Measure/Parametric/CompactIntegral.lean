import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Filter _root_.MeasureTheory _root_.Set
open scoped _root_.Topology

namespace DifferentialGeometry.Integral.Measure

theorem integral_contOn_compact
    {P X W : Type*} [TopologicalSpace P] [FirstCountableTopology P]
    [TopologicalSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    [SecondCountableTopologyEither X W]
    (μ : _root_.MeasureTheory.Measure X) [_root_.MeasureTheory.IsFiniteMeasure μ]
    (F : P → X → W) {K : Set P} (hK : IsCompact K)
    (hF : ContinuousOn (fun p : P × X => F p.1 p.2)
      (K ×ˢ (Set.univ : Set X))) :
    ContinuousOn (fun p : P => ∫ x, F p x ∂μ) K := by
  have hKX : IsCompact (K ×ˢ (Set.univ : Set X)) :=
    hK.prod isCompact_univ
  have hnorm : ContinuousOn (fun p : P × X => ‖F p.1 p.2‖)
      (K ×ˢ (Set.univ : Set X)) := hF.norm
  obtain ⟨C, hC⟩ := hKX.exists_bound_of_continuousOn hnorm
  let C₀ : ℝ := _root_.Max.max C 0
  have hC₀ : 0 ≤ C₀ := le_max_right C 0
  have hCint : _root_.MeasureTheory.Integrable (fun _ : X => C₀) μ := _root_.MeasureTheory.integrable_const C₀
  intro p hp
  have hmeas : ∀ᶠ q in 𝓝[K] p, _root_.MeasureTheory.AEStronglyMeasurable (F q) μ := by
    filter_upwards [self_mem_nhdsWithin] with q hq
    have hslice : Continuous (F q) := by
      rw [← continuousOn_univ]
      exact hF.comp (continuousOn_const.prodMk continuousOn_id)
        (fun x _ => ⟨hq, Set.mem_univ x⟩)
    exact hslice.aestronglyMeasurable
  have hbound : ∀ᶠ q in 𝓝[K] p,
      ∀ᵐ x ∂μ, ‖F q x‖ ≤ (fun _ : X => C₀) x := by
    filter_upwards [self_mem_nhdsWithin] with q hq
    filter_upwards with x
    simpa only [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _), C₀] using
      (hC (q, x) ⟨hq, Set.mem_univ x⟩).trans (le_max_left C 0)
  have hlim : ∀ᵐ x ∂μ,
      Tendsto (fun q => F q x) (𝓝[K] p) (𝓝 (F p x)) := by
    filter_upwards with x
    have hx : ContinuousOn (fun q : P => F q x) K :=
      hF.comp (continuousOn_id.prodMk continuousOn_const)
        (fun q hq => ⟨hq, Set.mem_univ x⟩)
    exact hx p hp
  exact _root_.MeasureTheory.tendsto_integral_filter_of_dominated_convergence
    (fun _ : X => C₀) hmeas hbound hCint hlim

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.Measure.integral_contOn_compact then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.Measure.integral_contOn_compact"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.Measure.integral_contOn_compact ``Submission.DifferentialGeometry.Integral.Measure.integral_contOn_compact

attribute [local instance] Measure.Subtype.measureSpace in
theorem continuousOn_intervalIntegral_of_continuousOn_compact
    {P W : Type*} [TopologicalSpace P] [FirstCountableTopology P]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    {K : Set P} (hK : IsCompact K) {a b : ℝ} (hab : a ≤ b)
    {f : P → ℝ → W}
    (hf : ContinuousOn (fun p : P × ℝ => f p.1 p.2) (K ×ˢ _root_.Set.Icc a b)) :
    ContinuousOn (fun p => ∫ q in a..b, f p q) K := by
  let : CompactSpace (_root_.Set.Icc a b) := isCompact_iff_compactSpace.mp _root_.CompactIccSpace.isCompact_Icc
  let : _root_.MeasureTheory.IsFiniteMeasure (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure (_root_.Set.Icc a b)) :=
    ⟨by
      rw [Measure.Subtype.volume_univ measurableSet_Icc.nullMeasurableSet]
      exact isCompact_Icc.measure_lt_top⟩
  have hcont : ContinuousOn (fun p : P × _root_.Set.Icc a b => f p.1 p.2.val)
      (K ×ˢ (Set.univ : Set (_root_.Set.Icc a b))) := by
    exact hf.comp
      (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)).continuousOn
      (fun p hp => ⟨hp.1, p.2.property⟩)
  have h := integral_contOn_compact (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure (_root_.Set.Icc a b))
    (fun p q => f p q) hK hcont
  refine h.congr (fun p _hp => ?_)
  change (∫ q in a..b, f p q) = ∫ q : _root_.Set.Icc a b, f p q
  rw [_root_.MeasureTheory.integral_subtype measurableSet_Icc, _root_.MeasureTheory.integral_Icc_eq_integral_Ioc]
  exact intervalIntegral.integral_of_le hab

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.Measure.continuousOn_intervalIntegral_of_continuousOn_compact then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.Measure.continuousOn_intervalIntegral_of_continuousOn_compact"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.Measure.continuousOn_intervalIntegral_of_continuousOn_compact ``Submission.DifferentialGeometry.Integral.Measure.continuousOn_intervalIntegral_of_continuousOn_compact

end DifferentialGeometry.Integral.Measure

end
