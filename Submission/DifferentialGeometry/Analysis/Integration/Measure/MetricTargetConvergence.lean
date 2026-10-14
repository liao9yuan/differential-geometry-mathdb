import Submission.DifferentialGeometry.Topology.MetricSpace.DistanceConvergence
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

section

set_option autoImplicit false
noncomputable section

open _root_.Filter _root_.MeasureTheory
open scoped _root_.Topology

open _root_.DenseRange in
theorem DenseRange.exists_ae_tendsto_of_ae_tendsto_dist
    {A I X : Type*} [MeasurableSpace A] [Countable I]
    [PseudoMetricSpace X] [ProperSpace X]
    {a : I → X} (ha : DenseRange a) (μ : _root_.MeasureTheory.Measure A) (u : ℕ → A → X)
    (hu : ∀ i, ∀ᵐ z ∂μ, ∃ r : ℝ,
      _root_.Filter.Tendsto (fun n => _root_.Dist.dist (u n z) (a i)) _root_.Filter.atTop (𝓝 r)) :
    ∃ v : A → X, ∀ᵐ z ∂μ, _root_.Filter.Tendsto (fun n => u n z) _root_.Filter.atTop (𝓝 (v z)) := by
  classical
  let P : A → Prop := fun z => ∃ x : X,
    _root_.Filter.Tendsto (fun n => u n z) _root_.Filter.atTop (𝓝 x)
  have hP : ∀ᵐ z ∂μ, P z := by
    filter_upwards [ae_all_iff.mpr hu] with z hz
    exact ha.exists_tendsto_of_tendsto_dist hz
  let v : A → X := fun z => if h : P z then h.choose else u 0 z
  refine ⟨v, ?_⟩
  filter_upwards [hP] with z hz
  simpa only [v, dif_pos hz] using hz.choose_spec

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DenseRange.exists_ae_tendsto_of_ae_tendsto_dist then
    throwError "Refusing to shadow existing declaration DenseRange.exists_ae_tendsto_of_ae_tendsto_dist"
  Lean.modifyEnv fun env => Lean.addAlias env `DenseRange.exists_ae_tendsto_of_ae_tendsto_dist ``Submission.DenseRange.exists_ae_tendsto_of_ae_tendsto_dist

open _root_.DenseRange in
theorem DenseRange.exists_aemeasurable_ae_tendsto_of_ae_tendsto_dist
    {A I X : Type*} [MeasurableSpace A] [Countable I]
    [PseudoMetricSpace X] [ProperSpace X] [MeasurableSpace X] [BorelSpace X]
    {a : I → X} (ha : DenseRange a) (μ : _root_.MeasureTheory.Measure A) (u : ℕ → A → X)
    (hum : ∀ n, AEMeasurable (u n) μ)
    (hu : ∀ i, ∀ᵐ z ∂μ, ∃ r : ℝ,
      _root_.Filter.Tendsto (fun n => _root_.Dist.dist (u n z) (a i)) _root_.Filter.atTop (𝓝 r)) :
    ∃ v : A → X, AEMeasurable v μ ∧
      ∀ᵐ z ∂μ, _root_.Filter.Tendsto (fun n => u n z) _root_.Filter.atTop (𝓝 (v z)) := by
  obtain ⟨v, hv⟩ := ha.exists_ae_tendsto_of_ae_tendsto_dist μ u hu
  exact ⟨v, aemeasurable_of_tendsto_metrizable_ae' hum hv, hv⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DenseRange.exists_aemeasurable_ae_tendsto_of_ae_tendsto_dist then
    throwError "Refusing to shadow existing declaration DenseRange.exists_aemeasurable_ae_tendsto_of_ae_tendsto_dist"
  Lean.modifyEnv fun env => Lean.addAlias env `DenseRange.exists_aemeasurable_ae_tendsto_of_ae_tendsto_dist ``Submission.DenseRange.exists_aemeasurable_ae_tendsto_of_ae_tendsto_dist

end

end
