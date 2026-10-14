import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.EnergyBound.WeightedIntegrability

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Connection

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Set _root_.MeasureTheory _root_.Filter _root_.Topology _root_.Function
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.Matrix _root_.InnerProductSpace _root_.BigOperators
  RealInnerProductSpace ENNReal NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.L2
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.Chart
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.MetricExtension hiding chartTargetEuclid
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1Compl

private local instance _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instMeasurableSpace_differentialGeometry : MeasurableSpace E := borel E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instMeasurableSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instMeasurableSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instBorelSpace_differentialGeometry : BorelSpace E := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instBorelSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instBorelSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instMeasurableSpace_differentialGeometry_1 : MeasurableSpace M := borel M

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instMeasurableSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instMeasurableSpace_differentialGeometry_1 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instBorelSpace_differentialGeometry_1 : BorelSpace M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instBorelSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instBorelSpace_differentialGeometry_1 target :: scope.openDecls } }

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

section ExplicitNormBound

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [CompactSpace M]
  [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]


theorem eLpNorm_weighted_contDiffOn_mul_le
    (g : SmoothRiemannianMetric I M) (α : M)
    {c : EuclN → ℝ}
    (hc : ContDiffOn ℝ ∞ c (chartTargetEuclid (I := I) (M := M) α))
    {K : Set EuclN} (hK_compact : IsCompact K)
    (hK_in : K ⊆ chartTargetEuclid (I := I) (M := M) α)
    {w : EuclN → ℝ}
    (hw_zero : ∀ᵐ y ∂((chartPulledWeightedMeasure (I := I) g α).restrict
        (chartTargetEuclid (I := I) (M := M) α)),
      y ∉ K → w y = 0) :
    ∃ C : ℝ, 0 ≤ C ∧
      _root_.MeasureTheory.eLpNorm (fun y => c y * w y) 2
          ((chartPulledWeightedMeasure (I := I) g α).restrict
            (chartTargetEuclid (I := I) (M := M) α))
        ≤ ENNReal.ofReal C *
          _root_.MeasureTheory.eLpNorm w 2
            ((chartPulledWeightedMeasure (I := I) g α).restrict
              (chartTargetEuclid (I := I) (M := M) α)) := by
  classical
  set μw : _root_.MeasureTheory.Measure EuclN :=
    (chartPulledWeightedMeasure (I := I) g α).restrict
      (chartTargetEuclid (I := I) (M := M) α) with hμw_def
  have hcontOn_K : ContinuousOn c K := hc.continuousOn.mono hK_in
  have hbdd : ∃ C : ℝ, 0 ≤ C ∧ ∀ y ∈ K, ‖c y‖ ≤ C := by
    by_cases hK_empty : K = ∅
    · exact ⟨0, le_refl _, fun y hy => absurd (hK_empty ▸ hy) (Set.notMem_empty y)⟩
    · obtain ⟨C₀, hC₀⟩ := hK_compact.bddAbove_image hcontOn_K.norm
      exact ⟨max C₀ 0, le_max_right _ _,
        fun y hy => (hC₀ ⟨y, hy, rfl⟩).trans (le_max_left _ _)⟩
  obtain ⟨C, hC_nn, hC_bd⟩ := hbdd
  refine ⟨C, hC_nn, ?_⟩
  have h_dom : ∀ᵐ y ∂μw, ‖c y * w y‖ ≤ ‖(C : ℝ) • w y‖ := by
    filter_upwards [hw_zero] with y hy
    by_cases hyK : y ∈ K
    · have hlhs : ‖c y * w y‖ = ‖c y‖ * ‖w y‖ := norm_mul _ _
      have hrhs : ‖(C : ℝ) • w y‖ = C * ‖w y‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hC_nn]
      rw [hlhs, hrhs]
      exact mul_le_mul_of_nonneg_right (hC_bd y hyK) (norm_nonneg _)
    · rw [hy hyK, _root_.MulZeroClass.mul_zero, smul_zero, norm_zero]
  have h_mono :
      eLpNorm (fun y => c y * w y) 2 μw ≤ _root_.MeasureTheory.eLpNorm (fun y => (C : ℝ) • w y) 2 μw :=
    eLpNorm_mono_ae (μ := μw) h_dom
  have h_smul :
      _root_.MeasureTheory.eLpNorm (fun y => (C : ℝ) • w y) 2 μw
        = ENNReal.ofReal C * _root_.MeasureTheory.eLpNorm w 2 μw := by
    have h := _root_.MeasureTheory.eLpNorm_const_smul (μ := μw) (p := 2) (C : ℝ) w
    rw [Real.enorm_of_nonneg hC_nn] at h
    change _root_.MeasureTheory.eLpNorm (fun y => (C : ℝ) • w y) 2 μw =
      ENNReal.ofReal C * _root_.MeasureTheory.eLpNorm w 2 μw at h
    exact h
  calc
    _root_.MeasureTheory.eLpNorm (fun y => c y * w y) 2 μw
        ≤ _root_.MeasureTheory.eLpNorm (fun y => (C : ℝ) • w y) 2 μw := h_mono
    _ = ENNReal.ofReal C * _root_.MeasureTheory.eLpNorm w 2 μw := h_smul

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eLpNorm_weighted_contDiffOn_mul_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eLpNorm_weighted_contDiffOn_mul_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eLpNorm_weighted_contDiffOn_mul_le ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eLpNorm_weighted_contDiffOn_mul_le

theorem eLpNorm_weighted_contDiffOn_mul_le_uniform
    (g : SmoothRiemannianMetric I M) (α : M)
    {c : EuclN → ℝ}
    (hc : ContDiffOn ℝ ∞ c (chartTargetEuclid (I := I) (M := M) α))
    {K : Set EuclN} (hK_compact : IsCompact K)
    (hK_in : K ⊆ chartTargetEuclid (I := I) (M := M) α) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ w : EuclN → ℝ,
        _root_.MeasureTheory.MemLp w 2
            ((chartPulledWeightedMeasure (I := I) g α).restrict
              (chartTargetEuclid (I := I) (M := M) α)) →
        (∀ᵐ y ∂((chartPulledWeightedMeasure (I := I) g α).restrict
            (chartTargetEuclid (I := I) (M := M) α)), y ∉ K → w y = 0) →
        _root_.MeasureTheory.eLpNorm (fun y => c y * w y) 2
            ((chartPulledWeightedMeasure (I := I) g α).restrict
              (chartTargetEuclid (I := I) (M := M) α))
          ≤ ENNReal.ofReal C *
            _root_.MeasureTheory.eLpNorm w 2
              ((chartPulledWeightedMeasure (I := I) g α).restrict
                (chartTargetEuclid (I := I) (M := M) α)) := by
  classical
  set μw : _root_.MeasureTheory.Measure EuclN :=
    (chartPulledWeightedMeasure (I := I) g α).restrict
      (chartTargetEuclid (I := I) (M := M) α) with hμw_def
  have hcontOn_K : ContinuousOn c K := hc.continuousOn.mono hK_in
  have hbdd : ∃ C : ℝ, 0 ≤ C ∧ ∀ y ∈ K, ‖c y‖ ≤ C := by
    by_cases hK_empty : K = ∅
    · exact ⟨0, le_refl _, fun y hy => absurd (hK_empty ▸ hy) (Set.notMem_empty y)⟩
    · obtain ⟨C₀, hC₀⟩ := hK_compact.bddAbove_image hcontOn_K.norm
      exact ⟨max C₀ 0, le_max_right _ _,
        fun y hy => (hC₀ ⟨y, hy, rfl⟩).trans (le_max_left _ _)⟩
  obtain ⟨C, hC_nn, hC_bd⟩ := hbdd
  refine ⟨C, hC_nn, fun w hw hw_zero => ?_⟩
  have h_dom : ∀ᵐ y ∂μw, ‖c y * w y‖ ≤ ‖(C : ℝ) • w y‖ := by
    filter_upwards [hw_zero] with y hy
    by_cases hyK : y ∈ K
    · have hlhs : ‖c y * w y‖ = ‖c y‖ * ‖w y‖ := norm_mul _ _
      have hrhs : ‖(C : ℝ) • w y‖ = C * ‖w y‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hC_nn]
      rw [hlhs, hrhs]
      exact mul_le_mul_of_nonneg_right (hC_bd y hyK) (norm_nonneg _)
    · rw [hy hyK, _root_.MulZeroClass.mul_zero, smul_zero, norm_zero]
  have h_mono :
      eLpNorm (fun y => c y * w y) 2 μw ≤ _root_.MeasureTheory.eLpNorm (fun y => (C : ℝ) • w y) 2 μw :=
    eLpNorm_mono_ae (μ := μw) h_dom
  have h_smul :
      _root_.MeasureTheory.eLpNorm (fun y => (C : ℝ) • w y) 2 μw
        = ENNReal.ofReal C * _root_.MeasureTheory.eLpNorm w 2 μw := by
    have h := _root_.MeasureTheory.eLpNorm_const_smul (μ := μw) (p := 2) (C : ℝ) w
    rw [Real.enorm_of_nonneg hC_nn] at h
    change _root_.MeasureTheory.eLpNorm (fun y => (C : ℝ) • w y) 2 μw =
      ENNReal.ofReal C * _root_.MeasureTheory.eLpNorm w 2 μw at h
    exact h
  calc
    _root_.MeasureTheory.eLpNorm (fun y => c y * w y) 2 μw
        ≤ _root_.MeasureTheory.eLpNorm (fun y => (C : ℝ) • w y) 2 μw := h_mono
    _ = ENNReal.ofReal C * _root_.MeasureTheory.eLpNorm w 2 μw := h_smul

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eLpNorm_weighted_contDiffOn_mul_le_uniform then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eLpNorm_weighted_contDiffOn_mul_le_uniform"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eLpNorm_weighted_contDiffOn_mul_le_uniform ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eLpNorm_weighted_contDiffOn_mul_le_uniform

end ExplicitNormBound

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
