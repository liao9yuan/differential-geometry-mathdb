import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.EnergyBound.WeightedCoefficientL2Bound
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.Cross.RightDivergence

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Geometry.Curvature


noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Set _root_.Filter _root_.MeasureTheory
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.BigOperators _root_.Matrix _root_.ENNReal _root_.NNReal
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral


open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.L2
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.Chart
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.TensorRegularity
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.MetricExtension hiding chartTargetEuclid
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1Compl

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

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

section PerSummandBound


omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
private lemma eLpNorm_indicatorPou_mul_le
    (g : SmoothRiemannianMetric I M) (α : M)
    {c : EuclN → ℝ}
    (hc : ContDiffOn ℝ ∞ c (chartTargetEuclid (I := I) (M := M) α))
    (w : EuclN → ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧
      _root_.MeasureTheory.eLpNorm
          (fun y => Set.indicator (chartPouKernel (I := I) (M := M) α) c y * w y)
          2
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
  obtain ⟨C, hC_nn, hC_bd⟩ :=
    exists_bound_on_chartPouKernel (I := I) (M := M) α hc
  refine ⟨C, hC_nn, ?_⟩
  have hci_bd : ∀ y : EuclN,
      ‖Set.indicator (chartPouKernel (I := I) (M := M) α) c y‖ ≤ C := by
    intro y
    by_cases hy : y ∈ chartPouKernel (I := I) (M := M) α
    · rw [Set.indicator_of_mem hy]; exact hC_bd y hy
    · rw [Set.indicator_of_notMem hy, norm_zero]; exact hC_nn
  have h_dom : ∀ᵐ y ∂μw,
      ‖Set.indicator (chartPouKernel (I := I) (M := M) α) c y * w y‖ ≤
        ‖(C : ℝ) • w y‖ := by
    refine Filter.Eventually.of_forall (fun y => ?_)
    have hlhs :
        ‖Set.indicator (chartPouKernel (I := I) (M := M) α) c y * w y‖ =
          ‖Set.indicator (chartPouKernel (I := I) (M := M) α) c y‖ * ‖w y‖ :=
      norm_mul _ _
    have hrhs : ‖(C : ℝ) • w y‖ = C * ‖w y‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hC_nn]
    rw [hlhs, hrhs]
    exact mul_le_mul_of_nonneg_right (hci_bd y) (norm_nonneg _)
  have h_mono :
      _root_.MeasureTheory.eLpNorm
          (fun y => Set.indicator (chartPouKernel (I := I) (M := M) α) c y * w y)
          2 μw
        ≤ _root_.MeasureTheory.eLpNorm (fun y => (C : ℝ) • w y) 2 μw :=
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
    _root_.MeasureTheory.eLpNorm
        (fun y => Set.indicator (chartPouKernel (I := I) (M := M) α) c y * w y)
        2 μw
        ≤ _root_.MeasureTheory.eLpNorm (fun y => (C : ℝ) • w y) 2 μw := h_mono
    _ = ENNReal.ofReal C * _root_.MeasureTheory.eLpNorm w 2 μw := h_smul

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eLpNorm_indicatorPou_mul_le
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eLpNorm_indicatorPou_mul_le target :: scope.openDecls } }


omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
private lemma eLpNorm_indicatorPou_mul_le_uniform
    (g : SmoothRiemannianMetric I M) (α : M)
    {c : EuclN → ℝ}
    (hc : ContDiffOn ℝ ∞ c (chartTargetEuclid (I := I) (M := M) α)) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ w : EuclN → ℝ,
        _root_.MeasureTheory.eLpNorm
            (fun y => Set.indicator (chartPouKernel (I := I) (M := M) α) c y *
              w y) 2
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
  obtain ⟨C, hC_nn, hC_bd⟩ :=
    exists_bound_on_chartPouKernel (I := I) (M := M) α hc
  refine ⟨C, hC_nn, fun w => ?_⟩
  have hci_bd : ∀ y : EuclN,
      ‖Set.indicator (chartPouKernel (I := I) (M := M) α) c y‖ ≤ C := by
    intro y
    by_cases hy : y ∈ chartPouKernel (I := I) (M := M) α
    · rw [Set.indicator_of_mem hy]; exact hC_bd y hy
    · rw [Set.indicator_of_notMem hy, norm_zero]; exact hC_nn
  have h_dom : ∀ᵐ y ∂μw,
      ‖Set.indicator (chartPouKernel (I := I) (M := M) α) c y * w y‖ ≤
        ‖(C : ℝ) • w y‖ := by
    refine Filter.Eventually.of_forall (fun y => ?_)
    have hlhs :
        ‖Set.indicator (chartPouKernel (I := I) (M := M) α) c y * w y‖ =
          ‖Set.indicator (chartPouKernel (I := I) (M := M) α) c y‖ * ‖w y‖ :=
      norm_mul _ _
    have hrhs : ‖(C : ℝ) • w y‖ = C * ‖w y‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hC_nn]
    rw [hlhs, hrhs]
    exact mul_le_mul_of_nonneg_right (hci_bd y) (norm_nonneg _)
  have h_mono :
      _root_.MeasureTheory.eLpNorm
          (fun y => Set.indicator (chartPouKernel (I := I) (M := M) α) c y * w y)
          2 μw
        ≤ _root_.MeasureTheory.eLpNorm (fun y => (C : ℝ) • w y) 2 μw :=
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
    _root_.MeasureTheory.eLpNorm
        (fun y => Set.indicator (chartPouKernel (I := I) (M := M) α) c y * w y)
        2 μw
        ≤ _root_.MeasureTheory.eLpNorm (fun y => (C : ℝ) • w y) 2 μw := h_mono
    _ = ENNReal.ofReal C * _root_.MeasureTheory.eLpNorm w 2 μw := h_smul

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eLpNorm_indicatorPou_mul_le_uniform
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eLpNorm_indicatorPou_mul_le_uniform target :: scope.openDecls } }

end PerSummandBound

section MeasurabilityTransfer


omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] in
private lemma aestronglyMeasurable_weighted_of_chartL2
    (g : SmoothRiemannianMetric I M) (α : M)
    {f : EuclN → ℝ}
    (hf : _root_.MeasureTheory.AEStronglyMeasurable f (chartLebesgueMeasure (I := I) (M := M) α)) :
    _root_.MeasureTheory.AEStronglyMeasurable f
      ((chartPulledWeightedMeasure (I := I) g α).restrict
        (chartTargetEuclid (I := I) (M := M) α)) :=
  hf.mono_ac
    (chartPulledWeightedMeasure_restrict_absolutelyContinuous (I := I) (M := M)
      g α)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.aestronglyMeasurable_weighted_of_chartL2
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.aestronglyMeasurable_weighted_of_chartL2 target :: scope.openDecls } }

end MeasurabilityTransfer

section UniformConstant


omit [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)] in
private lemma exists_uniform_eLpNorm_bound
    {ι : Type*} [Finite ι]
    {μ : _root_.MeasureTheory.Measure EuclN} {f : ι → EuclN → ℝ} {a : ι → ℝ≥0∞}
    (h : ∀ j : ι, ∃ C : ℝ, 0 ≤ C ∧ _root_.MeasureTheory.eLpNorm (f j) 2 μ ≤ ENNReal.ofReal C * a j) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ j : ι, _root_.MeasureTheory.eLpNorm (f j) 2 μ ≤ ENNReal.ofReal C * a j := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  choose Cf hCf_nn hCf using h
  refine ⟨∑ j : ι, Cf j, Finset.sum_nonneg (fun j _ => hCf_nn j), fun j => ?_⟩
  refine (hCf j).trans (mul_le_mul_left ?_ (a j))
  exact ENNReal.ofReal_le_ofReal
    (Finset.single_le_sum (fun k _ => hCf_nn k) (Finset.mem_univ j))

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.exists_uniform_eLpNorm_bound
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.exists_uniform_eLpNorm_bound target :: scope.openDecls } }

end UniformConstant

section MainBound

omit [CompleteSpace E] in
theorem eLpNorm_crossRightGradCoeffDivLimit_le_uniform
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
        eLpNorm (crossRightGradCoeffDivLimit (I := I) (M := M)
            g r s i α P₀) 2
            ((chartPulledWeightedMeasure (I := I) g α).restrict
              (chartTargetEuclid (I := I) (M := M) α))
          ≤ ENNReal.ofReal C *
            ((∑ P : TensorCompIdx (E := E) r s,
                eLpNorm ((crossRightLimitComponent (I := I) (M := M)
                    g r s i α P :
                    Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) : EuclN → ℝ) 2
                  ((chartPulledWeightedMeasure (I := I) g α).restrict
                    (chartTargetEuclid (I := I) (M := M) α)))
              + (∑ P : TensorCompIdx (E := E) r s,
                  ∑ l : Fin (Module.finrank ℝ E),
                    eLpNorm ((cutoffPartialLpLimit (I := I) (M := M)
                        g r s i α P l :
                        Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) :
                        EuclN → ℝ) 2
                      ((chartPulledWeightedMeasure (I := I) g α).restrict
                        (chartTargetEuclid (I := I) (M := M) α)))) := by
  classical
  set ι : Type _ :=
    Fin (Module.finrank ℝ E) × TensorCompIdx (E := E) r s ×
      TensorCompIdx (E := E) r s with hι_def
  choose CcompF hCcompF_nn hCcompF using
    (fun j : ι => eLpNorm_indicatorPou_mul_le_uniform (I := I) (M := M) g α
      (euclidPartial_crossRightDivFactor_contDiffOn (I := I) (M := M)
        g r s α P₀ j.1 j.2.1 j.2.2))
  choose CpartF hCpartF_nn hCpartF using
    (fun j : ι => eLpNorm_indicatorPou_mul_le_uniform (I := I) (M := M) g α
      (crossRightDivFactor_contDiffOn (I := I) (M := M)
        g r s α P₀ j.1 j.2.1 j.2.2))
  refine ⟨max ((Fintype.card ι : ℝ) * ∑ j : ι, CcompF j)
      ((Fintype.card ι : ℝ) * ∑ j : ι, CpartF j),
    le_max_of_le_left (mul_nonneg (by positivity)
      (Finset.sum_nonneg (fun j _ => hCcompF_nn j))), fun i => ?_⟩
  set μw : _root_.MeasureTheory.Measure EuclN :=
    (chartPulledWeightedMeasure (I := I) g α).restrict
      (chartTargetEuclid (I := I) (M := M) α) with hμw_def
  set Acomp : TensorCompIdx (E := E) r s → EuclN → ℝ :=
    fun P => ((crossRightLimitComponent (I := I) (M := M)
      g r s i α P :
      Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) : EuclN → ℝ) with hAcomp_def
  set Apart : TensorCompIdx (E := E) r s → Fin (Module.finrank ℝ E) → EuclN → ℝ :=
    fun P l => ((cutoffPartialLpLimit (I := I) (M := M)
      g r s i α P l :
      Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) : EuclN → ℝ) with hApart_def
  set Sumcomp : ℝ≥0∞ :=
    ∑ P : TensorCompIdx (E := E) r s, _root_.MeasureTheory.eLpNorm (Acomp P) 2 μw with hSumcomp_def
  set Sumpart : ℝ≥0∞ :=
    ∑ P : TensorCompIdx (E := E) r s,
      ∑ l : Fin (Module.finrank ℝ E), _root_.MeasureTheory.eLpNorm (Apart P l) 2 μw with hSumpart_def
  set summandComp : ι → EuclN → ℝ :=
    fun j y => Set.indicator (chartPouKernel (I := I) (M := M) α)
        (euclidPartial (E := E) j.1
          (crossRightDivFactor (I := I) (M := M) g r s α P₀ j.1 j.2.1 j.2.2)) y *
      Acomp j.2.1 y with hsummandComp_def
  set summandPart : ι → EuclN → ℝ :=
    fun j y => Set.indicator (chartPouKernel (I := I) (M := M) α)
        (crossRightDivFactor (I := I) (M := M) g r s α P₀ j.1 j.2.1 j.2.2) y *
      Apart j.2.1 j.1 y with hsummandPart_def
  set Ccomp : ℝ := ∑ j : ι, CcompF j with hCcomp_def
  set Cpart : ℝ := ∑ j : ι, CpartF j with hCpart_def
  have hCcomp_nn : 0 ≤ Ccomp :=
    Finset.sum_nonneg (fun j _ => hCcompF_nn j)
  have hCpart_nn : 0 ≤ Cpart :=
    Finset.sum_nonneg (fun j _ => hCpartF_nn j)
  have hCcomp : ∀ j : ι,
      _root_.MeasureTheory.eLpNorm (summandComp j) 2 μw ≤
        ENNReal.ofReal Ccomp * _root_.MeasureTheory.eLpNorm (Acomp j.2.1) 2 μw := by
    intro j
    refine le_trans (hCcompF j (Acomp j.2.1)) ?_
    gcongr
    rw [hCcomp_def]
    exact Finset.single_le_sum (fun k _ => hCcompF_nn k) (Finset.mem_univ j)
  have hCpart : ∀ j : ι,
      _root_.MeasureTheory.eLpNorm (summandPart j) 2 μw ≤
        ENNReal.ofReal Cpart * _root_.MeasureTheory.eLpNorm (Apart j.2.1 j.1) 2 μw := by
    intro j
    refine le_trans (hCpartF j (Apart j.2.1 j.1)) ?_
    gcongr
    rw [hCpart_def]
    exact Finset.single_le_sum (fun k _ => hCpartF_nn k) (Finset.mem_univ j)
  have hAcomp_meas : ∀ P : TensorCompIdx (E := E) r s,
      AEStronglyMeasurable (Acomp P) μw := by
    intro P
    rw [hAcomp_def, hμw_def]
    exact aestronglyMeasurable_weighted_of_chartL2 (I := I) (M := M) g α
      (Lp.aestronglyMeasurable _)
  have hApart_meas : ∀ (P : TensorCompIdx (E := E) r s)
      (l : Fin (Module.finrank ℝ E)),
      AEStronglyMeasurable (Apart P l) μw := by
    intro P l
    rw [hApart_def, hμw_def]
    exact aestronglyMeasurable_weighted_of_chartL2 (I := I) (M := M) g α
      (Lp.aestronglyMeasurable _)
  have hsummandComp_meas : ∀ j, _root_.MeasureTheory.AEStronglyMeasurable (summandComp j) μw := by
    intro j
    rw [hsummandComp_def]
    refine AEStronglyMeasurable.mul ?_ (hAcomp_meas j.2.1)
    rw [hμw_def]
    exact aestronglyMeasurable_weighted_of_chartL2 (I := I) (M := M) g α
      (aestronglyMeasurable_indicator_mul (I := I) (M := M) α
        (euclidPartial_crossRightDivFactor_contDiffOn (I := I) (M := M)
          g r s α P₀ j.1 j.2.1 j.2.2))
  have hsummandPart_meas : ∀ j, _root_.MeasureTheory.AEStronglyMeasurable (summandPart j) μw := by
    intro j
    rw [hsummandPart_def]
    refine AEStronglyMeasurable.mul ?_ (hApart_meas j.2.1 j.1)
    rw [hμw_def]
    exact aestronglyMeasurable_weighted_of_chartL2 (I := I) (M := M) g α
      (aestronglyMeasurable_indicator_mul (I := I) (M := M) α
        (crossRightDivFactor_contDiffOn (I := I) (M := M)
          g r s α P₀ j.1 j.2.1 j.2.2))
  have h_funcA :
      (fun y => ∑ l : Fin (Module.finrank ℝ E),
          ∑ P : TensorCompIdx (E := E) r s,
            ∑ Q : TensorCompIdx (E := E) r s,
              Set.indicator (chartPouKernel (I := I) (M := M) α)
                  (euclidPartial (E := E) l
                    (crossRightDivFactor (I := I) (M := M)
                      g r s α P₀ l P Q)) y *
                (crossRightLimitComponent (I := I) (M := M)
                  g r s i α P :
                  EuclN → ℝ) y)
        = ∑ j : ι, summandComp j := by
    funext y
    rw [Finset.sum_apply]
    rw [show (Finset.univ : Finset ι) =
        (Finset.univ : Finset (Fin (Module.finrank ℝ E))) ×ˢ
          (Finset.univ : Finset (TensorCompIdx (E := E) r s ×
            TensorCompIdx (E := E) r s)) from
      (Finset.univ_product_univ).symm]
    rw [Finset.sum_product]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [show (Finset.univ : Finset (TensorCompIdx (E := E) r s ×
          TensorCompIdx (E := E) r s)) =
        (Finset.univ : Finset (TensorCompIdx (E := E) r s)) ×ˢ
          (Finset.univ : Finset (TensorCompIdx (E := E) r s)) from
      (Finset.univ_product_univ).symm]
    rw [Finset.sum_product]
  have h_funcB :
      (fun y => ∑ l : Fin (Module.finrank ℝ E),
          ∑ P : TensorCompIdx (E := E) r s,
            ∑ Q : TensorCompIdx (E := E) r s,
              Set.indicator (chartPouKernel (I := I) (M := M) α)
                  (crossRightDivFactor (I := I) (M := M)
                    g r s α P₀ l P Q) y *
                (cutoffPartialLpLimit (I := I) (M := M)
                  g r s i α P l :
                  EuclN → ℝ) y)
        = ∑ j : ι, summandPart j := by
    funext y
    rw [Finset.sum_apply]
    rw [show (Finset.univ : Finset ι) =
        (Finset.univ : Finset (Fin (Module.finrank ℝ E))) ×ˢ
          (Finset.univ : Finset (TensorCompIdx (E := E) r s ×
            TensorCompIdx (E := E) r s)) from
      (Finset.univ_product_univ).symm]
    rw [Finset.sum_product]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [show (Finset.univ : Finset (TensorCompIdx (E := E) r s ×
          TensorCompIdx (E := E) r s)) =
        (Finset.univ : Finset (TensorCompIdx (E := E) r s)) ×ˢ
          (Finset.univ : Finset (TensorCompIdx (E := E) r s)) from
      (Finset.univ_product_univ).symm]
    rw [Finset.sum_product]
  have h_triangle :
      eLpNorm (crossRightGradCoeffDivLimit (I := I) (M := M)
          g r s i α P₀) 2 μw
        ≤ (∑ j : ι, _root_.MeasureTheory.eLpNorm (summandComp j) 2 μw)
          + (∑ j : ι, _root_.MeasureTheory.eLpNorm (summandPart j) 2 μw) := by
    have h_split : crossRightGradCoeffDivLimit (I := I) (M := M)
        g r s i α P₀ =
        (∑ j : ι, summandComp j) + (∑ j : ι, summandPart j) := by
      rw [← h_funcA, ← h_funcB]
      rfl
    rw [h_split]
    refine le_trans (_root_.MeasureTheory.eLpNorm_add_le ?_ ?_ (by norm_num)) (add_le_add ?_ ?_)
    · exact Finset.aestronglyMeasurable_sum _ (fun j _ => hsummandComp_meas j)
    · exact Finset.aestronglyMeasurable_sum _ (fun j _ => hsummandPart_meas j)
    · exact _root_.MeasureTheory.eLpNorm_sum_le (fun j _ => hsummandComp_meas j) (by norm_num)
    · exact _root_.MeasureTheory.eLpNorm_sum_le (fun j _ => hsummandPart_meas j) (by norm_num)
  have h_groupA :
      (∑ j : ι, _root_.MeasureTheory.eLpNorm (summandComp j) 2 μw)
        ≤ ENNReal.ofReal ((Fintype.card ι : ℝ) * Ccomp) * Sumcomp := by
    have h_each : ∀ j : ι,
        eLpNorm (summandComp j) 2 μw ≤ ENNReal.ofReal Ccomp * Sumcomp := by
      intro j
      refine (hCcomp j).trans (mul_le_mul_right ?_ (ENNReal.ofReal Ccomp))
      rw [hSumcomp_def]
      exact Finset.single_le_sum (f := fun P => _root_.MeasureTheory.eLpNorm (Acomp P) 2 μw)
        (fun P _ => zero_le) (Finset.mem_univ j.2.1)
    refine le_trans (Finset.sum_le_sum (fun j _ => h_each j)) ?_
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast, mul_assoc]
  have h_groupB :
      (∑ j : ι, _root_.MeasureTheory.eLpNorm (summandPart j) 2 μw)
        ≤ ENNReal.ofReal ((Fintype.card ι : ℝ) * Cpart) * Sumpart := by
    have h_each : ∀ j : ι,
        eLpNorm (summandPart j) 2 μw ≤ ENNReal.ofReal Cpart * Sumpart := by
      intro j
      refine (hCpart j).trans (mul_le_mul_right ?_ (ENNReal.ofReal Cpart))
      rw [hSumpart_def]
      refine le_trans ?_
        (Finset.single_le_sum (f := fun P => ∑ l : Fin (Module.finrank ℝ E),
          _root_.MeasureTheory.eLpNorm (Apart P l) 2 μw)
          (fun P _ => zero_le) (Finset.mem_univ j.2.1))
      exact Finset.single_le_sum (f := fun l => _root_.MeasureTheory.eLpNorm (Apart j.2.1 l) 2 μw)
        (fun l _ => zero_le) (Finset.mem_univ j.1)
    refine le_trans (Finset.sum_le_sum (fun j _ => h_each j)) ?_
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast, mul_assoc]
  have hCcomp_le :
      ENNReal.ofReal ((Fintype.card ι : ℝ) * Ccomp) ≤
        ENNReal.ofReal
          (_root_.Max.max ((Fintype.card ι : ℝ) * Ccomp) ((Fintype.card ι : ℝ) * Cpart)) :=
    ENNReal.ofReal_le_ofReal (le_max_left _ _)
  have hCpart_le :
      ENNReal.ofReal ((Fintype.card ι : ℝ) * Cpart) ≤
        ENNReal.ofReal
          (_root_.Max.max ((Fintype.card ι : ℝ) * Ccomp) ((Fintype.card ι : ℝ) * Cpart)) :=
    ENNReal.ofReal_le_ofReal (le_max_right _ _)
  calc
    eLpNorm (crossRightGradCoeffDivLimit (I := I) (M := M)
        g r s i α P₀) 2 μw
        ≤ (∑ j : ι, _root_.MeasureTheory.eLpNorm (summandComp j) 2 μw)
          + (∑ j : ι, _root_.MeasureTheory.eLpNorm (summandPart j) 2 μw) := h_triangle
    _ ≤ ENNReal.ofReal ((Fintype.card ι : ℝ) * Ccomp) * Sumcomp
          + ENNReal.ofReal ((Fintype.card ι : ℝ) * Cpart) * Sumpart :=
        add_le_add h_groupA h_groupB
    _ ≤ ENNReal.ofReal
            (_root_.Max.max ((Fintype.card ι : ℝ) * Ccomp)
              ((Fintype.card ι : ℝ) * Cpart)) * Sumcomp
          + ENNReal.ofReal
              (_root_.Max.max ((Fintype.card ι : ℝ) * Ccomp)
                ((Fintype.card ι : ℝ) * Cpart)) * Sumpart :=
        add_le_add (mul_le_mul_left hCcomp_le _)
          (mul_le_mul_left hCpart_le _)
    _ = ENNReal.ofReal
            (_root_.Max.max ((Fintype.card ι : ℝ) * Ccomp)
              ((Fintype.card ι : ℝ) * Cpart)) * (Sumcomp + Sumpart) :=
        (mul_add _ _ _).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eLpNorm_crossRightGradCoeffDivLimit_le_uniform then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eLpNorm_crossRightGradCoeffDivLimit_le_uniform"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eLpNorm_crossRightGradCoeffDivLimit_le_uniform ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eLpNorm_crossRightGradCoeffDivLimit_le_uniform

end MainBound

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
