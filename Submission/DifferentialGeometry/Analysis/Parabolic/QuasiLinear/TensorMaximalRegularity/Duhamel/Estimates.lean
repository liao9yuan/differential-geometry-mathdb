import Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.Solution.TimeSupremumTrace

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Set _root_.Filter
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.ENNReal _root_.BigOperators
  RealInnerProductSpace InnerProductSpace NNReal

namespace DifferentialGeometry.Analysis.Parabolic

open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.MaximalRegularity
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear
open _root_.Submission.DifferentialGeometry.Analysis.Spectral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M]
  [SigmaCompactSpace M]

variable {g₀ : SmoothRiemannianMetric I M}

omit [BoundarylessManifold I M] in
theorem timeL2Inclusion_maximalRegularityDuhamelSolutionField {a : ℝ} {T : ℝ}
    (hT : 0 < T) (hT1 : T ≤ 1) {r s : ℕ}
    (u₀ : TensorHs (I := I) (M := M) g₀ r s (a + 2))
    (gforce : timeL2 (TensorHs (I := I) (M := M) g₀ r s a) T) :
    timeL2Inclusion (I := I) (M := M) (g := g₀) (r := r) (s := s)
        (show a + 1 ≤ a + 2 by linarith)
        (maximalRegularityDuhamelSolutionField (I := I) (M := M) (g := g₀) (r := r) (s := s)
          (T := T) a hT u₀ gforce) =
      maximalRegularityDuhamelSolutionFieldHa1 (I := I) (M := M) (g := g₀) (r := r) (s := s)
        (T := T) a hT u₀ gforce := by
  have h_compact := tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ r s
  refine timeModeCoeff_injective (I := I) (M := M) h_compact (fun i => ?_)
  rw [timeModeCoeff_timeL2Inclusion (I := I) (M := M) (g := g₀) (r := r) (s := s)]
  rw [maximalRegularityDuhamelSolutionField, maximalRegularityDuhamelSolutionFieldHa1,
    timeModeCoeff_add (I := I) (M := M), timeModeCoeff_add (I := I) (M := M),
    maximalRegularityHomogeneousSolutionField_timeModeCoeff (I := I) (M := M) (a := a) (T := T) hT.le u₀ i,
    maximalRegularityHomogeneousSolutionFieldHa1_timeModeCoeff (I := I) (M := M) (a := a) (T := T) hT.le u₀ i,
    maximalRegularitySolutionField_timeModeCoeff (I := I) (M := M)
      (h_compact := h_compact) (a := a) hT.le gforce i,
    maximalRegularitySolutionFieldHa1_timeModeCoeff (I := I) (M := M)
      (h_compact := h_compact) (a := a) hT hT1 gforce i]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.timeL2Inclusion_maximalRegularityDuhamelSolutionField then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.timeL2Inclusion_maximalRegularityDuhamelSolutionField"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.timeL2Inclusion_maximalRegularityDuhamelSolutionField ``Submission.DifferentialGeometry.Analysis.Parabolic.timeL2Inclusion_maximalRegularityDuhamelSolutionField

omit [BoundarylessManifold I M] in
theorem norm_maximalRegularityDuhamelSolutionField_zero_le {a : ℝ} {T : ℝ}
    (hT : 0 < T) {r s : ℕ}
    (F : timeL2 (TensorHs (I := I) (M := M) g₀ r s a) T) :
    ‖maximalRegularityDuhamelSolutionField (I := I) (M := M) (g := g₀) (r := r) (s := s)
        (T := T) a hT
        (0 : TensorHs (I := I) (M := M) g₀ r s (a + 2)) F‖ ≤ (1 + T) * ‖F‖ := by
  have h_compact := tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ r s
  rw [maximalRegularityDuhamelSolutionField]
  refine le_trans (norm_add_le _ _) ?_
  have hhom : ‖maximalRegularityHomogeneousSolutionField (I := I) (M := M) a T
      (0 : TensorHs (I := I) (M := M) g₀ r s (a + 2))‖ ≤
      Real.sqrt T * ‖(0 : TensorHs (I := I) (M := M) g₀ r s (a + 2))‖ :=
    maximalRegularityHomogeneousSolutionField_norm_le (I := I) (M := M)
      (h_compact := h_compact) _ hT.le
  rw [norm_zero, _root_.MulZeroClass.mul_zero] at hhom
  have hreg : ‖maximalRegularitySolutionField (I := I) (M := M) a hT.le F‖ ≤
      (1 + T) * ‖F‖ :=
    maximalRegularitySolutionField_norm_le (I := I) (M := M)
      (h_compact := h_compact) hT.le F
  have hhom0 : ‖maximalRegularityHomogeneousSolutionField (I := I) (M := M) a T
      (0 : TensorHs (I := I) (M := M) g₀ r s (a + 2))‖ = 0 :=
    le_antisymm hhom (norm_nonneg _)
  rw [hhom0, zero_add]
  exact hreg

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.norm_maximalRegularityDuhamelSolutionField_zero_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.norm_maximalRegularityDuhamelSolutionField_zero_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.norm_maximalRegularityDuhamelSolutionField_zero_le ``Submission.DifferentialGeometry.Analysis.Parabolic.norm_maximalRegularityDuhamelSolutionField_zero_le

omit [BoundarylessManifold I M] in
theorem maximalRegularityDuhamelSolutionField_zero_zero {a : ℝ} {T : ℝ}
    (hT : 0 < T) {r s : ℕ} :
    maximalRegularityDuhamelSolutionField (I := I) (M := M) (g := g₀) (r := r) (s := s)
        (T := T) a hT
        (0 : TensorHs (I := I) (M := M) g₀ r s (a + 2))
        (0 : timeL2 (TensorHs (I := I) (M := M) g₀ r s a) T) = 0 := by
  have h := norm_maximalRegularityDuhamelSolutionField_zero_le (I := I) (M := M) (g₀ := g₀)
    hT (0 : timeL2 (TensorHs (I := I) (M := M) g₀ r s a) T)
  rw [norm_zero, _root_.MulZeroClass.mul_zero] at h
  exact norm_le_zero_iff.mp h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.maximalRegularityDuhamelSolutionField_zero_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.maximalRegularityDuhamelSolutionField_zero_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.maximalRegularityDuhamelSolutionField_zero_zero ``Submission.DifferentialGeometry.Analysis.Parabolic.maximalRegularityDuhamelSolutionField_zero_zero

end DifferentialGeometry.Analysis.Parabolic

end
