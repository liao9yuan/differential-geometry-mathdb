import Submission.DifferentialGeometry.Analysis.Sobolev.Tensor.Chart.Components
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission


noncomputable section


open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.MeasureTheory _root_.Set _root_.Filter _root_.Submission.DifferentialGeometry.Tensor0SBundle
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.ENNReal _root_.BigOperators

namespace DifferentialGeometry
namespace Analysis
namespace Sobolev
namespace Tensor

open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.L2
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.Chart
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

noncomputable def tensorPouSobolevNorm
    (g : SmoothRiemannianMetric I M) {r s : ℕ}
    (k : ℕ) (T : SmoothCcTensor g r s) : ℝ≥0∞ :=
  (∑' α : M,
    ∑ IJ : (Fin r → Fin (Module.finrank ℝ E)) ×
        (Fin s → Fin (Module.finrank ℝ E)),
      ∑ j ∈ Finset.range (2 * k + 1),
        ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
          ENNReal.ofReal
            (((chartAtlasPOU I M α : M → ℝ)
                ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
              ‖iteratedFDeriv ℝ j
                  (tensorChartComponentRaw (I := I) (M := M) g r s T α IJ.1 IJ.2
                    ∘ (extChartAt I α).symm)
                  ((toEuclidean (E := E)).symm y)‖ ^ 2)
          ∂(_root_.MeasureTheory.MeasureSpace.volume :
            _root_.MeasureTheory.Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))))) ^ (1 / 2 : ℝ)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Tensor.tensorPouSobolevNorm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Tensor.tensorPouSobolevNorm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Tensor.tensorPouSobolevNorm ``Submission.DifferentialGeometry.Analysis.Sobolev.Tensor.tensorPouSobolevNorm

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
theorem tensorPouSobolevNorm_eq
    (g : SmoothRiemannianMetric I M) {r s : ℕ}
    (k : ℕ) (T : SmoothCcTensor g r s) :
    tensorPouSobolevNorm (I := I) (M := M) g k T =
      (∑' α : M,
        ∑ IJ : (Fin r → Fin (Module.finrank ℝ E)) ×
            (Fin s → Fin (Module.finrank ℝ E)),
          ∑ j ∈ Finset.range (2 * k + 1),
            ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
              ENNReal.ofReal
                (((chartAtlasPOU I M α : M → ℝ)
                    ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
                  ‖iteratedFDeriv ℝ j
                      (tensorChartComponentRaw (I := I) (M := M) g r s T α
                          IJ.1 IJ.2
                        ∘ (extChartAt I α).symm)
                      ((toEuclidean (E := E)).symm y)‖ ^ 2)
              ∂(_root_.MeasureTheory.MeasureSpace.volume :
                _root_.MeasureTheory.Measure (EuclideanSpace ℝ
                  (Fin (Module.finrank ℝ E))))) ^ (1 / 2 : ℝ) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Tensor.tensorPouSobolevNorm_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Tensor.tensorPouSobolevNorm_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Tensor.tensorPouSobolevNorm_eq ``Submission.DifferentialGeometry.Analysis.Sobolev.Tensor.tensorPouSobolevNorm_eq

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
theorem tensorPouSobolevNorm_nonneg
    (g : SmoothRiemannianMetric I M) {r s : ℕ}
    (k : ℕ) (T : SmoothCcTensor g r s) :
    0 ≤ tensorPouSobolevNorm (I := I) (M := M) g k T :=
  zero_le

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Tensor.tensorPouSobolevNorm_nonneg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Tensor.tensorPouSobolevNorm_nonneg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Tensor.tensorPouSobolevNorm_nonneg ``Submission.DifferentialGeometry.Analysis.Sobolev.Tensor.tensorPouSobolevNorm_nonneg

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
private lemma tensorChartComponentRaw_zero_section
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    tensorChartComponentRaw (I := I) (M := M) g r s
        (0 : SmoothCcTensor g r s) α Idx Jdx = (fun _ : M => 0) := by
  classical
  funext x
  have h := tensorChartComponent_smul (I := I) (M := M) g r s (0 : ℝ)
    (0 : SmoothCcTensor g r s) α Idx Jdx
  unfold tensorChartComponentRaw
  have h0 : (_root_.FiberBundle.trivializationAt (TensorRSModel r s ℝ E)
        (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ x
          ((0 : SmoothCcTensor g r s).toSection x) = 0 := by
    have hsec : (0 : SmoothCcTensor g r s).toSection x = 0 := by rfl
    rw [hsec]
    exact ContinuousLinearMap.map_zero _
  change tensorChartComponentProjection (E := E) r s Idx Jdx
      (tensorTrivProj (I := I) (M := M) g r s
        (0 : SmoothCcTensor g r s) α x) = 0
  unfold tensorTrivProj
  rw [h0]
  exact ContinuousLinearMap.map_zero _

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.Tensor.tensorChartComponentRaw_zero_section
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.Tensor.tensorChartComponentRaw_zero_section target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
private lemma tensorChartComponentRaw_comp_zero_section
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    (tensorChartComponentRaw (I := I) (M := M) g r s
        (0 : SmoothCcTensor g r s) α Idx Jdx ∘ (extChartAt I α).symm) =
      (fun _ : E => (0 : ℝ)) := by
  funext x
  change tensorChartComponentRaw (I := I) (M := M) g r s
      (0 : SmoothCcTensor g r s) α Idx Jdx ((extChartAt I α).symm x) = 0
  rw [tensorChartComponentRaw_zero_section (I := I) (M := M) g r s α Idx Jdx]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.Tensor.tensorChartComponentRaw_comp_zero_section
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.Tensor.tensorChartComponentRaw_comp_zero_section target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
theorem tensorPouSobolevNorm_zero_section
    (g : SmoothRiemannianMetric I M) {r s : ℕ} (k : ℕ) :
    tensorPouSobolevNorm (I := I) (M := M) g k
        (0 : SmoothCcTensor g r s) = 0 := by
  classical
  rw [tensorPouSobolevNorm_eq]
  have htsum :
      (∑' α : M,
        ∑ IJ : (Fin r → Fin (Module.finrank ℝ E)) ×
            (Fin s → Fin (Module.finrank ℝ E)),
          ∑ j ∈ Finset.range (2 * k + 1),
            ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
              ENNReal.ofReal
                (((chartAtlasPOU I M α : M → ℝ)
                    ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
                  ‖iteratedFDeriv ℝ j
                      (tensorChartComponentRaw (I := I) (M := M) g r s
                          (0 : SmoothCcTensor g r s) α IJ.1 IJ.2
                        ∘ (extChartAt I α).symm)
                      ((toEuclidean (E := E)).symm y)‖ ^ 2)
              ∂(_root_.MeasureTheory.MeasureSpace.volume :
                _root_.MeasureTheory.Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))))) =
        0 := by
    have hpt : ∀ α : M,
        (∑ IJ : (Fin r → Fin (Module.finrank ℝ E)) ×
            (Fin s → Fin (Module.finrank ℝ E)),
          ∑ j ∈ Finset.range (2 * k + 1),
            ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
              ENNReal.ofReal
                (((chartAtlasPOU I M α : M → ℝ)
                    ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
                  ‖iteratedFDeriv ℝ j
                      (tensorChartComponentRaw (I := I) (M := M) g r s
                          (0 : SmoothCcTensor g r s) α IJ.1 IJ.2
                        ∘ (extChartAt I α).symm)
                      ((toEuclidean (E := E)).symm y)‖ ^ 2)
              ∂(_root_.MeasureTheory.MeasureSpace.volume :
                _root_.MeasureTheory.Measure (EuclideanSpace ℝ
                  (Fin (Module.finrank ℝ E))))) = 0 := by
      intro α
      refine Finset.sum_eq_zero ?_
      intro IJ _
      refine Finset.sum_eq_zero ?_
      intro j _
      have hraw := tensorChartComponentRaw_comp_zero_section
        (I := I) (M := M) g r s α IJ.1 IJ.2
      have hiter : iteratedFDeriv ℝ j
          (tensorChartComponentRaw (I := I) (M := M) g r s
              (0 : SmoothCcTensor g r s) α IJ.1 IJ.2
            ∘ (extChartAt I α).symm) = 0 := by
        rw [hraw]
        exact iteratedFDeriv_fun_zero
      have hintegrand_zero :
          (fun y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) =>
            ENNReal.ofReal
              (((chartAtlasPOU I M α : M → ℝ)
                  ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
                ‖iteratedFDeriv ℝ j
                    (tensorChartComponentRaw (I := I) (M := M) g r s
                        (0 : SmoothCcTensor g r s) α IJ.1 IJ.2
                      ∘ (extChartAt I α).symm)
                    ((toEuclidean (E := E)).symm y)‖ ^ 2)) =
            (fun _ => 0) := by
        funext y
        rw [hiter]
        simp
      rw [hintegrand_zero]
      simp
    rw [tsum_congr hpt]
    exact tsum_zero
  rw [htsum]
  exact ENNReal.zero_rpow_of_pos (by norm_num)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Tensor.tensorPouSobolevNorm_zero_section then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Tensor.tensorPouSobolevNorm_zero_section"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Tensor.tensorPouSobolevNorm_zero_section ``Submission.DifferentialGeometry.Analysis.Sobolev.Tensor.tensorPouSobolevNorm_zero_section

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
theorem tensorPouSobolevNorm_le_succ
    (g : SmoothRiemannianMetric I M) {r s : ℕ}
    (k : ℕ) (T : SmoothCcTensor g r s) :
    tensorPouSobolevNorm (I := I) (M := M) g k T ≤
      tensorPouSobolevNorm (I := I) (M := M) g (k + 1) T := by
  classical
  rw [tensorPouSobolevNorm_eq, tensorPouSobolevNorm_eq]
  have hrange : Finset.range (2 * k + 1) ⊆ Finset.range (2 * (k + 1) + 1) :=
    Finset.range_subset_range.mpr (by omega)
  have hper_chart : ∀ α : M,
      (∑ IJ : (Fin r → Fin (Module.finrank ℝ E)) ×
          (Fin s → Fin (Module.finrank ℝ E)),
        ∑ j ∈ Finset.range (2 * k + 1),
          ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
            ENNReal.ofReal
              (((chartAtlasPOU I M α : M → ℝ)
                  ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
                ‖iteratedFDeriv ℝ j
                    (tensorChartComponentRaw (I := I) (M := M) g r s T α
                        IJ.1 IJ.2
                      ∘ (extChartAt I α).symm)
                    ((toEuclidean (E := E)).symm y)‖ ^ 2)
            ∂(_root_.MeasureTheory.MeasureSpace.volume :
              _root_.MeasureTheory.Measure (EuclideanSpace ℝ
                (Fin (Module.finrank ℝ E))))) ≤
      (∑ IJ : (Fin r → Fin (Module.finrank ℝ E)) ×
          (Fin s → Fin (Module.finrank ℝ E)),
        ∑ j ∈ Finset.range (2 * (k + 1) + 1),
          ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
            ENNReal.ofReal
              (((chartAtlasPOU I M α : M → ℝ)
                  ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
                ‖iteratedFDeriv ℝ j
                    (tensorChartComponentRaw (I := I) (M := M) g r s T α
                        IJ.1 IJ.2
                      ∘ (extChartAt I α).symm)
                    ((toEuclidean (E := E)).symm y)‖ ^ 2)
            ∂(_root_.MeasureTheory.MeasureSpace.volume :
              _root_.MeasureTheory.Measure (EuclideanSpace ℝ
                (Fin (Module.finrank ℝ E))))) := by
    intro α
    refine Finset.sum_le_sum ?_
    intro IJ _
    exact Finset.sum_le_sum_of_subset_of_nonneg hrange
      (by intro j _ _; exact zero_le)
  have htsum_le :
      (∑' α : M,
        ∑ IJ : (Fin r → Fin (Module.finrank ℝ E)) ×
            (Fin s → Fin (Module.finrank ℝ E)),
          ∑ j ∈ Finset.range (2 * k + 1),
            ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
              ENNReal.ofReal
                (((chartAtlasPOU I M α : M → ℝ)
                    ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
                  ‖iteratedFDeriv ℝ j
                      (tensorChartComponentRaw (I := I) (M := M) g r s T α
                          IJ.1 IJ.2
                        ∘ (extChartAt I α).symm)
                      ((toEuclidean (E := E)).symm y)‖ ^ 2)
              ∂(_root_.MeasureTheory.MeasureSpace.volume :
                _root_.MeasureTheory.Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))))) ≤
        (∑' α : M,
          ∑ IJ : (Fin r → Fin (Module.finrank ℝ E)) ×
              (Fin s → Fin (Module.finrank ℝ E)),
            ∑ j ∈ Finset.range (2 * (k + 1) + 1),
              ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
                ENNReal.ofReal
                  (((chartAtlasPOU I M α : M → ℝ)
                      ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
                    ‖iteratedFDeriv ℝ j
                        (tensorChartComponentRaw (I := I) (M := M) g r s T α
                            IJ.1 IJ.2
                          ∘ (extChartAt I α).symm)
                        ((toEuclidean (E := E)).symm y)‖ ^ 2)
                ∂(_root_.MeasureTheory.MeasureSpace.volume :
                  _root_.MeasureTheory.Measure (EuclideanSpace ℝ
                    (Fin (Module.finrank ℝ E))))) := by
    exact ENNReal.tsum_le_tsum hper_chart
  exact ENNReal.rpow_le_rpow htsum_le (by norm_num)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Tensor.tensorPouSobolevNorm_le_succ then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Tensor.tensorPouSobolevNorm_le_succ"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Tensor.tensorPouSobolevNorm_le_succ ``Submission.DifferentialGeometry.Analysis.Sobolev.Tensor.tensorPouSobolevNorm_le_succ

end Tensor
end Sobolev
end Analysis
end DifferentialGeometry
