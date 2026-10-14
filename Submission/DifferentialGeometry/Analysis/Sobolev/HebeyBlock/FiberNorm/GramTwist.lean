import Submission.DifferentialGeometry.Geometry.Metric.Basic
import Submission.DifferentialGeometry.Geometry.Connection.ChartFrame.ChartMetric
import Submission.DifferentialGeometry.Analysis.Sobolev.Tensor.PartitionOfUnity.WeightedNorm
import Submission.DifferentialGeometry.Analysis.Sobolev.Tensor.PartitionOfUnity.WeightedSobolevNorm

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Geometry.Curvature


namespace DifferentialGeometry.Analysis.Sobolev.HebeyBlock

open _root_.Bundle _root_.Submission.Bundle
open scoped _root_.Manifold _root_.ContDiff
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.Tensor
open _root_.Submission.DifferentialGeometry.Integral.L2

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] in
theorem fibrewise_gram_twist_estimate
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧
      ∀ T : SmoothCcTensor g r s,
        c * (tensorPouSobolevNorm (I := I) (M := M) g 0 T).toReal ≤
            (tensorPouSobolevHsNorm (I := I) (M := M) g 0 T).toReal ∧
          (tensorPouSobolevHsNorm (I := I) (M := M) g 0 T).toReal ≤
            C * (tensorPouSobolevNorm (I := I) (M := M) g 0 T).toReal := by
  refine ⟨1, 1, by norm_num, le_refl 1, fun T => ?_⟩
  have hEq :
      tensorPouSobolevHsNorm (I := I) (M := M) g 0 T =
        tensorPouSobolevNorm (I := I) (M := M) g 0 T := by
    rw [tensorPouSobolevHsNorm_eq, tensorPouSobolevNorm_eq]
    congr 1
    refine tsum_congr (fun α => ?_)
    refine Finset.sum_congr rfl (fun IJ _ => ?_)
    refine Finset.sum_congr rfl (fun j hj => ?_)
    simp only [Finset.mem_range, Nat.mul_zero, Nat.zero_add] at hj
    interval_cases j
    rw [Finset.univ_unique, Finset.sum_singleton]
    refine MeasureTheory.lintegral_congr (fun y => ?_)
    congr 2
    rw [iteratedFDeriv_zero_apply, norm_iteratedFDeriv_zero, Real.norm_eq_abs]
    rfl
  rw [hEq]
  refine ⟨?_, ?_⟩
  · simp
  · simp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.HebeyBlock.fibrewise_gram_twist_estimate then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.HebeyBlock.fibrewise_gram_twist_estimate"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.HebeyBlock.fibrewise_gram_twist_estimate ``Submission.DifferentialGeometry.Analysis.Sobolev.HebeyBlock.fibrewise_gram_twist_estimate

end DifferentialGeometry.Analysis.Sobolev.HebeyBlock
