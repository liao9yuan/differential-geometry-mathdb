import Submission.DifferentialGeometry.Analysis.Sobolev.Embedding.Reverse.Hebey
import Submission.DifferentialGeometry.Analysis.Sobolev.TensorHilbert.Hilbert.Defs

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.MeasureTheory _root_.Set _root_.Filter _root_.Topology
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.ENNReal _root_.NNReal _root_.BigOperators

namespace DifferentialGeometry.Analysis.Sobolev

open _root_.Submission.DifferentialGeometry.Integral.L2
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.Tensor

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

omit [BoundarylessManifold I M] in
theorem exists_toHs_norm_le_iteratedCovGrad_tensorL2Norm_sum
    (g : SmoothRiemannianMetric I M) (r s k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ T : SmoothCcTensor g r s,
        ‖DifferentialGeometry.Analysis.Sobolev.IntrinsicSobolev.SmoothCcTensor.toHs (g := g)
          (r := r) (s := s) k T‖ ≤
          C * ∑ j ∈ Finset.range (2 * k + 1),
            tensorL2Norm (I := I) (M := M) g r (s + j)
              (iteratedCovGrad g r s j T).toFun := by
  obtain ⟨C, hC_nn, hC⟩ :=
    exists_tensorPouSobolevHsNorm_toReal_le_iteratedCovGrad_tensorL2Norm_sum
      (I := I) (M := M) g r s k
  refine ⟨C, hC_nn, fun T => ?_⟩
  rw [DifferentialGeometry.Analysis.Sobolev.IntrinsicSobolev.tensorPouSobolevHilbert_norm_eq]
  exact hC T

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.exists_toHs_norm_le_iteratedCovGrad_tensorL2Norm_sum then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.exists_toHs_norm_le_iteratedCovGrad_tensorL2Norm_sum"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.exists_toHs_norm_le_iteratedCovGrad_tensorL2Norm_sum ``Submission.DifferentialGeometry.Analysis.Sobolev.exists_toHs_norm_le_iteratedCovGrad_tensorL2Norm_sum

end DifferentialGeometry.Analysis.Sobolev

end
