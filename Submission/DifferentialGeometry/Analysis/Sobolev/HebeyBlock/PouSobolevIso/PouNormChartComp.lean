import Submission.DifferentialGeometry.Analysis.Sobolev.TensorHilbert.Hilbert.Defs
import Submission.DifferentialGeometry.Analysis.Sobolev.HebeyBlock.ChartParallelTransportOpNorm.UniformChartBounds
import Submission.DifferentialGeometry.Analysis.Sobolev.HebeyBlock.FiberNorm.GramTwist

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission


namespace DifferentialGeometry.Analysis.Sobolev.HebeyBlock

open _root_.Bundle _root_.Submission.Bundle
open scoped _root_.Manifold _root_.ContDiff
open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.L2
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.Tensor

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M]
  [SigmaCompactSpace M]

omit [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [BoundarylessManifold I M] in
theorem pou_weighted_norm_equals_chart_component_norm_up_to_constant
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧
      ∀ T : SmoothCcTensor g r s,
        c * (tensorPouSobolevNorm (I := I) (M := M) g 0 T).toReal ≤
            (tensorPouSobolevHsNorm (I := I) (M := M) g 0 T).toReal ∧
          (tensorPouSobolevHsNorm (I := I) (M := M) g 0 T).toReal ≤
            C * (tensorPouSobolevNorm (I := I) (M := M) g 0 T).toReal :=
  fibrewise_gram_twist_estimate (I := I) (M := M) g r s

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.HebeyBlock.pou_weighted_norm_equals_chart_component_norm_up_to_constant then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.HebeyBlock.pou_weighted_norm_equals_chart_component_norm_up_to_constant"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.HebeyBlock.pou_weighted_norm_equals_chart_component_norm_up_to_constant ``Submission.DifferentialGeometry.Analysis.Sobolev.HebeyBlock.pou_weighted_norm_equals_chart_component_norm_up_to_constant

end DifferentialGeometry.Analysis.Sobolev.HebeyBlock
