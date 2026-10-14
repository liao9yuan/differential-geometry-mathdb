import Submission.DifferentialGeometry.Analysis.Sobolev.HebeyBlock.FiberNorm.ChartFrameNorm
import Submission.DifferentialGeometry.Analysis.Sobolev.HebeyBlock.FiberNorm.GramTwist
import Submission.DifferentialGeometry.Analysis.Sobolev.HebeyBlock.ChartParallelTransportOpNorm.ChristoffelCkBound
import Submission.DifferentialGeometry.Analysis.Sobolev.HebeyBlock.NablaTensor.NablaTensorFormula
import Submission.DifferentialGeometry.Analysis.Sobolev.HebeyBlock.NablaTensor.IteratedNabla
import Submission.DifferentialGeometry.Analysis.Sobolev.HebeyBlock.ChartParallelTransportOpNorm.UniformChartBounds
import Submission.DifferentialGeometry.Analysis.Sobolev.HebeyBlock.PouSobolevIso.PouNormChartComp
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.Variational.H1Compl

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

namespace DifferentialGeometry.Analysis.Sobolev.HebeyBlock

open _root_.Bundle _root_.Submission.Bundle
open scoped _root_.Manifold _root_.ContDiff
open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.Tensor
open _root_.Submission.DifferentialGeometry.Integral.L2

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem assemble_pou_h1_iso_intrinsic_h1
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧
      ∀ T : SmoothCcTensor g r s,
        c * (tensorPouSobolevNorm (I := I) (M := M) g 1 T).toReal ≤
            (tensorPouSobolevHsNorm (I := I) (M := M) g 1 T).toReal ∧
          (tensorPouSobolevHsNorm (I := I) (M := M) g 1 T).toReal ≤
            C * (tensorPouSobolevNorm (I := I) (M := M) g 1 T).toReal := by
  obtain ⟨c₁, C₁, hc₁_pos, hc₁_le_C₁, h₁⟩ :=
    iterated_nabla_vs_iterated_partial_equivalence_H1
      (I := I) (M := M) g r s 1
  obtain ⟨c₀, C₀, hc₀_pos, hc₀_le_C₀, h₀⟩ :=
    pou_weighted_norm_equals_chart_component_norm_up_to_constant
      (I := I) (M := M) g r s
  refine ⟨min c₀ c₁, _root_.Max.max C₀ C₁, lt_min hc₀_pos hc₁_pos, ?_, ?_⟩
  · exact (min_le_right c₀ c₁).trans (hc₁_le_C₁.trans (le_max_right C₀ C₁))
  · intro T
    obtain ⟨h_low, h_up⟩ := h₁ T
    refine ⟨?_, ?_⟩
    · have h_norm_op_nn :
          (0 : ℝ) ≤ (tensorPouSobolevNorm (I := I) (M := M) g 1 T).toReal :=
        ENNReal.toReal_nonneg
      calc
        min c₀ c₁ * (tensorPouSobolevNorm (I := I) (M := M) g 1 T).toReal
            ≤ c₁ * (tensorPouSobolevNorm (I := I) (M := M) g 1 T).toReal := by
              exact mul_le_mul_of_nonneg_right (min_le_right c₀ c₁) h_norm_op_nn
        _ ≤ (tensorPouSobolevHsNorm (I := I) (M := M) g 1 T).toReal := h_low
    · have h_norm_op_nn :
          (0 : ℝ) ≤ (tensorPouSobolevNorm (I := I) (M := M) g 1 T).toReal :=
        ENNReal.toReal_nonneg
      calc
        (tensorPouSobolevHsNorm (I := I) (M := M) g 1 T).toReal
            ≤ C₁ * (tensorPouSobolevNorm (I := I) (M := M) g 1 T).toReal := h_up
        _ ≤ _root_.Max.max C₀ C₁ * (tensorPouSobolevNorm (I := I) (M := M) g 1 T).toReal := by
              exact mul_le_mul_of_nonneg_right (le_max_right C₀ C₁) h_norm_op_nn

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.HebeyBlock.assemble_pou_h1_iso_intrinsic_h1 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.HebeyBlock.assemble_pou_h1_iso_intrinsic_h1"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.HebeyBlock.assemble_pou_h1_iso_intrinsic_h1 ``Submission.DifferentialGeometry.Analysis.Sobolev.HebeyBlock.assemble_pou_h1_iso_intrinsic_h1

end DifferentialGeometry.Analysis.Sobolev.HebeyBlock
