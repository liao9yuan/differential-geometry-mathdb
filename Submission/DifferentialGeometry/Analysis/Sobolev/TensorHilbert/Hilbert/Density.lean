import Submission.DifferentialGeometry.Analysis.Sobolev.TensorHilbert.Hilbert.Defs

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section


open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.MeasureTheory _root_.Set _root_.Filter _root_.Submission.DifferentialGeometry.Tensor0SBundle
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.ENNReal _root_.BigOperators _root_.Matrix
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Sobolev
namespace IntrinsicSobolev

open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.L2
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.Tensor

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]


omit [NeZero (Module.finrank ℝ E)] in
theorem smoothCcTensor_denseRange_toHs
    (g : SmoothRiemannianMetric I M) (r s k : ℕ) :
    DenseRange
      (SmoothCcTensor.toHs (g := g) (r := r) (s := s) (k := k)) := by
  have hwrap_surj :
      Function.Surjective
        (fun T : SmoothCcTensor g r s =>
          (⟨T⟩ : SmoothCcTensorHs g r s k)) := by
    intro S; exact ⟨S.toCcTensor, by cases S; rfl⟩
  have hcoe :
      DenseRange
        (fun S : SmoothCcTensorHs g r s k =>
          (S : TensorPouSobolevHilbert g r s k)) :=
    UniformSpace.Completion.denseRange_coe
  have hcont :
      Continuous
        (fun S : SmoothCcTensorHs g r s k =>
          (S : TensorPouSobolevHilbert g r s k)) :=
    UniformSpace.Completion.continuous_coe _
  have hfun :
      (SmoothCcTensor.toHs (g := g) (r := r) (s := s) (k := k)) =
        (fun S : SmoothCcTensorHs g r s k =>
            (S : TensorPouSobolevHilbert g r s k)) ∘
          (fun T : SmoothCcTensor g r s =>
            (⟨T⟩ : SmoothCcTensorHs g r s k)) := by
    funext T; rfl
  rw [hfun]
  exact hcoe.comp (hwrap_surj.denseRange) hcont

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.IntrinsicSobolev.smoothCcTensor_denseRange_toHs then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.IntrinsicSobolev.smoothCcTensor_denseRange_toHs"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.IntrinsicSobolev.smoothCcTensor_denseRange_toHs ``Submission.DifferentialGeometry.Analysis.Sobolev.IntrinsicSobolev.smoothCcTensor_denseRange_toHs

end IntrinsicSobolev
end Sobolev
end Analysis
end DifferentialGeometry

end
