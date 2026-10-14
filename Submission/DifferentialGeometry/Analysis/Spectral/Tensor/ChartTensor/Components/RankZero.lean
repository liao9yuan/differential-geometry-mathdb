import Submission.DifferentialGeometry.Analysis.Elliptic.TensorRegularity.CovDeriv.SlotCorrectionComponent
import Submission.DifferentialGeometry.Tensor.RSTensor.RankZero

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Geometry.Curvature

noncomputable section
set_option backward.isDefEq.respectTransparency false

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Set _root_.Submission.DifferentialGeometry.Tensor0SBundle
open scoped _root_.Manifold _root_.Topology _root_.ContDiff

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.TensorRegularity
open _root_.Submission.DifferentialGeometry.Integral.L2

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] in
theorem scalar0_raw_eq
    (g : SmoothRiemannianMetric I M) (S : SmoothCcTensor g 0 0)
    (α : M) {x : M} (hx : x ∈ (chartAt H α).source) :
    tensorChartComponentRaw (I := I) (M := M) g 0 0 S α
        Fin.elim0 Fin.elim0 x =
      TensorRSField.scalar0 (n := (∞ : WithTop ℕ∞)) S.toSection x := by
  classical
  rw [tensorChartComponentRaw_eq_chartFrame (I := I) (M := M)
    g 0 0 S α hx Fin.elim0 Fin.elim0]
  have hunit :
      chartFrameBasisModel (I := I) (M := M) α x 0 Fin.elim0 =
        (tensor0SSpaceFiberContinuousLinearEquiv (I := I) 0 x).symm
          (ContinuousMultilinearMap.constOfIsEmpty ℝ
            (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ)) := by
    apply (tensor0SSpaceFiberContinuousLinearEquiv (I := I) 0 x).injective
    apply ContinuousMultilinearMap.ext
    intro v
    rw [tensor0SSpaceFiberContinuousLinearEquiv_apply_apply,
      ContinuousLinearEquiv.apply_symm_apply, chartFrameBasisModel_apply, Fin.prod_univ_zero,
      ContinuousMultilinearMap.constOfIsEmpty_apply]
  rw [hunit]
  have hone :
      Tensor0SField.one0 (𝕜 := ℝ) (E := E) (H := H)
          (I := I) (M := M) (∞ : WithTop ℕ∞) x =
        (tensor0SSpaceFiberContinuousLinearEquiv (I := I) 0 x).symm
          (ContinuousMultilinearMap.constOfIsEmpty ℝ
            (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ)) := by
    apply (tensor0SSpaceFiberContinuousLinearEquiv (I := I) 0 x).injective
    apply ContinuousMultilinearMap.ext
    intro v
    rw [tensor0SSpaceFiberContinuousLinearEquiv_apply_apply,
      ContinuousLinearEquiv.apply_symm_apply, ContinuousMultilinearMap.constOfIsEmpty_apply]
    exact Tensor0SField.one0_apply (𝕜 := ℝ) (E := E) (H := H)
      (I := I) (M := M) (∞ : WithTop ℕ∞) x v
  rw [TensorRSField.scalar0, Tensor0SField.toScalarField,
    TensorRSField.rs0_apply, hone, Tensor0SSpace.toModel,
    tensor0SSpace_continuousLinearEquiv_apply]
  exact congrArg
    (S.toSection x
      ((tensor0SSpaceFiberContinuousLinearEquiv (I := I) 0 x).symm
        (ContinuousMultilinearMap.constOfIsEmpty ℝ
          (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ))))
    (Subsingleton.elim _ _)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.scalar0_raw_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.scalar0_raw_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.scalar0_raw_eq ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.scalar0_raw_eq

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry
