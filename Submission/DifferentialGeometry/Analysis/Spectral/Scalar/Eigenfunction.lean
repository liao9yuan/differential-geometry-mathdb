import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.Estimates.Embedding.H2Pointwise
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Embedding.SmoothCompactSupportDense
import Submission.DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.Spectral.Synthesis
import Submission.DifferentialGeometry.Analysis.Elliptic.Regularity.SmoothScalar.PreH1

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.Analysis.HeatEquation

open _root_.Submission.DifferentialGeometry.Analysis.Spectral
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral (eigenvectorSmooth)
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian (SmoothScalar)
open _root_.Submission.DifferentialGeometry.Tensor0SBundle
open scoped _root_.Manifold _root_.ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E] [FiniteDimensional Real E]
variable [NeZero (Module.finrank Real E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [I.Boundaryless] [T2Space M] [CompactSpace M]

noncomputable def scalarEigenFunction (g : SmoothRiemannianMetric I M)
    (i : TensorEigenIdx (I := I) (M := M) g 0 0) : SmoothScalar g :=
  ⟨TensorRSField.scalar0 (eigenvectorSmooth g 0 0 i).toSection,
    TensorRSField.scalar0_smooth (eigenvectorSmooth g 0 0 i).toSection⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.HeatEquation.scalarEigenFunction then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.HeatEquation.scalarEigenFunction"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.HeatEquation.scalarEigenFunction ``Submission.DifferentialGeometry.Analysis.HeatEquation.scalarEigenFunction

theorem scalarEigenFunction_abs_le
    (g : SmoothRiemannianMetric I M) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (i : TensorEigenIdx (I := I) (M := M) g 0 0) (x : M),
      |(scalarEigenFunction g i).toFun x| ≤
        C * (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^
          (((Module.finrank ℝ E / 2 + 1 : ℕ) : ℝ) / 2) := by
  classical
  set σ : ℝ := ((Module.finrank ℝ E / 2 + 1 : ℕ) : ℝ)
  obtain ⟨C, hC, hb⟩ := scalar0_abs_le_hs (I := I) (M := M) g
  refine ⟨C, hC, ?_⟩
  intro i x
  have h1 := hb (eigenvectorSmooth g 0 0 i) x
  have hφ : (scalarEigenFunction g i).toFun x =
      TensorRSField.scalar0 (n := (∞ : WithTop ℕ∞))
        (eigenvectorSmooth g 0 0 i).toSection x := rfl
  have hnorm : ‖ccTensorToHs (I := I) (M := M) g 0 σ (eigenvectorSmooth g 0 0 i)‖ =
      Real.sqrt (tensorSobolevWeight (I := I) (M := M) i σ) := by
    rw [ccToHs_eigen g 0 (by dsimp [σ]; positivity),
      Parabolic.MaximalRegularity.norm_tensorHsBasisVec]
  rw [hnorm] at h1
  have hsqrt : Real.sqrt (tensorSobolevWeight (I := I) (M := M) i σ) =
      (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ (σ / 2) := by
    unfold tensorSobolevWeight
    have hnonneg : 0 ≤ 1 + TensorEigenIdx.lambda (I := I) (M := M) i := by
      linarith [tensor_lambda_nonneg (I := I) (M := M) i]
    rw [Real.sqrt_eq_rpow]
    rw [← Real.rpow_mul hnonneg]
    congr 1
    ring
  rw [hsqrt] at h1
  simpa [hφ] using h1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.HeatEquation.scalarEigenFunction_abs_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.HeatEquation.scalarEigenFunction_abs_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.HeatEquation.scalarEigenFunction_abs_le ``Submission.DifferentialGeometry.Analysis.HeatEquation.scalarEigenFunction_abs_le

end DifferentialGeometry.Analysis.HeatEquation
