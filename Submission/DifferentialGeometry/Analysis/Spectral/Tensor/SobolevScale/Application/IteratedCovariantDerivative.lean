import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Jet.Bounds.IteratedCovariantDerivative
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Embedding.SmoothCompactSupportDense
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.Iterated.Linear

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Analysis.Spectral

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Set _root_.Filter _root_.Submission.DifferentialGeometry.Tensor0SBundle
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.ENNReal _root_.BigOperators

namespace DifferentialGeometry
namespace Analysis
namespace Spectral

open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open _root_.Submission.DifferentialGeometry.Integral.L2
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow _root_.Submission.DifferentialGeometry.Analysis.Sobolev
    DifferentialGeometry.Analysis.Spectral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance _root_.Submission.DifferentialGeometry.Analysis.Spectral.instCompleteSpace_differentialGeometry : CompleteSpace E := FiniteDimensional.complete ℝ E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Spectral.instCompleteSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Spectral.instCompleteSpace_differentialGeometry target :: scope.openDecls } }

private noncomputable def iterCovGradCcLin
    (g : SmoothRiemannianMetric I M) (s j : ℕ) :
    SmoothCcTensor g 0 s →ₗ[ℝ] SmoothCcTensor g 0 (s + j) where
  toFun := iteratedCovGrad (I := I) g 0 s j
  map_add' := iteratedCovGrad_add (I := I) (M := M) g 0 s j
  map_smul' := iteratedCovGrad_smul (I := I) (M := M) g 0 s j

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Spectral.iterCovGradCcLin
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Spectral.iterCovGradCcLin target :: scope.openDecls } }

noncomputable def iterCovGradHs
    (g : SmoothRiemannianMetric I M) (s j k : ℕ) :
    TensorHs (I := I) (M := M) g 0 s ((k : ℝ) + (j : ℝ)) →L[ℝ]
      TensorHs (I := I) (M := M) g 0 (s + j) (k : ℝ) :=
  ((ccToHsLin (I := I) (M := M) g (s + j) (k : ℝ)).comp
      (iterCovGradCcLin (I := I) (M := M) g s j)).extendOfNorm
    (ccToHsLin (I := I) (M := M) g s ((k : ℝ) + (j : ℝ)))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.iterCovGradHs then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.iterCovGradHs"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.iterCovGradHs ``Submission.DifferentialGeometry.Analysis.Spectral.iterCovGradHs

theorem iterCovGradHs_apply_ccTensorToHs
    (g : SmoothRiemannianMetric I M) (s j k : ℕ)
    (W : SmoothCcTensor g 0 s) :
    iterCovGradHs (I := I) (M := M) g s j k
        (ccTensorToHs (I := I) (M := M) g s ((k : ℝ) + (j : ℝ)) W) =
      ccTensorToHs (I := I) (M := M) g (s + j) (k : ℝ)
        (iteratedCovGrad (I := I) g 0 s j W) := by
  have hdense : DenseRange
      (ccToHsLin (I := I) (M := M) g s ((k : ℝ) + (j : ℝ))) :=
    ccToHsLin_dense (I := I) (M := M) g s (by positivity)
  obtain ⟨C, _, hC⟩ := ccGrad_le (I := I) (M := M) g s j k
  change
    (((ccToHsLin (I := I) (M := M) g (s + j) (k : ℝ)).comp
        (iterCovGradCcLin (I := I) (M := M) g s j)).extendOfNorm
      (ccToHsLin (I := I) (M := M) g s ((k : ℝ) + (j : ℝ))))
        ((ccToHsLin (I := I) (M := M) g s ((k : ℝ) + (j : ℝ))) W) =
      ((ccToHsLin (I := I) (M := M) g (s + j) (k : ℝ)).comp
        (iterCovGradCcLin (I := I) (M := M) g s j)) W
  apply LinearMap.extendOfNorm_eq hdense
  refine ⟨C, ?_⟩
  intro S
  change
    ‖ccTensorToHs (I := I) (M := M) g (s + j) (k : ℝ)
        (iteratedCovGrad (I := I) g 0 s j S)‖ ≤
      C * ‖ccTensorToHs (I := I) (M := M) g s ((k : ℝ) + (j : ℝ)) S‖
  have hkj : ((k + j : ℕ) : ℝ) = (k : ℝ) + (j : ℝ) := by norm_num
  rw [← hkj]
  exact hC S

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.iterCovGradHs_apply_ccTensorToHs then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.iterCovGradHs_apply_ccTensorToHs"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.iterCovGradHs_apply_ccTensorToHs ``Submission.DifferentialGeometry.Analysis.Spectral.iterCovGradHs_apply_ccTensorToHs

end Spectral
end Analysis
end DifferentialGeometry

end
