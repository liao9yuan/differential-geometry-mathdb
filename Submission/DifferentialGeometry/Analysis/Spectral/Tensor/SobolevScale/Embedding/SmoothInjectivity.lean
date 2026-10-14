import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Embedding.SmoothCompactSupportDense
import Submission.DifferentialGeometry.Analysis.Integration.L2.Hilbert.DenseSubset

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.IntrinsicSobolev.SmoothCcTensorHs
open _root_.Submission.DifferentialGeometry.Geometry.Curvature

noncomputable section

open _root_.Bundle _root_.Submission.Bundle
open scoped _root_.Manifold _root_.Topology _root_.ContDiff

namespace DifferentialGeometry.Analysis.Spectral

open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open _root_.Submission.DifferentialGeometry.Integral.L2

variable
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
      [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

theorem ccToHs_injective (g : SmoothRiemannianMetric I M) (s : ℕ) (σ : ℝ) :
    Function.Injective (ccTensorToHs (I := I) (M := M) g s σ) := by
  intro S T hST
  apply SmoothCcTensor.smoothCcTensor_eq_of_toL2_eq S T
  let hcompact := tensorResolventL2_isCompactOperator
    (I := I) (M := M) g 0 s
  apply (tensorResolventHilbertEigenbasisSigma
    (I := I) (M := M) hcompact).repr.injective
  ext i
  have hi := congrArg (fun u => u.coeff i) hST
  simpa only [ccTensorToHs_coeff, tensorL2Coeff] using hi

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.ccToHs_injective then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.ccToHs_injective"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.ccToHs_injective ``Submission.DifferentialGeometry.Analysis.Spectral.ccToHs_injective

end DifferentialGeometry.Analysis.Spectral

end
