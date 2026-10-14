import Submission.DifferentialGeometry.Analysis.Elliptic.ComplexPlane.GreenIdentity
import Submission.DifferentialGeometry.Analysis.Integration.Convolution.Laplacian

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission



noncomputable section

open _root_.Set _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.InnerProductSpace _root_.Submission.InnerProductSpace
open scoped _root_.Topology _root_.ContDiff _root_.Convolution

namespace DifferentialGeometry.Analysis



theorem fderiv_convolution_smooth_right_apply {k f : ℂ → ℝ}
    (hk : _root_.MeasureTheory.LocallyIntegrable k _root_.MeasureTheory.MeasureSpace.volume) (hc : HasCompactSupport f)
    (hf : ContDiff ℝ 1 f) (z v : ℂ) :
    fderiv ℝ (k ⋆[ContinuousLinearMap.mul ℝ ℝ] f) z v =
      (k ⋆[ContinuousLinearMap.mul ℝ ℝ] (fun q => fderiv ℝ f q v)) z := by
  rw [(hc.hasFDerivAt_convolution_right (ContinuousLinearMap.mul ℝ ℝ) hk hf z).fderiv]
  exact _root_.MeasureTheory.convolution_precompR_apply _ hk (hc.fderiv ℝ)
    (hf.continuous_fderiv (by norm_num)) z v

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.fderiv_convolution_smooth_right_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.fderiv_convolution_smooth_right_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.fderiv_convolution_smooth_right_apply ``Submission.DifferentialGeometry.Analysis.fderiv_convolution_smooth_right_apply



theorem laplacian_convolution_smooth_right {k f : ℂ → ℝ}
    (hk : _root_.MeasureTheory.LocallyIntegrable k _root_.MeasureTheory.MeasureSpace.volume) (hc : HasCompactSupport f)
    (hf : ContDiff ℝ 2 f) (z : ℂ) :
    Laplacian.laplacian (k ⋆[ContinuousLinearMap.mul ℝ ℝ] f) z =
      (k ⋆[ContinuousLinearMap.mul ℝ ℝ] Laplacian.laplacian f) z := by
  exact MeasureTheory.laplacian_convolution_right (ContinuousLinearMap.mul ℝ ℝ) hk hc hf z

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.laplacian_convolution_smooth_right then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.laplacian_convolution_smooth_right"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.laplacian_convolution_smooth_right ``Submission.DifferentialGeometry.Analysis.laplacian_convolution_smooth_right

end DifferentialGeometry.Analysis
