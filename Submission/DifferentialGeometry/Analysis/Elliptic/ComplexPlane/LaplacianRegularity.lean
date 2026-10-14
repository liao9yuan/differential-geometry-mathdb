import Submission.DifferentialGeometry.Analysis.InnerProductSpace.Laplacian

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission



noncomputable section

open _root_.InnerProductSpace _root_.Submission.InnerProductSpace _root_.Laplacian
open scoped _root_.ContDiff

namespace DifferentialGeometry.Analysis




theorem continuous_laplacian {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → F} (hf : ContDiff ℝ 2 f) : Continuous (_root_.Laplacian.laplacian f) := by
  exact continuous_iff_continuousAt.mpr (fun _ => hf.contDiffAt.continuousAt_laplacian)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.continuous_laplacian then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.continuous_laplacian"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.continuous_laplacian ``Submission.DifferentialGeometry.Analysis.continuous_laplacian

end DifferentialGeometry.Analysis
