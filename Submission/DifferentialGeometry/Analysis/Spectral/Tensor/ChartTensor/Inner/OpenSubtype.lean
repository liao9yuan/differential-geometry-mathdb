import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.ChartTensor.Inner.InnerBridge
import Submission.DifferentialGeometry.Topology.Manifold.OpenSubtypeModel

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section
open scoped _root_.Manifold
namespace DifferentialGeometry.Analysis.Parabolic.TensorSpectral
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E]

theorem chartGramBilin_opens_model
    (U : TopologicalSpace.Opens E) (g : SmoothRiemannianMetric 𝓘(ℝ, E) U)
    (α b : U) (u w : E) :
    chartGramBilin (I := 𝓘(ℝ, E)) g α b u w = g.inner b u w := by
  rw [chartGramBilin_eq_innerJinv]
  simp only [Integral.L2.modelInnerAt_apply]
  unfold Tensor.Tensor0SRiemannian.chartTrivializationLinearMapSymm
  rw [symmL_opens_model]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartGramBilin_opens_model then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartGramBilin_opens_model"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartGramBilin_opens_model ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartGramBilin_opens_model

end DifferentialGeometry.Analysis.Parabolic.TensorSpectral
