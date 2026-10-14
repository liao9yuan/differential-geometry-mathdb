import Submission.DifferentialGeometry.Analysis.Sobolev.Tools.DifferenceQuotient

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.MeasureTheory _root_.Metric _root_.Filter _root_.Topology _root_.Set _root_.Function
open scoped _root_.ENNReal _root_.NNReal _root_.Convolution _root_.Pointwise _root_.BigOperators

namespace DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction

variable {d : ℕ} [NeZero d]

local notation "E" => EuclideanSpace ℝ (Fin d)

noncomputable def nirenbergTestFunction
    (k : Fin d) (h : ℝ) (η u : E → ℝ) : E → ℝ :=
  DifferentialGeometry.Analysis.Sobolev.diffQuot k (-h)
    (fun y : E => η y ^ 2 *
      DifferentialGeometry.Analysis.Sobolev.diffQuot k h u y)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.nirenbergTestFunction then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.nirenbergTestFunction"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.nirenbergTestFunction ``Submission.DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.nirenbergTestFunction

end DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction
