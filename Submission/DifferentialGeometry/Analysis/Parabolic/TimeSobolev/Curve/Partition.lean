import Mathlib.Data.Fin.Basic
import Mathlib.Data.Real.Basic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

namespace DifferentialGeometry.Analysis.Parabolic.TimeSobolev

def partitionIntervalLength {m : ℕ} (t : Fin (m + 1) → Real) (i : Fin m) : Real :=
  t i.succ - t i.castSucc

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.partitionIntervalLength then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TimeSobolev.partitionIntervalLength"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.partitionIntervalLength ``Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.partitionIntervalLength

end DifferentialGeometry.Analysis.Parabolic.TimeSobolev
