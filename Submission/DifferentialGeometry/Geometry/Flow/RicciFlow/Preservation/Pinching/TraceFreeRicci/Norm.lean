import Mathlib.Data.Real.Basic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

variable {M : Type*}

def traceFreeRicciNormSqAtOf (scalar ricciNormSq : Real) : Real :=
  ricciNormSq - scalar ^ 2 / 3

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.traceFreeRicciNormSqAtOf then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.traceFreeRicciNormSqAtOf"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.traceFreeRicciNormSqAtOf ``Submission.DifferentialGeometry.PDE.RicciFlow.traceFreeRicciNormSqAtOf

def traceFreeRicciNormSqOf
    (scalar ricciNormSq : Real -> M -> Real) (t : Real) (x : M) : Real :=
  traceFreeRicciNormSqAtOf (scalar t x) (ricciNormSq t x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.traceFreeRicciNormSqOf then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.traceFreeRicciNormSqOf"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.traceFreeRicciNormSqOf ``Submission.DifferentialGeometry.PDE.RicciFlow.traceFreeRicciNormSqOf

end DifferentialGeometry.PDE.RicciFlow
