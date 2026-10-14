import Mathlib.Analysis.Complex.Isometry
import Mathlib.Analysis.SpecialFunctions.Complex.CircleMap

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

theorem rotation_exp_circleMap (α θ : ℝ) :
    rotation (Circle.exp α) (circleMap 0 1 θ) = circleMap 0 1 (α + θ) := by
  simp [rotation_apply, Circle.coe_exp, circleMap, Complex.exp_add, add_mul]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `rotation_exp_circleMap then
    throwError "Refusing to shadow existing declaration rotation_exp_circleMap"
  Lean.modifyEnv fun env => Lean.addAlias env `rotation_exp_circleMap ``Submission.rotation_exp_circleMap
