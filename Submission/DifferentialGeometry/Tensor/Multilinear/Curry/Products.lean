import Mathlib.Analysis.Normed.Operator.Mul

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

namespace ContinuousLinearMap
open _root_.ContinuousLinearMap

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type*} [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]

open _root_.ContinuousLinearMap in
def evalCurriedFourLastTwo
    (F : E →L[𝕜] E →L[𝕜] E →L[𝕜] E →L[𝕜] 𝕜) (u w : E) :
    E →L[𝕜] E →L[𝕜] 𝕜 :=
  (ContinuousLinearMap.compL 𝕜 E (E →L[𝕜] E →L[𝕜] 𝕜) 𝕜
    ((ContinuousLinearMap.apply 𝕜 𝕜 w).comp
      (ContinuousLinearMap.apply 𝕜 (E →L[𝕜] 𝕜) u))).comp F

run_cmd do
  let env ← Lean.getEnv
  if env.contains `ContinuousLinearMap.evalCurriedFourLastTwo then
    throwError "Refusing to shadow existing declaration ContinuousLinearMap.evalCurriedFourLastTwo"
  Lean.modifyEnv fun env => Lean.addAlias env `ContinuousLinearMap.evalCurriedFourLastTwo ``Submission.ContinuousLinearMap.evalCurriedFourLastTwo

open _root_.ContinuousLinearMap in
def curriedBilinearMul (A B : E →L[𝕜] E →L[𝕜] 𝕜) :
    E →L[𝕜] E →L[𝕜] E →L[𝕜] E →L[𝕜] 𝕜 :=
  _root_.ContinuousLinearMap.precompL E
    (_root_.ContinuousLinearMap.precompR E
      (_root_.ContinuousLinearMap.precompL E (_root_.ContinuousLinearMap.precompR E (_root_.ContinuousLinearMap.mul 𝕜 𝕜)))) A B

run_cmd do
  let env ← Lean.getEnv
  if env.contains `ContinuousLinearMap.curriedBilinearMul then
    throwError "Refusing to shadow existing declaration ContinuousLinearMap.curriedBilinearMul"
  Lean.modifyEnv fun env => Lean.addAlias env `ContinuousLinearMap.curriedBilinearMul ``Submission.ContinuousLinearMap.curriedBilinearMul

open _root_.ContinuousLinearMap in
@[simp]
theorem curriedBilinearMul_apply
    (A B : E →L[𝕜] E →L[𝕜] 𝕜) (c v c' v' : E) :
    curriedBilinearMul A B c v c' v' = A c c' * B v v' := by
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `ContinuousLinearMap.curriedBilinearMul_apply then
    throwError "Refusing to shadow existing declaration ContinuousLinearMap.curriedBilinearMul_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `ContinuousLinearMap.curriedBilinearMul_apply ``Submission.ContinuousLinearMap.curriedBilinearMul_apply

open _root_.ContinuousLinearMap in
def evalCurriedThreeLast
    (f : E →L[𝕜] E →L[𝕜] E →L[𝕜] 𝕜) (e : E) :
    E →L[𝕜] E →L[𝕜] 𝕜 :=
  (_root_.ContinuousLinearMap.compL 𝕜 E (E →L[𝕜] 𝕜) 𝕜 (_root_.ContinuousLinearMap.apply 𝕜 𝕜 e)).comp f

run_cmd do
  let env ← Lean.getEnv
  if env.contains `ContinuousLinearMap.evalCurriedThreeLast then
    throwError "Refusing to shadow existing declaration ContinuousLinearMap.evalCurriedThreeLast"
  Lean.modifyEnv fun env => Lean.addAlias env `ContinuousLinearMap.evalCurriedThreeLast ``Submission.ContinuousLinearMap.evalCurriedThreeLast

end ContinuousLinearMap

end
