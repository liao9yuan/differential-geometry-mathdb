import Submission.DifferentialGeometry.Geometry.Connection.Trivial
import Submission.DifferentialGeometry.Geometry.Connection.AlongCurve

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open scoped _root_.Manifold

namespace CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

theorem connectionForm_trivial (x : M) :
    (trivial I M F).connectionForm (_root_.FiberBundle.trivializationAt F (Bundle.Trivial M F) x) x = 0 := by
  ext X v
  rw [connectionForm_apply _ _ (_root_.FiberBundle.mem_baseSet_trivializationAt F (Bundle.Trivial M F) x)]
  simp only [Bundle.Trivial.fiberBundle_trivializationAt', Bundle.Trivial.symmL_trivialization,
    Bundle.Trivial.continuousLinearMapAt_trivialization, ContinuousLinearMap.id_apply,
    trivial_apply, mvfderiv_const, zero_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `CovariantDerivative.connectionForm_trivial then
    throwError "Refusing to shadow existing declaration CovariantDerivative.connectionForm_trivial"
  Lean.modifyEnv fun env => Lean.addAlias env `CovariantDerivative.connectionForm_trivial ``Submission.CovariantDerivative.connectionForm_trivial

theorem derivAlongWithin_trivial (γ : ℝ → M) (Z : ℝ → F) (J : Set ℝ) (t : ℝ) :
    (trivial I M F).derivAlongWithin γ Z J t = derivWithin Z J t := by
  dsimp only [derivAlongWithin]
  rw [connectionForm_trivial]
  simp only [zero_apply, add_zero,
    Bundle.Trivial.fiberBundle_trivializationAt', Bundle.Trivial.symmL_trivialization,
    Bundle.Trivial.continuousLinearMapAt_trivialization, ContinuousLinearMap.id_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `CovariantDerivative.derivAlongWithin_trivial then
    throwError "Refusing to shadow existing declaration CovariantDerivative.derivAlongWithin_trivial"
  Lean.modifyEnv fun env => Lean.addAlias env `CovariantDerivative.derivAlongWithin_trivial ``Submission.CovariantDerivative.derivAlongWithin_trivial

end CovariantDerivative
