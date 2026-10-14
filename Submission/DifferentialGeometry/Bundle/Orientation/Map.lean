import Mathlib.LinearAlgebra.Orientation
import Mathlib.Data.Real.Basic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission



namespace DifferentialGeometry.VectorBundle

theorem map_orientation_trans_between {n : ℕ} {A B C : Type*}
    [AddCommGroup A] [Module ℝ A] [AddCommGroup B] [Module ℝ B]
    [AddCommGroup C] [Module ℝ C] (f : A ≃ₗ[ℝ] B) (g : B ≃ₗ[ℝ] C)
    (o : Orientation ℝ A (Fin n)) :
    Orientation.map (Fin n) g (Orientation.map (Fin n) f o) =
      Orientation.map (Fin n) (f.trans g) o := by
  induction o using Module.Ray.ind with
  | h v hv => rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.VectorBundle.map_orientation_trans_between then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.VectorBundle.map_orientation_trans_between"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.VectorBundle.map_orientation_trans_between ``Submission.DifferentialGeometry.VectorBundle.map_orientation_trans_between

end DifferentialGeometry.VectorBundle
