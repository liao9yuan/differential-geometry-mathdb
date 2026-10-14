import Mathlib.LinearAlgebra.Orientation

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

namespace DifferentialGeometry

theorem orientation_map_trans
    {R : Type*} [CommSemiring R] [PartialOrder R] [IsStrictOrderedRing R]
    {E F G : Type*} [AddCommMonoid E] [Module R E]
    [AddCommMonoid F] [Module R F] [AddCommMonoid G] [Module R G]
    {ι : Type*} (A : E ≃ₗ[R] F) (B : F ≃ₗ[R] G) (o : Orientation R E ι) :
    Orientation.map ι (A.trans B) o = Orientation.map ι B (Orientation.map ι A o) := by
  induction o using Module.Ray.ind with
  | h f hf => rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.orientation_map_trans then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.orientation_map_trans"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.orientation_map_trans ``Submission.DifferentialGeometry.orientation_map_trans

end DifferentialGeometry
