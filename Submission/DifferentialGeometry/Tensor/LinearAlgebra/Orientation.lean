import Submission.DifferentialGeometry.External.CanonicalTopology.LinearAlgebra.Orientation

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

namespace LinearEquiv
open _root_.LinearEquiv

variable {R E : Type*} [CommRing R] [AddCommGroup E] [Module R E] [Module.Free R E]

open _root_.LinearEquiv in
theorem det_neg_eq_neg_one_of_odd (hodd : Odd (Module.finrank R E)) :
    LinearMap.det ((LinearEquiv.neg R : E ≃ₗ[R] E).toLinearMap) = -1 := by
  change LinearMap.det (-LinearMap.id : E →ₗ[R] E) = -1
  rw [← neg_one_smul R (LinearMap.id : E →ₗ[R] E), LinearMap.det_smul, LinearMap.det_id, mul_one]
  exact hodd.neg_one_pow

run_cmd do
  let env ← Lean.getEnv
  if env.contains `LinearEquiv.det_neg_eq_neg_one_of_odd then
    throwError "Refusing to shadow existing declaration LinearEquiv.det_neg_eq_neg_one_of_odd"
  Lean.modifyEnv fun env => Lean.addAlias env `LinearEquiv.det_neg_eq_neg_one_of_odd ``Submission.LinearEquiv.det_neg_eq_neg_one_of_odd

end LinearEquiv

namespace Orientation
open _root_.Orientation

variable {R E ι : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
  [AddCommGroup E] [Module R E] [Fintype ι]

open _root_.Orientation in
theorem map_negLinearEquiv_of_odd (o : Orientation R E ι)
    (hcard : Fintype.card ι = Module.finrank R E) (hodd : Odd (Module.finrank R E)) :
    Orientation.map ι (LinearEquiv.neg R) o = -o := by
  apply (Orientation.map_eq_neg_iff_det_neg o _ hcard).mpr
  rw [LinearEquiv.det_neg_eq_neg_one_of_odd hodd]
  exact neg_one_lt_zero

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Orientation.map_negLinearEquiv_of_odd then
    throwError "Refusing to shadow existing declaration Orientation.map_negLinearEquiv_of_odd"
  Lean.modifyEnv fun env => Lean.addAlias env `Orientation.map_negLinearEquiv_of_odd ``Submission.Orientation.map_negLinearEquiv_of_odd

end Orientation
