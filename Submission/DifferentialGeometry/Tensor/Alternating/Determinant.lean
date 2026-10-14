import Mathlib.LinearAlgebra.Determinant

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

namespace AlternatingMap
open _root_.AlternatingMap

open _root_.AlternatingMap in
theorem map_linearMap_eq_det_mul {R E ι : Type*} [CommRing R] [AddCommGroup E] [Module R E]
    [Finite ι] (b : Module.Basis ι R E) (α : E [⋀^ι]→ₗ[R] R)
    (f : E →ₗ[R] E) (v : ι → E) : α (f ∘ v) = LinearMap.det f * α v := by
  classical
  let _ := Fintype.ofFinite ι
  rw [α.eq_smul_basis_det b]
  simp only [_root_.AlternatingMap.smul_apply, smul_eq_mul, Module.Basis.det_comp]
  exact mul_left_comm _ _ _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `AlternatingMap.map_linearMap_eq_det_mul then
    throwError "Refusing to shadow existing declaration AlternatingMap.map_linearMap_eq_det_mul"
  Lean.modifyEnv fun env => Lean.addAlias env `AlternatingMap.map_linearMap_eq_det_mul ``Submission.AlternatingMap.map_linearMap_eq_det_mul

end AlternatingMap
