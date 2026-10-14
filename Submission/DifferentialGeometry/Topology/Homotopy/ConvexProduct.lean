import Mathlib.Analysis.Convex.Contractible

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.ContinuousMap
namespace DifferentialGeometry.HomotopyEquiv
variable (X : Type*) [TopologicalSpace X]
  {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [ContinuousAdd E] [ContinuousSMul ℝ E] {s : Set E}


def productConvex (hs : Convex ℝ s) (c : s) : (X × s) ≃ₕ X where
  toFun := ⟨Prod.fst, continuous_fst⟩
  invFun := (ContinuousMap.id X).prodMk (ContinuousMap.const X c)
  left_inv := ⟨{
    toFun := fun p => (p.2.1, ⟨(1 - (p.1 : ℝ)) • c.val + (p.1 : ℝ) • p.2.2.val,
      hs c.property p.2.2.property (sub_nonneg.mpr p.1.property.2)
        p.1.property.1 (sub_add_cancel 1 (p.1 : ℝ))⟩)
    continuous_toFun := by fun_prop
    map_zero_left := by intro p; ext <;> simp
    map_one_left := by intro p; ext <;> simp }⟩
  right_inv := ContinuousMap.Homotopic.refl _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.HomotopyEquiv.productConvex then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.HomotopyEquiv.productConvex"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.HomotopyEquiv.productConvex ``Submission.DifferentialGeometry.HomotopyEquiv.productConvex


@[simp]
theorem productConvex_apply (hs : Convex ℝ s) (c : s) (p : X × s) :
    productConvex X hs c p = p.1 := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.HomotopyEquiv.productConvex_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.HomotopyEquiv.productConvex_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.HomotopyEquiv.productConvex_apply ``Submission.DifferentialGeometry.HomotopyEquiv.productConvex_apply


@[simp]
theorem productConvex_symm_apply (hs : Convex ℝ s) (c : s) (x : X) :
    (productConvex X hs c).symm x = (x, c) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.HomotopyEquiv.productConvex_symm_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.HomotopyEquiv.productConvex_symm_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.HomotopyEquiv.productConvex_symm_apply ``Submission.DifferentialGeometry.HomotopyEquiv.productConvex_symm_apply

end DifferentialGeometry.HomotopyEquiv
