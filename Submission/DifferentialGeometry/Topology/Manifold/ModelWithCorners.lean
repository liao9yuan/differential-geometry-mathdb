import Mathlib.Geometry.Manifold.Diffeomorph

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
namespace ModelWithCorners
open _root_.ModelWithCorners

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  {H : Type*} [TopologicalSpace H]

open _root_.ModelWithCorners in
@[simp] theorem transContinuousLinearEquiv_trans (I : ModelWithCorners 𝕜 E H) (e : E ≃L[𝕜] F) (f : F ≃L[𝕜] G) :
    (I.transContinuousLinearEquiv e).transContinuousLinearEquiv f =
      I.transContinuousLinearEquiv (e.trans f) := by
  ext x <;> simp [_root_.ModelWithCorners.transContinuousLinearEquiv, PartialEquiv.trans]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `ModelWithCorners.transContinuousLinearEquiv_trans then
    throwError "Refusing to shadow existing declaration ModelWithCorners.transContinuousLinearEquiv_trans"
  Lean.modifyEnv fun env => Lean.addAlias env `ModelWithCorners.transContinuousLinearEquiv_trans ``Submission.ModelWithCorners.transContinuousLinearEquiv_trans

open _root_.ModelWithCorners in
@[simp] theorem transContinuousLinearEquiv_refl (I : ModelWithCorners 𝕜 E H) :
    I.transContinuousLinearEquiv (ContinuousLinearEquiv.refl 𝕜 E) = I := by
  ext x <;> simp [_root_.ModelWithCorners.transContinuousLinearEquiv, PartialEquiv.trans]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `ModelWithCorners.transContinuousLinearEquiv_refl then
    throwError "Refusing to shadow existing declaration ModelWithCorners.transContinuousLinearEquiv_refl"
  Lean.modifyEnv fun env => Lean.addAlias env `ModelWithCorners.transContinuousLinearEquiv_refl ``Submission.ModelWithCorners.transContinuousLinearEquiv_refl

open _root_.ModelWithCorners in
theorem transContinuousLinearEquiv_symm (I : ModelWithCorners 𝕜 E H) (e : E ≃L[𝕜] F) :
    (I.transContinuousLinearEquiv e).transContinuousLinearEquiv e.symm = I := by
  ext x <;> simp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `ModelWithCorners.transContinuousLinearEquiv_symm then
    throwError "Refusing to shadow existing declaration ModelWithCorners.transContinuousLinearEquiv_symm"
  Lean.modifyEnv fun env => Lean.addAlias env `ModelWithCorners.transContinuousLinearEquiv_symm ``Submission.ModelWithCorners.transContinuousLinearEquiv_symm

open _root_.ModelWithCorners in
instance boundaryless_transContinuousLinearEquiv
    (I : ModelWithCorners 𝕜 E H) [I.Boundaryless] (e : E ≃L[𝕜] F) :
    (I.transContinuousLinearEquiv e).Boundaryless where
  range_eq_univ := by
    rw [I.transContinuousLinearEquiv_range, I.range_eq_univ, Set.image_univ]
    exact e.surjective.range_eq

run_cmd do
  let env ← Lean.getEnv
  if env.contains `ModelWithCorners.boundaryless_transContinuousLinearEquiv then
    throwError "Refusing to shadow existing declaration ModelWithCorners.boundaryless_transContinuousLinearEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `ModelWithCorners.boundaryless_transContinuousLinearEquiv ``Submission.ModelWithCorners.boundaryless_transContinuousLinearEquiv

end ModelWithCorners
