import Submission.DifferentialGeometry.Tensor.RSTensor.Defs
import Submission.DifferentialGeometry.Tensor.Multilinear.Bundle.TensorProduct

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.Tensor0SBundle.Tensor0SSpace

open _root_.Bundle _root_.Submission.Bundle

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners 𝕜 E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]

noncomputable def product {r s : ℕ} {x : M}
    (A : Tensor0SSpace r I x) (B : Tensor0SSpace s I x) :
    Tensor0SSpace (r + s) I x :=
  (tensor0SSpaceFiberContinuousLinearEquiv (I := I) (r + s) x).symm
    ((((tensor0SSpaceFiberContinuousLinearEquiv (I := I) r x A).smulRight
      (tensor0SSpaceFiberContinuousLinearEquiv (I := I) s x B)).uncurrySum).domDomCongr
        finSumFinEquiv)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor0SBundle.Tensor0SSpace.product then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor0SBundle.Tensor0SSpace.product"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor0SBundle.Tensor0SSpace.product ``Submission.DifferentialGeometry.Tensor0SBundle.Tensor0SSpace.product

@[simp]
theorem product_apply {r s : ℕ} {x : M}
    (A : Tensor0SSpace r I x) (B : Tensor0SSpace s I x)
    (v : Fin (r + s) → TangentSpace I x) :
    product A B v = A (v ∘ Fin.castAdd s) * B (v ∘ Fin.natAdd r) := by
  change
    ((((tensor0SSpaceFiberContinuousLinearEquiv (I := I) r x A).smulRight
      (tensor0SSpaceFiberContinuousLinearEquiv (I := I) s x B)).uncurrySum).domDomCongr
        finSumFinEquiv) v = _
  simp only [ContinuousMultilinearMap.domDomCongr_apply,
    ContinuousMultilinearMap.uncurrySum_apply, ContinuousMultilinearMap.smulRight_apply,
    tensor0SSpaceFiberContinuousLinearEquiv_apply_apply]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor0SBundle.Tensor0SSpace.product_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor0SBundle.Tensor0SSpace.product_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor0SBundle.Tensor0SSpace.product_apply ``Submission.DifferentialGeometry.Tensor0SBundle.Tensor0SSpace.product_apply

end DifferentialGeometry.Tensor0SBundle.Tensor0SSpace
