import Submission.DifferentialGeometry.Analysis.Integration.L2.SmoothSections.Defs

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section


open _root_.Manifold
open scoped _root_.Manifold _root_.ContDiff

namespace DifferentialGeometry
namespace Integral
namespace L2
namespace SmoothCcTensor

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

def retagEquiv
    (g h : SmoothRiemannianMetric I M) (r s : ℕ) :
    SmoothCcTensor g r s ≃ₗ[ℝ] SmoothCcTensor h r s where
  toFun S := ⟨S.toSection, S.hasCompactSupport⟩
  invFun S := ⟨S.toSection, S.hasCompactSupport⟩
  left_inv S := by
    ext
    rfl
  right_inv S := by
    ext
    rfl
  map_add' S T := by
    ext
    rfl
  map_smul' c S := by
    ext
    rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.L2.SmoothCcTensor.retagEquiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.L2.SmoothCcTensor.retagEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.L2.SmoothCcTensor.retagEquiv ``Submission.DifferentialGeometry.Integral.L2.SmoothCcTensor.retagEquiv


@[simp]
theorem retag_toSection
    (g h : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) :
    (retagEquiv g h r s S).toSection = S.toSection := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.L2.SmoothCcTensor.retag_toSection then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.L2.SmoothCcTensor.retag_toSection"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.L2.SmoothCcTensor.retag_toSection ``Submission.DifferentialGeometry.Integral.L2.SmoothCcTensor.retag_toSection

end SmoothCcTensor
end L2
end Integral
end DifferentialGeometry
