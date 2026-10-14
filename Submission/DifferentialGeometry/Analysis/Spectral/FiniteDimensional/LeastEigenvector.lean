import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Mathlib.Analysis.Normed.Module.RCLike.Real

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section
open _root_.Set _root_.Metric
open scoped _root_.InnerProductSpace

namespace DifferentialGeometry.Analysis

theorem exists_unit_least_eigenvector
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [Nontrivial E]
    (A : E →L[ℝ] E) (hA : IsSelfAdjoint A) :
    ∃ (μ : ℝ) (w : E), ‖w‖ = 1 ∧ A w = μ • w ∧
      ∀ x : E, ‖x‖ = 1 → μ ≤ ⟪A x, x⟫_ℝ := by
  obtain ⟨w, hw, hmin⟩ := (isCompact_sphere (0 : E) 1).exists_isMinOn
    (NormedSpace.sphere_nonempty.mpr zero_le_one) A.reApplyInnerSelf_continuous.continuousOn
  have hnorm : ‖w‖ = 1 := by simpa only [mem_sphere_zero_iff_norm] using hw
  have heigen := hA.eq_smul_self_of_isLocalExtrOn_real
    (show IsLocalExtrOn A.reApplyInnerSelf (_root_.Metric.sphere (0 : E) ‖w‖) w from
      hnorm ▸ Or.inl hmin.localize)
  refine ⟨⟪A w, w⟫_ℝ, w, hnorm, ?_, ?_⟩
  · simpa [ContinuousLinearMap.rayleighQuotient, ContinuousLinearMap.reApplyInnerSelf_apply,
      hnorm] using heigen
  · intro x hx
    exact hmin (mem_sphere_zero_iff_norm.mpr hx)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.exists_unit_least_eigenvector then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.exists_unit_least_eigenvector"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.exists_unit_least_eigenvector ``Submission.DifferentialGeometry.Analysis.exists_unit_least_eigenvector

end DifferentialGeometry.Analysis
