import Submission.DifferentialGeometry.Analysis.Spectral.FiniteDimensional.LowSpectralCluster

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open scoped _root_.InnerProductSpace
namespace DifferentialGeometry.Analysis
private abbrev E3 := EuclideanSpace ℝ (Fin 3)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.E3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.E3 target :: scope.openDecls } }

theorem iInf_rayleigh_ge_scaled_relative_low_cluster
    (A B : E3 →L[ℝ] E3) (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    {v : E3} (hv : ‖v‖ = 1) {δ ε : ℝ}
    (hcloseA : ∀ x : E3,
      ‖(A - InnerProductSpace.rankOne ℝ v v) x‖ ≤ δ * ‖x‖)
    (hcloseB : ∀ x : E3,
      ‖(B - InnerProductSpace.rankOne ℝ v v) x‖ ≤ ε * ‖x‖)
    {t α η : ℝ} (ht : 1 ≤ t) (hα : 0 ≤ α)
    (hincrement : ∀ x : E3,
      α * (‖x‖ ^ 2 - ⟪v, x⟫_ℝ ^ 2) - η * ‖x‖ ^ 2 ≤
        ⟪(B - t • A) x, x⟫_ℝ) :
    (⨅ x : {x : E3 // x ≠ 0}, A.rayleighQuotient x) +
        α * (1 - 2 * ε) - η - (t - 1) * δ ≤
      (⨅ x : {x : E3 // x ≠ 0}, B.rayleighQuotient x) := by
  obtain ⟨_, _, _, hleastA, _, _⟩ :=
    exists_unit_least_eigenvector_low_cluster A hA hv hcloseA
  have hscale := mul_le_mul_of_nonneg_left (abs_le.mp hleastA).1 (sub_nonneg.mpr ht)
  have hgain := iInf_rayleigh_ge_relative_low_cluster A B hA hB hv hcloseB
    (le_trans zero_le_one ht) hα hincrement
  nlinarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.iInf_rayleigh_ge_scaled_relative_low_cluster then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.iInf_rayleigh_ge_scaled_relative_low_cluster"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.iInf_rayleigh_ge_scaled_relative_low_cluster ``Submission.DifferentialGeometry.Analysis.iInf_rayleigh_ge_scaled_relative_low_cluster

end DifferentialGeometry.Analysis
