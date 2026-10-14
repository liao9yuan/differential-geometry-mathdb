import Submission.DifferentialGeometry.Analysis.Calculus.Matrix.Determinant
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open scoped _root_.ContDiff

namespace DifferentialGeometry
namespace Analysis

variable {n : ℕ} {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

open scoped _root_.Matrix.Norms.Elementwise in
theorem contDiff_det_of_entries (N : X → Matrix (Fin n) (Fin n) ℝ)
    (hN : ∀ a b : Fin n, ContDiff ℝ ∞ (fun x => N x a b)) :
    ContDiff ℝ ∞ (fun x => (N x).det) := by
  exact (Matrix.contDiff_det (𝕜 := ℝ) (n := ∞)).comp
    (contDiff_pi.mpr fun i => contDiff_pi.mpr (hN i))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.contDiff_det_of_entries then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.contDiff_det_of_entries"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.contDiff_det_of_entries ``Submission.DifferentialGeometry.Analysis.contDiff_det_of_entries

theorem contDiff_adjugate_of_entries (N : X → Matrix (Fin n) (Fin n) ℝ)
    (hN : ∀ a b : Fin n, ContDiff ℝ ∞ (fun x => N x a b)) (k l : Fin n) :
    ContDiff ℝ ∞ (fun x => (N x).adjugate k l) := by
  classical
  simp_rw [Matrix.adjugate_apply]
  refine contDiff_det_of_entries (fun x => (N x).updateRow l (Pi.single k 1)) (fun a b => ?_)
  rcases eq_or_ne a l with h | h
  · subst h
    simp only [Matrix.updateRow_self]
    exact contDiff_const
  · simp only [Matrix.updateRow_ne h]
    exact hN a b

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.contDiff_adjugate_of_entries then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.contDiff_adjugate_of_entries"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.contDiff_adjugate_of_entries ``Submission.DifferentialGeometry.Analysis.contDiff_adjugate_of_entries

theorem contDiffAt_inv_of_entries (N : X → Matrix (Fin n) (Fin n) ℝ)
    (hN : ∀ a b : Fin n, ContDiff ℝ ∞ (fun x => N x a b)) {x₀ : X} (hx₀ : (N x₀).det ≠ 0)
    (k l : Fin n) :
    ContDiffAt ℝ ∞ (fun x => (N x)⁻¹ k l) x₀ := by
  have hcongr : (fun x => (N x)⁻¹ k l) = fun x => ((N x).det)⁻¹ * (N x).adjugate k l := by
    funext x
    rw [Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, Ring.inverse_eq_inv]
  rw [hcongr]
  exact ((contDiff_det_of_entries N hN).contDiffAt.inv hx₀).mul
    (contDiff_adjugate_of_entries N hN k l).contDiffAt

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.contDiffAt_inv_of_entries then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.contDiffAt_inv_of_entries"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.contDiffAt_inv_of_entries ``Submission.DifferentialGeometry.Analysis.contDiffAt_inv_of_entries

end Analysis
end DifferentialGeometry

end
