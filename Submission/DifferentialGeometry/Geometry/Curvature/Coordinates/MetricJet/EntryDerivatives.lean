import Submission.DifferentialGeometry.Geometry.Curvature.Coordinates.MetricJet.Curvature

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open scoped _root_.ContDiff

namespace DifferentialGeometry
namespace Analysis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ}


def matEntryCLM (l m : Fin n) : (Fin n → Fin n → ℝ) →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) m).comp
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => Fin n → ℝ) l)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.matEntryCLM then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.matEntryCLM"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.matEntryCLM ``Submission.DifferentialGeometry.Analysis.matEntryCLM

@[simp] theorem matEntryCLM_apply (l m : Fin n) (M : Fin n → Fin n → ℝ) :
    matEntryCLM l m M = M l m := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.matEntryCLM_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.matEntryCLM_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.matEntryCLM_apply ``Submission.DifferentialGeometry.Analysis.matEntryCLM_apply

theorem fderiv_matEntry {G : E → (Fin n → Fin n → ℝ)} {y : E} (hG : DifferentiableAt ℝ G y)
    (v : E) (l m : Fin n) :
    (fderiv ℝ G y) v l m = fderiv ℝ (fun w => G w l m) y v := by
  have hL : fderiv ℝ (fun w => G w l m) y = (matEntryCLM l m).comp (fderiv ℝ G y) :=
    ((matEntryCLM l m).hasFDerivAt.comp y hG.hasFDerivAt).fderiv
  rw [hL]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.fderiv_matEntry then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.fderiv_matEntry"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.fderiv_matEntry ``Submission.DifferentialGeometry.Analysis.fderiv_matEntry

theorem fderiv2_matEntry {G : E → (Fin n → Fin n → ℝ)} {y : E}
    (hG : DifferentiableAt ℝ (fun w => fderiv ℝ G w) y) (u v : E) (l m : Fin n) :
    ((fderiv ℝ (fun w => fderiv ℝ G w) y) u) v l m
      = fderiv ℝ (fun w => (fderiv ℝ G w) v l m) y u := by
  have hL : fderiv ℝ (fun w => (fderiv ℝ G w) v l m) y
      = ((matEntryCLM l m).comp (ContinuousLinearMap.apply ℝ (Fin n → Fin n → ℝ) v)).comp
          (fderiv ℝ (fun w => fderiv ℝ G w) y) :=
    (((matEntryCLM l m).comp (ContinuousLinearMap.apply ℝ (Fin n → Fin n → ℝ) v)).hasFDerivAt.comp
      y hG.hasFDerivAt).fderiv
  rw [hL]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.fderiv2_matEntry then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.fderiv2_matEntry"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.fderiv2_matEntry ``Submission.DifferentialGeometry.Analysis.fderiv2_matEntry

end Analysis
end DifferentialGeometry

end
