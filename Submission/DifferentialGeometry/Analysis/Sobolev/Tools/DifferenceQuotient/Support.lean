import Submission.DifferentialGeometry.Analysis.Sobolev.Tools.DifferenceQuotient

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.MeasureTheory _root_.Metric _root_.Filter _root_.Topology _root_.Set _root_.Function
open scoped _root_.ENNReal _root_.NNReal _root_.Convolution _root_.Pointwise _root_.BigOperators

namespace DifferentialGeometry.Analysis.Sobolev

variable {d : ℕ} [NeZero d]

local notation "E" => EuclideanSpace ℝ (Fin d)

omit [NeZero d] in
theorem hasCompactSupport_translate_of_hasCompactSupport
    {v : E → ℝ} (hv : HasCompactSupport v) (k : Fin d) (h : ℝ) :
    HasCompactSupport
      (DifferentialGeometry.Analysis.Sobolev.translate k h v) := by
  let φ : E ≃ₜ E := Homeomorph.addRight (h • EuclideanSpace.single k 1)
  have heq :
      DifferentialGeometry.Analysis.Sobolev.translate k h v = v ∘ φ := by
    funext x
    rfl
  rw [heq]
  exact hv.comp_homeomorph φ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.hasCompactSupport_translate_of_hasCompactSupport then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.hasCompactSupport_translate_of_hasCompactSupport"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.hasCompactSupport_translate_of_hasCompactSupport ``Submission.DifferentialGeometry.Analysis.Sobolev.hasCompactSupport_translate_of_hasCompactSupport

omit [NeZero d] in
theorem hasCompactSupport_diffQuot_of_hasCompactSupport
    {v : E → ℝ} (hv : HasCompactSupport v) (k : Fin d) (h : ℝ) :
    HasCompactSupport
      (DifferentialGeometry.Analysis.Sobolev.diffQuot k h v) := by
  by_cases hh : h = 0
  · subst hh
    rw [DifferentialGeometry.Analysis.Sobolev.diffQuot_zero_h]
    exact HasCompactSupport.zero
  · have heq :
        DifferentialGeometry.Analysis.Sobolev.diffQuot k h v =
          (h⁻¹ : ℝ) •
            (DifferentialGeometry.Analysis.Sobolev.translate k h v - v) := by
      funext x
      rw [DifferentialGeometry.Analysis.Sobolev.diffQuot_apply_of_ne
        (d := d) k hh v x]
      change (v (x + h • EuclideanSpace.single k 1) - v x) / h =
        h⁻¹ • (v (x + h • EuclideanSpace.single k 1) - v x)
      rw [div_eq_inv_mul, smul_eq_mul]
    rw [heq]
    have h_translate :
        HasCompactSupport
          (DifferentialGeometry.Analysis.Sobolev.translate k h v) :=
      hasCompactSupport_translate_of_hasCompactSupport (d := d) hv k h
    have h_diff :
        HasCompactSupport
          (DifferentialGeometry.Analysis.Sobolev.translate k h v - v) :=
      h_translate.sub hv
    exact h_diff.smul_left

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.hasCompactSupport_diffQuot_of_hasCompactSupport then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.hasCompactSupport_diffQuot_of_hasCompactSupport"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.hasCompactSupport_diffQuot_of_hasCompactSupport ``Submission.DifferentialGeometry.Analysis.Sobolev.hasCompactSupport_diffQuot_of_hasCompactSupport


end DifferentialGeometry.Analysis.Sobolev
