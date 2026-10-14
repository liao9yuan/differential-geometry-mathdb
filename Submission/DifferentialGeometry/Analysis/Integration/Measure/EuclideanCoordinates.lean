import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Constructions.Pi

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.MeasureTheory

namespace EuclideanSpace
open _root_.EuclideanSpace

variable (d : ℕ)

open _root_.EuclideanSpace in
def finSuccEquivProd : EuclideanSpace ℝ (Fin (d + 1)) ≃L[ℝ]
    ℝ × EuclideanSpace ℝ (Fin d) :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin (d + 1) => ℝ)).trans
    ((Fin.consEquivL ℝ (fun _ : Fin (d + 1) => ℝ)).symm.trans
      (ContinuousLinearEquiv.prodCongr (ContinuousLinearEquiv.refl ℝ ℝ)
        (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)).symm))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `EuclideanSpace.finSuccEquivProd then
    throwError "Refusing to shadow existing declaration EuclideanSpace.finSuccEquivProd"
  Lean.modifyEnv fun env => Lean.addAlias env `EuclideanSpace.finSuccEquivProd ``Submission.EuclideanSpace.finSuccEquivProd

open _root_.EuclideanSpace in
theorem finSuccEquivProd_apply (x : EuclideanSpace ℝ (Fin (d + 1))) :
    finSuccEquivProd d x = (x 0, WithLp.toLp 2 (fun i => x i.succ)) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `EuclideanSpace.finSuccEquivProd_apply then
    throwError "Refusing to shadow existing declaration EuclideanSpace.finSuccEquivProd_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `EuclideanSpace.finSuccEquivProd_apply ``Submission.EuclideanSpace.finSuccEquivProd_apply

open _root_.EuclideanSpace in
theorem measurePreserving_finSuccEquivProd : _root_.MeasureTheory.MeasurePreserving (finSuccEquivProd d) := by
  have h₁ := EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin (d + 1))
  have h₂ := _root_.MeasureTheory.volume_preserving_piFinSuccAbove (fun _ : Fin (d + 1) => ℝ) 0
  have h₃ := (MeasurePreserving.id (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure ℝ)).prod
    (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin d)).symm
  convert h₃.comp (h₂.comp h₁) using 1
  · funext x
    simp [finSuccEquivProd_apply, Function.comp_def, MeasurableEquiv.piFinSuccAbove]
    rfl
  · rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `EuclideanSpace.measurePreserving_finSuccEquivProd then
    throwError "Refusing to shadow existing declaration EuclideanSpace.measurePreserving_finSuccEquivProd"
  Lean.modifyEnv fun env => Lean.addAlias env `EuclideanSpace.measurePreserving_finSuccEquivProd ``Submission.EuclideanSpace.measurePreserving_finSuccEquivProd

open _root_.EuclideanSpace in
theorem finSuccEquivProd_single_zero :
    finSuccEquivProd d (EuclideanSpace.single 0 1) = (1, 0) := by
  rw [finSuccEquivProd_apply]
  ext i <;> simp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `EuclideanSpace.finSuccEquivProd_single_zero then
    throwError "Refusing to shadow existing declaration EuclideanSpace.finSuccEquivProd_single_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `EuclideanSpace.finSuccEquivProd_single_zero ``Submission.EuclideanSpace.finSuccEquivProd_single_zero

open _root_.EuclideanSpace in
theorem finSuccEquivProd_single_succ (i : Fin d) :
    finSuccEquivProd d (EuclideanSpace.single i.succ 1) =
      (0, EuclideanSpace.single i 1) := by
  rw [finSuccEquivProd_apply]
  ext j <;> simp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `EuclideanSpace.finSuccEquivProd_single_succ then
    throwError "Refusing to shadow existing declaration EuclideanSpace.finSuccEquivProd_single_succ"
  Lean.modifyEnv fun env => Lean.addAlias env `EuclideanSpace.finSuccEquivProd_single_succ ``Submission.EuclideanSpace.finSuccEquivProd_single_succ

end EuclideanSpace

end
