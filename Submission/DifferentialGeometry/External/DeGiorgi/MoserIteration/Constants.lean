-- Modified 2026-04-28: updated internal import paths for project namespace
import Submission.DifferentialGeometry.External.DeGiorgi.BallScaling
import Submission.DifferentialGeometry.External.DeGiorgi.DeGiorgiIteration
import Submission.DifferentialGeometry.External.DeGiorgi.Localization

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

/-!
# Moser Iteration Constants

This module contains the anchor constants for the Chapter 06 Moser iteration.
-/

noncomputable section

open _root_.MeasureTheory

namespace DeGiorgi

variable {d : ℕ} [NeZero d]

/-- The anchor constant coming from the normalized De Giorgi `L² → L∞` bound. -/
noncomputable def CMoserAnchor (d : ℕ) [NeZero d] : ℝ :=
  _root_.Max.max 1
    (_root_.Max.max ((CDeGiorgiSubsolutionNormalized d) ^ 2)
      (8 * (Mst : ℝ) ^ 2 * (CGns d 2) ^ 2))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DeGiorgi.CMoserAnchor then
    throwError "Refusing to shadow existing declaration DeGiorgi.CMoserAnchor"
  Lean.modifyEnv fun env => Lean.addAlias env `DeGiorgi.CMoserAnchor ``Submission.DeGiorgi.CMoserAnchor

/-- The geometric decay ratio `q = (d-2)/d` used in the Moser iteration. -/
noncomputable def moserDecayRatio (d : ℕ) [hNeZero : NeZero d] : ℝ := by
  let _ := hNeZero
  exact ((d : ℝ) - 2) / (d : ℝ)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DeGiorgi.moserDecayRatio then
    throwError "Refusing to shadow existing declaration DeGiorgi.moserDecayRatio"
  Lean.modifyEnv fun env => Lean.addAlias env `DeGiorgi.moserDecayRatio ``Submission.DeGiorgi.moserDecayRatio

/-- Dimension-only constant `C(d)` for the basic Moser `L^p → L∞` estimate.

It is chosen large enough to absorb both the existing `p = 2` De Giorgi anchor
and the purely geometric product appearing in the exact Moser iteration. -/
noncomputable def CMoser (d : ℕ) [NeZero d] : ℝ :=
  let base := CMoserAnchor d
  if _hd : 2 < (d : ℝ) then
    _root_.Max.max base
      (((32 : ℝ) * base) ^ ((d : ℝ) / 2) *
        4 ^ (∑' n : ℕ, (n : ℝ) * moserDecayRatio d ^ n))
  else
    base

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DeGiorgi.CMoser then
    throwError "Refusing to shadow existing declaration DeGiorgi.CMoser"
  Lean.modifyEnv fun env => Lean.addAlias env `DeGiorgi.CMoser ``Submission.DeGiorgi.CMoser

theorem one_le_C_MoserAnchor : 1 ≤ CMoserAnchor d := by
  simp [CMoserAnchor]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DeGiorgi.one_le_C_MoserAnchor then
    throwError "Refusing to shadow existing declaration DeGiorgi.one_le_C_MoserAnchor"
  Lean.modifyEnv fun env => Lean.addAlias env `DeGiorgi.one_le_C_MoserAnchor ``Submission.DeGiorgi.one_le_C_MoserAnchor

theorem C_DeGiorgi_subsolution_normalized_sq_le_C_MoserAnchor :
    (CDeGiorgiSubsolutionNormalized d) ^ 2 ≤ CMoserAnchor d := by
  simp [CMoserAnchor]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DeGiorgi.C_DeGiorgi_subsolution_normalized_sq_le_C_MoserAnchor then
    throwError "Refusing to shadow existing declaration DeGiorgi.C_DeGiorgi_subsolution_normalized_sq_le_C_MoserAnchor"
  Lean.modifyEnv fun env => Lean.addAlias env `DeGiorgi.C_DeGiorgi_subsolution_normalized_sq_le_C_MoserAnchor ``Submission.DeGiorgi.C_DeGiorgi_subsolution_normalized_sq_le_C_MoserAnchor

theorem cutoff_sobolev_anchor_le_C_MoserAnchor :
    8 * (Mst : ℝ) ^ 2 * (CGns d 2) ^ 2 ≤ CMoserAnchor d := by
  simp [CMoserAnchor]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DeGiorgi.cutoff_sobolev_anchor_le_C_MoserAnchor then
    throwError "Refusing to shadow existing declaration DeGiorgi.cutoff_sobolev_anchor_le_C_MoserAnchor"
  Lean.modifyEnv fun env => Lean.addAlias env `DeGiorgi.cutoff_sobolev_anchor_le_C_MoserAnchor ``Submission.DeGiorgi.cutoff_sobolev_anchor_le_C_MoserAnchor

theorem C_MoserAnchor_le_C_Moser :
    CMoserAnchor d ≤ CMoser d := by
  by_cases hd : 2 < (d : ℝ)
  · simp [CMoser, hd]
  · simp [CMoser, hd]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DeGiorgi.C_MoserAnchor_le_C_Moser then
    throwError "Refusing to shadow existing declaration DeGiorgi.C_MoserAnchor_le_C_Moser"
  Lean.modifyEnv fun env => Lean.addAlias env `DeGiorgi.C_MoserAnchor_le_C_Moser ``Submission.DeGiorgi.C_MoserAnchor_le_C_Moser

theorem one_le_C_Moser : 1 ≤ CMoser d := by
  exact (one_le_C_MoserAnchor (d := d)).trans (C_MoserAnchor_le_C_Moser (d := d))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DeGiorgi.one_le_C_Moser then
    throwError "Refusing to shadow existing declaration DeGiorgi.one_le_C_Moser"
  Lean.modifyEnv fun env => Lean.addAlias env `DeGiorgi.one_le_C_Moser ``Submission.DeGiorgi.one_le_C_Moser

theorem C_DeGiorgi_subsolution_normalized_sq_le_C_Moser :
    (CDeGiorgiSubsolutionNormalized d) ^ 2 ≤ CMoser d := by
  exact
    (C_DeGiorgi_subsolution_normalized_sq_le_C_MoserAnchor (d := d)).trans
      (C_MoserAnchor_le_C_Moser (d := d))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DeGiorgi.C_DeGiorgi_subsolution_normalized_sq_le_C_Moser then
    throwError "Refusing to shadow existing declaration DeGiorgi.C_DeGiorgi_subsolution_normalized_sq_le_C_Moser"
  Lean.modifyEnv fun env => Lean.addAlias env `DeGiorgi.C_DeGiorgi_subsolution_normalized_sq_le_C_Moser ``Submission.DeGiorgi.C_DeGiorgi_subsolution_normalized_sq_le_C_Moser

end DeGiorgi
