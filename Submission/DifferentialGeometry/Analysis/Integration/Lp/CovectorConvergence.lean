import Submission.DifferentialGeometry.Analysis.Integration.Lp.BoundedConvergence
import Mathlib.Analysis.Normed.Module.FiniteDimension

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission


noncomputable section

namespace MeasureTheory.MemLp
open _root_.MeasureTheory _root_.MeasureTheory.MemLp

open _root_.Filter
open scoped _root_.ENNReal _root_.Topology

variable {α E F : Type*} [MeasurableSpace α]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {μ : Measure α} [IsFiniteMeasure μ] {p : ℝ≥0∞} [Fact (1 ≤ p)]

open _root_.MeasureTheory _root_.MeasureTheory.MemLp in
theorem tendsto_toLp_of_ae_tendsto_apply_of_ae_norm_le
    (hp : p ≠ ∞) (u : ℕ → α → E →L[ℝ] F) (u₀ : α → E →L[ℝ] F)
    (hu : ∀ n, _root_.MeasureTheory.MemLp (u n) p μ) (hu₀ : _root_.MeasureTheory.MemLp u₀ p μ) {C : ℝ}
    (hbound : ∀ n, ∀ᵐ x ∂μ, ‖u n x‖ ≤ C)
    (hlim : ∀ᵐ x ∂μ, ∀ v, _root_.Filter.Tendsto (fun n => u n x v) _root_.Filter.atTop (𝓝 (u₀ x v))) :
    Tendsto (fun n => (hu n).toLp (u n)) _root_.Filter.atTop (𝓝 (hu₀.toLp u₀)) := by
  classical
  let e₁ : E ≃L[ℝ] Fin (Module.finrank ℝ E) → ℝ :=
    ContinuousLinearEquiv.ofFinrankEq (Module.finrank_fin_fun ℝ).symm
  let e : (E →L[ℝ] F) ≃L[ℝ] (Fin (Module.finrank ℝ E) → F) :=
    (e₁.arrowCongr (1 : F ≃L[ℝ] F)).trans
      (ContinuousLinearEquiv.piRing (Fin (Module.finrank ℝ E)))
  apply Lp.tendsto_of_ae_tendsto_of_ae_norm_le hp
  · intro n
    filter_upwards [(hu n).coeFn_toLp, hbound n] with x hx hb
    simpa only [hx] using hb
  · filter_upwards [hlim, _root_.MeasureTheory.ae_all_iff.mpr (fun n => (hu n).coeFn_toLp),
      hu₀.coeFn_toLp] with x hx hxseq hxzero
    have he : _root_.Filter.Tendsto (fun n => e (u n x)) _root_.Filter.atTop (𝓝 (e (u₀ x))) := by
      apply tendsto_pi_nhds.mpr
      intro i
      exact hx _
    have hraw : _root_.Filter.Tendsto (fun n => u n x) _root_.Filter.atTop (𝓝 (u₀ x)) := by
      simpa only [Function.comp_def, ContinuousLinearEquiv.symm_apply_apply] using
        (e.symm.continuous.tendsto (e (u₀ x))).comp he
    simpa only [hxseq, hxzero] using hraw

run_cmd do
  let env ← Lean.getEnv
  if env.contains `MeasureTheory.MemLp.tendsto_toLp_of_ae_tendsto_apply_of_ae_norm_le then
    throwError "Refusing to shadow existing declaration MeasureTheory.MemLp.tendsto_toLp_of_ae_tendsto_apply_of_ae_norm_le"
  Lean.modifyEnv fun env => Lean.addAlias env `MeasureTheory.MemLp.tendsto_toLp_of_ae_tendsto_apply_of_ae_norm_le ``Submission.MeasureTheory.MemLp.tendsto_toLp_of_ae_tendsto_apply_of_ae_norm_le

end MeasureTheory.MemLp
