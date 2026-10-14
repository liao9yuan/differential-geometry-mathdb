import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section
open _root_.Filter _root_.MeasureTheory _root_.Set
open scoped _root_.ENNReal _root_.Topology

namespace MeasureTheory
open _root_.MeasureTheory

open _root_.MeasureTheory _root_.MeasureTheory.Lp in
theorem Lp.eq_of_integral_contDiff_mul_dual_eq_on_denseRange
    {A X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (ι : A → X) (hι : DenseRange ι)
    {μ : _root_.MeasureTheory.Measure ℝ} [_root_.MeasureTheory.IsLocallyFiniteMeasure μ]
    {p : ℝ≥0∞} (hp : 1 ≤ p) (L₁ L₂ : _root_.MeasureTheory.Lp (X →L[ℝ] ℝ) p μ)
    (h : ∀ (φ : ℝ → ℝ), ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      ∀ x : A, (∫ t, φ t * L₁ t (ι x) ∂μ) = ∫ t, φ t * L₂ t (ι x) ∂μ) :
    L₁ = L₂ := by
  apply Lp.ext
  apply ae_eq_of_integral_contDiff_smul_eq
    ((Lp.memLp L₁).locallyIntegrable hp)
    ((Lp.memLp L₂).locallyIntegrable hp)
  intro φ hφ hφc
  have hint (L : _root_.MeasureTheory.Lp (X →L[ℝ] ℝ) p μ) : _root_.MeasureTheory.Integrable (fun t => φ t • L t) μ :=
    ((Lp.memLp L).locallyIntegrable hp).integrable_smul_left_of_hasCompactSupport
      hφ.continuous hφc
  apply DFunLike.coe_injective
  apply hι.equalizer (∫ t, φ t • L₁ t ∂μ).continuous (∫ t, φ t • L₂ t ∂μ).continuous
  funext x
  simp only [Function.comp_apply]
  rw [ContinuousLinearMap.integral_apply (hint L₁),
    ContinuousLinearMap.integral_apply (hint L₂)]
  exact h φ hφ hφc x

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.MeasureTheory.Lp
  let env ← Lean.getEnv
  if env.contains `MeasureTheory.Lp.eq_of_integral_contDiff_mul_dual_eq_on_denseRange then
    throwError "Refusing to shadow existing declaration MeasureTheory.Lp.eq_of_integral_contDiff_mul_dual_eq_on_denseRange"
  Lean.modifyEnv fun env => Lean.addAlias env `MeasureTheory.Lp.eq_of_integral_contDiff_mul_dual_eq_on_denseRange ``Submission.MeasureTheory.Lp.eq_of_integral_contDiff_mul_dual_eq_on_denseRange

end MeasureTheory
