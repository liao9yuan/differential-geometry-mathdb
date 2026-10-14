import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Topology.Instances.ENNReal.Lemmas

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

section

set_option autoImplicit false
noncomputable section

open _root_.Set _root_.Filter _root_.MeasureTheory
open scoped _root_.Topology _root_.ENNReal

namespace MeasureTheory
open _root_.MeasureTheory

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

open _root_.MeasureTheory in
theorem ae_exists_subseq_bounded_of_integral_bound
    {f : ℕ → X → ℝ} (hf : ∀ n, _root_.MeasureTheory.Integrable (f n) μ)
    (hpos : ∀ n, 0 ≤ᵐ[μ] f n) {B : ℝ} (hB : ∀ n, (∫ x, f n x ∂μ) ≤ B) :
    ∀ᵐ x ∂μ, ∃ (σ : ℕ → ℕ) (C : ℝ), StrictMono σ ∧ ∀ n, f (σ n) x ≤ C := by
  let F : ℕ → X → ℝ≥0∞ := fun n x => ENNReal.ofReal (f n x)
  have hF (n : ℕ) : AEMeasurable (F n) μ := (hf n).aemeasurable.ennreal_ofReal
  have hbound (n : ℕ) : (∫⁻ x, F n x ∂μ) ≤ ENNReal.ofReal B := by
    rw [show (∫⁻ x, F n x ∂μ) = ENNReal.ofReal (∫ x, f n x ∂μ) from
      (_root_.MeasureTheory.ofReal_integral_eq_lintegral_ofReal (hf n) (hpos n)).symm]
    exact ENNReal.ofReal_le_ofReal (hB n)
  have hi : (∫⁻ x, _root_.Filter.liminf (fun n => F n x) _root_.Filter.atTop ∂μ) ≤ ENNReal.ofReal B :=
    (_root_.MeasureTheory.lintegral_liminf_le' hF).trans ((_root_.Filter.liminf_le_limsup).trans
      (_root_.Filter.limsup_le_of_le (by isBoundedDefault) (Eventually.of_forall hbound)))
  have hmeas : AEMeasurable (fun x => _root_.Filter.liminf (fun n => F n x) _root_.Filter.atTop) μ := by
    simp only [_root_.Filter.liminf_eq_iSup_iInf_of_nat]
    exact AEMeasurable.iSup fun n => AEMeasurable.biInf (s := {i : ℕ | n ≤ i})
      (_root_.Set.to_countable _) (fun i _ => hF i)
  have hfinite := _root_.MeasureTheory.ae_lt_top' hmeas (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hi)
  filter_upwards [hfinite] with x hx
  let a : ℝ≥0∞ := _root_.Filter.liminf (fun n => F n x) _root_.Filter.atTop
  have ha : a ≠ ⊤ := hx.ne
  have hlt : a < ENNReal.ofReal (a.toReal + 1) := by
    rw [ENNReal.ofReal_add ENNReal.toReal_nonneg zero_le_one, ENNReal.ofReal_toReal ha]
    exact ENNReal.lt_add_right ha (by simp)
  have hfreq : ∃ᶠ n in _root_.Filter.atTop, F n x < ENNReal.ofReal (a.toReal + 1) :=
    _root_.Filter.frequently_lt_of_liminf_lt (by isBoundedDefault) hlt
  obtain ⟨σ, hσ, hσbound⟩ := _root_.Filter.extraction_of_frequently_atTop hfreq
  refine ⟨σ, a.toReal + 1, hσ, ?_⟩
  intro n
  have h := hσbound n
  exact le_of_lt ((ENNReal.ofReal_lt_ofReal_iff (by positivity : 0 < a.toReal + 1)).mp h)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `MeasureTheory.ae_exists_subseq_bounded_of_integral_bound then
    throwError "Refusing to shadow existing declaration MeasureTheory.ae_exists_subseq_bounded_of_integral_bound"
  Lean.modifyEnv fun env => Lean.addAlias env `MeasureTheory.ae_exists_subseq_bounded_of_integral_bound ``Submission.MeasureTheory.ae_exists_subseq_bounded_of_integral_bound

end MeasureTheory

end

end
