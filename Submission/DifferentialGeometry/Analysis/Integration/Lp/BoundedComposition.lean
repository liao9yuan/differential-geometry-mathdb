import Submission.DifferentialGeometry.Analysis.Integration.Lp.BoundedConvergence

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

section

noncomputable section

open _root_.Filter _root_.MeasureTheory _root_.Submission.MeasureTheory
open scoped _root_.ENNReal _root_.Topology

namespace MeasureTheory
open _root_.MeasureTheory

open _root_.MeasureTheory in
theorem memLp_and_tendsto_eLpNorm_comp_of_ae_tendsto_of_bounded
    {α X F : Type*} [MeasurableSpace α] [TopologicalSpace X]
    [NormedAddCommGroup F] {μ : _root_.MeasureTheory.Measure α} [_root_.MeasureTheory.IsFiniteMeasure μ]
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hpt : p ≠ ⊤)
    {Φ : X → F} (hΦ : Continuous Φ) {D : ℝ} (hD : ∀ x, ‖Φ x‖ ≤ D)
    {U : ℕ → α → X} {v : α → X}
    (hU : ∀ n, _root_.MeasureTheory.AEStronglyMeasurable (Φ ∘ U n) μ)
    (hlim : ∀ᵐ x ∂μ, _root_.Filter.Tendsto (fun n => U n x) _root_.Filter.atTop (𝓝 (v x))) :
    _root_.MeasureTheory.MemLp (Φ ∘ v) p μ ∧
      Tendsto (fun n => _root_.MeasureTheory.eLpNorm (fun x => Φ (U n x) - Φ (v x)) p μ) _root_.Filter.atTop (𝓝 0) := by
  let : Fact (1 ≤ p) := ⟨hp⟩
  have hscalar : ∀ᵐ x ∂μ, _root_.Filter.Tendsto (fun n => Φ (U n x)) _root_.Filter.atTop (𝓝 (Φ (v x))) :=
    hlim.mono fun x hx => (hΦ.tendsto (v x)).comp hx
  have hfm (n : ℕ) : _root_.MeasureTheory.MemLp (Φ ∘ U n) p μ :=
    MemLp.of_bound (hU n) D (Eventually.of_forall fun x => hD (U n x))
  have hvm : _root_.MeasureTheory.MemLp (Φ ∘ v) p μ := MemLp.of_bound
    (aestronglyMeasurable_of_tendsto_ae _root_.Filter.atTop hU hscalar) D
    (Eventually.of_forall fun x => hD (v x))
  have hbound : ∀ n, ∀ᵐ x ∂μ, ‖(hfm n).toLp (Φ ∘ U n) x‖ ≤ D := by
    intro n
    filter_upwards [(hfm n).coeFn_toLp] with x hx
    rw [hx]
    exact hD (U n x)
  have hLp : ∀ᵐ x ∂μ, _root_.Filter.Tendsto (fun n => (hfm n).toLp (Φ ∘ U n) x)
      atTop (𝓝 (hvm.toLp (Φ ∘ v) x)) := by
    filter_upwards [hscalar, _root_.MeasureTheory.ae_all_iff.mpr (fun n => (hfm n).coeFn_toLp),
      hvm.coeFn_toLp] with x hx hn hv
    simpa only [hn, hv, Function.comp_apply] using hx
  refine ⟨hvm, ?_⟩
  exact (Lp.tendsto_Lp_iff_tendsto_eLpNorm''
    (fun n => Φ ∘ U n) hfm (Φ ∘ v) hvm).mp
    (Lp.tendsto_of_ae_tendsto_of_ae_norm_le hpt
      (fun n => (hfm n).toLp (Φ ∘ U n)) (hvm.toLp (Φ ∘ v)) hbound hLp)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `MeasureTheory.memLp_and_tendsto_eLpNorm_comp_of_ae_tendsto_of_bounded then
    throwError "Refusing to shadow existing declaration MeasureTheory.memLp_and_tendsto_eLpNorm_comp_of_ae_tendsto_of_bounded"
  Lean.modifyEnv fun env => Lean.addAlias env `MeasureTheory.memLp_and_tendsto_eLpNorm_comp_of_ae_tendsto_of_bounded ``Submission.MeasureTheory.memLp_and_tendsto_eLpNorm_comp_of_ae_tendsto_of_bounded

end MeasureTheory

end

end
