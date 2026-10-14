import Submission.DifferentialGeometry.Analysis.Sobolev.Tools.CutoffDiffQuotLp

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Filter _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Set _root_.Metric
open scoped _root_.ENNReal

namespace DifferentialGeometry.Analysis.Sobolev

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

private theorem indicator_one_memLp_top {K : Set E} (hK : MeasurableSet K) :
    MemLp (K.indicator (fun _ => (1 : ℝ))) ∞ volume := by
  apply _root_.MeasureTheory.memLp_top_of_bound (measurable_const.indicator hK).aestronglyMeasurable 1
  exact Eventually.of_forall fun x => by
    by_cases hx : x ∈ K <;> simp [hx]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.indicator_one_memLp_top
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.indicator_one_memLp_top target :: scope.openDecls } }

private theorem tsupport_indicator_one_subset (K : Set E) :
    tsupport (K.indicator (fun _ => (1 : ℝ))) ⊆ closure K := by
  apply closure_mono
  intro x hx
  by_contra hxK
  exact hx (_root_.Set.indicator_of_notMem hxK _)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.tsupport_indicator_one_subset
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.tsupport_indicator_one_subset target :: scope.openDecls } }

theorem integrable_integral_sq_diffQuot_on_comp
    {Z Y : Type*} [MeasurableSpace Z] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {μ : _root_.MeasureTheory.Measure Z} {Ω K : Set E} (hΩ : MeasurableSet Ω) (hK : MeasurableSet K)
    (k : Fin d) (h : ℝ) (hroom : _root_.Metric.cthickening |h| K ⊆ Ω)
    (A : Y →L[ℝ] _root_.MeasureTheory.Lp ℝ 2 (volume.restrict Ω)) {u : Z → Y} (hu : _root_.MeasureTheory.MemLp u 2 μ) :
    Integrable (fun t => ∫ x in K, (diffQuot k h (A (u t)) x)^2) μ := by
  let χ := K.indicator (fun _ => (1 : ℝ))
  have hχ : _root_.MeasureTheory.MemLp χ ∞ volume := indicator_one_memLp_top hK
  have hχroom : _root_.Metric.cthickening |h| (tsupport χ) ⊆ Ω :=
    (_root_.Metric.cthickening_subset_of_subset |h| (tsupport_indicator_one_subset K)).trans
      (by simpa only [_root_.Metric.cthickening_closure] using hroom)
  have hint := integrable_integral_sq_cutoff_diffQuot_comp hΩ hχ k h hχroom A hu
  apply hint.congr
  filter_upwards [] with t
  rw [← _root_.MeasureTheory.integral_indicator hK]
  apply _root_.MeasureTheory.integral_congr_ae
  filter_upwards [] with x
  by_cases hx : x ∈ K <;> simp [χ, hx]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.integrable_integral_sq_diffQuot_on_comp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.integrable_integral_sq_diffQuot_on_comp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.integrable_integral_sq_diffQuot_on_comp ``Submission.DifferentialGeometry.Analysis.Sobolev.integrable_integral_sq_diffQuot_on_comp

theorem diffQuot_congr_ae_on
    {Ω K : Set E} (hΩ : MeasurableSet Ω) (hK : MeasurableSet K)
    (k : Fin d) (h : ℝ) (hroom : _root_.Metric.cthickening |h| K ⊆ Ω)
    {u v : E → ℝ} (huv : u =ᵐ[volume.restrict Ω] v) :
    diffQuot k h u =ᵐ[volume.restrict K] diffQuot k h v := by
  let χ := K.indicator (fun _ => (1 : ℝ))
  have hχroom : _root_.Metric.cthickening |h| (tsupport χ) ⊆ Ω :=
    (_root_.Metric.cthickening_subset_of_subset |h| (tsupport_indicator_one_subset K)).trans
      (by simpa only [_root_.Metric.cthickening_closure] using hroom)
  have heq : (fun x => χ x * diffQuot k h u x) =ᵐ[volume.restrict K]
      fun x => χ x * diffQuot k h v x :=
    (cutoff_diffQuot_congr_ae_local hΩ k h χ hχroom huv).filter_mono
      (_root_.MeasureTheory.ae_mono Measure.restrict_le_self)
  filter_upwards [heq, _root_.MeasureTheory.ae_restrict_mem hK] with x hx hxK
  simpa only [χ, _root_.Set.indicator_of_mem hxK, one_mul] using hx

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.diffQuot_congr_ae_on then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.diffQuot_congr_ae_on"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.diffQuot_congr_ae_on ``Submission.DifferentialGeometry.Analysis.Sobolev.diffQuot_congr_ae_on

end DifferentialGeometry.Analysis.Sobolev
