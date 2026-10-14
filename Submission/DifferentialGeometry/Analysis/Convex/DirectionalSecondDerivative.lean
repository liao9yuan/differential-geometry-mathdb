import Submission.DifferentialGeometry.Analysis.Convex.SecondDerivative
import Mathlib.MeasureTheory.Measure.Haar.Disintegration
import Mathlib.MeasureTheory.Constructions.Polish.StronglyMeasurable
import Mathlib.Tactic.Module

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Set _root_.Filter _root_.MeasureTheory
open scoped _root_.Topology

namespace DifferentialGeometry.Analysis.Calculus

theorem exists_measurable_directional_second_derivative_of_concave_sub_quadratic
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] {μ : _root_.MeasureTheory.Measure E} [Measure.IsAddHaarMeasure μ]
    {f : E → ℝ} {U : Set E} (hU : IsOpen U) (B : E →L[ℝ] E →L[ℝ] ℝ)
    (hf : ConcaveOn ℝ U (fun x => f x - B x x / 2))
    (v : E) (h : ℕ → ℝ) (hh : _root_.Filter.Tendsto h _root_.Filter.atTop (𝓝 0)) (hne : ∀ n, h n ≠ 0) :
    ∃ q : E → ℝ, Measurable q ∧
      (∀ x, q x = _root_.Filter.limUnder _root_.Filter.atTop (fun n =>
        (U.indicator f (x + h n • v) - 2 * U.indicator f x +
          U.indicator f (x - h n • v)) / (h n) ^ 2)) ∧
      ∀ᵐ x ∂μ, x ∈ U →
        _root_.Filter.Tendsto (fun n => (f (x + h n • v) - 2 * f x + f (x - h n • v)) / (h n) ^ 2)
          atTop (𝓝 (q x)) := by
  classical
  let F : E → ℝ := U.indicator f
  let D : ℕ → E → ℝ := fun n x =>
    (F (x + h n • v) - 2 * F x + F (x - h n • v)) / (h n) ^ 2
  have hfcont : ContinuousOn f U := by
    have hpoly : Continuous (fun x : E => B x x / 2) := by fun_prop
    have hsum : ContinuousOn (fun x => (f x - B x x / 2) + B x x / 2) U :=
      (hf.continuousOn hU).add hpoly.continuousOn
    simpa only [sub_add_cancel] using hsum
  have hFmeas : Measurable F :=
    hfcont.measurable_piecewise continuousOn_const hU.measurableSet
  have hDmeas : ∀ n, Measurable (D n) := by
    intro n
    exact (((hFmeas.comp (continuous_id.add continuous_const).measurable).sub
      (measurable_const.mul hFmeas)).add
        (hFmeas.comp (continuous_id.sub continuous_const).measurable)).div_const _
  let good : Set E := Uᶜ ∪ {x | ∃ c, _root_.Filter.Tendsto (fun n => D n x) _root_.Filter.atTop (𝓝 c)}
  have hgood : MeasurableSet good :=
    hU.measurableSet.compl.union (MeasureTheory.measurableSet_exists_tendsto hDmeas)
  have hhne : _root_.Filter.Tendsto h _root_.Filter.atTop (𝓝[≠] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hh, Eventually.of_forall hne⟩
  have hgoodAE : ∀ᵐ x ∂μ, x ∈ good := by
    apply MeasureTheory.ae_mem_of_ae_add_linearMap_mem
      (LinearMap.toSpanSingleton ℝ E v) _root_.MeasureTheory.MeasureSpace.volume μ hgood
    intro a
    let line : ℝ →ᵃ[ℝ] E := AffineMap.lineMap a (a + v)
    have hline : ∀ t, line t = a + t • v := by
      intro t
      simp only [line, AffineMap.lineMap_apply_module', add_sub_cancel_left]
      exact add_comm _ _
    have hlinecont : Continuous line := by
      have heq : (line : ℝ → E) = fun t => a + t • v := funext hline
      rw [heq]
      fun_prop
    let g : ℝ → ℝ := fun t => f (line t) - B (line t) (line t) / 2
    have hg : ConcaveOn ℝ (line ⁻¹' U) g := hf.comp_affineMap line
    have hlineU : IsOpen (line ⁻¹' U) := hU.preimage hlinecont
    filter_upwards [hg.ae_tendsto_second_central_difference hlineU] with t ht
    change a + t • v ∈ good
    by_cases htU : a + t • v ∈ U
    · apply Or.inr
      have htline : t ∈ line ⁻¹' U := by simpa only [_root_.Set.mem_preimage, hline] using htU
      have hlim := ((ht htline).comp hhne).add_const (B v v)
      refine ⟨_, hlim.congr' ?_⟩
      have hpU : ∀ᶠ n in _root_.Filter.atTop, a + t • v + h n • v ∈ U := by
        have hp : _root_.Filter.Tendsto (fun n => a + t • v + h n • v) _root_.Filter.atTop (𝓝 (a + t • v)) := by
          simpa only [zero_smul, add_zero] using tendsto_const_nhds.add (hh.smul_const v)
        exact hp.eventually (hU.mem_nhds htU)
      have hmU : ∀ᶠ n in _root_.Filter.atTop, a + t • v - h n • v ∈ U := by
        have hm : _root_.Filter.Tendsto (fun n => a + t • v - h n • v) _root_.Filter.atTop (𝓝 (a + t • v)) := by
          simpa only [zero_smul, sub_zero] using tendsto_const_nhds.sub (hh.smul_const v)
        exact hm.eventually (hU.mem_nhds htU)
      filter_upwards [hpU, hmU] with n hnP hnM
      have hp : a + (t + h n) • v = a + t • v + h n • v := by module
      have hm : a + (t - h n) • v = a + t • v - h n • v := by module
      dsimp only [D, F, g, Function.comp_def]
      simp only [hline, hp, hm, _root_.Set.indicator_of_mem hnP, _root_.Set.indicator_of_mem hnM,
        _root_.Set.indicator_of_mem htU, map_add, map_sub, map_smul, add_apply, sub_apply, smul_apply,
        smul_eq_mul]
      field_simp [hne n]
      ring
    · exact Or.inl htU
  let q : E → ℝ := fun x => _root_.Filter.limUnder _root_.Filter.atTop (fun n => D n x)
  have hqmeas : Measurable q :=
    (StronglyMeasurable.limUnder (fun n => (hDmeas n).stronglyMeasurable)).measurable
  refine ⟨q, hqmeas, fun _ => rfl, ?_⟩
  filter_upwards [hgoodAE] with x hx
  intro hxU
  have hxconv : ∃ c, _root_.Filter.Tendsto (fun n => D n x) _root_.Filter.atTop (𝓝 c) := hx.resolve_left (not_not.mpr hxU)
  have hlim : _root_.Filter.Tendsto (fun n => D n x) _root_.Filter.atTop (𝓝 (q x)) := tendsto_nhds_limUnder hxconv
  apply hlim.congr'
  have hpU : ∀ᶠ n in _root_.Filter.atTop, x + h n • v ∈ U := by
    have hp : _root_.Filter.Tendsto (fun n => x + h n • v) _root_.Filter.atTop (𝓝 x) := by
      simpa only [zero_smul, add_zero] using tendsto_const_nhds.add (hh.smul_const v)
    exact hp.eventually (hU.mem_nhds hxU)
  have hmU : ∀ᶠ n in _root_.Filter.atTop, x - h n • v ∈ U := by
    have hm : _root_.Filter.Tendsto (fun n => x - h n • v) _root_.Filter.atTop (𝓝 x) := by
      simpa only [zero_smul, sub_zero] using tendsto_const_nhds.sub (hh.smul_const v)
    exact hm.eventually (hU.mem_nhds hxU)
  filter_upwards [hpU, hmU] with n hnP hnM
  simp only [D, F, _root_.Set.indicator_of_mem hnP, _root_.Set.indicator_of_mem hnM, _root_.Set.indicator_of_mem hxU]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Calculus.exists_measurable_directional_second_derivative_of_concave_sub_quadratic then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Calculus.exists_measurable_directional_second_derivative_of_concave_sub_quadratic"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Calculus.exists_measurable_directional_second_derivative_of_concave_sub_quadratic ``Submission.DifferentialGeometry.Analysis.Calculus.exists_measurable_directional_second_derivative_of_concave_sub_quadratic

end DifferentialGeometry.Analysis.Calculus
