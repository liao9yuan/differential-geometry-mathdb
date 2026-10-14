import Submission.DifferentialGeometry.Analysis.Sobolev.Nirenberg.TestFunction.Sobolev
import Submission.DifferentialGeometry.Analysis.Sobolev.Tools.DiffQuotLocal

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.MeasureTheory _root_.Set _root_.Metric
open scoped _root_.ENNReal _root_.ContDiff

namespace DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction

open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.NirenbergCrossBoundsNonSmooth

variable {d : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin d)

private theorem memLp_cutoff_mul
    {Ω : Set E} (hΩ : IsOpen Ω) {u χ : E → ℝ}
    (hu : _root_.MeasureTheory.MemLp u 2 (volume.restrict Ω))
    (hχ : Continuous χ) (hχc : HasCompactSupport χ) (hχs : tsupport χ ⊆ Ω) :
    MemLp (fun x => χ x * u x) 2 volume := by
  have hm : _root_.MeasureTheory.MemLp (fun x => χ x * u x) 2 (volume.restrict Ω) := hu.mul' ((hχ.memLp_of_hasCompactSupport hχc : _root_.MeasureTheory.MemLp χ ∞ _root_.MeasureTheory.MeasureSpace.volume).restrict Ω)
  have hi := (_root_.MeasureTheory.memLp_indicator_iff_restrict hΩ.measurableSet).mpr hm
  have heq : Ω.indicator (fun x => χ x * u x) = fun x => χ x * u x := by
    funext x
    by_cases hx : x ∈ Ω
    · rw [_root_.Set.indicator_of_mem hx]
    · rw [_root_.Set.indicator_of_notMem hx, image_eq_zero_of_notMem_tsupport (fun hs => hx (hχs hs)), _root_.MulZeroClass.zero_mul]
  rwa [heq] at hi

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.memLp_cutoff_mul
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.memLp_cutoff_mul target :: scope.openDecls } }

private theorem nirenbergTest_partial_congr
    (k j : Fin d) (h : ℝ) (η : E → ℝ) {u v g G : E → ℝ}
    (huv : _root_.Set.EqOn u v (_root_.Metric.cthickening |h| (tsupport η)))
    (hgG : _root_.Set.EqOn g G (_root_.Metric.cthickening |h| (tsupport η))) :
    (fun x => (η x)^2 * diffQuot k h g x +
      2 * η x * fderiv ℝ η x (EuclideanSpace.single j 1) * diffQuot k h u x) =
    (fun x => (η x)^2 * diffQuot k h G x +
      2 * η x * fderiv ℝ η x (EuclideanSpace.single j 1) * diffQuot k h v x) := by
  funext x
  by_cases hx : η x = 0
  · simp [hx]
  by_cases hh : h = 0
  · simp [hh]
  have hxs : x ∈ tsupport η := subset_tsupport η hx
  have hbase : x ∈ _root_.Metric.cthickening |h| (tsupport η) := _root_.Metric.self_subset_cthickening _ hxs
  have hshift : x + h • EuclideanSpace.single k (1 : ℝ) ∈ _root_.Metric.cthickening |h| (tsupport η) := by
    apply _root_.Metric.closedBall_subset_cthickening hxs |h|
    rw [_root_.Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul]
    simp only [PiLp.norm_single, _root_.NormOneClass.norm_one, mul_one, Real.norm_eq_abs, le_refl]
  simp only [diffQuot_apply_of_ne k hh, huv hbase, huv hshift, hgG hbase, hgG hshift]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.nirenbergTest_partial_congr
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.nirenbergTest_partial_congr target :: scope.openDecls } }

theorem hasWeakPartialDeriv_nirenbergTestFunction_local
    {Ω : Set E} (hΩ : IsOpen Ω) {u g η : E → ℝ}
    (hu : _root_.MeasureTheory.MemLp u 2 (volume.restrict Ω)) (hg : _root_.MeasureTheory.MemLp g 2 (volume.restrict Ω))
    (k j : Fin d) (h : ℝ) (hweak : DeGiorgi.HasWeakPartialDeriv j g u Ω)
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηc : HasCompactSupport η)
    (hηs : _root_.Metric.cthickening |h| (tsupport η) ⊆ Ω) :
    let G := diffQuot k (-h) (fun x => (η x)^2 * diffQuot k h g x +
      2 * η x * fderiv ℝ η x (EuclideanSpace.single j 1) * diffQuot k h u x)
    DeGiorgi.HasWeakPartialDeriv j G (nirenbergTestFunction k h η u) univ := by
  obtain ⟨δ, χ, hδ, _, hχ, hχc, _, hχone, hχs⟩ :=
    exists_smooth_cutoff_with_neighborhood (hηc.cthickening (r := |h|)) hΩ hηs
  let v := fun x => χ x * u x
  let w := fun x => χ x * g x + fderiv ℝ χ x (EuclideanSpace.single j 1) * u x
  have hv : _root_.MeasureTheory.MemLp v 2 volume := memLp_cutoff_mul hΩ hu hχ.continuous hχc hχs
  have hDχ := (hχ.continuous_fderiv (by simp)).clm_apply
    (continuous_const : Continuous (fun _ : E => EuclideanSpace.single j (1 : ℝ)))
  have hw : _root_.MeasureTheory.MemLp w 2 volume :=
    (memLp_cutoff_mul hΩ hg hχ.continuous hχc hχs).add
      (memLp_cutoff_mul hΩ hu hDχ (hχc.fderiv_apply (𝕜 := ℝ) (EuclideanSpace.single j 1))
        ((tsupport_fderiv_apply_subset ℝ (EuclideanSpace.single j 1)).trans hχs))
  have hvu : _root_.Set.EqOn v u (_root_.Metric.cthickening |h| (tsupport η)) := by
    intro x hx
    simp only [v, hχone x (_root_.Metric.self_subset_cthickening _ hx), one_mul]
  have hwg : _root_.Set.EqOn w g (_root_.Metric.cthickening |h| (tsupport η)) := by
    intro x hx
    simp only [w, hχone x (_root_.Metric.self_subset_cthickening _ hx), one_mul,
      fderiv_cutoff_apply_zero_on_cthickening hδ hχone hx j, _root_.MulZeroClass.zero_mul, add_zero]
  have htest := nirenbergTestFunction_congr_of_eqOn_cthickening k h hvu
  have hpart := nirenbergTest_partial_congr k j h η hvu hwg
  have hvloc : _root_.MeasureTheory.LocallyIntegrable v (volume.restrict _root_.Set.univ) := by
    simpa only [Measure.restrict_univ] using hv.locallyIntegrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hwloc : _root_.MeasureTheory.LocallyIntegrable w (volume.restrict _root_.Set.univ) := by
    simpa only [Measure.restrict_univ] using hw.locallyIntegrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hvwp : DeGiorgi.HasWeakPartialDeriv j w v univ :=
    hasWeakPartialDeriv_mul_cutoff_univ hΩ hu hg j hweak hχ hχc hχs
  have hwp := hasWeakPartialDeriv_nirenbergTestFunction k j h hη hvloc hwloc hvwp
  rw [htest, hpart] at hwp
  exact hwp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.hasWeakPartialDeriv_nirenbergTestFunction_local then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.hasWeakPartialDeriv_nirenbergTestFunction_local"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.hasWeakPartialDeriv_nirenbergTestFunction_local ``Submission.DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.hasWeakPartialDeriv_nirenbergTestFunction_local

theorem memLp_nirenbergTestFunction_partial_local
    {Ω : Set E} (hΩ : IsOpen Ω) {u g η : E → ℝ}
    (hu : _root_.MeasureTheory.MemLp u 2 (volume.restrict Ω)) (hg : _root_.MeasureTheory.MemLp g 2 (volume.restrict Ω))
    (k j : Fin d) (h : ℝ)
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηc : HasCompactSupport η)
    (hηs : _root_.Metric.cthickening |h| (tsupport η) ⊆ Ω) :
    let G := diffQuot k (-h) (fun x => (η x)^2 * diffQuot k h g x +
      2 * η x * fderiv ℝ η x (EuclideanSpace.single j 1) * diffQuot k h u x)
    MemLp G 2 volume := by
  obtain ⟨δ, χ, hδ, _, hχ, hχc, _, hχone, hχs⟩ :=
    exists_smooth_cutoff_with_neighborhood (hηc.cthickening (r := |h|)) hΩ hηs
  let v := fun x => χ x * u x
  let w := fun x => χ x * g x + fderiv ℝ χ x (EuclideanSpace.single j 1) * u x
  have hv : _root_.MeasureTheory.MemLp v 2 volume := memLp_cutoff_mul hΩ hu hχ.continuous hχc hχs
  have hDχ := (hχ.continuous_fderiv (by simp)).clm_apply
    (continuous_const : Continuous (fun _ : E => EuclideanSpace.single j (1 : ℝ)))
  have hw : _root_.MeasureTheory.MemLp w 2 volume :=
    (memLp_cutoff_mul hΩ hg hχ.continuous hχc hχs).add
      (memLp_cutoff_mul hΩ hu hDχ (hχc.fderiv_apply (𝕜 := ℝ) (EuclideanSpace.single j 1))
        ((tsupport_fderiv_apply_subset ℝ (EuclideanSpace.single j 1)).trans hχs))
  have hvu : _root_.Set.EqOn v u (_root_.Metric.cthickening |h| (tsupport η)) := by
    intro x hx
    simp only [v, hχone x (_root_.Metric.self_subset_cthickening _ hx), one_mul]
  have hwg : _root_.Set.EqOn w g (_root_.Metric.cthickening |h| (tsupport η)) := by
    intro x hx
    simp only [w, hχone x (_root_.Metric.self_subset_cthickening _ hx), one_mul,
      fderiv_cutoff_apply_zero_on_cthickening hδ hχone hx j, _root_.MulZeroClass.zero_mul, add_zero]
  have hpart := nirenbergTest_partial_congr k j h η hvu hwg
  change _root_.MeasureTheory.MemLp (diffQuot k (-h) _) 2 _root_.MeasureTheory.MeasureSpace.volume
  rw [← hpart]
  have hηsqc : HasCompactSupport (fun x => (η x)^2) :=
    hηc.comp_left (g := fun y : ℝ => y ^ 2) (by simp)
  have hηsq : _root_.MeasureTheory.MemLp (fun x => (η x)^2) ∞ volume :=
    (hη.continuous.pow 2).memLp_of_hasCompactSupport hηsqc
  have hηDc : HasCompactSupport
      (fun x => 2 * η x * fderiv ℝ η x (EuclideanSpace.single j 1)) := (hηc.mul_left).mul_right
  have hηD : _root_.MeasureTheory.MemLp (fun x => 2 * η x * fderiv ℝ η x (EuclideanSpace.single j 1)) ∞ volume :=
    ((continuous_const.mul hη.continuous).mul
      ((hη.continuous_fderiv (by simp)).clm_apply continuous_const)).memLp_of_hasCompactSupport hηDc
  have hfirst : _root_.MeasureTheory.MemLp (fun x => (η x)^2 * diffQuot k h w x) 2 volume :=
    (memLp_diffQuot_two k h hw).mul' hηsq
  have hsecond : _root_.MeasureTheory.MemLp (fun x => 2 * η x * fderiv ℝ η x (EuclideanSpace.single j 1) * diffQuot k h v x)
      2 volume := (memLp_diffQuot_two k h hv).mul' hηD
  exact memLp_diffQuot_two k (-h) (hfirst.add hsecond)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.memLp_nirenbergTestFunction_partial_local then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.memLp_nirenbergTestFunction_partial_local"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.memLp_nirenbergTestFunction_partial_local ``Submission.DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.memLp_nirenbergTestFunction_partial_local

end DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction
