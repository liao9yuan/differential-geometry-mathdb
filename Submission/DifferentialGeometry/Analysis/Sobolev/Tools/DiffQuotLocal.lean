import Submission.DifferentialGeometry.Analysis.Sobolev.Tools.DifferenceQuotient.WeakDerivativeBound
import Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.Density

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.MeasureTheory _root_.Metric _root_.Filter _root_.Set _root_.Function
open scoped _root_.ENNReal _root_.Topology _root_.ContDiff

namespace DifferentialGeometry.Analysis.Sobolev

variable {d : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin d)

private theorem memLp_mul_cutoff
    {Ω : Set E} (hΩ : MeasurableSet Ω) {u η : E → ℝ}
    (hu : _root_.MeasureTheory.MemLp u 2 (volume.restrict Ω))
    (hη : Continuous η) (hηc : HasCompactSupport η) (hηs : tsupport η ⊆ Ω) :
    MemLp (fun x => η x * u x) 2 volume := by
  have hm : _root_.MeasureTheory.MemLp (fun x => η x * u x) 2 (volume.restrict Ω) :=
    hu.mul' ((hη.memLp_of_hasCompactSupport hηc : _root_.MeasureTheory.MemLp η ∞ _root_.MeasureTheory.MeasureSpace.volume).restrict Ω)
  have hi := (_root_.MeasureTheory.memLp_indicator_iff_restrict hΩ).mpr hm
  have heq : Ω.indicator (fun x => η x * u x) = fun x => η x * u x := by
    funext x
    by_cases hx : x ∈ Ω
    · rw [_root_.Set.indicator_of_mem hx]
    · rw [_root_.Set.indicator_of_notMem hx,
        image_eq_zero_of_notMem_tsupport (fun h => hx (hηs h)), _root_.MulZeroClass.zero_mul]
  rwa [heq] at hi

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.memLp_mul_cutoff
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.memLp_mul_cutoff target :: scope.openDecls } }

theorem hasWeakPartialDeriv_mul_cutoff_univ
    {Ω : Set E} (hΩ : IsOpen Ω) {u g η : E → ℝ}
    (hu : _root_.MeasureTheory.MemLp u 2 (volume.restrict Ω)) (hg : _root_.MeasureTheory.MemLp g 2 (volume.restrict Ω))
    (k : Fin d) (hweak : DeGiorgi.HasWeakPartialDeriv k g u Ω)
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηc : HasCompactSupport η)
    (hηs : tsupport η ⊆ Ω) :
    DeGiorgi.HasWeakPartialDeriv k
      (fun x => η x * g x + fderiv ℝ η x (EuclideanSpace.single k 1) * u x)
      (fun x => η x * u x) univ := by
  let e : E := EuclideanSpace.single k 1
  let Dη : E → ℝ := fun x => fderiv ℝ η x e
  have hDη : Continuous Dη :=
    (hη.continuous_fderiv (by simp)).clm_apply continuous_const
  have hDηc : HasCompactSupport Dη := hηc.fderiv_apply (𝕜 := ℝ) e
  have hDηs : tsupport Dη ⊆ Ω :=
    (tsupport_fderiv_apply_subset ℝ e).trans hηs
  have hηu := memLp_mul_cutoff hΩ.measurableSet hu hη.continuous hηc hηs
  have hηg := memLp_mul_cutoff hΩ.measurableSet hg hη.continuous hηc hηs
  have hDηu := memLp_mul_cutoff hΩ.measurableSet hu hDη hDηc hDηs
  intro φ hφ hφc _
  have hηφ : ContDiff ℝ (⊤ : ℕ∞) (fun x => η x * φ x) := hη.mul hφ
  have hηφc : HasCompactSupport (fun x => η x * φ x) := hηc.mul_right
  have hηφs : tsupport (fun x => η x * φ x) ⊆ Ω :=
    (tsupport_smul_subset_left η φ).trans hηs
  have hw := hweak (fun x => η x * φ x) hηφ hηφc hηφs
  have hfd (x : E) : fderiv ℝ (fun y => η y * φ y) x e =
      η x * fderiv ℝ φ x e + Dη x * φ x := by
    rw [fderiv_fun_mul (hη.differentiable (by simp)).differentiableAt
      (hφ.differentiable (by simp)).differentiableAt]
    simp only [add_apply, smul_apply, smul_eq_mul, Dη]
    ring
  have hL : _root_.MeasureTheory.Integrable (fun x => η x * u x * fderiv ℝ φ x e) volume :=
    hηu.integrable_mul ((hφ.continuous_fderiv (by simp)).clm_apply
      continuous_const |>.memLp_of_hasCompactSupport (hφc.fderiv_apply (𝕜 := ℝ) e) :
        _root_.MeasureTheory.MemLp (fun x => fderiv ℝ φ x e) 2 _root_.MeasureTheory.MeasureSpace.volume)
  have hC : _root_.MeasureTheory.Integrable (fun x => Dη x * u x * φ x) volume :=
    hDηu.integrable_mul (hφ.continuous.memLp_of_hasCompactSupport hφc : _root_.MeasureTheory.MemLp φ 2 _root_.MeasureTheory.MeasureSpace.volume)
  have hR : _root_.MeasureTheory.Integrable (fun x => η x * g x * φ x) volume :=
    hηg.integrable_mul (hφ.continuous.memLp_of_hasCompactSupport hφc : _root_.MeasureTheory.MemLp φ 2 _root_.MeasureTheory.MeasureSpace.volume)
  have hzero (x : E) (hx : x ∉ Ω) : η x = 0 ∧ Dη x = 0 :=
    ⟨image_eq_zero_of_notMem_tsupport (fun h => hx (hηs h)),
      image_eq_zero_of_notMem_tsupport (fun h => hx (hDηs h))⟩
  have hleft : (∫ x in Ω, u x * fderiv ℝ (fun y => η y * φ y) x e) =
      (∫ x, η x * u x * fderiv ℝ φ x e) + ∫ x, Dη x * u x * φ x := by
    calc
      _ = ∫ x in Ω, (η x * u x * fderiv ℝ φ x e + Dη x * u x * φ x) := by
        apply _root_.MeasureTheory.integral_congr_ae
        filter_upwards with x
        rw [hfd]
        ring
      _ = ∫ x, (η x * u x * fderiv ℝ φ x e + Dη x * u x * φ x) :=
        _root_.MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
          rcases hzero x hx with ⟨h1, h2⟩
          simp only [h1, h2, _root_.MulZeroClass.zero_mul, zero_add]
      _ = _ := _root_.MeasureTheory.integral_add hL hC
  have hright : (∫ x in Ω, g x * (η x * φ x)) = ∫ x, η x * g x * φ x := by
    calc
      _ = ∫ x in Ω, η x * g x * φ x := by
        apply _root_.MeasureTheory.integral_congr_ae
        filter_upwards with x
        ring
      _ = _ := _root_.MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
        simp only [(hzero x hx).1, _root_.MulZeroClass.zero_mul]
  rw [hleft, hright] at hw
  simp only [Measure.restrict_univ]
  change (∫ x, η x * u x * fderiv ℝ φ x e) =
    -∫ x, (η x * g x + Dη x * u x) * φ x
  simp_rw [add_mul]
  rw [_root_.MeasureTheory.integral_add hR hC]
  linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.hasWeakPartialDeriv_mul_cutoff_univ then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.hasWeakPartialDeriv_mul_cutoff_univ"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.hasWeakPartialDeriv_mul_cutoff_univ ``Submission.DifferentialGeometry.Analysis.Sobolev.hasWeakPartialDeriv_mul_cutoff_univ

theorem eLpNorm_diffQuot_le_eLpNorm_weakPartial_local
    {Ω Ω' Ω'' : Set E} (hΩ : IsOpen Ω) (hΩ' : IsOpen Ω') (hΩ'' : IsOpen Ω'')
    (hΩ'c : IsCompact (closure Ω')) (hΩ'Ω : closure Ω' ⊆ Ω)
    (hΩ''c : IsCompact (closure Ω''))
    {u g : E → ℝ} (hu : _root_.MeasureTheory.MemLp u 2 (volume.restrict Ω))
    (hg : _root_.MeasureTheory.MemLp g 2 (volume.restrict Ω))
    (k : Fin d) (hweak : DeGiorgi.HasWeakPartialDeriv k g u Ω)
    {h0 : ℝ} (hh0 : 0 < h0) (hthick : _root_.Metric.cthickening h0 (closure Ω'') ⊆ Ω')
    {h : ℝ} (hh : |h| ≤ h0) :
    _root_.MeasureTheory.eLpNorm (diffQuot k h u) 2 (volume.restrict Ω'') ≤
      eLpNorm g 2 (volume.restrict Ω') := by
  by_cases hhzero : h = 0
  · simp only [hhzero, diffQuot_zero_h, _root_.MeasureTheory.eLpNorm_zero, zero_le]
  obtain ⟨δ, η, hδ, _, hη, hηc, _, hηone, hηs⟩ :=
    Euclidean.exists_smooth_cutoff_with_neighborhood hΩ'c hΩ hΩ'Ω
  let v : E → ℝ := fun x => η x * u x
  let w : E → ℝ := fun x => η x * g x +
    fderiv ℝ η x (EuclideanSpace.single k 1) * u x
  have hv : _root_.MeasureTheory.MemLp v 2 volume := memLp_mul_cutoff hΩ.measurableSet hu hη.continuous hηc hηs
  have hDη : Continuous (fun x => fderiv ℝ η x (EuclideanSpace.single k 1)) :=
    (hη.continuous_fderiv (by simp)).clm_apply continuous_const
  have hDηc := hηc.fderiv_apply (𝕜 := ℝ) (EuclideanSpace.single k 1)
  have hDηs : tsupport (fun x => fderiv ℝ η x (EuclideanSpace.single k 1)) ⊆ Ω :=
    (tsupport_fderiv_apply_subset ℝ (EuclideanSpace.single k 1)).trans hηs
  have hw : _root_.MeasureTheory.MemLp w 2 volume :=
    (memLp_mul_cutoff hΩ.measurableSet hg hη.continuous hηc hηs).add
      (memLp_mul_cutoff hΩ.measurableSet hu hDη hDηc hDηs)
  have hwp : DeGiorgi.HasWeakPartialDeriv k w v univ :=
    hasWeakPartialDeriv_mul_cutoff_univ hΩ hu hg k hweak hη hηc hηs
  have hηeq (x : E) (hx : x ∈ Ω') : η x = 1 :=
    hηone x (_root_.Metric.self_subset_cthickening (closure Ω') (subset_closure hx))
  have hweq (x : E) (hx : x ∈ Ω') : w x = g x := by
    dsimp only [w]
    rw [hηeq x hx,
      Euclidean.fderiv_cutoff_apply_zero_on_cthickening hδ hηone (subset_closure hx) k]
    ring
  have hveq (x : E) (hx : x ∈ Ω') : v x = u x := by
    dsimp only [v]
    rw [hηeq x hx, one_mul]
  have hdq (x : E) (hx : x ∈ Ω'') : diffQuot k h v x = diffQuot k h u x := by
    have hx' : x ∈ Ω' := hthick (_root_.Metric.self_subset_cthickening (closure Ω'') (subset_closure hx))
    have hxshift : x + h • EuclideanSpace.single k 1 ∈ Ω' := by
      apply hthick
      apply _root_.Metric.closedBall_subset_cthickening (subset_closure hx) h0
      rw [_root_.Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul]
      simpa only [PiLp.norm_single, _root_.NormOneClass.norm_one, mul_one, Real.norm_eq_abs] using hh
    simp only [diffQuot_apply_of_ne k hhzero, hveq x hx', hveq _ hxshift]
  calc
    _root_.MeasureTheory.eLpNorm (diffQuot k h u) 2 (volume.restrict Ω'') =
        eLpNorm (diffQuot k h v) 2 (volume.restrict Ω'') :=
      _root_.MeasureTheory.eLpNorm_congr_ae ((_root_.MeasureTheory.ae_restrict_mem hΩ''.measurableSet).mono fun x hx => (hdq x hx).symm)
    _ ≤ _root_.MeasureTheory.eLpNorm w 2 (volume.restrict Ω') :=
      eLpNorm_diffQuot_le_eLpNorm_weakPartial hv hw k hwp hΩ' hΩ'' hΩ''c hh0 hthick hhzero hh
    _ = _root_.MeasureTheory.eLpNorm g 2 (volume.restrict Ω') :=
      _root_.MeasureTheory.eLpNorm_congr_ae ((_root_.MeasureTheory.ae_restrict_mem hΩ'.measurableSet).mono hweq)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.eLpNorm_diffQuot_le_eLpNorm_weakPartial_local then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.eLpNorm_diffQuot_le_eLpNorm_weakPartial_local"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.eLpNorm_diffQuot_le_eLpNorm_weakPartial_local ``Submission.DifferentialGeometry.Analysis.Sobolev.eLpNorm_diffQuot_le_eLpNorm_weakPartial_local

end DifferentialGeometry.Analysis.Sobolev
