import Submission.DifferentialGeometry.Analysis.Calculus.AbsolutelyContinuous.Energy
import Mathlib.Analysis.Calculus.Deriv.AffineMap
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Average
import Submission.DifferentialGeometry.External.DeGiorgi.UnitBallApproximation
import Submission.DifferentialGeometry.External.DeGiorgi.Poincare
import Submission.DifferentialGeometry.Analysis.Integration.L2Convergence

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Set _root_.Filter _root_.MeasureTheory
open scoped _root_.NNReal _root_.ENNReal _root_.Topology _root_.Pointwise

namespace DifferentialGeometry.Analysis.Sobolev

private theorem integrable_prod_restrict_of_continuous
    {X Y : Type*} [NormedAddCommGroup X] [NormedAddCommGroup Y]
    [ProperSpace X] [ProperSpace Y] [MeasurableSpace X] [BorelSpace X]
    [MeasurableSpace Y] [BorelSpace Y] {μ : _root_.MeasureTheory.Measure X} {ν : _root_.MeasureTheory.Measure Y}
    [_root_.MeasureTheory.IsFiniteMeasureOnCompacts μ] [_root_.MeasureTheory.IsFiniteMeasureOnCompacts ν]
    {s : Set X} {t : Set Y} (hs : MeasurableSet s) (ht : MeasurableSet t)
    (hbs : Bornology.IsBounded s) (hbt : Bornology.IsBounded t)
    {f : X × Y → ℝ} (hf : Continuous f) :
    Integrable f ((μ.restrict s).prod (ν.restrict t)) := by
  rw [Measure.prod_restrict]
  exact hf.continuousOn.integrableOn_of_subset_isCompact
    (hbs.isCompact_closure.prod hbt.isCompact_closure) (hs.prod ht)
    (_root_.Set.prod_mono subset_closure subset_closure) (hbs.prod hbt).measure_lt_top.ne

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.integrable_prod_restrict_of_continuous
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.integrable_prod_restrict_of_continuous target :: scope.openDecls } }

variable {d : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin d)

private theorem integral_affine_le_of_convex
    {Ω : Set E} (hΩ : MeasurableSet Ω) (hbΩ : Bornology.IsBounded Ω)
    (hcΩ : Convex ℝ Ω) (h : E → ℝ) (hh : Continuous h) (hpos : ∀ z ∈ Ω, 0 ≤ h z)
    {x : E} (hx : x ∈ Ω) {t : ℝ} (ht : t ∈ _root_.Set.Icc (1 / 2 : ℝ) 1) :
    (∫ y in Ω, h ((1 - t) • x + t • y)) ≤ (2 : ℝ) ^ d * ∫ y in Ω, h y := by
  have ht0 : 0 < t := by linarith [ht.1]
  let S : Set E := (fun y => (1 - t) • x + t • y) '' Ω
  have hS : S ⊆ Ω := by
    rintro z ⟨y, hy, rfl⟩
    exact hcΩ hx hy (sub_nonneg.mpr ht.2) ht0.le (by ring)
  have hi : _root_.MeasureTheory.IntegrableOn h Ω volume := hh.continuousOn.integrableOn_of_subset_isCompact
    hbΩ.isCompact_closure hΩ subset_closure hbΩ.measure_lt_top.ne
  have heq : (∫ y in Ω, h ((1 - t) • x + t • y)) =
      (t ^ d)⁻¹ * ∫ z in S, h z := by
    rw [Measure.setIntegral_comp_smul_of_pos _root_.MeasureTheory.MeasureSpace.volume (fun y => h ((1 - t) • x + y)) Ω ht0]
    rw [finrank_euclideanSpace_fin, smul_eq_mul]
    congr 1
    have himage : S = ((1 - t) • x + ·) '' (t • Ω) := by
      ext z
      simp only [S, _root_.Set.mem_image, _root_.Set.mem_smul_set]
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact ⟨t • y, ⟨y, hy, rfl⟩, rfl⟩
      · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
        exact ⟨y, hy, rfl⟩
    rw [himage]
    exact ((_root_.MeasureTheory.measurePreserving_add_left _root_.MeasureTheory.MeasureSpace.volume ((1 - t) • x)).setIntegral_image_emb
      (MeasurableEquiv.addLeft ((1 - t) • x)).measurableEmbedding h (t • Ω)).symm
  have hsmall : (∫ z in S, h z) ≤ ∫ z in Ω, h z :=
    _root_.MeasureTheory.setIntegral_mono_set hi ((_root_.MeasureTheory.ae_restrict_iff' hΩ).mpr (Eventually.of_forall hpos)) hS.eventuallyLE
  have hpow : (t ^ d)⁻¹ ≤ (2 : ℝ) ^ d := by
    rw [← inv_pow]
    apply pow_le_pow_left₀ (inv_nonneg.mpr ht0.le)
    have h := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1 / 2) ht.1
    norm_num only [one_div, inv_div, inv_one, div_one] at h
    exact h
  rw [heq]
  exact (mul_le_mul_of_nonneg_left hsmall (inv_nonneg.mpr (pow_nonneg ht0.le d))).trans
    (mul_le_mul_of_nonneg_right hpow
      (_root_.MeasureTheory.setIntegral_nonneg_of_ae_restrict ((_root_.MeasureTheory.ae_restrict_iff' hΩ).mpr (Eventually.of_forall hpos))))

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.integral_affine_le_of_convex
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.integral_affine_le_of_convex target :: scope.openDecls } }

private theorem integral_pair_lineMap_le_of_convex
    {Ω : Set E} (hΩ : MeasurableSet Ω) (hbΩ : Bornology.IsBounded Ω)
    (hcΩ : Convex ℝ Ω) (h : E → ℝ) (hh : Continuous h) (hpos : ∀ z ∈ Ω, 0 ≤ h z)
    {t : ℝ} (ht : t ∈ _root_.Set.Icc (0 : ℝ) 1) :
    (∫ x in Ω, ∫ y in Ω, h (AffineMap.lineMap x y t)) ≤
      (2 : ℝ) ^ d * volume.real Ω * ∫ z in Ω, h z := by
  let ν := volume.restrict Ω
  let : _root_.MeasureTheory.IsFiniteMeasure ν := isFiniteMeasure_restrict.mpr hbΩ.measure_lt_top.ne
  have hcont : Continuous (fun z : E × E => h (AffineMap.lineMap z.1 z.2 t)) := by
    simp only [AffineMap.lineMap_apply_module]
    fun_prop
  have hi : _root_.MeasureTheory.Integrable (fun z : E × E => h (AffineMap.lineMap z.1 z.2 t)) (ν.prod ν) :=
    integrable_prod_restrict_of_continuous hΩ hΩ hbΩ hbΩ hcont
  have hbound (q : ℝ) (hq : q ∈ _root_.Set.Icc (1 / 2 : ℝ) 1) :
      (∫ x in Ω, ∫ y in Ω, h (AffineMap.lineMap x y q)) ≤
        (2 : ℝ) ^ d * volume.real Ω * ∫ z in Ω, h z := by
    have hic : Continuous (fun z : E × E => h (AffineMap.lineMap z.1 z.2 q)) := by
      simp only [AffineMap.lineMap_apply_module]
      fun_prop
    have hii : _root_.MeasureTheory.Integrable (fun z : E × E => h (AffineMap.lineMap z.1 z.2 q)) (ν.prod ν) :=
      integrable_prod_restrict_of_continuous hΩ hΩ hbΩ hbΩ hic
    calc
      _ ≤ ∫ _ in Ω, (2 : ℝ) ^ d * ∫ z in Ω, h z := by
        apply _root_.MeasureTheory.setIntegral_mono_on hii.integral_prod_left (_root_.MeasureTheory.integrable_const _) hΩ
        intro x hx
        simpa only [AffineMap.lineMap_apply_module] using
          integral_affine_le_of_convex hΩ hbΩ hcΩ h hh hpos hx hq
      _ = _ := by rw [_root_.MeasureTheory.setIntegral_const, smul_eq_mul]; ring
  by_cases hhalf : (1 / 2 : ℝ) ≤ t
  · exact hbound t ⟨hhalf, ht.2⟩
  · have hq : 1 - t ∈ _root_.Set.Icc (1 / 2 : ℝ) 1 := by constructor <;> linarith [ht.1]
    have heq : (∫ x in Ω, ∫ y in Ω, h (AffineMap.lineMap x y t)) =
        ∫ x in Ω, ∫ y in Ω, h (AffineMap.lineMap x y (1 - t)) := by
      rw [_root_.MeasureTheory.integral_integral_swap hi]
      congr 1
      funext x
      congr 1
      funext y
      congr 1
      simp only [AffineMap.lineMap_apply_module, sub_sub_cancel]
      exact add_comm _ _
    rw [heq]
    exact hbound (1 - t) hq

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.integral_pair_lineMap_le_of_convex
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.integral_pair_lineMap_le_of_convex target :: scope.openDecls } }

private theorem norm_sub_sq_le_integral_lineMap_fderiv
    {u : E → ℝ} (hu : ContDiff ℝ 1 u) (x y : E) :
    ‖u x - u y‖ ^ 2 ≤ ‖x - y‖ ^ 2 *
      ∫ t in _root_.Set.Icc (0 : ℝ) 1, ‖fderiv ℝ u (AffineMap.lineMap x y t)‖ ^ 2 := by
  let v : ℝ → ℝ := u ∘ AffineMap.lineMap x y
  have hv (t : ℝ) : HasDerivAt v
      (fderiv ℝ u (AffineMap.lineMap x y t) (y - x)) t :=
    hu.differentiable (by norm_num) |>.differentiableAt.hasFDerivAt.comp_hasDerivAt t
      AffineMap.hasDerivAt_lineMap
  have hline : Continuous (fun t : ℝ => AffineMap.lineMap x y t) := by
    simp only [AffineMap.lineMap_apply_module]
    fun_prop
  have hcont : Continuous (fun t => fderiv ℝ u (AffineMap.lineMap x y t) (y - x)) :=
    ((hu.continuous_fderiv (by norm_num)).comp hline).clm_apply continuous_const
  have heq : (∫ t in _root_.Set.Icc (0 : ℝ) 1,
      fderiv ℝ u (AffineMap.lineMap x y t) (y - x)) = u y - u x := by
    rw [_root_.MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one]
    simpa only [v, Function.comp_apply, AffineMap.lineMap_apply_zero,
      AffineMap.lineMap_apply_one] using
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hv t)
        (hcont.intervalIntegrable 0 1)
  have hm : _root_.MeasureTheory.MemLp (fun t => fderiv ℝ u (AffineMap.lineMap x y t) (y - x)) 2
      (volume.restrict (_root_.Set.Icc (0 : ℝ) 1)) := by
    obtain ⟨R, hR⟩ := (isCompact_Icc.image hcont).isBounded.exists_norm_le
    apply MemLp.of_bound hcont.aestronglyMeasurable R
    filter_upwards [_root_.MeasureTheory.ae_restrict_mem measurableSet_Icc] with t ht
    exact hR _ (_root_.Set.mem_image_of_mem _ ht)
  have hcs := integral_sq_le_measure_mul_integral_sq hm
  rw [heq] at hcs
  have hmeasure : (volume.restrict (_root_.Set.Icc (0 : ℝ) 1)).real _root_.Set.univ = 1 := by
    simp [Measure.real]
  rw [hmeasure, one_mul] at hcs
  have hi : _root_.MeasureTheory.IntegrableOn (fun t => ‖fderiv ℝ u (AffineMap.lineMap x y t)‖ ^ 2)
      (_root_.Set.Icc (0 : ℝ) 1) := by
    apply Continuous.integrableOn_Icc
    exact (((hu.continuous_fderiv (by norm_num)).comp hline).norm).pow 2
  calc
    _ = (u y - u x) ^ 2 := by rw [Real.norm_eq_abs, sq_abs]; ring
    _ ≤ ∫ t in _root_.Set.Icc (0 : ℝ) 1, (fderiv ℝ u (AffineMap.lineMap x y t) (y - x)) ^ 2 := hcs
    _ ≤ ∫ t in _root_.Set.Icc (0 : ℝ) 1, ‖x - y‖ ^ 2 * ‖fderiv ℝ u (AffineMap.lineMap x y t)‖ ^ 2 := by
      apply _root_.MeasureTheory.integral_mono_ae hm.integrable_sq (hi.const_mul _)
      apply Eventually.of_forall
      intro t
      have h := (fderiv ℝ u (AffineMap.lineMap x y t)).le_opNorm (y - x)
      have hsq := pow_le_pow_left₀ (norm_nonneg _) h 2
      simpa only [Real.norm_eq_abs, sq_abs, mul_pow, norm_sub_rev y x, mul_comm] using hsq
    _ = _ := _root_.MeasureTheory.integral_const_mul _ _

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.norm_sub_sq_le_integral_lineMap_fderiv
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.norm_sub_sq_le_integral_lineMap_fderiv target :: scope.openDecls } }

theorem integral_integral_norm_sub_sq_le_of_convex
    {Ω : Set E} (hΩ : MeasurableSet Ω) (hbΩ : Bornology.IsBounded Ω)
    (hcΩ : Convex ℝ Ω) {u : E → ℝ} (hu : ContDiff ℝ 1 u)
    {D : ℝ} (hdiam : ∀ x ∈ Ω, ∀ y ∈ Ω, ‖x - y‖ ≤ D) :
    (∫ x in Ω, ∫ y in Ω, ‖u x - u y‖ ^ 2) ≤
      (2 : ℝ) ^ d * D ^ 2 * volume.real Ω * ∫ z in Ω, ‖fderiv ℝ u z‖ ^ 2 := by
  let ν := volume.restrict Ω
  let τm := volume.restrict (_root_.Set.Icc (0 : ℝ) 1)
  let : _root_.MeasureTheory.IsFiniteMeasure ν := isFiniteMeasure_restrict.mpr hbΩ.measure_lt_top.ne
  let h (z : E) := ‖fderiv ℝ u z‖ ^ 2
  have hh : Continuous h := (hu.continuous_fderiv (by norm_num)).norm.pow 2
  let H (z : ℝ × (E × E)) := h (AffineMap.lineMap z.2.1 z.2.2 z.1)
  have hHc : Continuous H := by
    dsimp only [H]
    apply hh.comp
    simp only [AffineMap.lineMap_apply_module]
    fun_prop
  have hHi : _root_.MeasureTheory.Integrable H (τm.prod (ν.prod ν)) := by
    rw [show ν.prod ν = (volume.prod _root_.MeasureTheory.MeasureSpace.volume).restrict (Ω ×ˢ Ω) from Measure.prod_restrict Ω Ω]
    exact integrable_prod_restrict_of_continuous measurableSet_Icc (hΩ.prod hΩ)
      isCompact_Icc.isBounded (hbΩ.prod hbΩ) hHc
  have hPi : _root_.MeasureTheory.Integrable (fun z : E × E => ‖u z.1 - u z.2‖ ^ 2) (ν.prod ν) :=
    integrable_prod_restrict_of_continuous hΩ hΩ hbΩ hbΩ (by fun_prop)
  have hswap : (∫ z : E × E, ∫ t, H (t, z) ∂τm ∂ν.prod ν) =
      ∫ t, ∫ z : E × E, H (t, z) ∂ν.prod ν ∂τm :=
    (_root_.MeasureTheory.integral_integral_swap hHi).symm
  have hinner (t : ℝ) (ht : t ∈ _root_.Set.Icc (0 : ℝ) 1) :
      (∫ z : E × E, H (t, z) ∂ν.prod ν) ≤
        (2 : ℝ) ^ d * volume.real Ω * ∫ z in Ω, h z := by
    have hit : _root_.MeasureTheory.Integrable (fun z : E × E => H (t, z)) (ν.prod ν) :=
      integrable_prod_restrict_of_continuous hΩ hΩ hbΩ hbΩ (hHc.comp (by fun_prop))
    rw [_root_.MeasureTheory.integral_prod _ hit]
    exact integral_pair_lineMap_le_of_convex hΩ hbΩ hcΩ h hh (fun z _ => sq_nonneg _) ht
  calc
    _ = ∫ z : E × E, ‖u z.1 - u z.2‖ ^ 2 ∂ν.prod ν := (_root_.MeasureTheory.integral_prod _ hPi).symm
    _ ≤ ∫ z : E × E, D ^ 2 * ∫ t, H (t, z) ∂τm ∂ν.prod ν := by
      apply _root_.MeasureTheory.integral_mono_ae hPi (hHi.integral_prod_right.const_mul _)
      rw [Measure.prod_restrict]
      filter_upwards [_root_.MeasureTheory.ae_restrict_mem (hΩ.prod hΩ)] with z hz
      exact (norm_sub_sq_le_integral_lineMap_fderiv hu z.1 z.2).trans
        (mul_le_mul_of_nonneg_right
          (pow_le_pow_left₀ (norm_nonneg _) (hdiam z.1 hz.1 z.2 hz.2) 2)
          (_root_.MeasureTheory.integral_nonneg fun t => sq_nonneg _))
    _ = D ^ 2 * ∫ t, ∫ z : E × E, H (t, z) ∂ν.prod ν ∂τm := by
      rw [_root_.MeasureTheory.integral_const_mul, hswap]
    _ ≤ D ^ 2 * ∫ _t : ℝ, ((2 : ℝ) ^ d * volume.real Ω * ∫ z in Ω, h z) ∂τm := by
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg D)
      apply _root_.MeasureTheory.integral_mono_ae hHi.integral_prod_left (_root_.MeasureTheory.integrable_const _)
      filter_upwards [_root_.MeasureTheory.ae_restrict_mem measurableSet_Icc] with t ht
      exact hinner t ht
    _ = _ := by
      have hm : τm.real _root_.Set.univ = 1 := by simp [τm, Measure.real]
      rw [_root_.MeasureTheory.integral_const, hm, one_smul]
      dsimp only [h]
      ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.integral_integral_norm_sub_sq_le_of_convex then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.integral_integral_norm_sub_sq_le_of_convex"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.integral_integral_norm_sub_sq_le_of_convex ``Submission.DifferentialGeometry.Analysis.Sobolev.integral_integral_norm_sub_sq_le_of_convex

theorem integral_norm_sub_average_sq_le_of_convex
    {Ω : Set E} (hΩ : MeasurableSet Ω) (hbΩ : Bornology.IsBounded Ω)
    (hcΩ : Convex ℝ Ω) {u : E → ℝ} (hu : ContDiff ℝ 1 u)
    {D : ℝ} (hdiam : ∀ x ∈ Ω, ∀ y ∈ Ω, ‖x - y‖ ≤ D) :
    (∫ x in Ω, ‖u x - ⨍ y in Ω, u y‖ ^ 2) ≤
      (2 : ℝ) ^ d * D ^ 2 * ∫ z in Ω, ‖fderiv ℝ u z‖ ^ 2 := by
  by_cases hzero : _root_.MeasureTheory.MeasureSpace.volume Ω = 0
  · simp only [Measure.restrict_eq_zero.mpr hzero, _root_.MeasureTheory.integral_zero_measure, _root_.MulZeroClass.mul_zero, le_refl]
  let ν := volume.restrict Ω
  let : _root_.MeasureTheory.IsFiniteMeasure ν := isFiniteMeasure_restrict.mpr hbΩ.measure_lt_top.ne
  let m := volume.real Ω
  have hm : 0 < m := ENNReal.toReal_pos hzero hbΩ.measure_lt_top.ne
  have hmeasure : ν.real _root_.Set.univ = m := by simp [ν, m, Measure.real]
  let av := ⨍ y in Ω, u y
  have hum : _root_.MeasureTheory.MemLp u 2 ν := by
    obtain ⟨R, hR⟩ := (hbΩ.isCompact_closure.image hu.continuous).isBounded.exists_norm_le
    apply MemLp.of_bound hu.continuous.aestronglyMeasurable R
    filter_upwards [_root_.MeasureTheory.ae_restrict_mem hΩ] with x hx
    exact hR _ (_root_.Set.mem_image_of_mem u (subset_closure hx))
  have hui : _root_.MeasureTheory.Integrable u ν := hum.integrable (by norm_num)
  have hav : m * av = ∫ y, u y ∂ν := by
    have h := _root_.MeasureTheory.measure_smul_average (μ := ν) u
    simpa only [hmeasure, smul_eq_mul] using h
  have hpoint (x : E) : m * ‖u x - av‖ ^ 2 ≤ ∫ y, ‖u x - u y‖ ^ 2 ∂ν := by
    have hd : _root_.MeasureTheory.MemLp (fun y => u x - u y) 2 ν := (_root_.MeasureTheory.memLp_const (u x)).sub hum
    have hcs := integral_sq_le_measure_mul_integral_sq hd
    have heq : (∫ y, u x - u y ∂ν) = m * (u x - av) := by
      rw [_root_.MeasureTheory.integral_sub (_root_.MeasureTheory.integrable_const _) hui, _root_.MeasureTheory.integral_const, hmeasure, smul_eq_mul, ← hav]
      ring
    rw [heq, hmeasure] at hcs
    simp only [Real.norm_eq_abs, sq_abs]
    apply (mul_le_mul_iff_right₀ hm).mp
    simpa only [mul_pow, pow_two, mul_assoc, mul_left_comm] using hcs
  have hvi : _root_.MeasureTheory.Integrable (fun x => ‖u x - av‖ ^ 2) ν := by
    have hv := (hum.sub (_root_.MeasureTheory.memLp_const av)).norm.integrable_sq
    exact hv
  have hPi : _root_.MeasureTheory.Integrable (fun z : E × E => ‖u z.1 - u z.2‖ ^ 2) (ν.prod ν) :=
    integrable_prod_restrict_of_continuous hΩ hΩ hbΩ hbΩ (by fun_prop)
  have hmean : m * (∫ x, ‖u x - av‖ ^ 2 ∂ν) ≤
      ∫ x, ∫ y, ‖u x - u y‖ ^ 2 ∂ν ∂ν := by
    rw [← _root_.MeasureTheory.integral_const_mul]
    exact _root_.MeasureTheory.integral_mono_ae (hvi.const_mul m) hPi.integral_prod_left (Eventually.of_forall hpoint)
  have hp := integral_integral_norm_sub_sq_le_of_convex hΩ hbΩ hcΩ hu hdiam
  have hprod : m * (∫ x, ‖u x - av‖ ^ 2 ∂ν) ≤
      m * ((2 : ℝ) ^ d * D ^ 2 * ∫ z in Ω, ‖fderiv ℝ u z‖ ^ 2) := by
    apply (hmean.trans hp).trans_eq
    dsimp only [m]
    ring
  exact (mul_le_mul_iff_right₀ hm).mp hprod

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.integral_norm_sub_average_sq_le_of_convex then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.integral_norm_sub_average_sq_le_of_convex"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.integral_norm_sub_average_sq_le_of_convex ``Submission.DifferentialGeometry.Analysis.Sobolev.integral_norm_sub_average_sq_le_of_convex

theorem integral_norm_sub_average_sq_le_diam_of_convex
    {Ω : Set E} (hΩ : MeasurableSet Ω) (hbΩ : Bornology.IsBounded Ω)
    (hcΩ : Convex ℝ Ω) {u : E → ℝ} (hu : ContDiff ℝ 1 u) :
    (∫ x in Ω, ‖u x - ⨍ y in Ω, u y‖ ^ 2) ≤
      (2 : ℝ) ^ d * Metric.diam Ω ^ 2 * ∫ z in Ω, ‖fderiv ℝ u z‖ ^ 2 := by
  apply integral_norm_sub_average_sq_le_of_convex hΩ hbΩ hcΩ hu
  intro x hx y hy
  simpa only [dist_eq_norm] using Metric.dist_le_diam_of_mem hbΩ hx hy

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.integral_norm_sub_average_sq_le_diam_of_convex then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.integral_norm_sub_average_sq_le_diam_of_convex"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.integral_norm_sub_average_sq_le_diam_of_convex ``Submission.DifferentialGeometry.Analysis.Sobolev.integral_norm_sub_average_sq_le_diam_of_convex

end DifferentialGeometry.Analysis.Sobolev

end

noncomputable section

open _root_.Set _root_.Filter _root_.MeasureTheory
open scoped _root_.ENNReal _root_.ContDiff _root_.Topology

namespace DifferentialGeometry.Analysis.Sobolev.Euclidean

private theorem integral_sub_average_sq_eq
    {X : Type*} [MeasurableSpace X] {μ : _root_.MeasureTheory.Measure X} [_root_.MeasureTheory.IsFiniteMeasure μ]
    {f : X → ℝ} (hf : _root_.MeasureTheory.MemLp f 2 μ) :
    (∫ x, (f x - ⨍ y, f y ∂μ) ^ 2 ∂μ) =
      (∫ x, f x ^ 2 ∂μ) - μ.real _root_.Set.univ * (⨍ y, f y ∂μ) ^ 2 := by
  let m := ⨍ y, f y ∂μ
  have hfm : _root_.MeasureTheory.Integrable f μ := hf.integrable (by norm_num)
  have hav : μ.real _root_.Set.univ * m = ∫ x, f x ∂μ := by
    simpa only [m, smul_eq_mul] using _root_.MeasureTheory.measure_smul_average (μ := μ) f
  have heq (x : X) : (f x - m) ^ 2 = f x ^ 2 - 2 * m * f x + m ^ 2 := by ring
  change (∫ x, (f x - m) ^ 2 ∂μ) = (∫ x, f x ^ 2 ∂μ) - μ.real _root_.Set.univ * m ^ 2
  simp_rw [heq]
  have hsub : _root_.MeasureTheory.Integrable (fun x => f x ^ 2 - 2 * m * f x) μ := by
    simpa only [Pi.sub_def] using hf.integrable_sq.sub (hfm.const_mul (2 * m))
  rw [_root_.MeasureTheory.integral_add hsub (_root_.MeasureTheory.integrable_const _),
    _root_.MeasureTheory.integral_sub hf.integrable_sq (hfm.const_mul (2 * m)), _root_.MeasureTheory.integral_const_mul, _root_.MeasureTheory.integral_const,
    smul_eq_mul, ← hav]
  ring

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.integral_sub_average_sq_eq
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.Euclidean.integral_sub_average_sq_eq target :: scope.openDecls } }

private theorem tendsto_integral_sub_average_sq_of_tendsto_eLpNorm
    {X : Type*} [MeasurableSpace X] {μ : _root_.MeasureTheory.Measure X} [_root_.MeasureTheory.IsFiniteMeasure μ]
    {f : ℕ → X → ℝ} {u : X → ℝ}
    (hf : ∀ n, _root_.MeasureTheory.MemLp (f n) 2 μ) (hu : _root_.MeasureTheory.MemLp u 2 μ)
    (hlim : _root_.Filter.Tendsto (fun n => _root_.MeasureTheory.eLpNorm (fun x => f n x - u x) 2 μ) _root_.Filter.atTop (𝓝 0)) :
    _root_.Filter.Tendsto (fun n => ∫ x, (f n x - ⨍ y, f n y ∂μ) ^ 2 ∂μ) _root_.Filter.atTop
      (𝓝 (∫ x, (u x - ⨍ y, u y ∂μ) ^ 2 ∂μ)) := by
  have hint : _root_.Filter.Tendsto (fun n => ∫ x, f n x ∂μ) _root_.Filter.atTop (𝓝 (∫ x, u x ∂μ)) := by
    simpa only [mul_one] using
      DifferentialGeometry.Analysis.Integration.tendsto_integral_mul_of_eLpNorm_two
        hf hu (_root_.MeasureTheory.memLp_const (1 : ℝ)) hlim
  have hav : _root_.Filter.Tendsto (fun n => ⨍ x, f n x ∂μ) _root_.Filter.atTop (𝓝 (⨍ x, u x ∂μ)) := by
    simpa only [_root_.MeasureTheory.average_eq, smul_eq_mul] using hint.const_mul (μ.real _root_.Set.univ)⁻¹
  have hsq :=
    DifferentialGeometry.Analysis.Integration.tendsto_integral_sq_of_eLpNorm_two hf hu hlim
  simp_rw [integral_sub_average_sq_eq (hf _), integral_sub_average_sq_eq hu]
  exact hsq.sub ((hav.pow 2).const_mul (μ.real _root_.Set.univ))

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.tendsto_integral_sub_average_sq_of_tendsto_eLpNorm
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.Euclidean.tendsto_integral_sub_average_sq_of_tendsto_eLpNorm target :: scope.openDecls } }

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

private theorem integral_sub_average_sq_le_of_convex_subset_unitBall_posdim
    [NeZero d] {S : Set E} (hS : MeasurableSet S) (hconv : Convex ℝ S)
    (hsub : S ⊆ Metric.ball (0 : E) 1) {u : E → ℝ}
    (hu : DeGiorgi.MemW1pWitness 2 u (Metric.ball (0 : E) 1))
    {D : ℝ} (hdiam : ∀ x ∈ S, ∀ y ∈ S, ‖x - y‖ ≤ D) :
    (∫ x in S, (u x - ⨍ y in S, u y) ^ 2) ≤
      (2 : ℝ) ^ d * D ^ 2 * ∫ x in S, ‖hu.weakGrad x‖ ^ 2 := by
  let μ := volume.restrict S
  have hSb : Bornology.IsBounded S := Metric.isBounded_ball.subset hsub
  let _ : _root_.MeasureTheory.IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr hSb.measure_lt_top.ne
  obtain ⟨φ, hφ, hφc, hval, hder⟩ := DeGiorgi.exists_smooth_W12_approx_on_unitBall hu
  have hum : _root_.MeasureTheory.MemLp u 2 μ := hu.memLp.mono_measure (Measure.restrict_mono_set _root_.MeasureTheory.MeasureSpace.volume hsub)
  have hφm (n : ℕ) : _root_.MeasureTheory.MemLp (φ n) 2 μ :=
    ((hφ n).continuous.memLp_of_hasCompactSupport (hφc n)).restrict S
  have hvalS : _root_.Filter.Tendsto (fun n => _root_.MeasureTheory.eLpNorm (fun x => φ n x - u x) 2 μ) _root_.Filter.atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hval
      (fun _ => zero_le) (fun n => _root_.MeasureTheory.eLpNorm_mono_measure _ (Measure.restrict_mono_set _root_.MeasureTheory.MeasureSpace.volume hsub))
  have hvar := tendsto_integral_sub_average_sq_of_tendsto_eLpNorm hφm hum hvalS
  have hdm (n : ℕ) (i : Fin d) : _root_.MeasureTheory.MemLp (fun x => fderiv ℝ (φ n) x
      (EuclideanSpace.single i 1)) 2 μ :=
    ((((hφ n).continuous_fderiv (by simp)).clm_apply continuous_const).memLp_of_hasCompactSupport
      ((hφc n).fderiv_apply ℝ (EuclideanSpace.single i 1))).restrict S
  have hgm (i : Fin d) : _root_.MeasureTheory.MemLp (fun x => hu.weakGrad x i) 2 μ :=
    (hu.weakGrad_component_memLp i).mono_measure (Measure.restrict_mono_set _root_.MeasureTheory.MeasureSpace.volume hsub)
  have hderS (i : Fin d) : _root_.Filter.Tendsto (fun n => _root_.MeasureTheory.eLpNorm (fun x =>
      fderiv ℝ (φ n) x (EuclideanSpace.single i 1) - hu.weakGrad x i) 2 μ)
      atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hder i)
      (fun _ => zero_le) (fun n => _root_.MeasureTheory.eLpNorm_mono_measure _ (Measure.restrict_mono_set _root_.MeasureTheory.MeasureSpace.volume hsub))
  have hgrad : _root_.Filter.Tendsto (fun n => ∫ x in S, ‖fderiv ℝ (φ n) x‖ ^ 2) _root_.Filter.atTop
      (𝓝 (∫ x in S, ‖hu.weakGrad x‖ ^ 2)) := by
    have hn (n : ℕ) : (∫ x in S, ‖fderiv ℝ (φ n) x‖ ^ 2) =
        ∑ i : Fin d, ∫ x in S, (fderiv ℝ (φ n) x (EuclideanSpace.single i 1)) ^ 2 := by
      simp only [DeGiorgi.norm_fderiv_eq_smoothGradNorm, DeGiorgi.smoothGradNorm,
        EuclideanSpace.norm_sq_eq, Real.norm_eq_abs, sq_abs]
      exact _root_.MeasureTheory.integral_finsetSum _ fun i _ => (hdm n i).integrable_sq
    have hg : (∫ x in S, ‖hu.weakGrad x‖ ^ 2) =
        ∑ i : Fin d, ∫ x in S, (hu.weakGrad x i) ^ 2 := by
      simp_rw [EuclideanSpace.norm_sq_eq, Real.norm_eq_abs, sq_abs]
      exact _root_.MeasureTheory.integral_finsetSum _ fun i _ => (hgm i).integrable_sq
    simp_rw [hn, hg]
    exact tendsto_finsetSum Finset.univ fun i _ =>
      DifferentialGeometry.Analysis.Integration.tendsto_integral_sq_of_eLpNorm_two
        (fun n => hdm n i) (hgm i) (hderS i)
  apply le_of_tendsto_of_tendsto hvar (hgrad.const_mul ((2 : ℝ) ^ d * D ^ 2))
  apply Eventually.of_forall
  intro n
  simpa only [Real.norm_eq_abs, sq_abs] using
    DifferentialGeometry.Analysis.Sobolev.integral_norm_sub_average_sq_le_of_convex
      hS hSb hconv ((hφ n).of_le (by simp)) hdiam

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.integral_sub_average_sq_le_of_convex_subset_unitBall_posdim
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.Euclidean.integral_sub_average_sq_le_of_convex_subset_unitBall_posdim target :: scope.openDecls } }

theorem integral_sub_average_sq_le_of_convex_subset_unitBall
    {S : Set E} (hS : MeasurableSet S) (hconv : Convex ℝ S)
    (hsub : S ⊆ Metric.ball (0 : E) 1) {u : E → ℝ}
    (hu : DeGiorgi.MemW1pWitness 2 u (Metric.ball (0 : E) 1))
    {D : ℝ} (hdiam : ∀ x ∈ S, ∀ y ∈ S, ‖x - y‖ ≤ D) :
    (∫ x in S, (u x - ⨍ y in S, u y) ^ 2) ≤
      (2 : ℝ) ^ d * D ^ 2 * ∫ x in S, ‖hu.weakGrad x‖ ^ 2 := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · have heq : u = fun _ => u 0 := funext fun x => congrArg u (Subsingleton.elim x 0)
    have huc : ContDiff ℝ 1 u := by rw [heq]; exact contDiff_const
    have h := DifferentialGeometry.Analysis.Sobolev.integral_norm_sub_average_sq_le_of_convex
      hS (Metric.isBounded_ball.subset hsub) hconv huc hdiam
    have hd0 (x : EuclideanSpace ℝ (Fin 0)) : fderiv ℝ u x = 0 := by
      rw [heq]
      exact fderiv_const_apply _
    simp only [hd0, ContinuousLinearMap.opNorm_zero, zero_pow (by decide : 2 ≠ 0),
      _root_.MeasureTheory.integral_zero, _root_.MulZeroClass.mul_zero, Real.norm_eq_abs, sq_abs] at h
    exact h.trans (by positivity)
  · let _ : NeZero d := ⟨hd.ne'⟩
    exact integral_sub_average_sq_le_of_convex_subset_unitBall_posdim hS hconv hsub hu hdiam

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Euclidean.integral_sub_average_sq_le_of_convex_subset_unitBall then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Euclidean.integral_sub_average_sq_le_of_convex_subset_unitBall"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Euclidean.integral_sub_average_sq_le_of_convex_subset_unitBall ``Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.integral_sub_average_sq_le_of_convex_subset_unitBall

theorem integral_norm_sub_average_sq_le_of_convex_subset_unitBall
    {ι : Type*} [Fintype ι] {S : Set E} (hS : MeasurableSet S) (hconv : Convex ℝ S)
    (hsub : S ⊆ Metric.ball (0 : E) 1) {u : E → EuclideanSpace ℝ ι}
    (hu : ∀ i, DeGiorgi.MemW1pWitness 2 (fun x => u x i) (Metric.ball (0 : E) 1))
    {D : ℝ} (hdiam : ∀ x ∈ S, ∀ y ∈ S, ‖x - y‖ ≤ D) :
    (∫ x in S, ‖u x - ⨍ y in S, u y‖ ^ 2) ≤
      (2 : ℝ) ^ d * D ^ 2 * ∑ i, ∫ x in S, ‖(hu i).weakGrad x‖ ^ 2 := by
  classical
  let μ := volume.restrict S
  have hSb : Bornology.IsBounded S := Metric.isBounded_ball.subset hsub
  let _ : _root_.MeasureTheory.IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr hSb.measure_lt_top.ne
  have hm (i : ι) : _root_.MeasureTheory.MemLp (fun x => u x i) 2 μ :=
    (hu i).memLp.mono_measure (Measure.restrict_mono_set _root_.MeasureTheory.MeasureSpace.volume hsub)
  have hum : _root_.MeasureTheory.MemLp u 2 μ := MemLp.of_eval_piLp hm
  have hui : _root_.MeasureTheory.Integrable u μ := hum.integrable (by norm_num)
  have hav (i : ι) : (⨍ y in S, u y) i = ⨍ y in S, u y i := by
    rw [_root_.MeasureTheory.setAverage_eq, _root_.MeasureTheory.setAverage_eq]
    change (volume.real S)⁻¹ * (∫ y in S, u y) i = _
    have he := (EuclideanSpace.proj i).integral_comp_comm hui
    change (∫ y in S, u y i) = (∫ y in S, u y) i at he
    rw [he, smul_eq_mul]
  have hi (i : ι) : _root_.MeasureTheory.Integrable (fun x => (u x i - ⨍ y in S, u y i) ^ 2) μ :=
    ((hm i).sub (_root_.MeasureTheory.memLp_const _)).integrable_sq
  have heq : (∫ x in S, ‖u x - ⨍ y in S, u y‖ ^ 2) =
      ∑ i, ∫ x in S, (u x i - ⨍ y in S, u y i) ^ 2 := by
    simp_rw [EuclideanSpace.norm_sq_eq, PiLp.sub_apply, hav, Real.norm_eq_abs, sq_abs]
    exact _root_.MeasureTheory.integral_finsetSum _ fun i _ => hi i
  rw [heq, Finset.mul_sum]
  exact Finset.sum_le_sum fun i _ =>
    integral_sub_average_sq_le_of_convex_subset_unitBall hS hconv hsub (hu i) hdiam

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Euclidean.integral_norm_sub_average_sq_le_of_convex_subset_unitBall then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Euclidean.integral_norm_sub_average_sq_le_of_convex_subset_unitBall"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Euclidean.integral_norm_sub_average_sq_le_of_convex_subset_unitBall ``Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.integral_norm_sub_average_sq_le_of_convex_subset_unitBall

theorem integral_norm_sub_average_sq_inter_ball_le_weakGrad
    {ι : Type*} [Fintype ι] {u : E → EuclideanSpace ℝ ι}
    (hu : ∀ i, DeGiorgi.MemW1pWitness 2 (fun x => u x i) (Metric.ball (0 : E) 1))
    (x₀ : E) (r : ℝ) :
    (∫ x in Metric.ball (0 : E) 1 ∩ Metric.ball x₀ r,
      ‖u x - ⨍ y in Metric.ball (0 : E) 1 ∩ Metric.ball x₀ r, u y‖ ^ 2) ≤
      (2 : ℝ) ^ (d + 2) * r ^ 2 *
        ∑ i, ∫ x in Metric.ball (0 : E) 1 ∩ Metric.ball x₀ r, ‖(hu i).weakGrad x‖ ^ 2 := by
  have h := integral_norm_sub_average_sq_le_of_convex_subset_unitBall
    (Metric.isOpen_ball.measurableSet.inter Metric.isOpen_ball.measurableSet)
    ((convex_ball (0 : E) 1).inter (convex_ball x₀ r)) _root_.Set.inter_subset_left hu
    (D := 2 * r) (fun x hx y hy => by
      have hx' : _root_.Dist.dist x x₀ < r := hx.2
      have hy' : _root_.Dist.dist y x₀ < r := hy.2
      simpa only [dist_eq_norm] using (dist_triangle_right x y x₀).trans
        (show _root_.Dist.dist x x₀ + _root_.Dist.dist y x₀ ≤ 2 * r from by linarith [hx', hy']))
  have hc : (2 : ℝ) ^ d * (2 * r) ^ 2 = (2 : ℝ) ^ (d + 2) * r ^ 2 := by
    rw [pow_add, mul_pow]
    ring
  simpa only [hc] using h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Euclidean.integral_norm_sub_average_sq_inter_ball_le_weakGrad then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Euclidean.integral_norm_sub_average_sq_inter_ball_le_weakGrad"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Euclidean.integral_norm_sub_average_sq_inter_ball_le_weakGrad ``Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.integral_norm_sub_average_sq_inter_ball_le_weakGrad

end DifferentialGeometry.Analysis.Sobolev.Euclidean

end
