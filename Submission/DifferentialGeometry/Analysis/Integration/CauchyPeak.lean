import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.PeakFunction
import Mathlib.MeasureTheory.Function.Jacobian

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.Bornology _root_.Complex _root_.Filter _root_.MeasureTheory _root_.Real _root_.Set
open scoped _root_.Topology

namespace DifferentialGeometry.Analysis.Integration

theorem tendsto_integral_regularized_inv_sq_smul_of_integrable_of_ae_lower_bound
    {α V : Type*} {m : MeasurableSpace α} {μ : _root_.MeasureTheory.Measure α}
    [NormedAddCommGroup V] [NormedSpace Real V]
    {u : α → Real} {b : α → V} {δ : Real}
    (hu : AEMeasurable u μ) (hb : _root_.MeasureTheory.Integrable b μ)
    (hδ : 0 < δ) (huδ : ∀ᵐ x ∂μ, δ ≤ u x) :
    _root_.Filter.Tendsto
      (fun ε : Real => ∫ x, (ε * (u x + ε)⁻¹ ^ 2) • b x ∂μ)
      (𝓝[>] 0) (𝓝 0) := by
  let F : Real → α → V := fun ε x => (ε * (u x + ε)⁻¹ ^ 2) • b x
  have hF_meas : ∀ ε : Real, _root_.MeasureTheory.AEStronglyMeasurable (F ε) μ := by
    intro ε
    exact (((hu.add_const ε).inv.pow_const 2).const_mul ε).aestronglyMeasurable.smul
      hb.aestronglyMeasurable
  have hbound_integrable : _root_.MeasureTheory.Integrable (fun x => δ⁻¹ * ‖b x‖) μ := by
    simpa only [smul_eq_mul] using hb.norm.const_mul δ⁻¹
  have hbound : ∀ᶠ ε : Real in 𝓝[>] 0,
      ∀ᵐ x ∂μ, ‖F ε x‖ ≤ δ⁻¹ * ‖b x‖ := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    change 0 < ε at hε
    filter_upwards [huδ] with x hx
    have hu_pos : 0 < u x := hδ.trans_le hx
    have hden_pos : 0 < u x + ε := add_pos hu_pos hε
    have hscalar_nonneg : 0 ≤ ε * (u x + ε)⁻¹ ^ 2 :=
      mul_nonneg hε.le (sq_nonneg _)
    have hscalar_le : ε * (u x + ε)⁻¹ ^ 2 ≤ δ⁻¹ := by
      calc
        ε * (u x + ε)⁻¹ ^ 2 ≤ (u x + ε) * (u x + ε)⁻¹ ^ 2 :=
          mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hu_pos.le) (sq_nonneg _)
        _ = (u x + ε)⁻¹ := by field_simp
        _ ≤ δ⁻¹ := (inv_le_inv₀ hden_pos hδ).2
          (hx.trans (le_add_of_nonneg_right hε.le))
    calc
      ‖F ε x‖ = (ε * (u x + ε)⁻¹ ^ 2) * ‖b x‖ := by
        change ‖(ε * (u x + ε)⁻¹ ^ 2) • b x‖ = _
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hscalar_nonneg]
      _ ≤ δ⁻¹ * ‖b x‖ :=
        mul_le_mul_of_nonneg_right hscalar_le (norm_nonneg _)
  have hlim : ∀ᵐ x ∂μ, _root_.Filter.Tendsto (fun ε => F ε x) (𝓝[>] 0) (𝓝 0) := by
    filter_upwards [huδ] with x hx
    have hu_ne : u x ≠ 0 := ne_of_gt (hδ.trans_le hx)
    have hε : _root_.Filter.Tendsto (fun ε : Real => ε) (𝓝[>] 0) (𝓝 0) :=
      tendsto_id.mono_left nhdsWithin_le_nhds
    have hden : _root_.Filter.Tendsto (fun ε : Real => u x + ε) (𝓝[>] 0) (𝓝 (u x)) :=
      by simpa only [add_zero] using tendsto_const_nhds.add hε
    have hscalar : _root_.Filter.Tendsto (fun ε : Real => ε * (u x + ε)⁻¹ ^ 2)
        (𝓝[>] 0) (𝓝 0) := by
      simpa only [_root_.MulZeroClass.zero_mul] using hε.mul ((hden.inv₀ hu_ne).pow 2)
    simpa only [F, zero_smul] using hscalar.smul_const (b x)
  simpa only [F, _root_.MeasureTheory.integral_zero] using
    _root_.MeasureTheory.tendsto_integral_filter_of_dominated_convergence
      (fun x => δ⁻¹ * ‖b x‖)
      (Filter.Eventually.of_forall hF_meas) hbound hbound_integrable hlim

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Integration.tendsto_integral_regularized_inv_sq_smul_of_integrable_of_ae_lower_bound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Integration.tendsto_integral_regularized_inv_sq_smul_of_integrable_of_ae_lower_bound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Integration.tendsto_integral_regularized_inv_sq_smul_of_integrable_of_ae_lower_bound ``Submission.DifferentialGeometry.Analysis.Integration.tendsto_integral_regularized_inv_sq_smul_of_integrable_of_ae_lower_bound

def cauchyPeak (z : Complex) : Real :=
  (Real.pi * (1 + ‖z‖ ^ 2) ^ 2)⁻¹

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Integration.cauchyPeak then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Integration.cauchyPeak"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Integration.cauchyPeak ``Submission.DifferentialGeometry.Analysis.Integration.cauchyPeak

private theorem integral_radial_cauchyPeak :
    ∫ r in _root_.Set.Ioi (0 : Real), r * (1 + r ^ 2)⁻¹ ^ 2 = 1 / 2 := by
  let F : Real → Real := fun r => -(1 / 2) * (1 + r ^ 2)⁻¹
  let F' : Real → Real := fun r => r * (1 + r ^ 2)⁻¹ ^ 2
  have hderiv : ∀ r ∈ _root_.Set.Ici (0 : Real), HasDerivAt F (F' r) r := by
    intro r hr
    have hbase : HasDerivAt (fun s : Real => 1 + s ^ 2) (2 * r) r := by
      have hsum := (hasDerivAt_const (x := r) (c := (1 : Real))).add
        ((hasDerivAt_id r).mul (hasDerivAt_id r))
      have hfun : ((fun _ : Real => 1) + id * id) =
          (fun s : Real => 1 + s ^ 2) := by
        funext s
        simp only [Pi.add_apply, Pi.mul_apply, id_eq, pow_two]
      rw [hfun] at hsum
      simpa only [zero_add, one_mul, mul_one, id_eq, two_mul] using hsum
    have hne : 1 + r ^ 2 ≠ 0 := by positivity
    have hinv := hbase.inv hne
    have hmul := hinv.const_mul (-(1 / 2 : Real))
    have hmul' : HasDerivAt
        (fun s : Real => -(1 / 2) * (1 + s ^ 2)⁻¹)
        (-(1 / 2) * (-(2 * r) / (1 + r ^ 2) ^ 2)) r := hmul
    change HasDerivAt (fun s : Real => -(1 / 2) * (1 + s ^ 2)⁻¹)
      (r * (1 + r ^ 2)⁻¹ ^ 2) r
    convert hmul' using 1
    field_simp
  have hnonneg : ∀ r ∈ _root_.Set.Ioi (0 : Real), 0 ≤ F' r := by
    intro r hr
    dsimp [F']
    exact mul_nonneg hr.le (sq_nonneg _)
  have hden : _root_.Filter.Tendsto (fun r : Real => 1 + r ^ 2) _root_.Filter.atTop atTop := by
    exact _root_.Filter.tendsto_atTop_add_const_left _root_.Filter.atTop 1 (_root_.Filter.tendsto_pow_atTop (by norm_num))
  have hlim : _root_.Filter.Tendsto F _root_.Filter.atTop (𝓝 0) := by
    have hinv : _root_.Filter.Tendsto (fun r : Real => (1 + r ^ 2)⁻¹) _root_.Filter.atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp hden
    simpa [F] using hinv.const_mul (-(1 / 2 : Real))
  have hmain := MeasureTheory.integral_Ioi_of_hasDerivAt_of_nonneg'
    hderiv hnonneg hlim
  simpa [F, F'] using hmain

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Integration.integral_radial_cauchyPeak
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Integration.integral_radial_cauchyPeak target :: scope.openDecls } }

theorem cauchyPeak_nonneg (z : Complex) : 0 ≤ cauchyPeak z := by
  dsimp [cauchyPeak]
  positivity

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Integration.cauchyPeak_nonneg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Integration.cauchyPeak_nonneg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Integration.cauchyPeak_nonneg ``Submission.DifferentialGeometry.Analysis.Integration.cauchyPeak_nonneg

theorem integral_cauchyPeak : ∫ z : Complex, cauchyPeak z = 1 := by
  calc
    ∫ z : Complex, cauchyPeak z =
        ∫ p in polarCoord.target,
          p.1 * cauchyPeak (Complex.polarCoord.symm p) := by
      simpa [smul_eq_mul] using
        (Complex.integral_comp_polarCoord_symm cauchyPeak).symm
    _ = (∫ r in _root_.Set.Ioi (0 : Real), r * (1 + r ^ 2)⁻¹ ^ 2) *
        ∫ _ in _root_.Set.Ioo (-Real.pi) Real.pi, Real.pi⁻¹ := by
      change (∫ p in _root_.Set.Ioi (0 : Real) ×ˢ _root_.Set.Ioo (-Real.pi) Real.pi,
          p.1 * cauchyPeak (Complex.polarCoord.symm p)) = _
      rw [← MeasureTheory.setIntegral_prod_mul,
        MeasureTheory.Measure.volume_eq_prod]
      refine _root_.MeasureTheory.setIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Ioo) ?_
      intro p hp
      dsimp [cauchyPeak]
      rw [Complex.norm_polarCoord_symm, abs_of_pos hp.1]
      field_simp [Real.pi_ne_zero]
    _ = 1 := by
      rw [integral_radial_cauchyPeak]
      rw [_root_.MeasureTheory.integral_const]
      have hvolume : MeasureTheory.volume.real (_root_.Set.Ioo (-Real.pi) Real.pi) =
          2 * Real.pi := by
        rw [MeasureTheory.Measure.real, Real.volume_Ioo,
          ENNReal.toReal_ofReal]
        · ring
        · linarith [Real.pi_pos]
      simp only [MeasurableSet.univ, _root_.MeasureTheory.measureReal_restrict_apply,
        _root_.Set.univ_inter, hvolume, smul_eq_mul]
      field_simp [Real.pi_ne_zero]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Integration.integral_cauchyPeak then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Integration.integral_cauchyPeak"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Integration.integral_cauchyPeak ``Submission.DifferentialGeometry.Analysis.Integration.integral_cauchyPeak

theorem cauchyPeak_decay :
    _root_.Filter.Tendsto (fun z : Complex => ‖z‖ ^ Module.finrank Real Complex * cauchyPeak z)
      (_root_.Bornology.cobounded Complex) (𝓝 0) := by
  rw [Complex.finrank_real_complex]
  have hnorm : _root_.Filter.Tendsto (fun z : Complex => ‖z‖) (_root_.Bornology.cobounded Complex) atTop :=
    tendsto_norm_cobounded_atTop
  have hscalar : _root_.Filter.Tendsto
      (fun r : Real => r ^ 2 * (Real.pi * (1 + r ^ 2) ^ 2)⁻¹)
      atTop (𝓝 0) := by
    have hzero : _root_.Filter.Tendsto (fun r : Real => (Real.pi * r ^ 2)⁻¹) _root_.Filter.atTop (𝓝 0) := by
      have hpow : _root_.Filter.Tendsto (fun r : Real => r ^ 2) _root_.Filter.atTop atTop :=
        _root_.Filter.tendsto_pow_atTop (by norm_num)
      have hmul : _root_.Filter.Tendsto (fun r : Real => Real.pi * r ^ 2) _root_.Filter.atTop atTop :=
        hpow.const_mul_atTop Real.pi_pos
      exact tendsto_inv_atTop_zero.comp hmul
    refine squeeze_zero' ?_ ?_ hzero
    · filter_upwards [_root_.Filter.eventually_gt_atTop (0 : Real)] with r hr
      positivity
    · filter_upwards [_root_.Filter.eventually_gt_atTop (0 : Real)] with r hr
      rw [inv_eq_one_div, inv_eq_one_div]
      rw [mul_one_div]
      change r ^ 2 / (Real.pi * (1 + r ^ 2) ^ 2) ≤
        1 / (Real.pi * r ^ 2)
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      calc
        r ^ 2 * (Real.pi * r ^ 2) = Real.pi * (r ^ 2) ^ 2 := by ring
        _ ≤ Real.pi * (1 + r ^ 2) ^ 2 :=
          mul_le_mul_of_nonneg_left (by nlinarith [sq_nonneg r]) Real.pi_pos.le
        _ = 1 * (Real.pi * (1 + r ^ 2) ^ 2) := by ring
  apply (hscalar.comp hnorm).congr'
  exact Filter.Eventually.of_forall fun z => by
    simp only [Function.comp_apply, cauchyPeak]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Integration.cauchyPeak_decay then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Integration.cauchyPeak_decay"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Integration.cauchyPeak_decay ``Submission.DifferentialGeometry.Analysis.Integration.cauchyPeak_decay

theorem tendsto_integral_cauchyPeak_smul_of_integrable
    {V : Type*} [NormedAddCommGroup V] [NormedSpace Real V] [CompleteSpace V]
    {g : Complex → V} (hg : _root_.MeasureTheory.Integrable g) (hcont : ContinuousAt g 0) :
    _root_.Filter.Tendsto
      (fun c : Real => ∫ z : Complex,
        (c ^ 2 * cauchyPeak (c • z)) • g z)
      atTop (𝓝 (g 0)) := by
  simpa only [Complex.finrank_real_complex] using
    tendsto_integral_comp_smul_smul_of_integrable
      cauchyPeak_nonneg integral_cauchyPeak cauchyPeak_decay hg hcont

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Integration.tendsto_integral_cauchyPeak_smul_of_integrable then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Integration.tendsto_integral_cauchyPeak_smul_of_integrable"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Integration.tendsto_integral_cauchyPeak_smul_of_integrable ``Submission.DifferentialGeometry.Analysis.Integration.tendsto_integral_cauchyPeak_smul_of_integrable

theorem tendsto_integral_regularized_quadratic_kernel_mul_of_integrable
    {a : Real} (ha : a ≠ 0) {g : Complex → Real}
    (hg : _root_.MeasureTheory.Integrable g) (hcont : ContinuousAt g 0) :
    _root_.Filter.Tendsto
      (fun c : Real => ∫ z : Complex,
        (a ^ 2 / c ^ 2) * g z *
          (a ^ 2 * ‖z‖ ^ 2 + a ^ 2 / c ^ 2)⁻¹ ^ 2)
      atTop (𝓝 (Real.pi / a ^ 2 * g 0)) := by
  have hbase := tendsto_integral_cauchyPeak_smul_of_integrable hg hcont
  have hscaled := hbase.const_mul (Real.pi / a ^ 2)
  apply hscaled.congr'
  filter_upwards [_root_.Filter.eventually_gt_atTop (0 : Real)] with c hc
  rw [← _root_.MeasureTheory.integral_const_mul]
  apply _root_.MeasureTheory.integral_congr_ae
  filter_upwards with z
  simp only [smul_eq_mul]
  rw [cauchyPeak]
  rw [norm_smul]
  simp only [Real.norm_eq_abs, abs_of_pos hc]
  field_simp [ha, ne_of_gt hc, Real.pi_ne_zero]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Integration.tendsto_integral_regularized_quadratic_kernel_mul_of_integrable then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Integration.tendsto_integral_regularized_quadratic_kernel_mul_of_integrable"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Integration.tendsto_integral_regularized_quadratic_kernel_mul_of_integrable ``Submission.DifferentialGeometry.Analysis.Integration.tendsto_integral_regularized_quadratic_kernel_mul_of_integrable

theorem tendsto_integral_regularized_quadratic_kernel_mul_of_integrable_nhdsGT_zero
    {a : Real} (ha : a ≠ 0) {g : Complex → Real}
    (hg : _root_.MeasureTheory.Integrable g) (hcont : ContinuousAt g 0) :
    _root_.Filter.Tendsto
      (fun ε : Real => ∫ z : Complex,
        ε * g z * (a ^ 2 * ‖z‖ ^ 2 + ε)⁻¹ ^ 2)
      (𝓝[>] 0) (𝓝 (Real.pi / a ^ 2 * g 0)) := by
  let c : Real → Real := fun ε => |a| * (Real.sqrt ε)⁻¹
  have hsqrt_full : _root_.Filter.Tendsto (fun ε : Real => Real.sqrt ε) (𝓝 0) (𝓝 0) := by
    simpa only [Real.sqrt_zero] using Real.continuous_sqrt.tendsto (0 : Real)
  have hsqrt : _root_.Filter.Tendsto (fun ε : Real => Real.sqrt ε) (𝓝[>] 0) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨hsqrt_full.mono_left nhdsWithin_le_nhds, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact Real.sqrt_pos.2 hε
  have hc : _root_.Filter.Tendsto c (𝓝[>] 0) atTop := by
    exact (tendsto_inv_nhdsGT_zero.comp hsqrt).const_mul_atTop (abs_pos.2 ha)
  have hbase :=
    (tendsto_integral_regularized_quadratic_kernel_mul_of_integrable ha hg hcont).comp hc
  apply hbase.congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  change 0 < ε at hε
  apply _root_.MeasureTheory.integral_congr_ae
  filter_upwards with z
  have hsqrt_pos : 0 < Real.sqrt ε := Real.sqrt_pos.2 hε
  have hscale : a ^ 2 / c ε ^ 2 = ε := by
    dsimp [c]
    field_simp [ha, ne_of_gt hsqrt_pos]
    rw [sq_abs, Real.sq_sqrt hε.le]
  rw [hscale]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Integration.tendsto_integral_regularized_quadratic_kernel_mul_of_integrable_nhdsGT_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Integration.tendsto_integral_regularized_quadratic_kernel_mul_of_integrable_nhdsGT_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Integration.tendsto_integral_regularized_quadratic_kernel_mul_of_integrable_nhdsGT_zero ``Submission.DifferentialGeometry.Analysis.Integration.tendsto_integral_regularized_quadratic_kernel_mul_of_integrable_nhdsGT_zero

theorem tendsto_integral_regularized_quadratic_kernel_mul_of_integrable_nhdsGT_zero_of_finrank_eq_two
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace Real F]
    [FiniteDimensional Real F] [MeasurableSpace F] [BorelSpace F]
    (hdim : Module.finrank Real F = 2)
    {a : Real} (ha : a ≠ 0) {g : F → Real}
    (hg : _root_.MeasureTheory.Integrable g _root_.MeasureTheory.MeasureSpace.volume) (hcont : ContinuousAt g 0) :
    _root_.Filter.Tendsto
      (fun ε : Real => ∫ z : F,
        ε * g z * (a ^ 2 * ‖z‖ ^ 2 + ε)⁻¹ ^ 2 ∂volume)
      (𝓝[>] 0) (𝓝 (Real.pi / a ^ 2 * g 0)) := by
  let v : OrthonormalBasis (Fin 2) Real F :=
    (stdOrthonormalBasis Real F).reindex (finCongr hdim)
  let e : Complex ≃ₗᵢ[Real] F := Complex.isometryOfOrthonormal v
  have he_pres : _root_.MeasureTheory.MeasurePreserving e _root_.MeasureTheory.MeasureSpace.volume volume := e.measurePreserving
  have he_emb : MeasurableEmbedding e := e.toHomeomorph.measurableEmbedding
  have hge : _root_.MeasureTheory.Integrable (g ∘ e) :=
    he_pres.integrable_comp_emb he_emb |>.mpr hg
  have hconte : ContinuousAt (g ∘ e) 0 := by
    have he_cont : ContinuousAt (e : Complex → F) (0 : Complex) := e.continuousAt
    have hcont' : ContinuousAt g (e 0) := by
      simpa only [map_zero] using hcont
    exact hcont'.comp (x := (0 : Complex)) he_cont
  have hbase :=
    tendsto_integral_regularized_quadratic_kernel_mul_of_integrable_nhdsGT_zero
      ha hge hconte
  have heq :
      (fun ε : Real => ∫ z : Complex,
        ε * (g ∘ e) z * (a ^ 2 * ‖z‖ ^ 2 + ε)⁻¹ ^ 2) =
      (fun ε : Real => ∫ z : F,
        ε * g z * (a ^ 2 * ‖z‖ ^ 2 + ε)⁻¹ ^ 2 ∂volume) := by
    funext ε
    simpa only [Function.comp_apply, LinearIsometryEquiv.norm_map] using
      he_pres.integral_comp he_emb
        (fun z : F => ε * g z * (a ^ 2 * ‖z‖ ^ 2 + ε)⁻¹ ^ 2)
  rw [heq] at hbase
  simpa only [Function.comp_apply, map_zero] using hbase

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Integration.tendsto_integral_regularized_quadratic_kernel_mul_of_integrable_nhdsGT_zero_of_finrank_eq_two then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Integration.tendsto_integral_regularized_quadratic_kernel_mul_of_integrable_nhdsGT_zero_of_finrank_eq_two"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Integration.tendsto_integral_regularized_quadratic_kernel_mul_of_integrable_nhdsGT_zero_of_finrank_eq_two ``Submission.DifferentialGeometry.Analysis.Integration.tendsto_integral_regularized_quadratic_kernel_mul_of_integrable_nhdsGT_zero_of_finrank_eq_two

theorem tendsto_setIntegral_regularized_quadratic_kernel_mul_of_integrableOn_nhdsGT_zero_of_finrank_eq_two
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace Real F]
    [FiniteDimensional Real F] [MeasurableSpace F] [BorelSpace F]
    (hdim : Module.finrank Real F = 2)
    {a : Real} (ha : a ≠ 0) {s : Set F}
    (hs : MeasurableSet s) (h0 : s ∈ 𝓝 (0 : F))
    {g : F → Real} (hg : _root_.MeasureTheory.IntegrableOn g s _root_.MeasureTheory.MeasureSpace.volume) (hcont : ContinuousAt g 0) :
    _root_.Filter.Tendsto
      (fun ε : Real => ∫ z in s,
        ε * g z * (a ^ 2 * ‖z‖ ^ 2 + ε)⁻¹ ^ 2 ∂volume)
      (𝓝[>] 0) (𝓝 (Real.pi / a ^ 2 * g 0)) := by
  have h0s : (0 : F) ∈ s := mem_of_mem_nhds h0
  have hindicator : s.indicator g =ᶠ[𝓝 (0 : F)] g := by
    filter_upwards [h0] with z hz
    rw [_root_.Set.indicator_of_mem hz]
  have hbase :=
    tendsto_integral_regularized_quadratic_kernel_mul_of_integrable_nhdsGT_zero_of_finrank_eq_two
      hdim ha (hg.integrable_indicator hs) (hcont.congr_of_eventuallyEq hindicator)
  rw [_root_.Set.indicator_of_mem h0s] at hbase
  apply hbase.congr'
  filter_upwards with ε
  rw [← _root_.MeasureTheory.integral_indicator hs]
  apply _root_.MeasureTheory.integral_congr_ae
  filter_upwards with z
  by_cases hz : z ∈ s
  · simp only [_root_.Set.indicator_of_mem hz]
  · simp only [_root_.Set.indicator_of_notMem hz, _root_.MulZeroClass.mul_zero, _root_.MulZeroClass.zero_mul]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Integration.tendsto_setIntegral_regularized_quadratic_kernel_mul_of_integrableOn_nhdsGT_zero_of_finrank_eq_two then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Integration.tendsto_setIntegral_regularized_quadratic_kernel_mul_of_integrableOn_nhdsGT_zero_of_finrank_eq_two"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Integration.tendsto_setIntegral_regularized_quadratic_kernel_mul_of_integrableOn_nhdsGT_zero_of_finrank_eq_two ``Submission.DifferentialGeometry.Analysis.Integration.tendsto_setIntegral_regularized_quadratic_kernel_mul_of_integrableOn_nhdsGT_zero_of_finrank_eq_two

theorem tendsto_setIntegral_regularized_quadratic_kernel_mul_of_integrableOn_nhdsGT_zero
    {a : Real} (ha : a ≠ 0) {s : Set Complex}
    (hs : MeasurableSet s) (h0 : s ∈ 𝓝 (0 : Complex))
    {g : Complex → Real} (hg : _root_.MeasureTheory.IntegrableOn g s) (hcont : ContinuousAt g 0) :
    _root_.Filter.Tendsto
      (fun ε : Real => ∫ z in s,
        ε * g z * (a ^ 2 * ‖z‖ ^ 2 + ε)⁻¹ ^ 2)
      (𝓝[>] 0) (𝓝 (Real.pi / a ^ 2 * g 0)) := by
  exact
    tendsto_setIntegral_regularized_quadratic_kernel_mul_of_integrableOn_nhdsGT_zero_of_finrank_eq_two
      Complex.finrank_real_complex ha hs h0 hg hcont

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Integration.tendsto_setIntegral_regularized_quadratic_kernel_mul_of_integrableOn_nhdsGT_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Integration.tendsto_setIntegral_regularized_quadratic_kernel_mul_of_integrableOn_nhdsGT_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Integration.tendsto_setIntegral_regularized_quadratic_kernel_mul_of_integrableOn_nhdsGT_zero ``Submission.DifferentialGeometry.Analysis.Integration.tendsto_setIntegral_regularized_quadratic_kernel_mul_of_integrableOn_nhdsGT_zero

theorem tendsto_setIntegral_regularized_quadratic_kernel_comp_mul_abs_det_fderiv_of_integrableOn_nhdsGT_zero_of_finrank_eq_two
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace Real F]
    [FiniteDimensional Real F] [MeasurableSpace F] [BorelSpace F]
    (hdim : Module.finrank Real F = 2)
    {a : Real} (ha : a ≠ 0) {s : Set F} (hs : MeasurableSet s)
    {φ : F → F} {φ' : F → F →L[Real] F}
    (hφ' : ∀ z ∈ s, HasFDerivWithinAt φ (φ' z) s z)
    (hφ : _root_.Set.InjOn φ s) (h0 : φ '' s ∈ 𝓝 (0 : F))
    {g : F → Real} (hg : _root_.MeasureTheory.IntegrableOn g (φ '' s) _root_.MeasureTheory.MeasureSpace.volume)
    (hcont : ContinuousAt g 0) :
    _root_.Filter.Tendsto
      (fun ε : Real => ∫ z in s,
        |(φ' z).det| *
          (ε * g (φ z) * (a ^ 2 * ‖φ z‖ ^ 2 + ε)⁻¹ ^ 2) ∂volume)
      (𝓝[>] 0) (𝓝 (Real.pi / a ^ 2 * g 0)) := by
  have himage : MeasurableSet (φ '' s) :=
    _root_.MeasureTheory.measurable_image_of_fderivWithin hs hφ' hφ
  have hbase :=
    tendsto_setIntegral_regularized_quadratic_kernel_mul_of_integrableOn_nhdsGT_zero_of_finrank_eq_two
      hdim ha himage h0 hg hcont
  apply hbase.congr'
  filter_upwards with ε
  simpa only [smul_eq_mul] using
    (_root_.MeasureTheory.integral_image_eq_integral_abs_det_fderiv_smul _root_.MeasureTheory.MeasureSpace.volume hs hφ' hφ
      (fun z : F =>
        ε * g z * (a ^ 2 * ‖z‖ ^ 2 + ε)⁻¹ ^ 2))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Integration.tendsto_setIntegral_regularized_quadratic_kernel_comp_mul_abs_det_fderiv_of_integrableOn_nhdsGT_zero_of_finrank_eq_two then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Integration.tendsto_setIntegral_regularized_quadratic_kernel_comp_mul_abs_det_fderiv_of_integrableOn_nhdsGT_zero_of_finrank_eq_two"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Integration.tendsto_setIntegral_regularized_quadratic_kernel_comp_mul_abs_det_fderiv_of_integrableOn_nhdsGT_zero_of_finrank_eq_two ``Submission.DifferentialGeometry.Analysis.Integration.tendsto_setIntegral_regularized_quadratic_kernel_comp_mul_abs_det_fderiv_of_integrableOn_nhdsGT_zero_of_finrank_eq_two

theorem tendsto_setIntegral_regularized_quadratic_kernel_comp_mul_abs_det_fderiv_of_integrableOn_nhdsGT_zero
    {a : Real} (ha : a ≠ 0) {s : Set Complex} (hs : MeasurableSet s)
    {φ : Complex → Complex} {φ' : Complex → Complex →L[Real] Complex}
    (hφ' : ∀ z ∈ s, HasFDerivWithinAt φ (φ' z) s z)
    (hφ : _root_.Set.InjOn φ s) (h0 : φ '' s ∈ 𝓝 (0 : Complex))
    {g : Complex → Real} (hg : _root_.MeasureTheory.IntegrableOn g (φ '' s))
    (hcont : ContinuousAt g 0) :
    _root_.Filter.Tendsto
      (fun ε : Real => ∫ z in s,
        |(φ' z).det| *
          (ε * g (φ z) * (a ^ 2 * ‖φ z‖ ^ 2 + ε)⁻¹ ^ 2))
      (𝓝[>] 0) (𝓝 (Real.pi / a ^ 2 * g 0)) := by
  exact
    tendsto_setIntegral_regularized_quadratic_kernel_comp_mul_abs_det_fderiv_of_integrableOn_nhdsGT_zero_of_finrank_eq_two
      Complex.finrank_real_complex ha hs hφ' hφ h0 hg hcont

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Integration.tendsto_setIntegral_regularized_quadratic_kernel_comp_mul_abs_det_fderiv_of_integrableOn_nhdsGT_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Integration.tendsto_setIntegral_regularized_quadratic_kernel_comp_mul_abs_det_fderiv_of_integrableOn_nhdsGT_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Integration.tendsto_setIntegral_regularized_quadratic_kernel_comp_mul_abs_det_fderiv_of_integrableOn_nhdsGT_zero ``Submission.DifferentialGeometry.Analysis.Integration.tendsto_setIntegral_regularized_quadratic_kernel_comp_mul_abs_det_fderiv_of_integrableOn_nhdsGT_zero

end DifferentialGeometry.Analysis.Integration
