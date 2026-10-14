import Submission.DifferentialGeometry.Analysis.Integration.Lp.Bilinear
import Mathlib.Analysis.Normed.Operator.Mul

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission


noncomputable section

namespace MeasureTheory
open _root_.MeasureTheory

open _root_.Filter
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.AEStronglyMeasurable
  (clm_apply_of_apply_aestronglyMeasurable)
open scoped _root_.Topology

variable {X E F A : Type*} [MeasurableSpace X] {μ : Measure X}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

open _root_.MeasureTheory in
theorem integrable_clm_apply_of_ae_norm_le
    (b : X → E →L[ℝ] F)
    (hb : ∀ v, _root_.MeasureTheory.AEStronglyMeasurable (fun x ↦ b x v) μ)
    {M : ℝ} (hM : ∀ᵐ x ∂μ, ‖b x‖ ≤ M)
    {f : X → E} (hf : _root_.MeasureTheory.Integrable f μ) :
    Integrable (fun x ↦ b x (f x)) μ := by
  have hmeas : _root_.MeasureTheory.AEStronglyMeasurable (fun x ↦ b x (f x)) μ :=
    clm_apply_of_apply_aestronglyMeasurable b hb f hf.aestronglyMeasurable
  refine (hf.norm.const_mul M).mono' hmeas ?_
  filter_upwards [hM] with x hx
  exact ((b x).le_opNorm (f x)).trans
    (mul_le_mul_of_nonneg_right hx (norm_nonneg _))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `MeasureTheory.integrable_clm_apply_of_ae_norm_le then
    throwError "Refusing to shadow existing declaration MeasureTheory.integrable_clm_apply_of_ae_norm_le"
  Lean.modifyEnv fun env => Lean.addAlias env `MeasureTheory.integrable_clm_apply_of_ae_norm_le ``Submission.MeasureTheory.integrable_clm_apply_of_ae_norm_le

open _root_.MeasureTheory in
theorem norm_integral_clm_apply_sub_le
    (b : X → E →L[ℝ] F)
    (hb : ∀ v, _root_.MeasureTheory.AEStronglyMeasurable (fun x ↦ b x v) μ)
    {M : ℝ} (hM : ∀ᵐ x ∂μ, ‖b x‖ ≤ M)
    {f g : X → E} (hf : _root_.MeasureTheory.Integrable f μ) (hg : _root_.MeasureTheory.Integrable g μ) :
    ‖(∫ x, b x (f x) ∂μ) - ∫ x, b x (g x) ∂μ‖ ≤
      M * ∫ x, ‖f x - g x‖ ∂μ := by
  rw [← _root_.MeasureTheory.integral_sub (integrable_clm_apply_of_ae_norm_le b hb hM hf)
    (integrable_clm_apply_of_ae_norm_le b hb hM hg)]
  have heq : (fun x ↦ b x (f x) - b x (g x)) =
      fun x ↦ b x (f x - g x) := by
    funext x
    exact ((b x).map_sub (f x) (g x)).symm
  rw [heq]
  calc
    _ ≤ ∫ x, M * ‖f x - g x‖ ∂μ := by
      apply _root_.MeasureTheory.norm_integral_le_of_norm_le ((hf.sub hg).norm.const_mul M)
      filter_upwards [hM] with x hx
      exact ((b x).le_opNorm (f x - g x)).trans
        (mul_le_mul_of_nonneg_right hx (norm_nonneg _))
    _ = M * ∫ x, ‖f x - g x‖ ∂μ := _root_.MeasureTheory.integral_const_mul _ _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `MeasureTheory.norm_integral_clm_apply_sub_le then
    throwError "Refusing to shadow existing declaration MeasureTheory.norm_integral_clm_apply_sub_le"
  Lean.modifyEnv fun env => Lean.addAlias env `MeasureTheory.norm_integral_clm_apply_sub_le ``Submission.MeasureTheory.norm_integral_clm_apply_sub_le

open _root_.MeasureTheory in
theorem tendsto_integral_clm_apply_of_tendsto_integral_norm_sub
    {l : Filter A} (b : X → E →L[ℝ] F)
    (hb : ∀ v, _root_.MeasureTheory.AEStronglyMeasurable (fun x ↦ b x v) μ)
    {M : ℝ} (hM : ∀ᵐ x ∂μ, ‖b x‖ ≤ M)
    {f : A → X → E} {g : X → E}
    (hf : ∀ᶠ i in l, _root_.MeasureTheory.Integrable (f i) μ) (hg : _root_.MeasureTheory.Integrable g μ)
    (hlim : _root_.Filter.Tendsto (fun i ↦ ∫ x, ‖f i x - g x‖ ∂μ) l (𝓝 0)) :
    Tendsto (fun i ↦ ∫ x, b x (f i x) ∂μ) l (𝓝 (∫ x, b x (g x) ∂μ)) := by
  have herr : _root_.Filter.Tendsto (fun i ↦ (∫ x, b x (f i x) ∂μ) - ∫ x, b x (g x) ∂μ)
      l (𝓝 0) := by
    apply squeeze_zero_norm'
      (hf.mono fun i hi ↦ norm_integral_clm_apply_sub_le b hb hM hi hg)
    simpa only [_root_.MulZeroClass.mul_zero] using hlim.const_mul M
  simpa only [sub_add_cancel, zero_add] using
    herr.add (tendsto_const_nhds (x := ∫ x, b x (g x) ∂μ))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `MeasureTheory.tendsto_integral_clm_apply_of_tendsto_integral_norm_sub then
    throwError "Refusing to shadow existing declaration MeasureTheory.tendsto_integral_clm_apply_of_tendsto_integral_norm_sub"
  Lean.modifyEnv fun env => Lean.addAlias env `MeasureTheory.tendsto_integral_clm_apply_of_tendsto_integral_norm_sub ``Submission.MeasureTheory.tendsto_integral_clm_apply_of_tendsto_integral_norm_sub

open _root_.MeasureTheory in
theorem tendsto_integral_clm_apply_of_tendsto_l1
    {l : Filter A} (b : X → E →L[ℝ] F)
    (hb : ∀ v, _root_.MeasureTheory.AEStronglyMeasurable (fun x ↦ b x v) μ)
    {M : ℝ} (hM : ∀ᵐ x ∂μ, ‖b x‖ ≤ M)
    {f : A → _root_.MeasureTheory.Lp E 1 μ} {g : _root_.MeasureTheory.Lp E 1 μ} (hlim : _root_.Filter.Tendsto f l (𝓝 g)) :
    Tendsto (fun i ↦ ∫ x, b x (f i x) ∂μ) l (𝓝 (∫ x, b x (g x) ∂μ)) := by
  apply tendsto_integral_clm_apply_of_tendsto_integral_norm_sub b hb hM
    (Eventually.of_forall fun i ↦ _root_.MeasureTheory.memLp_one_iff_integrable.mp (Lp.memLp (f i)))
    (_root_.MeasureTheory.memLp_one_iff_integrable.mp (Lp.memLp g))
  have hdist := hlim.dist (tendsto_const_nhds (x := g))
  simp only [dist_self] at hdist
  simp_rw [L1.dist_eq_integral_dist, dist_eq_norm] at hdist
  exact hdist

run_cmd do
  let env ← Lean.getEnv
  if env.contains `MeasureTheory.tendsto_integral_clm_apply_of_tendsto_l1 then
    throwError "Refusing to shadow existing declaration MeasureTheory.tendsto_integral_clm_apply_of_tendsto_l1"
  Lean.modifyEnv fun env => Lean.addAlias env `MeasureTheory.tendsto_integral_clm_apply_of_tendsto_l1 ``Submission.MeasureTheory.tendsto_integral_clm_apply_of_tendsto_l1

open _root_.MeasureTheory in
theorem tendsto_integral_mul_of_tendsto_integral_norm_sub
    {l : Filter A} (c : X → ℝ) (hc : _root_.MeasureTheory.AEStronglyMeasurable c μ)
    {M : ℝ} (hM : ∀ᵐ x ∂μ, ‖c x‖ ≤ M)
    {f : A → X → ℝ} {g : X → ℝ}
    (hf : ∀ᶠ i in l, _root_.MeasureTheory.Integrable (f i) μ) (hg : _root_.MeasureTheory.Integrable g μ)
    (hlim : _root_.Filter.Tendsto (fun i ↦ ∫ x, ‖f i x - g x‖ ∂μ) l (𝓝 0)) :
    Tendsto (fun i ↦ ∫ x, c x * f i x ∂μ) l (𝓝 (∫ x, c x * g x ∂μ)) := by
  let b : X → ℝ →L[ℝ] ℝ := fun x ↦ ContinuousLinearMap.lsmul ℝ ℝ (c x)
  have hb : ∀ v, _root_.MeasureTheory.AEStronglyMeasurable (fun x ↦ b x v) μ := by
    intro v
    simpa only [b, ContinuousLinearMap.lsmul_apply, smul_eq_mul] using hc.mul_const v
  have hB : ∀ᵐ x ∂μ, ‖b x‖ ≤ M := by
    filter_upwards [hM] with x hx
    exact (ContinuousLinearMap.opNorm_lsmul_apply_le (𝕜 := ℝ) (E := ℝ) (c x)).trans hx
  simpa only [b, ContinuousLinearMap.lsmul_apply, smul_eq_mul] using
    tendsto_integral_clm_apply_of_tendsto_integral_norm_sub b hb hB hf hg hlim

run_cmd do
  let env ← Lean.getEnv
  if env.contains `MeasureTheory.tendsto_integral_mul_of_tendsto_integral_norm_sub then
    throwError "Refusing to shadow existing declaration MeasureTheory.tendsto_integral_mul_of_tendsto_integral_norm_sub"
  Lean.modifyEnv fun env => Lean.addAlias env `MeasureTheory.tendsto_integral_mul_of_tendsto_integral_norm_sub ``Submission.MeasureTheory.tendsto_integral_mul_of_tendsto_integral_norm_sub

open _root_.MeasureTheory in
theorem tendsto_integral_clm_apply_add_mul_of_tendsto_integral_norm_sub
    {l : Filter A} (b : X → E →L[ℝ] ℝ) (c : X → ℝ)
    (hb : ∀ v, _root_.MeasureTheory.AEStronglyMeasurable (fun x ↦ b x v) μ)
    (hc : _root_.MeasureTheory.AEStronglyMeasurable c μ)
    {M N : ℝ} (hM : ∀ᵐ x ∂μ, ‖b x‖ ≤ M) (hN : ∀ᵐ x ∂μ, ‖c x‖ ≤ N)
    {u : A → X → E} {v : X → E} {f : A → X → ℝ} {g : X → ℝ}
    (hu : ∀ᶠ i in l, _root_.MeasureTheory.Integrable (u i) μ) (hv : _root_.MeasureTheory.Integrable v μ)
    (hf : ∀ᶠ i in l, _root_.MeasureTheory.Integrable (f i) μ) (hg : _root_.MeasureTheory.Integrable g μ)
    (hulim : _root_.Filter.Tendsto (fun i ↦ ∫ x, ‖u i x - v x‖ ∂μ) l (𝓝 0))
    (hflim : _root_.Filter.Tendsto (fun i ↦ ∫ x, ‖f i x - g x‖ ∂μ) l (𝓝 0)) :
    _root_.Filter.Tendsto (fun i ↦ ∫ x, b x (u i x) + c x * f i x ∂μ)
      l (𝓝 (∫ x, b x (v x) + c x * g x ∂μ)) := by
  have hsum :=
    (tendsto_integral_clm_apply_of_tendsto_integral_norm_sub b hb hM hu hv hulim).add
      (tendsto_integral_mul_of_tendsto_integral_norm_sub c hc hN hf hg hflim)
  rw [← _root_.MeasureTheory.integral_add (integrable_clm_apply_of_ae_norm_le b hb hM hv)
    (hg.bdd_mul hc hN)] at hsum
  refine hsum.congr' ?_
  filter_upwards [hu, hf] with i hui hfi
  exact (_root_.MeasureTheory.integral_add (integrable_clm_apply_of_ae_norm_le b hb hM hui)
    (hfi.bdd_mul hc hN)).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `MeasureTheory.tendsto_integral_clm_apply_add_mul_of_tendsto_integral_norm_sub then
    throwError "Refusing to shadow existing declaration MeasureTheory.tendsto_integral_clm_apply_add_mul_of_tendsto_integral_norm_sub"
  Lean.modifyEnv fun env => Lean.addAlias env `MeasureTheory.tendsto_integral_clm_apply_add_mul_of_tendsto_integral_norm_sub ``Submission.MeasureTheory.tendsto_integral_clm_apply_add_mul_of_tendsto_integral_norm_sub

open _root_.MeasureTheory in
theorem integral_clm_apply_add_mul_nonneg_of_tendsto_integral_norm_sub
    {l : Filter A} [_root_.Filter.NeBot l] (b : X → E →L[ℝ] ℝ) (c : X → ℝ)
    (hb : ∀ v, _root_.MeasureTheory.AEStronglyMeasurable (fun x ↦ b x v) μ)
    (hc : _root_.MeasureTheory.AEStronglyMeasurable c μ)
    {M N : ℝ} (hM : ∀ᵐ x ∂μ, ‖b x‖ ≤ M) (hN : ∀ᵐ x ∂μ, ‖c x‖ ≤ N)
    {u : A → X → E} {v : X → E} {f : A → X → ℝ} {g : X → ℝ}
    (hu : ∀ᶠ i in l, _root_.MeasureTheory.Integrable (u i) μ) (hv : _root_.MeasureTheory.Integrable v μ)
    (hf : ∀ᶠ i in l, _root_.MeasureTheory.Integrable (f i) μ) (hg : _root_.MeasureTheory.Integrable g μ)
    (hulim : _root_.Filter.Tendsto (fun i ↦ ∫ x, ‖u i x - v x‖ ∂μ) l (𝓝 0))
    (hflim : _root_.Filter.Tendsto (fun i ↦ ∫ x, ‖f i x - g x‖ ∂μ) l (𝓝 0))
    (hnonneg : ∀ᶠ i in l, 0 ≤ ∫ x, b x (u i x) + c x * f i x ∂μ) :
    0 ≤ ∫ x, b x (v x) + c x * g x ∂μ := by
  exact le_of_tendsto_of_tendsto tendsto_const_nhds
    (tendsto_integral_clm_apply_add_mul_of_tendsto_integral_norm_sub
      b c hb hc hM hN hu hv hf hg hulim hflim) hnonneg

run_cmd do
  let env ← Lean.getEnv
  if env.contains `MeasureTheory.integral_clm_apply_add_mul_nonneg_of_tendsto_integral_norm_sub then
    throwError "Refusing to shadow existing declaration MeasureTheory.integral_clm_apply_add_mul_nonneg_of_tendsto_integral_norm_sub"
  Lean.modifyEnv fun env => Lean.addAlias env `MeasureTheory.integral_clm_apply_add_mul_nonneg_of_tendsto_integral_norm_sub ``Submission.MeasureTheory.integral_clm_apply_add_mul_nonneg_of_tendsto_integral_norm_sub

end MeasureTheory
