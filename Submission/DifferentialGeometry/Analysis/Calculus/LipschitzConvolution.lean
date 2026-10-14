import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.Rademacher

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.MeasureTheory _root_.Filter _root_.Metric _root_.ContinuousLinearMap
open scoped _root_.Topology _root_.ContDiff _root_.Convolution _root_.NNReal

namespace ContDiffBump
open _root_.ContDiffBump

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {μ : Measure E} [μ.IsAddHaarMeasure]

open _root_.ContDiffBump in
theorem lipschitz_normed_convolution (φ : ContDiffBump (0 : E)) {f : E → F} {C : ℝ≥0}
    (hf : LipschitzWith C f) : LipschitzWith C (φ.normed μ ⋆[_root_.ContinuousLinearMap.lsmul ℝ ℝ, μ] f) := by
  have hi (x : E) : _root_.MeasureTheory.Integrable (fun t => φ.normed μ t • f (x - t)) μ :=
    φ.hasCompactSupport_normed.convolutionExists_left_of_continuous_right (_root_.ContinuousLinearMap.lsmul ℝ ℝ)
      φ.integrable_normed.locallyIntegrable hf.continuous x
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [_root_.MeasureTheory.convolution_def, _root_.ContinuousLinearMap.lsmul_apply, dist_eq_norm]
  rw [← _root_.MeasureTheory.integral_sub (hi x) (hi y)]
  calc
    ‖∫ t, φ.normed μ t • f (x - t) - φ.normed μ t • f (y - t) ∂μ‖ ≤
        ∫ t, φ.normed μ t * ((C : ℝ) * ‖x - y‖) ∂μ := by
      apply _root_.MeasureTheory.norm_integral_le_of_norm_le (φ.integrable_normed.mul_const _)
      filter_upwards [] with t
      rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_nonneg (φ.nonneg_normed t)]
      apply mul_le_mul_of_nonneg_left _ (φ.nonneg_normed t)
      simpa only [dist_eq_norm, sub_sub_sub_cancel_right] using hf.dist_le_mul (x - t) (y - t)
    _ = (C : ℝ) * ‖x - y‖ := by rw [_root_.MeasureTheory.integral_mul_const, φ.integral_normed, one_mul]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `ContDiffBump.lipschitz_normed_convolution then
    throwError "Refusing to shadow existing declaration ContDiffBump.lipschitz_normed_convolution"
  Lean.modifyEnv fun env => Lean.addAlias env `ContDiffBump.lipschitz_normed_convolution ``Submission.ContDiffBump.lipschitz_normed_convolution

open _root_.ContDiffBump in
theorem dist_normed_convolution_le_mul [CompleteSpace F] (φ : ContDiffBump (0 : E))
    {f : E → F} {C : ℝ≥0} (hf : LipschitzWith C f) (x : E) :
    dist ((φ.normed μ ⋆[_root_.ContinuousLinearMap.lsmul ℝ ℝ, μ] f) x) (f x) ≤ (C : ℝ) * φ.rOut := by
  apply φ.dist_normed_convolution_le hf.continuous.aestronglyMeasurable
  intro y hy
  exact (hf.dist_le_mul y x).trans (mul_le_mul_of_nonneg_left (mem_ball.mp hy).le C.coe_nonneg)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `ContDiffBump.dist_normed_convolution_le_mul then
    throwError "Refusing to shadow existing declaration ContDiffBump.dist_normed_convolution_le_mul"
  Lean.modifyEnv fun env => Lean.addAlias env `ContDiffBump.dist_normed_convolution_le_mul ``Submission.ContDiffBump.dist_normed_convolution_le_mul

open _root_.ContDiffBump in
theorem convolution_tendstoUniformly_of_lipschitz [CompleteSpace F]
    {ι : Type*} {φ : ι → ContDiffBump (0 : E)} {l : Filter ι} {f : E → F} {C : ℝ≥0}
    (hφ : _root_.Filter.Tendsto (fun i => (φ i).rOut) l (𝓝 0)) (hf : LipschitzWith C f) :
    TendstoUniformly (fun i => (φ i).normed μ ⋆[_root_.ContinuousLinearMap.lsmul ℝ ℝ, μ] f) f l := by
  apply Metric.tendstoUniformly_iff.mpr
  intro ε hε
  have h : _root_.Filter.Tendsto (fun i => (C : ℝ) * (φ i).rOut) l (𝓝 0) := by
    simpa using hφ.const_mul (C : ℝ)
  filter_upwards [h.eventually (gt_mem_nhds hε)] with i hi x
  exact (dist_comm _ _).trans_le ((φ i).dist_normed_convolution_le_mul hf x) |>.trans_lt hi

run_cmd do
  let env ← Lean.getEnv
  if env.contains `ContDiffBump.convolution_tendstoUniformly_of_lipschitz then
    throwError "Refusing to shadow existing declaration ContDiffBump.convolution_tendstoUniformly_of_lipschitz"
  Lean.modifyEnv fun env => Lean.addAlias env `ContDiffBump.convolution_tendstoUniformly_of_lipschitz ``Submission.ContDiffBump.convolution_tendstoUniformly_of_lipschitz

end ContDiffBump

namespace LipschitzWith
open _root_.LipschitzWith

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

open _root_.LipschitzWith in
theorem exists_contDiff_lipschitz_tendstoUniformly {f : E → F} {C : ℝ≥0}
    (hf : LipschitzWith C f) :
    ∃ g : ℕ → E → F, (∀ n, ContDiff ℝ ∞ (g n)) ∧
      (∀ n, LipschitzWith C (g n)) ∧ TendstoUniformly g f atTop := by
  borelize E
  let φ (n : ℕ) : ContDiffBump (0 : E) :=
    ⟨(1 / ((n : ℝ) + 1)) / 2, 1 / ((n : ℝ) + 1), by positivity,
      half_lt_self (by positivity)⟩
  let μ : _root_.MeasureTheory.Measure E := Measure.addHaar
  refine ⟨fun n => (φ n).normed μ ⋆[_root_.ContinuousLinearMap.lsmul ℝ ℝ, μ] f, ?_, ?_, ?_⟩
  · intro n
    exact (φ n).hasCompactSupport_normed.contDiff_convolution_left (_root_.ContinuousLinearMap.lsmul ℝ ℝ)
      (φ n).contDiff_normed hf.continuous.locallyIntegrable
  · exact fun n => (φ n).lipschitz_normed_convolution hf
  · exact ContDiffBump.convolution_tendstoUniformly_of_lipschitz
      tendsto_one_div_add_atTop_nhds_zero_nat hf

run_cmd do
  let env ← Lean.getEnv
  if env.contains `LipschitzWith.exists_contDiff_lipschitz_tendstoUniformly then
    throwError "Refusing to shadow existing declaration LipschitzWith.exists_contDiff_lipschitz_tendstoUniformly"
  Lean.modifyEnv fun env => Lean.addAlias env `LipschitzWith.exists_contDiff_lipschitz_tendstoUniformly ``Submission.LipschitzWith.exists_contDiff_lipschitz_tendstoUniformly

end LipschitzWith

namespace ContDiffBump
open _root_.ContDiffBump

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {μ : Measure E} [μ.IsAddHaarMeasure]

open _root_.ContDiffBump in
theorem hasFDerivAt_normed_convolution_of_lipschitz
    (φ : ContDiffBump (0 : E)) {f : E → F} {C : ℝ≥0}
    (hf : LipschitzWith C f) (x : E) :
    HasFDerivAt (φ.normed μ ⋆[_root_.ContinuousLinearMap.lsmul ℝ ℝ, μ] f)
      ((φ.normed μ ⋆[_root_.ContinuousLinearMap.lsmul ℝ ℝ, μ] fderiv ℝ f) x) x := by
  have hi (y : E) : _root_.MeasureTheory.Integrable (fun t => φ.normed μ t • f (y - t)) μ :=
    φ.hasCompactSupport_normed.convolutionExists_left_of_continuous_right (_root_.ContinuousLinearMap.lsmul ℝ ℝ)
      φ.integrable_normed.locallyIntegrable hf.continuous y
  have hm : _root_.MeasureTheory.AEStronglyMeasurable (fun t => φ.normed μ t • fderiv ℝ f (x - t)) μ := by
    exact φ.continuous_normed.aestronglyMeasurable.smul
      ((measurable_fderiv ℝ f).comp (measurable_const.sub measurable_id)).aestronglyMeasurable
  have hd : ∀ᵐ t ∂μ, DifferentiableAt ℝ f (x - t) := by
    exact (μ.measurePreserving_sub_left x).quasiMeasurePreserving.ae (hf.ae_differentiableAt (μ := μ))
  have h := hasFDerivAt_integral_of_dominated_loc_of_lip'
    (F := fun y t => φ.normed μ t • f (y - t))
    (F' := fun t => φ.normed μ t • fderiv ℝ f (x - t))
    (bound := fun t => φ.normed μ t * (C : ℝ))
    (s := Set.univ) Filter.univ_mem (fun y _ => (hi y).aestronglyMeasurable) (hi x) hm
    (by
      filter_upwards [] with t y _
      rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_nonneg (φ.nonneg_normed t)]
      rw [mul_assoc]
      apply mul_le_mul_of_nonneg_left _ (φ.nonneg_normed t)
      simpa only [sub_sub_sub_cancel_right] using hf.norm_sub_le (y - t) (x - t))
    (φ.integrable_normed.mul_const (C : ℝ))
    (by
      filter_upwards [hd] with t ht
      simpa [Function.comp_def, Pi.smul_def, Pi.sub_def] using (ht.hasFDerivAt.comp x
        ((hasFDerivAt_id x).sub (hasFDerivAt_const t x))).const_smul (φ.normed μ t))
  exact h.2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `ContDiffBump.hasFDerivAt_normed_convolution_of_lipschitz then
    throwError "Refusing to shadow existing declaration ContDiffBump.hasFDerivAt_normed_convolution_of_lipschitz"
  Lean.modifyEnv fun env => Lean.addAlias env `ContDiffBump.hasFDerivAt_normed_convolution_of_lipschitz ``Submission.ContDiffBump.hasFDerivAt_normed_convolution_of_lipschitz

end ContDiffBump

section

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {μ : Measure E}

omit [FiniteDimensional ℝ F] in
open _root_.LipschitzWith in
theorem LipschitzWith.locallyIntegrable_fderiv [CompleteSpace F] [SecondCountableTopology F]
    [_root_.MeasureTheory.IsLocallyFiniteMeasure μ]
    {f : E → F} {C : ℝ≥0} (hf : LipschitzWith C f) :
    LocallyIntegrable (fderiv ℝ f) μ := by
  apply locallyIntegrable_iff.mpr
  intro k hk
  exact (_root_.MeasureTheory.integrableOn_const (C := (C : ℝ)) hk.measure_ne_top).mono'
    (measurable_fderiv ℝ f).aestronglyMeasurable
    (Filter.Eventually.of_forall fun _ => norm_fderiv_le_of_lipschitz ℝ hf)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `LipschitzWith.locallyIntegrable_fderiv then
    throwError "Refusing to shadow existing declaration LipschitzWith.locallyIntegrable_fderiv"
  Lean.modifyEnv fun env => Lean.addAlias env `LipschitzWith.locallyIntegrable_fderiv ``Submission.LipschitzWith.locallyIntegrable_fderiv

namespace ContDiffBump
open _root_.ContDiffBump

variable [μ.IsAddHaarMeasure]

open _root_.ContDiffBump in
theorem ae_fderiv_normed_convolution_tendsto_of_lipschitz
    {ι : Type*} {φ : ι → ContDiffBump (0 : E)} {l : Filter ι} {K : ℝ}
    {f : E → F} {C : ℝ≥0}
    (hφ : _root_.Filter.Tendsto (fun i => (φ i).rOut) l (𝓝 0))
    (hφ_ratio : ∀ᶠ i in l, (φ i).rOut ≤ K * (φ i).rIn)
    (hf : LipschitzWith C f) :
    ∀ᵐ x ∂μ, _root_.Filter.Tendsto (fun i => fderiv ℝ ((φ i).normed μ ⋆[_root_.ContinuousLinearMap.lsmul ℝ ℝ, μ] f) x)
      l (𝓝 (fderiv ℝ f x)) := by
  filter_upwards [_root_.ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable hφ hφ_ratio
    (hf.locallyIntegrable_fderiv (μ := μ))] with x hx
  exact hx.congr (fun i => ((φ i).hasFDerivAt_normed_convolution_of_lipschitz hf x).fderiv.symm)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `ContDiffBump.ae_fderiv_normed_convolution_tendsto_of_lipschitz then
    throwError "Refusing to shadow existing declaration ContDiffBump.ae_fderiv_normed_convolution_tendsto_of_lipschitz"
  Lean.modifyEnv fun env => Lean.addAlias env `ContDiffBump.ae_fderiv_normed_convolution_tendsto_of_lipschitz ``Submission.ContDiffBump.ae_fderiv_normed_convolution_tendsto_of_lipschitz

open _root_.ContDiffBump in
theorem integral_norm_sub_fderiv_normed_convolution_sq_tendsto_of_lipschitz
    {ι : Type*} {φ : ι → ContDiffBump (0 : E)} {l : Filter ι} [l.IsCountablyGenerated]
    {K : ℝ} {f : E → F} {C : ℝ≥0} {s : Set E}
    (hφ : _root_.Filter.Tendsto (fun i => (φ i).rOut) l (𝓝 0))
    (hφ_ratio : ∀ᶠ i in l, (φ i).rOut ≤ K * (φ i).rIn)
    (hf : LipschitzWith C f) (hs : μ s ≠ ⊤) :
    _root_.Filter.Tendsto (fun i => ∫ x in s,
      ‖fderiv ℝ ((φ i).normed μ ⋆[_root_.ContinuousLinearMap.lsmul ℝ ℝ, μ] f) x - fderiv ℝ f x‖ ^ 2 ∂μ)
      l (𝓝 0) := by
  have hlim := ae_fderiv_normed_convolution_tendsto_of_lipschitz (μ := μ) hφ hφ_ratio hf
  have hbound (i : ι) (x : E) :
      ‖fderiv ℝ ((φ i).normed μ ⋆[_root_.ContinuousLinearMap.lsmul ℝ ℝ, μ] f) x - fderiv ℝ f x‖ ≤ 2 * C := by
    calc
      ‖fderiv ℝ ((φ i).normed μ ⋆[_root_.ContinuousLinearMap.lsmul ℝ ℝ, μ] f) x - fderiv ℝ f x‖ ≤
          ‖fderiv ℝ ((φ i).normed μ ⋆[_root_.ContinuousLinearMap.lsmul ℝ ℝ, μ] f) x‖ + ‖fderiv ℝ f x‖ := norm_sub_le _ _
      _ ≤ (C : ℝ) + C := add_le_add
        (norm_fderiv_le_of_lipschitz ℝ ((φ i).lipschitz_normed_convolution hf))
        (norm_fderiv_le_of_lipschitz ℝ hf)
      _ = 2 * C := by ring
  have h := _root_.MeasureTheory.tendsto_integral_filter_of_dominated_convergence
    (μ := μ.restrict s) (f := fun _ : E => (0 : ℝ)) (fun _ : E => (2 * (C : ℝ)) ^ 2)
    (Filter.Eventually.of_forall fun i =>
      (((measurable_fderiv ℝ ((φ i).normed μ ⋆[_root_.ContinuousLinearMap.lsmul ℝ ℝ, μ] f)).sub
        (measurable_fderiv ℝ f)).norm.pow_const 2).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun i => Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ (norm_nonneg _) (hbound i x) 2)
    (_root_.MeasureTheory.integrableOn_const hs)
    (by
      filter_upwards [_root_.MeasureTheory.ae_restrict_of_ae hlim] with x hx
      simpa using ((hx.sub_const (fderiv ℝ f x)).norm.pow 2))
  simpa using h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `ContDiffBump.integral_norm_sub_fderiv_normed_convolution_sq_tendsto_of_lipschitz then
    throwError "Refusing to shadow existing declaration ContDiffBump.integral_norm_sub_fderiv_normed_convolution_sq_tendsto_of_lipschitz"
  Lean.modifyEnv fun env => Lean.addAlias env `ContDiffBump.integral_norm_sub_fderiv_normed_convolution_sq_tendsto_of_lipschitz ``Submission.ContDiffBump.integral_norm_sub_fderiv_normed_convolution_sq_tendsto_of_lipschitz

end ContDiffBump

end

namespace LipschitzWith
open _root_.LipschitzWith

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {μ : Measure E} [μ.IsAddHaarMeasure]

open _root_.LipschitzWith in
theorem exists_contDiff_lipschitz_tendstoUniformly_fderiv
    {f : E → F} {C : ℝ≥0} (hf : LipschitzWith C f) :
    ∃ g : ℕ → E → F, (∀ n, ContDiff ℝ ∞ (g n)) ∧
      (∀ n, LipschitzWith C (g n)) ∧ TendstoUniformly g f _root_.Filter.atTop ∧
      (∀ n x, ‖g n x - f x‖ ≤ (C : ℝ) / ((n : ℝ) + 1)) ∧
      (∀ᵐ x ∂μ, _root_.Filter.Tendsto (fun n => fderiv ℝ (g n) x) _root_.Filter.atTop (𝓝 (fderiv ℝ f x))) ∧
      ∀ s : Set E, μ s ≠ ⊤ →
        _root_.Filter.Tendsto (fun n => ∫ x in s, ‖fderiv ℝ (g n) x - fderiv ℝ f x‖ ^ 2 ∂μ)
          atTop (𝓝 0) := by
  let φ (n : ℕ) : ContDiffBump (0 : E) :=
    ⟨(1 / ((n : ℝ) + 1)) / 2, 1 / ((n : ℝ) + 1), by positivity,
      half_lt_self (by positivity)⟩
  have hφ : _root_.Filter.Tendsto (fun n => (φ n).rOut) _root_.Filter.atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hφ_ratio : ∀ᶠ n in _root_.Filter.atTop, (φ n).rOut ≤ 2 * (φ n).rIn := by
    filter_upwards [] with n
    dsimp [φ]
    linarith
  refine ⟨fun n => (φ n).normed μ ⋆[_root_.ContinuousLinearMap.lsmul ℝ ℝ, μ] f, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n
    exact (φ n).hasCompactSupport_normed.contDiff_convolution_left (_root_.ContinuousLinearMap.lsmul ℝ ℝ)
      (φ n).contDiff_normed hf.continuous.locallyIntegrable
  · exact fun n => (φ n).lipschitz_normed_convolution hf
  · exact ContDiffBump.convolution_tendstoUniformly_of_lipschitz hφ hf
  · intro n x
    have hrad : (φ n).rOut = 1 / ((n : ℝ) + 1) := rfl
    simpa only [dist_eq_norm, hrad, mul_one_div] using
      (φ n).dist_normed_convolution_le_mul (μ := μ) hf x
  · exact ContDiffBump.ae_fderiv_normed_convolution_tendsto_of_lipschitz hφ hφ_ratio hf
  · intro s hs
    exact ContDiffBump.integral_norm_sub_fderiv_normed_convolution_sq_tendsto_of_lipschitz
      hφ hφ_ratio hf hs

run_cmd do
  let env ← Lean.getEnv
  if env.contains `LipschitzWith.exists_contDiff_lipschitz_tendstoUniformly_fderiv then
    throwError "Refusing to shadow existing declaration LipschitzWith.exists_contDiff_lipschitz_tendstoUniformly_fderiv"
  Lean.modifyEnv fun env => Lean.addAlias env `LipschitzWith.exists_contDiff_lipschitz_tendstoUniformly_fderiv ``Submission.LipschitzWith.exists_contDiff_lipschitz_tendstoUniformly_fderiv

end LipschitzWith

namespace LipschitzWith
open _root_.LipschitzWith

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
  {μ : Measure E} [μ.IsAddHaarMeasure]

open _root_.LipschitzWith in
theorem exists_contDiff_nonneg_tsupport_subset_tendstoUniformly_fderiv
    {f : E → ℝ} {C : ℝ≥0} (hf : LipschitzWith C f)
    (hf0 : ∀ x, 0 ≤ f x) (hfc : HasCompactSupport f)
    {Ω : Set E} (hΩ : IsOpen Ω) (hfs : tsupport f ⊆ Ω) :
    ∃ K : Set E, IsCompact K ∧ K ⊆ Ω ∧ tsupport f ⊆ K ∧
      ∃ g : ℕ → E → ℝ, (∀ n, ContDiff ℝ ∞ (g n)) ∧
        (∀ n, LipschitzWith C (g n)) ∧ (∀ n, tsupport (g n) ⊆ K) ∧
        (∀ n x, 0 ≤ g n x) ∧ TendstoUniformly g f _root_.Filter.atTop ∧
        ∀ᵐ x ∂μ, _root_.Filter.Tendsto (fun n => fderiv ℝ (g n) x) _root_.Filter.atTop (𝓝 (fderiv ℝ f x)) := by
  obtain ⟨δ, hδ, hδΩ⟩ := hfc.isCompact.exists_cthickening_subset_open hΩ hfs
  let φ (n : ℕ) : ContDiffBump (0 : E) :=
    ⟨(δ / ((n : ℝ) + 1)) / 2, δ / ((n : ℝ) + 1), by positivity,
      half_lt_self (by positivity)⟩
  have hφ : _root_.Filter.Tendsto (fun n => (φ n).rOut) _root_.Filter.atTop (𝓝 0) := by
    simpa only [φ, mul_one_div, _root_.MulZeroClass.mul_zero] using
      tendsto_one_div_add_atTop_nhds_zero_nat.const_mul δ
  have hφ_ratio : ∀ᶠ n in _root_.Filter.atTop, (φ n).rOut ≤ 2 * (φ n).rIn := by
    filter_upwards [] with n
    dsimp [φ]
    linarith
  have hrad (n : ℕ) : (φ n).rOut ≤ δ := by
    dsimp only [φ]
    exact div_le_self hδ.le (by have := Nat.cast_nonneg (α := ℝ) n; linarith)
  refine ⟨cthickening δ (tsupport f), hfc.isCompact.cthickening, hδΩ,
    _root_.Metric.self_subset_cthickening (tsupport f),
    fun n => (φ n).normed μ ⋆[_root_.ContinuousLinearMap.lsmul ℝ ℝ, μ] f, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n
    exact (φ n).hasCompactSupport_normed.contDiff_convolution_left (_root_.ContinuousLinearMap.lsmul ℝ ℝ)
      (φ n).contDiff_normed hf.continuous.locallyIntegrable
  · exact fun n => (φ n).lipschitz_normed_convolution hf
  · intro n
    apply closure_minimal _ _root_.Metric.isClosed_cthickening
    intro x hx
    obtain ⟨y, hy, z, hz, rfl⟩ := _root_.MeasureTheory.support_convolution_subset_swap (_root_.ContinuousLinearMap.lsmul ℝ ℝ) hx
    apply _root_.Metric.mem_cthickening_of_dist_le (y + z) y δ (tsupport f) (subset_tsupport f hy)
    have hz' : _root_.Dist.dist z 0 < (φ n).rOut := by
      simpa only [(φ n).support_normed_eq, _root_.Metric.mem_ball] using hz
    simpa only [dist_eq_norm, add_sub_cancel_left, sub_zero] using hz'.le.trans (hrad n)
  · intro n x
    exact _root_.MeasureTheory.integral_nonneg fun y => mul_nonneg ((φ n).nonneg_normed y) (hf0 (x - y))
  · exact ContDiffBump.convolution_tendstoUniformly_of_lipschitz hφ hf
  · exact ContDiffBump.ae_fderiv_normed_convolution_tendsto_of_lipschitz hφ hφ_ratio hf

run_cmd do
  let env ← Lean.getEnv
  if env.contains `LipschitzWith.exists_contDiff_nonneg_tsupport_subset_tendstoUniformly_fderiv then
    throwError "Refusing to shadow existing declaration LipschitzWith.exists_contDiff_nonneg_tsupport_subset_tendstoUniformly_fderiv"
  Lean.modifyEnv fun env => Lean.addAlias env `LipschitzWith.exists_contDiff_nonneg_tsupport_subset_tendstoUniformly_fderiv ``Submission.LipschitzWith.exists_contDiff_nonneg_tsupport_subset_tendstoUniformly_fderiv

end LipschitzWith
