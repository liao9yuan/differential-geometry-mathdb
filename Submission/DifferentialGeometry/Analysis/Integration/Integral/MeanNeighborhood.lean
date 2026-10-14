import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Topology.MetricSpace.Thickening
import Submission.DifferentialGeometry.Analysis.Integration.Measure.BoundedDensity

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Set

namespace MeasureTheory
open _root_.MeasureTheory

variable {X F : Type*} [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

omit [CompleteSpace F] in
open _root_.MeasureTheory in
private theorem integral_norm_sq_le_integral_sq_norm {f : X → F} (hf : _root_.MeasureTheory.MemLp f 2 μ) :
    ‖∫ x, f x ∂μ‖ ^ 2 ≤ ∫ x, ‖f x‖ ^ 2 ∂μ := by
  have hg : _root_.MeasureTheory.MemLp (fun x => ‖f x‖) (ENNReal.ofReal 2) μ := by simpa using hf.norm
  have hh := _root_.MeasureTheory.integral_mul_le_Lp_mul_Lq_of_nonneg
    (f := fun x => ‖f x‖) (g := fun _ : X => (1 : ℝ)) Real.HolderConjugate.two_two
    (Filter.Eventually.of_forall fun x => norm_nonneg (f x))
    (Filter.Eventually.of_forall fun _ => (by norm_num : (0 : ℝ) ≤ 1)) hg (_root_.MeasureTheory.memLp_const _)
  have hn : 0 ≤ ∫ x, ‖f x‖ ∂μ := _root_.MeasureTheory.integral_nonneg fun x => norm_nonneg (f x)
  have hs : 0 ≤ ∫ x, ‖f x‖ ^ 2 ∂μ := _root_.MeasureTheory.integral_nonneg fun x => sq_nonneg ‖f x‖
  have hμ : μ.real _root_.Set.univ = 1 := by simp [Measure.real]
  simp only [mul_one, Real.rpow_two, one_pow, _root_.MeasureTheory.integral_const, hμ,
    one_smul, Real.sqrt_one, mul_one, ← Real.sqrt_eq_rpow] at hh
  have hsq := (sq_le_sq₀ hn (Real.sqrt_nonneg _)).mpr hh
  rw [Real.sq_sqrt hs] at hsq
  exact ((sq_le_sq₀ (norm_nonneg _) hn).mpr (_root_.MeasureTheory.norm_integral_le_integral_norm f)).trans hsq

run_cmd do
  let target := ``Submission.MeasureTheory.integral_norm_sq_le_integral_sq_norm
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `MeasureTheory.integral_norm_sq_le_integral_sq_norm target :: scope.openDecls } }

open _root_.MeasureTheory in
theorem integral_norm_sub_integral_sq_le_four_mul {f : X → F} (hf : _root_.MeasureTheory.MemLp f 2 μ) (a : F) :
    (∫ x, ‖f x - ∫ y, f y ∂μ‖ ^ 2 ∂μ) ≤ 4 * ∫ x, ‖f x - a‖ ^ 2 ∂μ := by
  let m := ∫ y, f y ∂μ
  have hfa : _root_.MeasureTheory.MemLp (fun x => f x - a) 2 μ := hf.sub (_root_.MeasureTheory.memLp_const _)
  have hfm : _root_.MeasureTheory.MemLp (fun x => f x - m) 2 μ := hf.sub (_root_.MeasureTheory.memLp_const _)
  have hfi : _root_.MeasureTheory.Integrable f μ := hf.integrable (by norm_num)
  have hm : ‖m - a‖ ^ 2 ≤ ∫ x, ‖f x - a‖ ^ 2 ∂μ := by
    have h := integral_norm_sq_le_integral_sq_norm hfa
    rw [_root_.MeasureTheory.integral_sub hfi (_root_.MeasureTheory.integrable_const a)] at h
    simpa only [_root_.MeasureTheory.integral_const, show μ.real _root_.Set.univ = 1 by simp [Measure.real], one_smul, m] using h
  have hb (x : X) : ‖f x - m‖ ^ 2 ≤ 2 * ‖f x - a‖ ^ 2 + 2 * ‖m - a‖ ^ 2 := by
    have ht := norm_sub_le (f x - a) (m - a)
    have heq : f x - a - (m - a) = f x - m := by abel
    rw [heq] at ht
    have hs := (sq_le_sq₀ (norm_nonneg _) (add_nonneg (norm_nonneg _) (norm_nonneg _))).mpr ht
    nlinarith [sq_nonneg (‖f x - a‖ - ‖m - a‖)]
  have hint : (∫ x, ‖f x - m‖ ^ 2 ∂μ) ≤
      ∫ x, 2 * ‖f x - a‖ ^ 2 + 2 * ‖m - a‖ ^ 2 ∂μ :=
    _root_.MeasureTheory.integral_mono (_root_.MeasureTheory.memLp_two_iff_integrable_sq_norm hfm.aestronglyMeasurable |>.mp hfm)
      ((_root_.MeasureTheory.memLp_two_iff_integrable_sq_norm hfa.aestronglyMeasurable |>.mp hfa).const_mul 2
        |>.add (_root_.MeasureTheory.integrable_const _)) hb
  have hsq : _root_.MeasureTheory.Integrable (fun x => ‖f x - a‖ ^ 2) μ :=
    (_root_.MeasureTheory.memLp_two_iff_integrable_sq_norm hfa.aestronglyMeasurable).mp hfa
  rw [_root_.MeasureTheory.integral_add (hsq.const_mul 2) (_root_.MeasureTheory.integrable_const _), _root_.MeasureTheory.integral_const_mul,
    _root_.MeasureTheory.integral_const, show μ.real _root_.Set.univ = 1 by simp [Measure.real], one_smul] at hint
  change (∫ x, ‖f x - m‖ ^ 2 ∂μ) ≤ _
  nlinarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `MeasureTheory.integral_norm_sub_integral_sq_le_four_mul then
    throwError "Refusing to shadow existing declaration MeasureTheory.integral_norm_sub_integral_sq_le_four_mul"
  Lean.modifyEnv fun env => Lean.addAlias env `MeasureTheory.integral_norm_sub_integral_sq_le_four_mul ``Submission.MeasureTheory.integral_norm_sub_integral_sq_le_four_mul

end MeasureTheory

end

section

open _root_.MeasureTheory _root_.Submission.MeasureTheory

namespace Metric
open _root_.Metric

variable {α X : Type*} [MeasurableSpace α] [PseudoMetricSpace X]
  {μ : Measure α} [IsProbabilityMeasure μ]

open _root_.Metric in
theorem infDist_sq_le_integral_dist_sq {K : Set X} {f : α → X} (z : X)
    (hfK : ∀ᵐ x ∂μ, f x ∈ K)
    (hf : _root_.MeasureTheory.Integrable (fun x => _root_.Dist.dist z (f x) ^ 2) μ) :
    infDist z K ^ 2 ≤ ∫ x, _root_.Dist.dist z (f x) ^ 2 ∂μ := by
  have hle : (fun _ : α => _root_.Metric.infDist z K ^ 2) ≤ᵐ[μ]
      (fun x => _root_.Dist.dist z (f x) ^ 2) := by
    filter_upwards [hfK] with x hx
    exact (sq_le_sq₀ _root_.Metric.infDist_nonneg dist_nonneg).mpr (_root_.Metric.infDist_le_dist_of_mem hx)
  simpa using _root_.MeasureTheory.integral_mono_ae (_root_.MeasureTheory.integrable_const (_root_.Metric.infDist z K ^ 2)) hf hle

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Metric.infDist_sq_le_integral_dist_sq then
    throwError "Refusing to shadow existing declaration Metric.infDist_sq_le_integral_dist_sq"
  Lean.modifyEnv fun env => Lean.addAlias env `Metric.infDist_sq_le_integral_dist_sq ``Submission.Metric.infDist_sq_le_integral_dist_sq

end Metric

namespace IsCompact
open _root_.IsCompact

variable {α X : Type*} [MeasurableSpace α] [PseudoMetricSpace X]

open _root_.IsCompact in
theorem exists_mem_of_integral_dist_sq_lt {K U : Set X} (hK : IsCompact K)
    (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (μ : _root_.MeasureTheory.Measure α) [_root_.MeasureTheory.IsProbabilityMeasure μ]
      (f : α → X) (z : X), (∀ᵐ x ∂μ, f x ∈ K) →
      _root_.MeasureTheory.Integrable (fun x => _root_.Dist.dist z (f x) ^ 2) μ →
      (∫ x, _root_.Dist.dist z (f x) ^ 2 ∂μ) < δ ^ 2 → z ∈ U := by
  obtain ⟨δ, hδ, hδU⟩ := hK.exists_cthickening_subset_open hU hKU
  refine ⟨δ, hδ, ?_⟩
  intro μ _ f z hfK hf hvar
  have hne : K.Nonempty := by
    obtain ⟨x, hx⟩ := hfK.exists
    exact ⟨f x, hx⟩
  have hinf : Metric.infDist z K < δ :=
    (sq_lt_sq₀ Metric.infDist_nonneg hδ.le).mp
      ((Metric.infDist_sq_le_integral_dist_sq z hfK hf).trans_lt hvar)
  obtain ⟨y, hyK, hzy⟩ := (Metric.infDist_lt_iff hne).mp hinf
  exact hδU (Metric.mem_cthickening_of_dist_le z y δ K hyK hzy.le)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `IsCompact.exists_mem_of_integral_dist_sq_lt then
    throwError "Refusing to shadow existing declaration IsCompact.exists_mem_of_integral_dist_sq_lt"
  Lean.modifyEnv fun env => Lean.addAlias env `IsCompact.exists_mem_of_integral_dist_sq_lt ``Submission.IsCompact.exists_mem_of_integral_dist_sq_lt

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

open _root_.IsCompact in
theorem exists_integral_mem_of_integral_norm_sub_sq_lt {K U : Set F} (hK : IsCompact K)
    (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (μ : _root_.MeasureTheory.Measure α) [_root_.MeasureTheory.IsProbabilityMeasure μ]
      (f : α → F), _root_.MeasureTheory.AEStronglyMeasurable f μ → (∀ᵐ x ∂μ, f x ∈ K) →
      (∫ x, ‖f x - ∫ y, f y ∂μ‖ ^ 2 ∂μ) < δ ^ 2 → (∫ y, f y ∂μ) ∈ U := by
  obtain ⟨δ, hδ, hδU⟩ := hK.exists_mem_of_integral_dist_sq_lt (α := α) hU hKU
  refine ⟨δ, hδ, ?_⟩
  intro μ _ f hf hfK hvar
  obtain ⟨C, hC⟩ := hK.isBounded.exists_norm_le
  have hf₂ : _root_.MeasureTheory.MemLp f 2 μ := MemLp.of_bound hf C (hfK.mono fun x hx => hC (f x) hx)
  have hsub : _root_.MeasureTheory.MemLp (fun x => f x - ∫ y, f y ∂μ) 2 μ :=
    hf₂.sub (_root_.MeasureTheory.memLp_const _)
  have hint : _root_.MeasureTheory.Integrable (fun x => ‖f x - ∫ y, f y ∂μ‖ ^ 2) μ :=
    (_root_.MeasureTheory.memLp_two_iff_integrable_sq_norm hsub.aestronglyMeasurable).mp hsub
  apply hδU μ f (∫ y, f y ∂μ) hfK
  · simpa only [dist_eq_norm, norm_sub_rev] using hint
  · simpa only [dist_eq_norm, norm_sub_rev] using hvar

run_cmd do
  let env ← Lean.getEnv
  if env.contains `IsCompact.exists_integral_mem_of_integral_norm_sub_sq_lt then
    throwError "Refusing to shadow existing declaration IsCompact.exists_integral_mem_of_integral_norm_sub_sq_lt"
  Lean.modifyEnv fun env => Lean.addAlias env `IsCompact.exists_integral_mem_of_integral_norm_sub_sq_lt ``Submission.IsCompact.exists_integral_mem_of_integral_norm_sub_sq_lt

end IsCompact

end

noncomputable section

open _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Set

namespace IsCompact
open _root_.IsCompact

variable {X F : Type*} [MeasurableSpace X]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

open _root_.IsCompact in
theorem exists_integral_mem_of_integral_norm_sub_const_sq_lt
    {K U : Set F} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ δ > 0, ∀ (μ : _root_.MeasureTheory.Measure X) [_root_.MeasureTheory.IsProbabilityMeasure μ] (f : X → F) (a : F),
      _root_.MeasureTheory.AEStronglyMeasurable f μ → (∀ᵐ x ∂μ, f x ∈ K) →
      (∫ x, ‖f x - a‖ ^ 2 ∂μ) < δ ^ 2 → (∫ x, f x ∂μ) ∈ U := by
  obtain ⟨δ, hδ, hbound⟩ :=
    hK.exists_integral_mem_of_integral_norm_sub_sq_lt (α := X) hU hKU
  refine ⟨δ / 2, by positivity, ?_⟩
  intro μ _ f a hf hfK hsmall
  obtain ⟨C, hC⟩ := hK.isBounded.exists_norm_le
  have hf2 : _root_.MeasureTheory.MemLp f 2 μ := MemLp.of_bound hf C (hfK.mono fun x hx => hC (f x) hx)
  apply hbound μ f hf hfK
  have hvar := MeasureTheory.integral_norm_sub_integral_sq_le_four_mul hf2 a
  nlinarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `IsCompact.exists_integral_mem_of_integral_norm_sub_const_sq_lt then
    throwError "Refusing to shadow existing declaration IsCompact.exists_integral_mem_of_integral_norm_sub_const_sq_lt"
  Lean.modifyEnv fun env => Lean.addAlias env `IsCompact.exists_integral_mem_of_integral_norm_sub_const_sq_lt ``Submission.IsCompact.exists_integral_mem_of_integral_norm_sub_const_sq_lt

end IsCompact

end

noncomputable section

open _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Set

namespace IsCompact
open _root_.IsCompact

variable {X F : Type*} [MeasurableSpace X]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

open _root_.IsCompact in
theorem exists_integral_weighted_mem_of_integral_norm_sub_sq_lt
    {K U : Set F} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ δ > 0, ∀ (μ : _root_.MeasureTheory.Measure X) (k : X → ℝ) (s : Set X) (C : ℝ)
      (f : X → F) (a : F),
      Measurable k → (∀ x, 0 ≤ k x) → (∫ x, k x ∂μ) = 1 →
      MeasurableSet s → Function.support k ⊆ s → (∀ x ∈ s, k x ≤ C) →
      _root_.MeasureTheory.AEStronglyMeasurable f (μ.restrict s) → (∀ᵐ x ∂μ.restrict s, f x ∈ K) →
      _root_.MeasureTheory.IntegrableOn (fun x => ‖f x - a‖ ^ 2) s μ →
      C * (∫ x in s, ‖f x - a‖ ^ 2 ∂μ) < δ ^ 2 →
      (∫ x, k x • f x ∂μ) ∈ U := by
  obtain ⟨δ, hδ, hbound⟩ :=
    hK.exists_integral_mem_of_integral_norm_sub_const_sq_lt (X := X) hU hKU
  refine ⟨δ, hδ, ?_⟩
  intro μ k s C f a hk hk0 hk1 hs hks hkC hf hfK hfi hsmall
  let ν := μ.withDensity (fun x => ENNReal.ofReal (k x))
  let : _root_.MeasureTheory.IsProbabilityMeasure ν := isProbabilityMeasure_withDensity_ofReal
    (Filter.Eventually.of_forall hk0) hk1
  have hνle : ν ≤ ENNReal.ofReal C • μ.restrict s :=
    withDensity_ofReal_le_const_smul_restrict hs hks hkC
  have hfν : _root_.MeasureTheory.AEStronglyMeasurable f ν :=
    (hf.smul_measure (ENNReal.ofReal C)).mono_measure hνle
  have hνK : ∀ᵐ x ∂ν, f x ∈ K :=
    ae_withDensity_of_support_subset hk.aemeasurable hs hks hfK
  have hvar : (∫ x, ‖f x - a‖ ^ 2 ∂ν) < δ ^ 2 :=
    (integral_withDensity_ofReal_le_const_mul_setIntegral hk hk0 hs hks hkC hfi
      (Filter.Eventually.of_forall fun _ => sq_nonneg _)).trans_lt hsmall
  have hm := hbound ν f a hfν hνK hvar
  have heq : (∫ x, f x ∂ν) = ∫ x, k x • f x ∂μ := by
    rw [integral_withDensity_eq_integral_toReal_smul hk.ennreal_ofReal
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    simp only [ENNReal.toReal_ofReal (hk0 _)]
  rwa [heq] at hm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `IsCompact.exists_integral_weighted_mem_of_integral_norm_sub_sq_lt then
    throwError "Refusing to shadow existing declaration IsCompact.exists_integral_weighted_mem_of_integral_norm_sub_sq_lt"
  Lean.modifyEnv fun env => Lean.addAlias env `IsCompact.exists_integral_weighted_mem_of_integral_norm_sub_sq_lt ``Submission.IsCompact.exists_integral_weighted_mem_of_integral_norm_sub_sq_lt

end IsCompact

end
