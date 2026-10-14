import Submission.DifferentialGeometry.Analysis.Calculus.Displacement
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.Linarith

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.MeasureTheory
open scoped _root_.InnerProductSpace

namespace DifferentialGeometry.Analysis

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

private theorem inner_ge_one_sub_of_tangent_variation {T : ℝ → E} {a b x₀ ε : ℝ}
    (hx₀ : x₀ ∈ _root_.Set.Icc a b) (hT : ContinuousOn T (_root_.Set.Icc a b))
    (hdT : DifferentiableOn ℝ T (_root_.Set.Ioo a b))
    (hi : IntervalIntegrable (fun s => ‖deriv T s‖) _root_.MeasureTheory.MeasureSpace.volume a b)
    (hvar : (∫ s in a..b, ‖deriv T s‖) ≤ ε) (hunit : ‖T x₀‖ = 1)
    {s : ℝ} (hs : s ∈ _root_.Set.Icc a b) : 1 - ε ≤ ⟪T s, T x₀⟫_ℝ := by
  have hn := (norm_sub_le_integral_norm_deriv_of_mem_Icc hT hdT hi hs hx₀).trans hvar
  have hc := real_inner_le_norm (T x₀ - T s) (T x₀)
  rw [inner_sub_left, real_inner_self_eq_norm_sq, hunit, norm_sub_rev] at hc
  nlinarith only [hn, hc]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.inner_ge_one_sub_of_tangent_variation
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.inner_ge_one_sub_of_tangent_variation target :: scope.openDecls } }

theorem mul_sub_le_inner_sub_of_tangent_variation {γ T : ℝ → E} {v : ℝ → ℝ}
    {a b x₀ C ε : ℝ} (hx₀ : x₀ ∈ _root_.Set.Icc a b) (hC : 0 ≤ C) (hε : ε ≤ 1)
    (hγ : ContinuousOn γ (_root_.Set.Icc a b))
    (hdγ : ∀ s ∈ _root_.Set.Ioo a b, HasDerivAt γ (v s • T s) s)
    (hv : ∀ s ∈ _root_.Set.Ioo a b, C ≤ v s)
    (hT : ContinuousOn T (_root_.Set.Icc a b)) (hdT : DifferentiableOn ℝ T (_root_.Set.Ioo a b))
    (hi : IntervalIntegrable (fun s => ‖deriv T s‖) _root_.MeasureTheory.MeasureSpace.volume a b)
    (hvar : (∫ s in a..b, ‖deriv T s‖) ≤ ε) (hunit : ‖T x₀‖ = 1)
    {x y : ℝ} (hx : x ∈ _root_.Set.Icc a b) (hy : y ∈ _root_.Set.Icc a b) (hxy : x ≤ y) :
    C * (1 - ε) * (y - x) ≤ ⟪γ y - γ x, T x₀⟫_ℝ := by
  let p := fun s => ⟪γ s, T x₀⟫_ℝ
  have hp : ContinuousOn p (_root_.Set.Icc a b) := hγ.inner continuousOn_const
  have hdir (s : ℝ) (hs : s ∈ _root_.Set.Icc a b) : 1 - ε ≤ ⟪T s, T x₀⟫_ℝ :=
    inner_ge_one_sub_of_tangent_variation hx₀ hT hdT hi hvar hunit hs
  have hder (s : ℝ) (hs : s ∈ _root_.Set.Ioo a b) : HasDerivAt p (v s * ⟪T s, T x₀⟫_ℝ) s := by
    simpa only [real_inner_smul_left, inner_zero_right, zero_add] using
      (hdγ s hs).inner ℝ (hasDerivAt_const s (T x₀))
  have hlow (s : ℝ) (hs : s ∈ interior (_root_.Set.Icc a b)) : C * (1 - ε) ≤ deriv p s := by
    rw [interior_Icc] at hs
    rw [(hder s hs).deriv]
    exact mul_le_mul (hv s hs) (hdir s (_root_.Set.Ioo_subset_Icc_self hs)) (sub_nonneg.mpr hε)
      (hC.trans (hv s hs))
  have h := (convex_Icc a b).mul_sub_le_image_sub_of_le_deriv hp
    (fun s hs => (hder s (by simpa only [interior_Icc] using hs)).differentiableAt.differentiableWithinAt)
    hlow x hx y hy hxy
  simpa only [p, inner_sub_left] using h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.mul_sub_le_inner_sub_of_tangent_variation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.mul_sub_le_inner_sub_of_tangent_variation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.mul_sub_le_inner_sub_of_tangent_variation ``Submission.DifferentialGeometry.Analysis.mul_sub_le_inner_sub_of_tangent_variation

theorem mul_integral_le_inner_sub_of_tangent_variation {γ T : ℝ → E} {v : ℝ → ℝ}
    {a b x₀ ε : ℝ} (hx₀ : x₀ ∈ _root_.Set.Icc a b)
    (hγ : ContinuousOn γ (_root_.Set.Icc a b))
    (hdγ : ∀ s ∈ _root_.Set.Ioo a b, HasDerivAt γ (v s • T s) s)
    (hv : ∀ s ∈ _root_.Set.Ioo a b, 0 ≤ v s)
    (hvi : IntervalIntegrable v _root_.MeasureTheory.MeasureSpace.volume a b)
    (hT : ContinuousOn T (_root_.Set.Icc a b)) (hdT : DifferentiableOn ℝ T (_root_.Set.Ioo a b))
    (hi : IntervalIntegrable (fun s => ‖deriv T s‖) _root_.MeasureTheory.MeasureSpace.volume a b)
    (hvar : (∫ s in a..b, ‖deriv T s‖) ≤ ε) (hunit : ‖T x₀‖ = 1)
    {x y : ℝ} (hx : x ∈ _root_.Set.Icc a b) (hy : y ∈ _root_.Set.Icc a b) (hxy : x ≤ y) :
    (1 - ε) * (∫ s in x..y, v s) ≤ ⟪γ y - γ x, T x₀⟫_ℝ := by
  let p := fun s => ⟪γ s, T x₀⟫_ℝ
  have hp : ContinuousOn p (_root_.Set.Icc a b) := hγ.inner continuousOn_const
  have hdir (s : ℝ) (hs : s ∈ _root_.Set.Icc a b) : 1 - ε ≤ ⟪T s, T x₀⟫_ℝ :=
    inner_ge_one_sub_of_tangent_variation hx₀ hT hdT hi hvar hunit hs
  have hder (s : ℝ) (hs : s ∈ _root_.Set.Ioo a b) : HasDerivAt p (v s * ⟪T s, T x₀⟫_ℝ) s := by
    simpa only [real_inner_smul_left, inner_zero_right, zero_add] using
      (hdγ s hs).inner ℝ (hasDerivAt_const s (T x₀))
  have hint : IntervalIntegrable (fun s => (1 - ε) * v s) _root_.MeasureTheory.MeasureSpace.volume x y := by
    apply (hvi.const_mul (1 - ε)).mono_set
    rw [_root_.Set.uIcc_of_le hxy, _root_.Set.uIcc_of_le (hx.1.trans hx.2)]
    exact _root_.Set.Icc_subset_Icc hx.1 hy.2
  have h := intervalIntegral.integral_le_sub_of_hasDeriv_right_of_le hxy
    (hp.mono (_root_.Set.Icc_subset_Icc hx.1 hy.2))
    (fun s hs => (hder s (_root_.Set.Ioo_subset_Ioo hx.1 hy.2 hs)).hasDerivWithinAt)
    ((intervalIntegrable_iff_integrableOn_Icc_of_le hxy).mp hint)
    (fun s hs => by
      have hsab := _root_.Set.Ioo_subset_Ioo hx.1 hy.2 hs
      simpa only [mul_comm] using
        mul_le_mul_of_nonneg_left (hdir s (_root_.Set.Ioo_subset_Icc_self hsab)) (hv s hsab))
  simpa only [p, intervalIntegral.integral_const_mul, inner_sub_left] using h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.mul_integral_le_inner_sub_of_tangent_variation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.mul_integral_le_inner_sub_of_tangent_variation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.mul_integral_le_inner_sub_of_tangent_variation ``Submission.DifferentialGeometry.Analysis.mul_integral_le_inner_sub_of_tangent_variation

theorem strictMonoOn_inner_of_tangent_variation {γ T : ℝ → E} {v : ℝ → ℝ}
    {a b x₀ ε : ℝ} (hx₀ : x₀ ∈ _root_.Set.Icc a b) (hε : ε < 1)
    (hγ : ContinuousOn γ (_root_.Set.Icc a b))
    (hdγ : ∀ s ∈ _root_.Set.Ioo a b, HasDerivAt γ (v s • T s) s)
    (hv : ∀ s ∈ _root_.Set.Ioo a b, 0 < v s)
    (hT : ContinuousOn T (_root_.Set.Icc a b)) (hdT : DifferentiableOn ℝ T (_root_.Set.Ioo a b))
    (hi : IntervalIntegrable (fun s => ‖deriv T s‖) _root_.MeasureTheory.MeasureSpace.volume a b)
    (hvar : (∫ s in a..b, ‖deriv T s‖) ≤ ε) (hunit : ‖T x₀‖ = 1) :
    StrictMonoOn (fun s => ⟪γ s, T x₀⟫_ℝ) (_root_.Set.Icc a b) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc a b) (hγ.inner continuousOn_const)
  intro s hs
  rw [interior_Icc] at hs
  have hder : HasDerivAt (fun s => ⟪γ s, T x₀⟫_ℝ) (v s * ⟪T s, T x₀⟫_ℝ) s := by
    simpa only [real_inner_smul_left, inner_zero_right, zero_add] using
      (hdγ s hs).inner ℝ (hasDerivAt_const s (T x₀))
  rw [hder.deriv]
  exact mul_pos (hv s hs) ((sub_pos.mpr hε).trans_le
    (inner_ge_one_sub_of_tangent_variation hx₀ hT hdT hi hvar hunit (_root_.Set.Ioo_subset_Icc_self hs)))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.strictMonoOn_inner_of_tangent_variation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.strictMonoOn_inner_of_tangent_variation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.strictMonoOn_inner_of_tangent_variation ``Submission.DifferentialGeometry.Analysis.strictMonoOn_inner_of_tangent_variation

theorem exists_unique_inner_projection_of_tangent_variation {γ T : ℝ → E} {v : ℝ → ℝ}
    {a b x₀ C ε : ℝ} (hx₀ : x₀ ∈ _root_.Set.Icc a b) (hC : 0 < C) (hε : ε < 1)
    (hγ : ContinuousOn γ (_root_.Set.Icc a b))
    (hdγ : ∀ s ∈ _root_.Set.Ioo a b, HasDerivAt γ (v s • T s) s)
    (hv : ∀ s ∈ _root_.Set.Ioo a b, C ≤ v s)
    (hT : ContinuousOn T (_root_.Set.Icc a b)) (hdT : DifferentiableOn ℝ T (_root_.Set.Ioo a b))
    (hi : IntervalIntegrable (fun s => ‖deriv T s‖) _root_.MeasureTheory.MeasureSpace.volume a b)
    (hvar : (∫ s in a..b, ‖deriv T s‖) ≤ ε) (hunit : ‖T x₀‖ = 1)
    {z : ℝ} (hz : z ∈ _root_.Set.Ioo (-C * (1 - ε) * (x₀ - a)) (C * (1 - ε) * (b - x₀))) :
    ∃! s, s ∈ _root_.Set.Ioo a b ∧ ⟪γ s - γ x₀, T x₀⟫_ℝ = z := by
  let p := fun s => ⟪γ s - γ x₀, T x₀⟫_ℝ
  have hab := hx₀.1.trans hx₀.2
  have hleft := mul_sub_le_inner_sub_of_tangent_variation hx₀ hC.le hε.le hγ hdγ hv hT hdT hi
    hvar hunit ⟨le_rfl, hab⟩ hx₀ hx₀.1
  have hright := mul_sub_le_inner_sub_of_tangent_variation hx₀ hC.le hε.le hγ hdγ hv hT hdT hi
    hvar hunit hx₀ ⟨hab, le_rfl⟩ hx₀.2
  have hp : ContinuousOn p (_root_.Set.Icc a b) := (hγ.sub continuousOn_const).inner continuousOn_const
  have hmem : z ∈ _root_.Set.Ioo (p a) (p b) := by
    dsimp only [p]
    simp only [_root_.Set.mem_Ioo, inner_sub_left] at hleft hright ⊢
    constructor <;> linarith only [hleft, hright, hz.1, hz.2]
  obtain ⟨s, hs, hsz⟩ := intermediate_value_Ioo hab hp hmem
  have hmono := strictMonoOn_inner_of_tangent_variation hx₀ hε hγ hdγ
    (fun s hs => hC.trans_le (hv s hs)) hT hdT hi hvar hunit
  refine ⟨s, ⟨hs, hsz⟩, ?_⟩
  intro w hw
  apply hmono.injOn (_root_.Set.Ioo_subset_Icc_self hw.1) (_root_.Set.Ioo_subset_Icc_self hs)
  have heq := hw.2.trans hsz.symm
  simp only [p, inner_sub_left] at heq
  linarith only [heq]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.exists_unique_inner_projection_of_tangent_variation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.exists_unique_inner_projection_of_tangent_variation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.exists_unique_inner_projection_of_tangent_variation ``Submission.DifferentialGeometry.Analysis.exists_unique_inner_projection_of_tangent_variation

theorem exists_unique_inner_projection_of_tangent_variation_of_integrable_speed {γ T : ℝ → E} {v : ℝ → ℝ}
    {a b x₀ ε : ℝ} (hx₀ : x₀ ∈ _root_.Set.Icc a b) (hε : ε < 1)
    (hγ : ContinuousOn γ (_root_.Set.Icc a b))
    (hdγ : ∀ s ∈ _root_.Set.Ioo a b, HasDerivAt γ (v s • T s) s)
    (hv : ∀ s ∈ _root_.Set.Ioo a b, 0 < v s)
    (hvi : IntervalIntegrable v _root_.MeasureTheory.MeasureSpace.volume a b)
    (hT : ContinuousOn T (_root_.Set.Icc a b)) (hdT : DifferentiableOn ℝ T (_root_.Set.Ioo a b))
    (hi : IntervalIntegrable (fun s => ‖deriv T s‖) _root_.MeasureTheory.MeasureSpace.volume a b)
    (hvar : (∫ s in a..b, ‖deriv T s‖) ≤ ε) (hunit : ‖T x₀‖ = 1)
    {z : ℝ} (hz : z ∈ _root_.Set.Ioo (-(1 - ε) * (∫ s in a..x₀, v s))
      ((1 - ε) * (∫ s in x₀..b, v s))) :
    ∃! s, s ∈ _root_.Set.Ioo a b ∧ ⟪γ s - γ x₀, T x₀⟫_ℝ = z := by
  let p := fun s => ⟪γ s - γ x₀, T x₀⟫_ℝ
  have hab := hx₀.1.trans hx₀.2
  have hleft := mul_integral_le_inner_sub_of_tangent_variation hx₀ hγ hdγ
    (fun s hs => (hv s hs).le) hvi hT hdT hi
    hvar hunit ⟨le_rfl, hab⟩ hx₀ hx₀.1
  have hright := mul_integral_le_inner_sub_of_tangent_variation hx₀ hγ hdγ
    (fun s hs => (hv s hs).le) hvi hT hdT hi
    hvar hunit hx₀ ⟨hab, le_rfl⟩ hx₀.2
  have hp : ContinuousOn p (_root_.Set.Icc a b) := (hγ.sub continuousOn_const).inner continuousOn_const
  have hmem : z ∈ _root_.Set.Ioo (p a) (p b) := by
    dsimp only [p]
    simp only [_root_.Set.mem_Ioo, inner_sub_left] at hleft hright ⊢
    constructor <;> linarith only [hleft, hright, hz.1, hz.2]
  obtain ⟨s, hs, hsz⟩ := intermediate_value_Ioo hab hp hmem
  have hmono := strictMonoOn_inner_of_tangent_variation hx₀ hε hγ hdγ hv hT hdT hi hvar hunit
  refine ⟨s, ⟨hs, hsz⟩, ?_⟩
  intro w hw
  apply hmono.injOn (_root_.Set.Ioo_subset_Icc_self hw.1) (_root_.Set.Ioo_subset_Icc_self hs)
  have heq := hw.2.trans hsz.symm
  simp only [p, inner_sub_left] at heq
  linarith only [heq]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.exists_unique_inner_projection_of_tangent_variation_of_integrable_speed then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.exists_unique_inner_projection_of_tangent_variation_of_integrable_speed"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.exists_unique_inner_projection_of_tangent_variation_of_integrable_speed ``Submission.DifferentialGeometry.Analysis.exists_unique_inner_projection_of_tangent_variation_of_integrable_speed


end DifferentialGeometry.Analysis
