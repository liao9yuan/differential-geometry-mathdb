import Submission.DifferentialGeometry.Analysis.Integration.Measure.Parametric.Composition
import Mathlib.MeasureTheory.Function.LpSpace.Basic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

open _root_.Filter
open scoped _root_.ENNReal _root_.NNReal

namespace MeasureTheory
open _root_.MeasureTheory

variable {α 𝕜 E F : Type*} [MeasurableSpace α] [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {μ : Measure α} {p : ℝ≥0∞}

open _root_.MeasureTheory _root_.MeasureTheory.MemLp in
theorem MemLp.clm_apply_of_bound {f : α → E} (hf : _root_.MeasureTheory.MemLp f p μ)
    (A : α → E →L[𝕜] F)
    (hA : ∀ v, _root_.MeasureTheory.AEStronglyMeasurable (fun a => A a v) μ)
    {C : ℝ} (hC : ∀ᵐ a ∂μ, ‖A a‖ ≤ C) :
    MemLp (fun a => A a (f a)) p μ := by
  have hm := aestronglyMeasurable_apply_of_ae_continuous hA
    (Filter.Eventually.of_forall (fun a => (A a).continuous)) hf.aestronglyMeasurable
  apply MemLp.of_le_mul (c := C) hf hm
  filter_upwards [hC] with a ha
  exact ((A a).le_opNorm (f a)).trans (mul_le_mul_of_nonneg_right ha (norm_nonneg _))

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.MeasureTheory.MemLp
  let env ← Lean.getEnv
  if env.contains `MeasureTheory.MemLp.clm_apply_of_bound then
    throwError "Refusing to shadow existing declaration MeasureTheory.MemLp.clm_apply_of_bound"
  Lean.modifyEnv fun env => Lean.addAlias env `MeasureTheory.MemLp.clm_apply_of_bound ``Submission.MeasureTheory.MemLp.clm_apply_of_bound

variable [Fact (1 ≤ p)]

open _root_.MeasureTheory _root_.MeasureTheory.Lp in
noncomputable def Lp.multiplicationOperator
    (A : α → E →L[𝕜] F)
    (hA : ∀ v, _root_.MeasureTheory.AEStronglyMeasurable (fun a => A a v) μ)
    (C : ℝ≥0) (hC : ∀ᵐ a ∂μ, ‖A a‖ ≤ (C : ℝ)) :
    Lp E p μ →L[𝕜] _root_.MeasureTheory.Lp F p μ := by
  let M : _root_.MeasureTheory.Lp E p μ → _root_.MeasureTheory.Lp F p μ := fun f =>
    ((Lp.memLp f).clm_apply_of_bound A hA hC).toLp (fun a => A a (f a))
  have hM (f : _root_.MeasureTheory.Lp E p μ) : M f =ᵐ[μ] fun a => A a (f a) :=
    ((Lp.memLp f).clm_apply_of_bound A hA hC).coeFn_toLp
  let L : _root_.MeasureTheory.Lp E p μ →ₗ[𝕜] _root_.MeasureTheory.Lp F p μ := {
    toFun := M
    map_add' := fun f g => by
      apply Lp.ext
      filter_upwards [hM (f + g), hM f, hM g, Lp.coeFn_add f g, Lp.coeFn_add (M f) (M g)]
        with a hfg hf hg hfgin hfgout
      rw [hfg, hfgout, hfgin]
      simp only [Pi.add_apply]
      rw [hf, hg, map_add]
    map_smul' := fun c f => by
      apply Lp.ext
      filter_upwards [hM (c • f), hM f, Lp.coeFn_smul c f, Lp.coeFn_smul c (M f)]
        with a hcf hf hcfin hcfout
      simp only [RingHom.id_apply]
      rw [hcf, hcfout, hcfin]
      simp only [Pi.smul_apply]
      rw [hf, map_smul] }
  apply L.mkContinuous (C : ℝ)
  intro f
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [hM f, hC] with a hfa ha
  change ‖M f a‖ ≤ _
  rw [hfa]
  exact ((A a).le_opNorm (f a)).trans (mul_le_mul_of_nonneg_right ha (norm_nonneg _))

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.MeasureTheory.Lp
  let env ← Lean.getEnv
  if env.contains `MeasureTheory.Lp.multiplicationOperator then
    throwError "Refusing to shadow existing declaration MeasureTheory.Lp.multiplicationOperator"
  Lean.modifyEnv fun env => Lean.addAlias env `MeasureTheory.Lp.multiplicationOperator ``Submission.MeasureTheory.Lp.multiplicationOperator

open _root_.MeasureTheory _root_.MeasureTheory.Lp in
theorem Lp.multiplicationOperator_apply_ae
    (A : α → E →L[𝕜] F)
    (hA : ∀ v, _root_.MeasureTheory.AEStronglyMeasurable (fun a => A a v) μ)
    (C : ℝ≥0) (hC : ∀ᵐ a ∂μ, ‖A a‖ ≤ (C : ℝ)) (f : _root_.MeasureTheory.Lp E p μ) :
    Lp.multiplicationOperator A hA C hC f =ᵐ[μ] fun a => A a (f a) :=
  ((Lp.memLp f).clm_apply_of_bound A hA hC).coeFn_toLp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `MeasureTheory.Lp.multiplicationOperator_apply_ae then
    throwError "Refusing to shadow existing declaration MeasureTheory.Lp.multiplicationOperator_apply_ae"
  Lean.modifyEnv fun env => Lean.addAlias env `MeasureTheory.Lp.multiplicationOperator_apply_ae ``Submission.MeasureTheory.Lp.multiplicationOperator_apply_ae

open _root_.MeasureTheory _root_.MeasureTheory.Lp in
theorem Lp.multiplicationOperator_norm_le
    (A : α → E →L[𝕜] F)
    (hA : ∀ v, _root_.MeasureTheory.AEStronglyMeasurable (fun a => A a v) μ)
    (C : ℝ≥0) (hC : ∀ᵐ a ∂μ, ‖A a‖ ≤ (C : ℝ)) :
    ‖Lp.multiplicationOperator (p := p) A hA C hC‖ ≤ (C : ℝ) := by
  apply ContinuousLinearMap.opNorm_le_bound _ C.coe_nonneg
  intro f
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [Lp.multiplicationOperator_apply_ae A hA C hC f, hC] with a hfa ha
  rw [hfa]
  exact ((A a).le_opNorm (f a)).trans (mul_le_mul_of_nonneg_right ha (norm_nonneg _))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `MeasureTheory.Lp.multiplicationOperator_norm_le then
    throwError "Refusing to shadow existing declaration MeasureTheory.Lp.multiplicationOperator_norm_le"
  Lean.modifyEnv fun env => Lean.addAlias env `MeasureTheory.Lp.multiplicationOperator_norm_le ``Submission.MeasureTheory.Lp.multiplicationOperator_norm_le


open _root_.MeasureTheory _root_.MeasureTheory.Lp in
theorem Lp.multiplicationOperator_congr
    {A B : α → E →L[𝕜] F}
    (hA : ∀ v, _root_.MeasureTheory.AEStronglyMeasurable (fun a => A a v) μ)
    (hB : ∀ v, _root_.MeasureTheory.AEStronglyMeasurable (fun a => B a v) μ)
    {C D : ℝ≥0} (hC : ∀ᵐ a ∂μ, ‖A a‖ ≤ (C : ℝ))
    (hD : ∀ᵐ a ∂μ, ‖B a‖ ≤ (D : ℝ)) (hAB : A =ᵐ[μ] B) :
    Lp.multiplicationOperator (p := p) A hA C hC =
      Lp.multiplicationOperator B hB D hD := by
  ext1 f
  apply Lp.ext
  filter_upwards [Lp.multiplicationOperator_apply_ae A hA C hC f,
    Lp.multiplicationOperator_apply_ae B hB D hD f, hAB] with a ha hb hab
  rw [ha, hb, hab]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `MeasureTheory.Lp.multiplicationOperator_congr then
    throwError "Refusing to shadow existing declaration MeasureTheory.Lp.multiplicationOperator_congr"
  Lean.modifyEnv fun env => Lean.addAlias env `MeasureTheory.Lp.multiplicationOperator_congr ``Submission.MeasureTheory.Lp.multiplicationOperator_congr

open _root_.MeasureTheory _root_.MeasureTheory.Lp in
theorem Lp.multiplicationOperator_const (A : E →L[𝕜] F) :
    Lp.multiplicationOperator (μ := μ) (p := p) (fun _ => A)
      (fun _ => _root_.MeasureTheory.aestronglyMeasurable_const) ‖A‖₊ (Filter.Eventually.of_forall (fun _ => le_rfl)) =
        A.compLpL p μ := by
  ext1 f
  apply Lp.ext
  exact (Lp.multiplicationOperator_apply_ae (fun _ => A)
    (fun _ => _root_.MeasureTheory.aestronglyMeasurable_const) ‖A‖₊
      (Filter.Eventually.of_forall (fun _ => le_rfl)) f).trans (A.coeFn_compLpL f).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `MeasureTheory.Lp.multiplicationOperator_const then
    throwError "Refusing to shadow existing declaration MeasureTheory.Lp.multiplicationOperator_const"
  Lean.modifyEnv fun env => Lean.addAlias env `MeasureTheory.Lp.multiplicationOperator_const ``Submission.MeasureTheory.Lp.multiplicationOperator_const

end MeasureTheory
