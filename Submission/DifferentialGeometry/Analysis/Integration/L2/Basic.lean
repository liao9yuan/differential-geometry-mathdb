import Submission.DifferentialGeometry.Analysis.Integration.Measure.Riemannian.Properties
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Topology.Algebra.Support

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission


noncomputable section

open _root_.Manifold _root_.MeasureTheory _root_.Set _root_.Filter
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.ENNReal

namespace DifferentialGeometry
namespace Integral
namespace L2

open _root_.Submission.DifferentialGeometry.Integral.Measure

theorem abs_integral_mul_le_eLpNorm_two
    {α : Type*} [MeasurableSpace α] {μ : _root_.MeasureTheory.Measure α} {f g : α → ℝ}
    (hf : _root_.MeasureTheory.MemLp f 2 μ) (hg : _root_.MeasureTheory.MemLp g 2 μ) :
    |∫ x, f x * g x ∂μ| ≤ (_root_.MeasureTheory.eLpNorm f 2 μ).toReal * (_root_.MeasureTheory.eLpNorm g 2 μ).toReal := by
  have habs :
      ENNReal.ofReal |∫ x, f x * g x ∂μ| ≤ _root_.MeasureTheory.eLpNorm f 2 μ * _root_.MeasureTheory.eLpNorm g 2 μ := by
    calc
      ENNReal.ofReal |∫ x, f x * g x ∂μ| ≤ ∫⁻ x, ‖f x * g x‖ₑ ∂μ := by
        rw [← Real.norm_eq_abs, ofReal_norm]
        exact _root_.MeasureTheory.enorm_integral_le_lintegral_enorm _
      _ = _root_.MeasureTheory.eLpNorm (fun x => g x * f x) 1 μ := by
        rw [_root_.MeasureTheory.eLpNorm_one_eq_lintegral_enorm]
        refine _root_.MeasureTheory.lintegral_congr fun x => ?_
        simp [enorm_mul, mul_comm]
      _ ≤ _root_.MeasureTheory.eLpNorm g 2 μ * _root_.MeasureTheory.eLpNorm f 2 μ := by
        have hmul : (fun x => g x * f x) = (g : α → ℝ) • (f : α → ℝ) := by
          funext x
          simp [smul_eq_mul]
        rw [hmul]
        let _ : ENNReal.HolderTriple (2 : ℝ≥0∞) (2 : ℝ≥0∞) 1 := by
          constructor
          rw [show (1 : ℝ≥0∞)⁻¹ = 1 by simp, ENNReal.inv_two_add_inv_two]
        exact _root_.MeasureTheory.eLpNorm_smul_le_mul_eLpNorm
          hf.aestronglyMeasurable hg.aestronglyMeasurable
      _ = _root_.MeasureTheory.eLpNorm f 2 μ * _root_.MeasureTheory.eLpNorm g 2 μ := mul_comm _ _
  have hfinite : _root_.MeasureTheory.eLpNorm f 2 μ * _root_.MeasureTheory.eLpNorm g 2 μ ≠ (⊤ : ℝ≥0∞) :=
    ENNReal.mul_ne_top hf.eLpNorm_lt_top.ne hg.eLpNorm_lt_top.ne
  have hreal := ENNReal.toReal_mono hfinite habs
  rw [ENNReal.toReal_ofReal (abs_nonneg _), ENNReal.toReal_mul] at hreal
  exact hreal

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.L2.abs_integral_mul_le_eLpNorm_two then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.L2.abs_integral_mul_le_eLpNorm_two"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.L2.abs_integral_mul_le_eLpNorm_two ``Submission.DifferentialGeometry.Integral.L2.abs_integral_mul_le_eLpNorm_two

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private local instance _root_.Submission.DifferentialGeometry.Integral.L2.instMeasurableSpace_differentialGeometry : MeasurableSpace E := borel E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Integral.L2.instMeasurableSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Integral.L2.instMeasurableSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Integral.L2.instBorelSpace_differentialGeometry : BorelSpace E := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Integral.L2.instBorelSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Integral.L2.instBorelSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Integral.L2.instMeasurableSpace_differentialGeometry_1 : MeasurableSpace M := borel M

run_cmd do
  let target := ``Submission.DifferentialGeometry.Integral.L2.instMeasurableSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Integral.L2.instMeasurableSpace_differentialGeometry_1 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Integral.L2.instBorelSpace_differentialGeometry_1 : BorelSpace M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Integral.L2.instBorelSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Integral.L2.instBorelSpace_differentialGeometry_1 target :: scope.openDecls } }

theorem aestronglyMeasurable_of_continuous
    {F : Type*} [NormedAddCommGroup F] [SecondCountableTopology F]
    {f : M → F} (hf : Continuous f) (μ : MeasureTheory.Measure M) :
    MeasureTheory.AEStronglyMeasurable f μ :=
  hf.aestronglyMeasurable

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.L2.aestronglyMeasurable_of_continuous then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.L2.aestronglyMeasurable_of_continuous"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.L2.aestronglyMeasurable_of_continuous ``Submission.DifferentialGeometry.Integral.L2.aestronglyMeasurable_of_continuous

omit [Module.Finite ℝ E] [IsManifold I ∞ M] in
theorem aestronglyMeasurable_of_contMDiff
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [SecondCountableTopology F]
    {f : M → F} (hf : ContMDiff I 𝓘(ℝ, F) ∞ f) (μ : MeasureTheory.Measure M) :
    MeasureTheory.AEStronglyMeasurable f μ :=
  aestronglyMeasurable_of_continuous (M := M) hf.continuous μ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.L2.aestronglyMeasurable_of_contMDiff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.L2.aestronglyMeasurable_of_contMDiff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.L2.aestronglyMeasurable_of_contMDiff ``Submission.DifferentialGeometry.Integral.L2.aestronglyMeasurable_of_contMDiff

omit [Module.Finite ℝ E] [IsManifold I ∞ M] in
theorem aestronglyMeasurable_of_contMDiff_of_nat
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [SecondCountableTopology F]
    {n : WithTop ℕ∞} {f : M → F} (hf : ContMDiff I 𝓘(ℝ, F) n f)
    (μ : MeasureTheory.Measure M) :
    MeasureTheory.AEStronglyMeasurable f μ :=
  aestronglyMeasurable_of_continuous (M := M) hf.continuous μ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.L2.aestronglyMeasurable_of_contMDiff_of_nat then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.L2.aestronglyMeasurable_of_contMDiff_of_nat"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.L2.aestronglyMeasurable_of_contMDiff_of_nat ``Submission.DifferentialGeometry.Integral.L2.aestronglyMeasurable_of_contMDiff_of_nat

theorem integrable_of_continuous_of_hasCompactSupport
    {F : Type*} [NormedAddCommGroup F]
    {μ : MeasureTheory.Measure M} [_root_.MeasureTheory.IsFiniteMeasureOnCompacts μ]
    {f : M → F} (hfc : Continuous f) (hfsup : HasCompactSupport f) :
    MeasureTheory.Integrable f μ :=
  hfc.integrable_of_hasCompactSupport hfsup

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.L2.integrable_of_continuous_of_hasCompactSupport then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.L2.integrable_of_continuous_of_hasCompactSupport"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.L2.integrable_of_continuous_of_hasCompactSupport ``Submission.DifferentialGeometry.Integral.L2.integrable_of_continuous_of_hasCompactSupport

omit [Module.Finite ℝ E] [IsManifold I ∞ M] in
theorem integrable_of_contMDiff_of_hasCompactSupport
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {μ : MeasureTheory.Measure M} [_root_.MeasureTheory.IsFiniteMeasureOnCompacts μ]
    {f : M → F} (hfc : ContMDiff I 𝓘(ℝ, F) ∞ f) (hfsup : HasCompactSupport f) :
    MeasureTheory.Integrable f μ :=
  integrable_of_continuous_of_hasCompactSupport hfc.continuous hfsup

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.L2.integrable_of_contMDiff_of_hasCompactSupport then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.L2.integrable_of_contMDiff_of_hasCompactSupport"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.L2.integrable_of_contMDiff_of_hasCompactSupport ``Submission.DifferentialGeometry.Integral.L2.integrable_of_contMDiff_of_hasCompactSupport

theorem integrable_of_continuous_compactSpace
    [T2Space M] [CompactSpace M]
    {F : Type*} [NormedAddCommGroup F]
    (g : SmoothRiemannianMetric I M)
    {f : M → F} (hf : Continuous f) :
    MeasureTheory.Integrable f (riemannianVolumeMeasure (I := I) (M := M) g) :=
  haveI : _root_.MeasureTheory.IsFiniteMeasureOnCompacts (riemannianVolumeMeasure (I := I) (M := M) g) :=
    riemannianVolumeMeasure_isFiniteMeasureOnCompacts (I := I) (M := M) g
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.L2.integrable_of_continuous_compactSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.L2.integrable_of_continuous_compactSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.L2.integrable_of_continuous_compactSpace ``Submission.DifferentialGeometry.Integral.L2.integrable_of_continuous_compactSpace

omit [Module.Finite ℝ E] [IsManifold I ∞ M] in
theorem integrable_of_contMDiff_compactSpace
    [CompactSpace M]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {μ : MeasureTheory.Measure M} [_root_.MeasureTheory.IsFiniteMeasureOnCompacts μ]
    {f : M → F} (hf : ContMDiff I 𝓘(ℝ, F) ∞ f) :
    MeasureTheory.Integrable f μ :=
  integrable_of_contMDiff_of_hasCompactSupport hf (HasCompactSupport.of_compactSpace f)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.L2.integrable_of_contMDiff_compactSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.L2.integrable_of_contMDiff_compactSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.L2.integrable_of_contMDiff_compactSpace ``Submission.DifferentialGeometry.Integral.L2.integrable_of_contMDiff_compactSpace

omit [Module.Finite ℝ E] [IsManifold I ∞ M] in
theorem lpNorm_two_sq_eq_integral_sq
    {μ : MeasureTheory.Measure M} {f : M → ℝ}
    (hf : MeasureTheory.AEStronglyMeasurable f μ) :
    MeasureTheory.lpNorm f 2 μ ^ 2 = ∫ x, f x ^ 2 ∂μ := by
  rw [MeasureTheory.lpNorm_eq_integral_norm_rpow_toReal
    (by norm_num) (by norm_num) hf]
  norm_num only [ENNReal.toReal_ofNat]
  have hnonneg : 0 ≤ ∫ x, ‖f x‖ ^ (2 : ℝ) ∂μ :=
    MeasureTheory.integral_nonneg (fun x => by positivity)
  rw [← Real.sqrt_eq_rpow]
  rw [sq, Real.mul_self_sqrt hnonneg]
  congr 1
  funext x
  rw [Real.norm_eq_abs]
  rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  exact sq_abs (f x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.L2.lpNorm_two_sq_eq_integral_sq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.L2.lpNorm_two_sq_eq_integral_sq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.L2.lpNorm_two_sq_eq_integral_sq ``Submission.DifferentialGeometry.Integral.L2.lpNorm_two_sq_eq_integral_sq

theorem integral_add_of_riemannianVolume
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {μ : MeasureTheory.Measure M}
    {f f' : M → F}
    (hf : MeasureTheory.Integrable f μ)
    (hf' : MeasureTheory.Integrable f' μ) :
    ∫ x, (f x + f' x) ∂μ = (∫ x, f x ∂μ) + (∫ x, f' x ∂μ) :=
  MeasureTheory.integral_add hf hf'

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.L2.integral_add_of_riemannianVolume then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.L2.integral_add_of_riemannianVolume"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.L2.integral_add_of_riemannianVolume ``Submission.DifferentialGeometry.Integral.L2.integral_add_of_riemannianVolume

theorem integral_smul_of_riemannianVolume
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {μ : MeasureTheory.Measure M}
    (c : ℝ) (f : M → F) :
    ∫ x, c • f x ∂μ = c • ∫ x, f x ∂μ :=
  MeasureTheory.integral_smul c f

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.L2.integral_smul_of_riemannianVolume then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.L2.integral_smul_of_riemannianVolume"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.L2.integral_smul_of_riemannianVolume ``Submission.DifferentialGeometry.Integral.L2.integral_smul_of_riemannianVolume

theorem integral_sub_of_riemannianVolume
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {μ : MeasureTheory.Measure M}
    {f f' : M → F}
    (hf : MeasureTheory.Integrable f μ)
    (hf' : MeasureTheory.Integrable f' μ) :
    ∫ x, (f x - f' x) ∂μ = (∫ x, f x ∂μ) - (∫ x, f' x ∂μ) :=
  MeasureTheory.integral_sub hf hf'

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.L2.integral_sub_of_riemannianVolume then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.L2.integral_sub_of_riemannianVolume"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.L2.integral_sub_of_riemannianVolume ``Submission.DifferentialGeometry.Integral.L2.integral_sub_of_riemannianVolume

theorem integral_neg_of_riemannianVolume
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {μ : MeasureTheory.Measure M} (f : M → F) :
    ∫ x, -f x ∂μ = -∫ x, f x ∂μ :=
  MeasureTheory.integral_neg f

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.L2.integral_neg_of_riemannianVolume then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.L2.integral_neg_of_riemannianVolume"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.L2.integral_neg_of_riemannianVolume ``Submission.DifferentialGeometry.Integral.L2.integral_neg_of_riemannianVolume

theorem integral_zero_of_riemannianVolume
    (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F]
    {μ : MeasureTheory.Measure M} :
    ∫ _ : M, (0 : F) ∂μ = 0 :=
  MeasureTheory.integral_zero M F

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.L2.integral_zero_of_riemannianVolume then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.L2.integral_zero_of_riemannianVolume"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.L2.integral_zero_of_riemannianVolume ``Submission.DifferentialGeometry.Integral.L2.integral_zero_of_riemannianVolume

theorem integral_const_of_riemannianVolume
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {μ : MeasureTheory.Measure M} (c : F) :
    ∫ _ : M, c ∂μ = μ.real _root_.Set.univ • c :=
  MeasureTheory.integral_const c

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.L2.integral_const_of_riemannianVolume then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.L2.integral_const_of_riemannianVolume"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.L2.integral_const_of_riemannianVolume ``Submission.DifferentialGeometry.Integral.L2.integral_const_of_riemannianVolume

theorem integral_congr_ae_of_riemannianVolume
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {μ : MeasureTheory.Measure M}
    {f f' : M → F}
    (h : f =ᵐ[μ] f') :
    ∫ x, f x ∂μ = ∫ x, f' x ∂μ :=
  MeasureTheory.integral_congr_ae h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.L2.integral_congr_ae_of_riemannianVolume then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.L2.integral_congr_ae_of_riemannianVolume"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.L2.integral_congr_ae_of_riemannianVolume ``Submission.DifferentialGeometry.Integral.L2.integral_congr_ae_of_riemannianVolume

theorem lintegral_add_left_of_riemannianVolume
    {μ : MeasureTheory.Measure M}
    {f : M → ℝ≥0∞} (hf : Measurable f) (f' : M → ℝ≥0∞) :
    ∫⁻ x, f x + f' x ∂μ = (∫⁻ x, f x ∂μ) + (∫⁻ x, f' x ∂μ) :=
  MeasureTheory.lintegral_add_left hf f'

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.L2.lintegral_add_left_of_riemannianVolume then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.L2.lintegral_add_left_of_riemannianVolume"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.L2.lintegral_add_left_of_riemannianVolume ``Submission.DifferentialGeometry.Integral.L2.lintegral_add_left_of_riemannianVolume

theorem lintegral_const_mul_of_riemannianVolume
    {μ : MeasureTheory.Measure M}
    (r : ℝ≥0∞) {f : M → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ x, r * f x ∂μ = r * ∫⁻ x, f x ∂μ :=
  MeasureTheory.lintegral_const_mul r hf

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.L2.lintegral_const_mul_of_riemannianVolume then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.L2.lintegral_const_mul_of_riemannianVolume"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.L2.lintegral_const_mul_of_riemannianVolume ``Submission.DifferentialGeometry.Integral.L2.lintegral_const_mul_of_riemannianVolume

end L2
end Integral
end DifferentialGeometry
