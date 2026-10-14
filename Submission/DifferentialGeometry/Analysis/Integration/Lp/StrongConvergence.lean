import Submission.DifferentialGeometry.Analysis.Integration.LpNorm
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Filter _root_.MeasureTheory
open scoped _root_.ENNReal _root_.Topology

namespace MeasureTheory
open _root_.MeasureTheory

variable {P X : Type*} [MeasurableSpace P] [NormedAddCommGroup X]
  {μ ν : Measure P}

open _root_.MeasureTheory in
private theorem tendsto_eLpNorm_sub_of_tendsto_eLpNorm_sub_of_ae_eq
    (u v : ℕ → P → X) (f g : P → X)
    (hu : ∀ n, _root_.MeasureTheory.AEStronglyMeasurable (fun x => u n x - f x) μ)
    (hv : ∀ n, _root_.MeasureTheory.AEStronglyMeasurable (fun x => v n x - g x) μ)
    (huf : _root_.Filter.Tendsto (fun n => _root_.MeasureTheory.eLpNorm (fun x => u n x - f x) 2 μ) _root_.Filter.atTop (𝓝 0))
    (hvg : _root_.Filter.Tendsto (fun n => _root_.MeasureTheory.eLpNorm (fun x => v n x - g x) 2 μ) _root_.Filter.atTop (𝓝 0))
    (hfg : f =ᵐ[μ] g) :
    Tendsto (fun n => _root_.MeasureTheory.eLpNorm (fun x => u n x - v n x) 2 μ) _root_.Filter.atTop (𝓝 0) := by
  have hbound (n : ℕ) : _root_.MeasureTheory.eLpNorm (fun x => u n x - v n x) 2 μ ≤
      eLpNorm (fun x => u n x - f x) 2 μ + _root_.MeasureTheory.eLpNorm (fun x => v n x - g x) 2 μ := by
    have heq : (fun x => u n x - v n x) =ᵐ[μ]
        (fun x => (u n x - f x) - (v n x - g x)) := by
      filter_upwards [hfg] with x hx
      rw [hx]
      abel
    rw [_root_.MeasureTheory.eLpNorm_congr_ae heq]
    exact _root_.MeasureTheory.eLpNorm_sub_le (f := fun x => u n x - f x) (g := fun x => v n x - g x)
      (p := 2) (μ := μ) (hu n) (hv n) (by norm_num)
  have hsum : _root_.Filter.Tendsto
      (fun n => _root_.MeasureTheory.eLpNorm (fun x => u n x - f x) 2 μ +
        eLpNorm (fun x => v n x - g x) 2 μ) _root_.Filter.atTop (𝓝 0) := by
    simpa only [add_zero] using huf.add hvg
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
    (fun _ => zero_le) hbound

run_cmd do
  let target := ``Submission.MeasureTheory.tendsto_eLpNorm_sub_of_tendsto_eLpNorm_sub_of_ae_eq
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `MeasureTheory.tendsto_eLpNorm_sub_of_tendsto_eLpNorm_sub_of_ae_eq target :: scope.openDecls } }

open _root_.MeasureTheory in
private theorem integral_norm_sub_sq_tendsto_zero
    (u v : ℕ → P → X) (f g : P → X)
    (hu : ∀ n, _root_.MeasureTheory.MemLp (u n) 2 μ) (hv : ∀ n, _root_.MeasureTheory.MemLp (v n) 2 μ)
    (hf : _root_.MeasureTheory.AEStronglyMeasurable f μ) (hg : _root_.MeasureTheory.AEStronglyMeasurable g μ)
    (huf : _root_.Filter.Tendsto (fun n => _root_.MeasureTheory.eLpNorm (fun x => u n x - f x) 2 μ) _root_.Filter.atTop (𝓝 0))
    (hvg : _root_.Filter.Tendsto (fun n => _root_.MeasureTheory.eLpNorm (fun x => v n x - g x) 2 μ) _root_.Filter.atTop (𝓝 0))
    (hfg : f =ᵐ[μ] g) :
    Tendsto (fun n => ∫ x, ‖u n x - v n x‖ ^ 2 ∂μ) _root_.Filter.atTop (𝓝 0) := by
  have h := tendsto_eLpNorm_sub_of_tendsto_eLpNorm_sub_of_ae_eq u v f g
    (fun n => (hu n).aestronglyMeasurable.sub hf)
    (fun n => (hv n).aestronglyMeasurable.sub hg) huf hvg hfg
  have hr := (ENNReal.tendsto_toReal (by simp : (0 : ℝ≥0∞) ≠ ∞)).comp h
  have heq (n : ℕ) : (∫ x, ‖u n x - v n x‖ ^ 2 ∂μ) =
      (_root_.MeasureTheory.eLpNorm (fun x => u n x - v n x) 2 μ).toReal ^ 2 := by
    have hsub : _root_.MeasureTheory.MemLp (fun x => u n x - v n x) 2 μ :=
      (hu n).sub (hv n)
    have hm : _root_.MeasureTheory.MemLp (fun x => ‖u n x - v n x‖) 2 μ := hsub.norm
    rw [DifferentialGeometry.Analysis.Integration.integral_sq_eq_l2 hm]
    rw [_root_.MeasureTheory.eLpNorm_norm]
  simpa only [heq, Function.comp_def, ENNReal.toReal_zero, zero_pow (by decide : 2 ≠ 0)]
    using hr.pow 2

run_cmd do
  let target := ``Submission.MeasureTheory.integral_norm_sub_sq_tendsto_zero
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `MeasureTheory.integral_norm_sub_sq_tendsto_zero target :: scope.openDecls } }

open _root_.MeasureTheory in
theorem tendsto_integral_norm_sub_sq_of_tendsto_eLpNorm_sub_of_ae_eq_of_measure_le
    (hν : ν ≤ μ) (u v : ℕ → P → X) (f g : P → X)
    (hu : ∀ n, _root_.MeasureTheory.MemLp (u n) 2 μ) (hv : ∀ n, _root_.MeasureTheory.MemLp (v n) 2 μ)
    (hf : _root_.MeasureTheory.AEStronglyMeasurable f μ) (hg : _root_.MeasureTheory.AEStronglyMeasurable g μ)
    (huf : _root_.Filter.Tendsto (fun n => _root_.MeasureTheory.eLpNorm (fun x => u n x - f x) 2 μ) _root_.Filter.atTop (𝓝 0))
    (hvg : _root_.Filter.Tendsto (fun n => _root_.MeasureTheory.eLpNorm (fun x => v n x - g x) 2 μ) _root_.Filter.atTop (𝓝 0))
    (hfg : f =ᵐ[ν] g) :
    Tendsto (fun n => ∫ x, ‖u n x - v n x‖ ^ 2 ∂ν) _root_.Filter.atTop (𝓝 0) := by
  apply integral_norm_sub_sq_tendsto_zero u v f g
    (fun n => (hu n).mono_measure hν) (fun n => (hv n).mono_measure hν)
    (hf.mono_measure hν) (hg.mono_measure hν) _ _ hfg
  · exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds huf
      (fun _ => zero_le) (fun n => _root_.MeasureTheory.eLpNorm_mono_measure _ hν)
  · exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hvg
      (fun _ => zero_le) (fun n => _root_.MeasureTheory.eLpNorm_mono_measure _ hν)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `MeasureTheory.tendsto_integral_norm_sub_sq_of_tendsto_eLpNorm_sub_of_ae_eq_of_measure_le then
    throwError "Refusing to shadow existing declaration MeasureTheory.tendsto_integral_norm_sub_sq_of_tendsto_eLpNorm_sub_of_ae_eq_of_measure_le"
  Lean.modifyEnv fun env => Lean.addAlias env `MeasureTheory.tendsto_integral_norm_sub_sq_of_tendsto_eLpNorm_sub_of_ae_eq_of_measure_le ``Submission.MeasureTheory.tendsto_integral_norm_sub_sq_of_tendsto_eLpNorm_sub_of_ae_eq_of_measure_le

open _root_.MeasureTheory in
theorem tendsto_integral_norm_sub_sq_of_tendsto_eLpNorm_sub_of_ae_eq
    (u v : ℕ → P → X) (f g : P → X)
    (hu : ∀ n, _root_.MeasureTheory.MemLp (u n) 2 μ) (hv : ∀ n, _root_.MeasureTheory.MemLp (v n) 2 μ)
    (hf : _root_.MeasureTheory.AEStronglyMeasurable f μ) (hg : _root_.MeasureTheory.AEStronglyMeasurable g μ)
    (huf : _root_.Filter.Tendsto (fun n => _root_.MeasureTheory.eLpNorm (fun x => u n x - f x) 2 μ) _root_.Filter.atTop (𝓝 0))
    (hvg : _root_.Filter.Tendsto (fun n => _root_.MeasureTheory.eLpNorm (fun x => v n x - g x) 2 μ) _root_.Filter.atTop (𝓝 0))
    (hfg : f =ᵐ[μ] g) :
    Tendsto (fun n => ∫ x, ‖u n x - v n x‖ ^ 2 ∂μ) _root_.Filter.atTop (𝓝 0) :=
  tendsto_integral_norm_sub_sq_of_tendsto_eLpNorm_sub_of_ae_eq_of_measure_le
    le_rfl u v f g hu hv hf hg huf hvg hfg

run_cmd do
  let env ← Lean.getEnv
  if env.contains `MeasureTheory.tendsto_integral_norm_sub_sq_of_tendsto_eLpNorm_sub_of_ae_eq then
    throwError "Refusing to shadow existing declaration MeasureTheory.tendsto_integral_norm_sub_sq_of_tendsto_eLpNorm_sub_of_ae_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `MeasureTheory.tendsto_integral_norm_sub_sq_of_tendsto_eLpNorm_sub_of_ae_eq ``Submission.MeasureTheory.tendsto_integral_norm_sub_sq_of_tendsto_eLpNorm_sub_of_ae_eq

open _root_.MeasureTheory in
theorem tendsto_setIntegral_norm_sub_sq_of_tendsto_eLpNorm_sub_of_ae_eq
    (S : Set P) (u v : ℕ → P → X) (f g : P → X)
    (hu : ∀ n, _root_.MeasureTheory.MemLp (u n) 2 μ) (hv : ∀ n, _root_.MeasureTheory.MemLp (v n) 2 μ)
    (hf : _root_.MeasureTheory.AEStronglyMeasurable f μ) (hg : _root_.MeasureTheory.AEStronglyMeasurable g μ)
    (huf : _root_.Filter.Tendsto (fun n => _root_.MeasureTheory.eLpNorm (fun x => u n x - f x) 2 μ) _root_.Filter.atTop (𝓝 0))
    (hvg : _root_.Filter.Tendsto (fun n => _root_.MeasureTheory.eLpNorm (fun x => v n x - g x) 2 μ) _root_.Filter.atTop (𝓝 0))
    (hfg : f =ᵐ[μ.restrict S] g) :
    Tendsto (fun n => ∫ x in S, ‖u n x - v n x‖ ^ 2 ∂μ) _root_.Filter.atTop (𝓝 0) :=
  tendsto_integral_norm_sub_sq_of_tendsto_eLpNorm_sub_of_ae_eq_of_measure_le
    Measure.restrict_le_self u v f g hu hv hf hg huf hvg hfg

run_cmd do
  let env ← Lean.getEnv
  if env.contains `MeasureTheory.tendsto_setIntegral_norm_sub_sq_of_tendsto_eLpNorm_sub_of_ae_eq then
    throwError "Refusing to shadow existing declaration MeasureTheory.tendsto_setIntegral_norm_sub_sq_of_tendsto_eLpNorm_sub_of_ae_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `MeasureTheory.tendsto_setIntegral_norm_sub_sq_of_tendsto_eLpNorm_sub_of_ae_eq ``Submission.MeasureTheory.tendsto_setIntegral_norm_sub_sq_of_tendsto_eLpNorm_sub_of_ae_eq

end MeasureTheory

end
