import Submission.DifferentialGeometry.Analysis.Integration.Lp.OperatorConvergence
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.Calculus.ContDiff.RCLike

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Filter
open scoped _root_.ENNReal _root_.Topology

namespace MeasureTheory
open _root_.MeasureTheory

variable {P X Y : Type*} [MeasurableSpace P] {μ : Measure P}
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

open _root_.MeasureTheory in
theorem tendsto_eLpNorm_clm_apply_of_strong_ae_tendsto
    (A : ℕ → P → X →L[ℝ] Y) (A₀ : P → X →L[ℝ] Y)
    (hA : ∀ n, _root_.MeasureTheory.AEStronglyMeasurable (A n) μ)
    {C : ℝ} (hC : ∀ n, ∀ᵐ t ∂μ, ‖A n t‖ ≤ C)
    (hconv : ∀ᵐ t ∂μ, _root_.Filter.Tendsto (fun n => A n t) _root_.Filter.atTop (𝓝 (A₀ t)))
    (v : ℕ → P → X) (v₀ : P → X)
    (hv : ∀ n, _root_.MeasureTheory.MemLp (v n) 2 μ) (hv₀ : _root_.MeasureTheory.MemLp v₀ 2 μ)
    (hlim : _root_.Filter.Tendsto (fun n => _root_.MeasureTheory.eLpNorm (fun t => v n t - v₀ t) 2 μ) _root_.Filter.atTop (𝓝 0)) :
    _root_.Filter.Tendsto (fun n => _root_.MeasureTheory.eLpNorm (fun t => A n t (v n t) - A₀ t (v₀ t)) 2 μ)
      atTop (𝓝 0) := by
  have hA₀ : _root_.MeasureTheory.AEStronglyMeasurable A₀ μ :=
    aestronglyMeasurable_of_tendsto_ae _root_.Filter.atTop hA hconv
  let B (n : ℕ) (t : P) := A n t (v n t - v₀ t)
  let D (n : ℕ) (t : P) := (A n t - A₀ t) (v₀ t)
  have hBm (n : ℕ) : _root_.MeasureTheory.AEStronglyMeasurable (B n) μ :=
    (ContinuousLinearMap.apply ℝ Y).aestronglyMeasurable_comp₂
      ((hv n).sub hv₀).aestronglyMeasurable (hA n)
  have hDm (n : ℕ) : _root_.MeasureTheory.AEStronglyMeasurable (D n) μ :=
    (ContinuousLinearMap.apply ℝ Y).aestronglyMeasurable_comp₂
      hv₀.aestronglyMeasurable ((hA n).sub hA₀)
  have hbound (n : ℕ) : _root_.MeasureTheory.eLpNorm (B n) 2 μ ≤
      ENNReal.ofReal C * _root_.MeasureTheory.eLpNorm (fun t => v n t - v₀ t) 2 μ := by
    apply _root_.MeasureTheory.eLpNorm_le_mul_eLpNorm_of_ae_le_mul _ 2
    filter_upwards [hC n] with t ht
    exact (A n t).le_opNorm (v n t - v₀ t) |>.trans
      (mul_le_mul_of_nonneg_right ht (norm_nonneg _))
  have hBl : _root_.Filter.Tendsto (fun n => _root_.MeasureTheory.eLpNorm (B n) 2 μ) _root_.Filter.atTop (𝓝 0) := by
    have ht := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal C) hlim
      (Or.inr ENNReal.ofReal_ne_top)
    simp only [_root_.MulZeroClass.mul_zero] at ht
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht
      (fun _ => zero_le) hbound
  have hDl : _root_.Filter.Tendsto (fun n => _root_.MeasureTheory.eLpNorm (D n) 2 μ) _root_.Filter.atTop (𝓝 0) :=
    tendsto_eLpNorm_clm_apply_sub_of_ae_tendsto (by norm_num) A A₀ hA hC hconv hv₀
  have heq (n : ℕ) : (fun t => A n t (v n t) - A₀ t (v₀ t)) = B n + D n := by
    funext t
    simp only [B, D, Pi.add_apply, map_sub, sub_apply]
    abel
  have ht : _root_.Filter.Tendsto (fun n => _root_.MeasureTheory.eLpNorm (B n) 2 μ + _root_.MeasureTheory.eLpNorm (D n) 2 μ) _root_.Filter.atTop (𝓝 0) := by
    simpa only [add_zero] using hBl.add hDl
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht (fun _ => zero_le)
  intro n
  change _root_.MeasureTheory.eLpNorm (fun t => A n t (v n t) - A₀ t (v₀ t)) 2 μ ≤ _
  rw [heq n]
  exact _root_.MeasureTheory.eLpNorm_add_le (hBm n) (hDm n) (by norm_num)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `MeasureTheory.tendsto_eLpNorm_clm_apply_of_strong_ae_tendsto then
    throwError "Refusing to shadow existing declaration MeasureTheory.tendsto_eLpNorm_clm_apply_of_strong_ae_tendsto"
  Lean.modifyEnv fun env => Lean.addAlias env `MeasureTheory.tendsto_eLpNorm_clm_apply_of_strong_ae_tendsto ``Submission.MeasureTheory.tendsto_eLpNorm_clm_apply_of_strong_ae_tendsto

end MeasureTheory

end

noncomputable section

open _root_.Set _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Filter
open scoped _root_.Topology _root_.ENNReal

namespace MeasureTheory
open _root_.MeasureTheory

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  {μ : Measure E}

open _root_.MeasureTheory in
theorem tendsto_eLpNorm_fderiv_comp_apply_of_ae_tendsto
    (f : ℕ → E → F) (f₀ : E → F) (r : F → G) (w : E)
    (V : E → F)
    (hf : ∀ n, ∀ᵐ x ∂μ, DifferentiableAt ℝ (f n) x)
    (hr : ∀ n, ∀ᵐ x ∂μ, DifferentiableAt ℝ r (f n x))
    (hA : ∀ n, _root_.MeasureTheory.AEStronglyMeasurable (fun x => fderiv ℝ r (f n x)) μ)
    {C : ℝ} (hC : ∀ n, ∀ᵐ x ∂μ, ‖fderiv ℝ r (f n x)‖ ≤ C)
    (hAr : ∀ᵐ x ∂μ, _root_.Filter.Tendsto (fun n => fderiv ℝ r (f n x)) _root_.Filter.atTop
      (𝓝 (fderiv ℝ r (f₀ x))))
    (hdf : ∀ n, _root_.MeasureTheory.MemLp (fun x => fderiv ℝ (f n) x w) 2 μ)
    (hV : _root_.MeasureTheory.MemLp V 2 μ)
    (hlim : _root_.Filter.Tendsto (fun n => _root_.MeasureTheory.eLpNorm (fun x => fderiv ℝ (f n) x w - V x) 2 μ)
      _root_.Filter.atTop (𝓝 0)) :
    _root_.Filter.Tendsto (fun n => _root_.MeasureTheory.eLpNorm (fun x =>
      fderiv ℝ (r ∘ f n) x w - fderiv ℝ r (f₀ x) (V x)) 2 μ) _root_.Filter.atTop (𝓝 0) := by
  have h := tendsto_eLpNorm_clm_apply_of_strong_ae_tendsto
    (fun n x => fderiv ℝ r (f n x)) (fun x => fderiv ℝ r (f₀ x))
    hA hC hAr (fun n x => fderiv ℝ (f n) x w) V hdf hV hlim
  apply h.congr'
  exact Filter.Eventually.of_forall fun n => _root_.MeasureTheory.eLpNorm_congr_ae (by
    filter_upwards [hf n, hr n] with x hfx hrx
    rw [fderiv_comp x hrx hfx]
    rfl)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `MeasureTheory.tendsto_eLpNorm_fderiv_comp_apply_of_ae_tendsto then
    throwError "Refusing to shadow existing declaration MeasureTheory.tendsto_eLpNorm_fderiv_comp_apply_of_ae_tendsto"
  Lean.modifyEnv fun env => Lean.addAlias env `MeasureTheory.tendsto_eLpNorm_fderiv_comp_apply_of_ae_tendsto ``Submission.MeasureTheory.tendsto_eLpNorm_fderiv_comp_apply_of_ae_tendsto

end MeasureTheory

end

noncomputable section

open _root_.Set _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Filter
open scoped _root_.Topology _root_.ENNReal

namespace MeasureTheory
open _root_.MeasureTheory

variable {d : ℕ} {ι : Type*} [Fintype ι]

open _root_.MeasureTheory in
local notation "E" => EuclideanSpace ℝ (Fin d)
open _root_.MeasureTheory in
local notation "F" => EuclideanSpace ℝ ι

open _root_.MeasureTheory in
theorem tendsto_eLpNorm_fderiv_comp_coordinate_of_ae_tendsto
    {Ω : Set E} (u : ℕ → E → F) (f : E → F) (r : F → F)
    (hu : ∀ n, ContDiff ℝ 1 (u n)) (hr : ContDiff ℝ 1 r)
    (j : Fin d) (G : E → F)
    (hA : ∀ n, _root_.MeasureTheory.AEStronglyMeasurable (fun x => fderiv ℝ r (u n x)) (volume.restrict Ω))
    {C : ℝ} (hC : ∀ n, ∀ᵐ x ∂volume.restrict Ω, ‖fderiv ℝ r (u n x)‖ ≤ C)
    (hAr : ∀ᵐ x ∂volume.restrict Ω, _root_.Filter.Tendsto (fun n => fderiv ℝ r (u n x)) _root_.Filter.atTop
      (𝓝 (fderiv ℝ r (f x))))
    (hdu : ∀ n, _root_.MeasureTheory.MemLp (fun x => fderiv ℝ (u n) x (EuclideanSpace.single j 1))
      2 (volume.restrict Ω))
    (hG : _root_.MeasureTheory.MemLp G 2 (volume.restrict Ω))
    (hlim : _root_.Filter.Tendsto (fun n => _root_.MeasureTheory.eLpNorm (fun x =>
      fderiv ℝ (u n) x (EuclideanSpace.single j 1) - G x) 2 (volume.restrict Ω)) _root_.Filter.atTop (𝓝 0))
    (i : ι) :
    _root_.Filter.Tendsto (fun n => _root_.MeasureTheory.eLpNorm (fun x =>
      fderiv ℝ (fun y => r (u n y) i) x (EuclideanSpace.single j 1) -
        (fderiv ℝ r (f x) (G x)) i) 2 (volume.restrict Ω)) _root_.Filter.atTop (𝓝 0) := by
  have ht := tendsto_eLpNorm_clm_apply_of_strong_ae_tendsto
    (fun n x => fderiv ℝ r (u n x)) (fun x => fderiv ℝ r (f x)) hA hC hAr
    (fun n x => fderiv ℝ (u n) x (EuclideanSpace.single j 1)) G hdu hG hlim
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht (fun _ => zero_le)
  intro n
  apply _root_.MeasureTheory.eLpNorm_mono_ae
  filter_upwards [] with x
  have hru :=
    (hr.differentiable (by simp) (u n x)).comp x ((hu n).differentiable (by simp) x)
  have hd : fderiv ℝ (fun y => r (u n y) i) x =
      (EuclideanSpace.proj i).comp (fderiv ℝ (r ∘ u n) x) :=
    ((EuclideanSpace.proj i : F →L[ℝ] ℝ).hasFDerivAt.comp x hru.hasFDerivAt).fderiv
  rw [hd, fderiv_comp x (hr.differentiable (by simp) (u n x))
    ((hu n).differentiable (by simp) x)]
  exact PiLp.norm_apply_le
    ((fderiv ℝ r (u n x)) (fderiv ℝ (u n) x (EuclideanSpace.single j 1)) -
      (fderiv ℝ r (f x)) (G x)) i

run_cmd do
  let env ← Lean.getEnv
  if env.contains `MeasureTheory.tendsto_eLpNorm_fderiv_comp_coordinate_of_ae_tendsto then
    throwError "Refusing to shadow existing declaration MeasureTheory.tendsto_eLpNorm_fderiv_comp_coordinate_of_ae_tendsto"
  Lean.modifyEnv fun env => Lean.addAlias env `MeasureTheory.tendsto_eLpNorm_fderiv_comp_coordinate_of_ae_tendsto ``Submission.MeasureTheory.tendsto_eLpNorm_fderiv_comp_coordinate_of_ae_tendsto

end MeasureTheory

end

noncomputable section

open _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Filter
open scoped _root_.ENNReal _root_.Topology _root_.NNReal

namespace MeasureTheory
open _root_.MeasureTheory

variable {X F : Type*} [MeasurableSpace X] {μ : Measure X}
  [NormedAddCommGroup F]

theorem LipschitzWith.tendsto_eLpNorm_comp_sub_of_fixed_ae
    {r : F → F} {C : ℝ≥0} (hr : LipschitzWith C r)
    (u : ℕ → X → F) (f : X → F)
    (hfixed : (fun x => r (f x)) =ᵐ[μ] f)
    (hlim : _root_.Filter.Tendsto (fun n => _root_.MeasureTheory.eLpNorm (fun x => u n x - f x) 2 μ) _root_.Filter.atTop (𝓝 0)) :
    Tendsto (fun n => _root_.MeasureTheory.eLpNorm (fun x => r (u n x) - f x) 2 μ) _root_.Filter.atTop (𝓝 0) := by
  have hbound (n : ℕ) : _root_.MeasureTheory.eLpNorm (fun x => r (u n x) - f x) 2 μ ≤
      (C : ℝ≥0∞) * _root_.MeasureTheory.eLpNorm (fun x => u n x - f x) 2 μ := by
    rw [← ENNReal.ofReal_coe_nnreal]
    apply _root_.MeasureTheory.eLpNorm_le_mul_eLpNorm_of_ae_le_mul (c := (C : ℝ)) _ 2
    filter_upwards [hfixed] with x hx
    calc
      ‖r (u n x) - f x‖ = ‖r (u n x) - r (f x)‖ := by rw [hx]
      _ ≤ (C : ℝ) * ‖u n x - f x‖ := hr.norm_sub_le (u n x) (f x)
  have ht := ENNReal.Tendsto.const_mul (a := (C : ℝ≥0∞)) hlim (Or.inr ENNReal.coe_ne_top)
  simp only [_root_.MulZeroClass.mul_zero] at ht
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht (fun _ => zero_le) hbound

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.MeasureTheory.LipschitzWith
  let env ← Lean.getEnv
  if env.contains `MeasureTheory.LipschitzWith.tendsto_eLpNorm_comp_sub_of_fixed_ae then
    throwError "Refusing to shadow existing declaration MeasureTheory.LipschitzWith.tendsto_eLpNorm_comp_sub_of_fixed_ae"
  Lean.modifyEnv fun env => Lean.addAlias env `MeasureTheory.LipschitzWith.tendsto_eLpNorm_comp_sub_of_fixed_ae ``Submission.MeasureTheory.LipschitzWith.tendsto_eLpNorm_comp_sub_of_fixed_ae

end MeasureTheory

end
