import Submission.DifferentialGeometry.Analysis.Parabolic.Euclidean.HeatKernel.Derivatives.Cancellation
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.MeasureTheory _root_.Real _root_.Set
open scoped _root_.ENNReal _root_.NNReal _root_.RealInnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace Euclidean

section TimeKernel

def heatScale12 (t : ℝ) : ℝ :=
  t ^ (-(1 : ℝ) / 2)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Euclidean.heatScale12 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Euclidean.heatScale12"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Euclidean.heatScale12 ``Submission.DifferentialGeometry.Analysis.Parabolic.Euclidean.heatScale12

theorem heatScale12_eq {t : ℝ} (ht : 0 < t) :
    heatScale12 t = (heatScale t)⁻¹ := by
  unfold heatScale12 heatScale
  rw [Real.sqrt_eq_rpow]
  convert Real.rpow_neg ht.le (1 / 2 : ℝ) using 1
  ring_nf

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Euclidean.heatScale12_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Euclidean.heatScale12_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Euclidean.heatScale12_eq ``Submission.DifferentialGeometry.Analysis.Parabolic.Euclidean.heatScale12_eq

theorem scale12_intble {t : ℝ} :
    IntervalIntegrable (fun s : ℝ => heatScale12 (t - s)) _root_.MeasureTheory.MeasureSpace.volume 0 t := by
  have hpow : IntervalIntegrable (fun u : ℝ => u ^ (-(1 : ℝ) / 2)) _root_.MeasureTheory.MeasureSpace.volume 0 t :=
    intervalIntegral.intervalIntegrable_rpow' (by norm_num)
  have href := hpow.symm.comp_sub_left t
  simpa only [heatScale12, sub_self, sub_zero] using href

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Euclidean.scale12_intble then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Euclidean.scale12_intble"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Euclidean.scale12_intble ``Submission.DifferentialGeometry.Analysis.Parabolic.Euclidean.scale12_intble

theorem timeScale12_int {t : ℝ} :
    ∫ s : ℝ in 0..t, heatScale12 (t - s) =
      2 * t ^ (1 / 2 : ℝ) := by
  unfold heatScale12
  rw [intervalIntegral.integral_comp_sub_left
    (fun u : ℝ => u ^ (-(1 : ℝ) / 2)) t]
  simp only [sub_self, sub_zero]
  rw [integral_rpow (Or.inl (by norm_num))]
  have hexp : -(1 : ℝ) / 2 + 1 = 1 / 2 := by ring
  rw [hexp, Real.zero_rpow (by norm_num : (1 / 2 : ℝ) ≠ 0)]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Euclidean.timeScale12_int then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Euclidean.timeScale12_int"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Euclidean.timeScale12_int ``Submission.DifferentialGeometry.Analysis.Parabolic.Euclidean.timeScale12_int

theorem scale34_intble {t : ℝ} :
    IntervalIntegrable (fun s : ℝ => heatScale34 (t - s)) _root_.MeasureTheory.MeasureSpace.volume 0 t := by
  have hpow : IntervalIntegrable (fun u : ℝ => u ^ (-(3 : ℝ) / 4)) _root_.MeasureTheory.MeasureSpace.volume 0 t :=
    intervalIntegral.intervalIntegrable_rpow' (by norm_num)
  have href := hpow.symm.comp_sub_left t
  simpa only [heatScale34, sub_self, sub_zero] using href

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Euclidean.scale34_intble then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Euclidean.scale34_intble"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Euclidean.scale34_intble ``Submission.DifferentialGeometry.Analysis.Parabolic.Euclidean.scale34_intble

theorem timeScale34_int {t : ℝ} :
    ∫ s : ℝ in 0..t, heatScale34 (t - s) =
      4 * t ^ (1 / 4 : ℝ) := by
  unfold heatScale34
  rw [intervalIntegral.integral_comp_sub_left
    (fun u : ℝ => u ^ (-(3 : ℝ) / 4)) t]
  simp only [sub_self, sub_zero]
  rw [integral_rpow (Or.inl (by norm_num))]
  have hexp : -(3 : ℝ) / 4 + 1 = 1 / 4 := by ring
  rw [hexp, Real.zero_rpow (by norm_num : (1 / 4 : ℝ) ≠ 0)]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Euclidean.timeScale34_int then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Euclidean.timeScale34_int"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Euclidean.timeScale34_int ``Submission.DifferentialGeometry.Analysis.Parabolic.Euclidean.timeScale34_int

end TimeKernel

section Duhamel

variable {V F : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
  [Nontrivial V]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

def d2DuhamelConst (v w : V) (K : ℝ≥0) : ℝ :=
  ‖v‖ * ‖w‖ * (K : ℝ) * heatC2Half V

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Euclidean.d2DuhamelConst then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Euclidean.d2DuhamelConst"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Euclidean.d2DuhamelConst ``Submission.DifferentialGeometry.Analysis.Parabolic.Euclidean.d2DuhamelConst

def d2DuhamelMajor (v w : V) (K : ℝ≥0) (t s : ℝ) : ℝ :=
  d2DuhamelConst v w K * heatScale34 (t - s)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Euclidean.d2DuhamelMajor then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Euclidean.d2DuhamelMajor"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Euclidean.d2DuhamelMajor ``Submission.DifferentialGeometry.Analysis.Parabolic.Euclidean.d2DuhamelMajor

omit [Nontrivial V] in
theorem d2DuhamelMajor_intble {t : ℝ} (v w : V) (K : ℝ≥0) :
    IntervalIntegrable (d2DuhamelMajor v w K t) _root_.MeasureTheory.MeasureSpace.volume 0 t := by
  exact (scale34_intble).const_mul (d2DuhamelConst v w K)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Euclidean.d2DuhamelMajor_intble then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Euclidean.d2DuhamelMajor_intble"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Euclidean.d2DuhamelMajor_intble ``Submission.DifferentialGeometry.Analysis.Parabolic.Euclidean.d2DuhamelMajor_intble

omit [Nontrivial V] in
theorem d2DuhamelMajor_int {t : ℝ} (v w : V) (K : ℝ≥0) :
    ∫ s : ℝ in 0..t, d2DuhamelMajor v w K t s =
      d2DuhamelConst v w K * (4 * t ^ (1 / 4 : ℝ)) := by
  unfold d2DuhamelMajor
  rw [intervalIntegral.integral_const_mul, timeScale34_int]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Euclidean.d2DuhamelMajor_int then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Euclidean.d2DuhamelMajor_int"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Euclidean.d2DuhamelMajor_int ``Submission.DifferentialGeometry.Analysis.Parabolic.Euclidean.d2DuhamelMajor_int

def heatD2Duhamel (t : ℝ) (v w : V) (f : ℝ → V → F) (x : V) : F :=
  ∫ s : ℝ in 0..t, heatD2Convolution (t - s) v w (f s) x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Euclidean.heatD2Duhamel then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Euclidean.heatD2Duhamel"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Euclidean.heatD2Duhamel ``Submission.DifferentialGeometry.Analysis.Parabolic.Euclidean.heatD2Duhamel

omit [Nontrivial V] [CompleteSpace F] in
theorem heatD2Duhamel_comm (t : ℝ) (v w : V) (f : ℝ → V → F) (x : V) :
    heatD2Duhamel t v w f x = heatD2Duhamel t w v f x := by
  unfold heatD2Duhamel
  apply intervalIntegral.integral_congr
  intro s _
  exact heatD2Convolution_comm (t - s) v w (f s) x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Euclidean.heatD2Duhamel_comm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Euclidean.heatD2Duhamel_comm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Euclidean.heatD2Duhamel_comm ``Submission.DifferentialGeometry.Analysis.Parabolic.Euclidean.heatD2Duhamel_comm

theorem heatD2Duhamel_int {t : ℝ} (ht : 0 < t) {K : ℝ≥0}
    (f : ℝ → V → F)
    (hf : ∀ s ∈ Set.Icc (0 : ℝ) t,
      HolderWith K (1 / 2 : ℝ≥0) (f s))
    (v w x : V)
    (hmeas : _root_.MeasureTheory.AEStronglyMeasurable
      (fun s : ℝ => heatD2Convolution (t - s) v w (f s) x)
      (volume.restrict (Set.uIoc (0 : ℝ) t))) :
    IntervalIntegrable
      (fun s : ℝ => heatD2Convolution (t - s) v w (f s) x) _root_.MeasureTheory.MeasureSpace.volume 0 t := by
  apply (d2DuhamelMajor_intble v w K).mono_fun' hmeas
  have hne : ∀ᵐ s ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure ℝ), s ≠ t := by
    simp [_root_.MeasureTheory.ae_iff, _root_.MeasureTheory.NullSingletonClass.measure_singleton]
  filter_upwards [_root_.MeasureTheory.ae_restrict_mem measurableSet_uIoc,
    ae_restrict_of_ae (s := Set.uIoc (0 : ℝ) t) hne] with s hs hst
  rw [Set.uIoc_of_le ht.le] at hs
  have hstlt : s < t := lt_of_le_of_ne hs.2 hst
  rw [heatD2Convolution_eq_cancel (sub_pos.mpr hstlt) (hf s ⟨hs.1.le, hs.2⟩) v w x]
  refine (heatD2Cancel_norm (sub_pos.mpr hstlt)
    (hf s ⟨hs.1.le, hs.2⟩) v w x).trans_eq ?_
  unfold d2DuhamelMajor d2DuhamelConst
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Euclidean.heatD2Duhamel_int then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Euclidean.heatD2Duhamel_int"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Euclidean.heatD2Duhamel_int ``Submission.DifferentialGeometry.Analysis.Parabolic.Euclidean.heatD2Duhamel_int

theorem heatD2Duhamel_norm {t : ℝ} (ht : 0 < t) {K : ℝ≥0}
    (f : ℝ → V → F)
    (hf : ∀ s ∈ Set.Icc (0 : ℝ) t,
      HolderWith K (1 / 2 : ℝ≥0) (f s))
    (v w x : V)
    (hmeas : _root_.MeasureTheory.AEStronglyMeasurable
      (fun s : ℝ => heatD2Convolution (t - s) v w (f s) x)
      (volume.restrict (Set.uIoc (0 : ℝ) t))) :
    ‖heatD2Duhamel t v w f x‖ ≤
      d2DuhamelConst v w K * (4 * t ^ (1 / 4 : ℝ)) := by
  have hint := heatD2Duhamel_int ht f hf v w x hmeas
  unfold heatD2Duhamel
  calc
    ‖∫ s : ℝ in 0..t, heatD2Convolution (t - s) v w (f s) x‖
        ≤ ∫ s : ℝ in 0..t, ‖heatD2Convolution (t - s) v w (f s) x‖ :=
      intervalIntegral.norm_integral_le_integral_norm ht.le
    _ ≤ ∫ s : ℝ in 0..t, d2DuhamelMajor v w K t s := by
      apply intervalIntegral.integral_mono_on_of_le_Ioo ht.le hint.norm
        (d2DuhamelMajor_intble v w K)
      intro s hs
      rw [heatD2Convolution_eq_cancel (sub_pos.mpr hs.2)
        (hf s ⟨hs.1.le, hs.2.le⟩) v w x]
      refine (heatD2Cancel_norm (sub_pos.mpr hs.2)
        (hf s ⟨hs.1.le, hs.2.le⟩) v w x).trans_eq ?_
      unfold d2DuhamelMajor d2DuhamelConst
      ring
    _ = d2DuhamelConst v w K * (4 * t ^ (1 / 4 : ℝ)) :=
      d2DuhamelMajor_int v w K

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Euclidean.heatD2Duhamel_norm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Euclidean.heatD2Duhamel_norm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Euclidean.heatD2Duhamel_norm ``Submission.DifferentialGeometry.Analysis.Parabolic.Euclidean.heatD2Duhamel_norm

end Duhamel

end Euclidean
end Parabolic
end Analysis
end DifferentialGeometry

end
