import Submission.DifferentialGeometry.Analysis.Parabolic.Euclidean.HeatKernel.Duhamel.Basic
import Submission.DifferentialGeometry.Analysis.Parabolic.Euclidean.HeatKernel.Convolution.Supremum

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.MeasureTheory _root_.Real _root_.Set
open scoped _root_.NNReal _root_.RealInnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace Euclidean

section ValuePotential

variable {V F : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
  [Nontrivial V]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

def d0DuhamelMajor (K : ℝ≥0) : ℝ := K

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Euclidean.d0DuhamelMajor then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Euclidean.d0DuhamelMajor"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Euclidean.d0DuhamelMajor ``Submission.DifferentialGeometry.Analysis.Parabolic.Euclidean.d0DuhamelMajor

theorem d0DuhamelMajor_intble (t : ℝ) (K : ℝ≥0) :
    IntervalIntegrable (fun _ : ℝ => d0DuhamelMajor K) _root_.MeasureTheory.MeasureSpace.volume 0 t := by
  simpa only [d0DuhamelMajor] using
    (intervalIntegrable_const :
      IntervalIntegrable (fun _ : ℝ => (K : ℝ)) _root_.MeasureTheory.MeasureSpace.volume 0 t)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Euclidean.d0DuhamelMajor_intble then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Euclidean.d0DuhamelMajor_intble"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Euclidean.d0DuhamelMajor_intble ``Submission.DifferentialGeometry.Analysis.Parabolic.Euclidean.d0DuhamelMajor_intble

theorem d0DuhamelMajor_int (t : ℝ) (K : ℝ≥0) :
    ∫ _ : ℝ in 0..t, d0DuhamelMajor K = t * (K : ℝ) := by
  simp only [d0DuhamelMajor, intervalIntegral.integral_const, sub_zero,
    smul_eq_mul]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Euclidean.d0DuhamelMajor_int then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Euclidean.d0DuhamelMajor_int"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Euclidean.d0DuhamelMajor_int ``Submission.DifferentialGeometry.Analysis.Parabolic.Euclidean.d0DuhamelMajor_int

def heatDuhamel (t : ℝ) (f : ℝ → BoundedContinuousFunction V F) (x : V) : F :=
  ∫ s : ℝ in 0..t, heatSup (t - s) (f s) x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Euclidean.heatDuhamel then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Euclidean.heatDuhamel"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Euclidean.heatDuhamel ``Submission.DifferentialGeometry.Analysis.Parabolic.Euclidean.heatDuhamel

omit [Nontrivial V] [CompleteSpace F] in
theorem heatDuhamel_const_eq_integral_heatSup
    (t : Real) (f : BoundedContinuousFunction V F) (x : V) :
    heatDuhamel t (fun _ ↦ f) x =
      ∫ s : Real in 0..t, heatSup s f x := by
  unfold heatDuhamel
  rw [intervalIntegral.integral_comp_sub_left
    (fun s : Real ↦ heatSup s f x) t]
  simp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Euclidean.heatDuhamel_const_eq_integral_heatSup then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Euclidean.heatDuhamel_const_eq_integral_heatSup"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Euclidean.heatDuhamel_const_eq_integral_heatSup ``Submission.DifferentialGeometry.Analysis.Parabolic.Euclidean.heatDuhamel_const_eq_integral_heatSup

omit [CompleteSpace F] in
theorem heatDuhamel_int {t : ℝ} (ht : 0 < t) {K : ℝ≥0}
    (f : ℝ → BoundedContinuousFunction V F)
    (hf : ∀ s ∈ Set.Icc (0 : ℝ) t, ‖f s‖ ≤ K) (x : V)
    (hmeas : _root_.MeasureTheory.AEStronglyMeasurable
      (fun s : ℝ => heatSup (t - s) (f s) x)
      (volume.restrict (Set.uIoc (0 : ℝ) t))) :
    IntervalIntegrable
      (fun s : ℝ => heatSup (t - s) (f s) x) _root_.MeasureTheory.MeasureSpace.volume 0 t := by
  apply (d0DuhamelMajor_intble t K).mono_fun' hmeas
  have hne : ∀ᵐ s ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure ℝ), s ≠ t := by
    simp [_root_.MeasureTheory.ae_iff, _root_.MeasureTheory.NullSingletonClass.measure_singleton]
  filter_upwards [_root_.MeasureTheory.ae_restrict_mem measurableSet_uIoc,
    ae_restrict_of_ae (s := Set.uIoc (0 : ℝ) t) hne] with s hs hst
  rw [Set.uIoc_of_le ht.le] at hs
  have hstlt : s < t := lt_of_le_of_ne hs.2 hst
  calc
    ‖heatSup (t - s) (f s) x‖ ≤ ‖f s‖ :=
      heatSup_contract (sub_pos.mpr hstlt) (f s) x
    _ ≤ K := hf s ⟨hs.1.le, hs.2⟩
    _ = d0DuhamelMajor K := by rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Euclidean.heatDuhamel_int then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Euclidean.heatDuhamel_int"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Euclidean.heatDuhamel_int ``Submission.DifferentialGeometry.Analysis.Parabolic.Euclidean.heatDuhamel_int

omit [CompleteSpace F] in
theorem heatDuhamel_norm {t : ℝ} (ht : 0 < t) {K : ℝ≥0}
    (f : ℝ → BoundedContinuousFunction V F)
    (hf : ∀ s ∈ Set.Icc (0 : ℝ) t, ‖f s‖ ≤ K) (x : V)
    (hmeas : _root_.MeasureTheory.AEStronglyMeasurable
      (fun s : ℝ => heatSup (t - s) (f s) x)
      (volume.restrict (Set.uIoc (0 : ℝ) t))) :
    ‖heatDuhamel t f x‖ ≤ t * (K : ℝ) := by
  have hint := heatDuhamel_int ht f hf x hmeas
  unfold heatDuhamel
  calc
    ‖∫ s : ℝ in 0..t, heatSup (t - s) (f s) x‖ ≤
        ∫ s : ℝ in 0..t, ‖heatSup (t - s) (f s) x‖ :=
      intervalIntegral.norm_integral_le_integral_norm ht.le
    _ ≤ ∫ _ : ℝ in 0..t, d0DuhamelMajor K := by
      apply intervalIntegral.integral_mono_on_of_le_Ioo ht.le hint.norm
        (d0DuhamelMajor_intble t K)
      intro s hs
      calc
        ‖heatSup (t - s) (f s) x‖ ≤ ‖f s‖ :=
          heatSup_contract (sub_pos.mpr hs.2) (f s) x
        _ ≤ K := hf s ⟨hs.1.le, hs.2.le⟩
        _ = d0DuhamelMajor K := by rfl
    _ = t * (K : ℝ) := d0DuhamelMajor_int t K

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Euclidean.heatDuhamel_norm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Euclidean.heatDuhamel_norm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Euclidean.heatDuhamel_norm ``Submission.DifferentialGeometry.Analysis.Parabolic.Euclidean.heatDuhamel_norm

omit [CompleteSpace F] in
theorem heatDuhamel_sqrt {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) {K : ℝ≥0}
    (f : ℝ → BoundedContinuousFunction V F)
    (hf : ∀ s ∈ Set.Icc (0 : ℝ) t, ‖f s‖ ≤ K) (x : V)
    (hmeas : _root_.MeasureTheory.AEStronglyMeasurable
      (fun s : ℝ => heatSup (t - s) (f s) x)
      (volume.restrict (Set.uIoc (0 : ℝ) t))) :
    ‖heatDuhamel t f x‖ ≤ Real.sqrt t * (K : ℝ) := by
  have htsqrt : t ≤ Real.sqrt t := by
    have hsqrt_le : Real.sqrt t ≤ 1 := Real.sqrt_le_one.mpr ht1
    nlinarith [Real.sq_sqrt ht.le, Real.sqrt_nonneg t]
  exact (heatDuhamel_norm ht f hf x hmeas).trans
    (mul_le_mul_of_nonneg_right htsqrt (NNReal.coe_nonneg K))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Euclidean.heatDuhamel_sqrt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Euclidean.heatDuhamel_sqrt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Euclidean.heatDuhamel_sqrt ``Submission.DifferentialGeometry.Analysis.Parabolic.Euclidean.heatDuhamel_sqrt
end ValuePotential

section GradientPotential

variable {V F : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
  [Nontrivial V]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

def d1DuhamelConst (v : V) (K : ℝ≥0) : ℝ :=
  ‖v‖ * (K : ℝ) * heatC1 V

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Euclidean.d1DuhamelConst then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Euclidean.d1DuhamelConst"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Euclidean.d1DuhamelConst ``Submission.DifferentialGeometry.Analysis.Parabolic.Euclidean.d1DuhamelConst

def d1DuhamelMajor (v : V) (K : ℝ≥0) (t s : ℝ) : ℝ :=
  d1DuhamelConst v K * heatScale12 (t - s)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Euclidean.d1DuhamelMajor then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Euclidean.d1DuhamelMajor"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Euclidean.d1DuhamelMajor ``Submission.DifferentialGeometry.Analysis.Parabolic.Euclidean.d1DuhamelMajor

omit [Nontrivial V] in
theorem d1DuhamelMajor_intble {t : ℝ} (v : V) (K : ℝ≥0) :
    IntervalIntegrable (d1DuhamelMajor v K t) _root_.MeasureTheory.MeasureSpace.volume 0 t := by
  exact (scale12_intble).const_mul (d1DuhamelConst v K)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Euclidean.d1DuhamelMajor_intble then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Euclidean.d1DuhamelMajor_intble"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Euclidean.d1DuhamelMajor_intble ``Submission.DifferentialGeometry.Analysis.Parabolic.Euclidean.d1DuhamelMajor_intble

omit [Nontrivial V] in
theorem d1DuhamelMajor_int {t : ℝ} (v : V) (K : ℝ≥0) :
    ∫ s : ℝ in 0..t, d1DuhamelMajor v K t s =
      d1DuhamelConst v K * (2 * t ^ (1 / 2 : ℝ)) := by
  unfold d1DuhamelMajor
  rw [intervalIntegral.integral_const_mul, timeScale12_int]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Euclidean.d1DuhamelMajor_int then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Euclidean.d1DuhamelMajor_int"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Euclidean.d1DuhamelMajor_int ``Submission.DifferentialGeometry.Analysis.Parabolic.Euclidean.d1DuhamelMajor_int

def heatD1Duhamel (t : ℝ) (v : V)
    (f : ℝ → BoundedContinuousFunction V F) (x : V) : F :=
  ∫ s : ℝ in 0..t, heatD1Sup (t - s) v (f s) x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Euclidean.heatD1Duhamel then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Euclidean.heatD1Duhamel"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Euclidean.heatD1Duhamel ``Submission.DifferentialGeometry.Analysis.Parabolic.Euclidean.heatD1Duhamel

omit [CompleteSpace F] in
theorem heatD1Duhamel_int {t : ℝ} (ht : 0 < t) {K : ℝ≥0}
    (f : ℝ → BoundedContinuousFunction V F)
    (hf : ∀ s ∈ Set.Icc (0 : ℝ) t, ‖f s‖ ≤ K)
    (v x : V)
    (hmeas : _root_.MeasureTheory.AEStronglyMeasurable
      (fun s : ℝ => heatD1Sup (t - s) v (f s) x)
      (volume.restrict (Set.uIoc (0 : ℝ) t))) :
    IntervalIntegrable
      (fun s : ℝ => heatD1Sup (t - s) v (f s) x) _root_.MeasureTheory.MeasureSpace.volume 0 t := by
  apply (d1DuhamelMajor_intble v K).mono_fun' hmeas
  have hne : ∀ᵐ s ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure ℝ), s ≠ t := by
    simp [_root_.MeasureTheory.ae_iff, _root_.MeasureTheory.NullSingletonClass.measure_singleton]
  filter_upwards [_root_.MeasureTheory.ae_restrict_mem measurableSet_uIoc,
    ae_restrict_of_ae (s := Set.uIoc (0 : ℝ) t) hne] with s hs hst
  rw [Set.uIoc_of_le ht.le] at hs
  have hstlt : s < t := lt_of_le_of_ne hs.2 hst
  have hpos : 0 < t - s := sub_pos.mpr hstlt
  have hcoef : 0 ≤ ‖v‖ * (heatScale (t - s))⁻¹ * heatC1 V := by
    exact mul_nonneg
      (mul_nonneg (norm_nonneg _) (inv_nonneg.mpr (heatScale_pos hpos).le))
      (heatC1_nonneg (V := V))
  calc
    ‖heatD1Sup (t - s) v (f s) x‖ ≤
        (‖v‖ * (heatScale (t - s))⁻¹ * heatC1 V) * ‖f s‖ :=
      heatD1Sup_norm hpos v (f s) x
    _ ≤ (‖v‖ * (heatScale (t - s))⁻¹ * heatC1 V) * (K : ℝ) :=
      mul_le_mul_of_nonneg_left (hf s ⟨hs.1.le, hs.2⟩) hcoef
    _ = d1DuhamelMajor v K t s := by
      rw [← heatScale12_eq hpos]
      unfold d1DuhamelMajor d1DuhamelConst
      ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Euclidean.heatD1Duhamel_int then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Euclidean.heatD1Duhamel_int"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Euclidean.heatD1Duhamel_int ``Submission.DifferentialGeometry.Analysis.Parabolic.Euclidean.heatD1Duhamel_int

omit [CompleteSpace F] in
theorem heatD1Duhamel_norm {t : ℝ} (ht : 0 < t) {K : ℝ≥0}
    (f : ℝ → BoundedContinuousFunction V F)
    (hf : ∀ s ∈ Set.Icc (0 : ℝ) t, ‖f s‖ ≤ K)
    (v x : V)
    (hmeas : _root_.MeasureTheory.AEStronglyMeasurable
      (fun s : ℝ => heatD1Sup (t - s) v (f s) x)
      (volume.restrict (Set.uIoc (0 : ℝ) t))) :
    ‖heatD1Duhamel t v f x‖ ≤
      2 * d1DuhamelConst v K * Real.sqrt t := by
  have hint := heatD1Duhamel_int ht f hf v x hmeas
  unfold heatD1Duhamel
  calc
    ‖∫ s : ℝ in 0..t, heatD1Sup (t - s) v (f s) x‖ ≤
        ∫ s : ℝ in 0..t, ‖heatD1Sup (t - s) v (f s) x‖ :=
      intervalIntegral.norm_integral_le_integral_norm ht.le
    _ ≤ ∫ s : ℝ in 0..t, d1DuhamelMajor v K t s := by
      apply intervalIntegral.integral_mono_on_of_le_Ioo ht.le hint.norm
        (d1DuhamelMajor_intble v K)
      intro s hs
      have hpos : 0 < t - s := sub_pos.mpr hs.2
      have hcoef : 0 ≤ ‖v‖ * (heatScale (t - s))⁻¹ * heatC1 V := by
        exact mul_nonneg
          (mul_nonneg (norm_nonneg _) (inv_nonneg.mpr (heatScale_pos hpos).le))
          (heatC1_nonneg (V := V))
      calc
        ‖heatD1Sup (t - s) v (f s) x‖ ≤
            (‖v‖ * (heatScale (t - s))⁻¹ * heatC1 V) * ‖f s‖ :=
          heatD1Sup_norm hpos v (f s) x
        _ ≤ (‖v‖ * (heatScale (t - s))⁻¹ * heatC1 V) *
            (K : ℝ) :=
          mul_le_mul_of_nonneg_left (hf s ⟨hs.1.le, hs.2.le⟩) hcoef
        _ = d1DuhamelMajor v K t s := by
          rw [← heatScale12_eq hpos]
          unfold d1DuhamelMajor d1DuhamelConst
          ring
    _ = d1DuhamelConst v K * (2 * t ^ (1 / 2 : ℝ)) :=
      d1DuhamelMajor_int v K
    _ = 2 * d1DuhamelConst v K * Real.sqrt t := by
      rw [Real.sqrt_eq_rpow]
      ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Euclidean.heatD1Duhamel_norm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Euclidean.heatD1Duhamel_norm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Euclidean.heatD1Duhamel_norm ``Submission.DifferentialGeometry.Analysis.Parabolic.Euclidean.heatD1Duhamel_norm

end GradientPotential

end Euclidean
end Parabolic
end Analysis
end DifferentialGeometry
