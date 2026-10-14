import Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.WeakDerivative.FundamentalTheorem

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section
open _root_.Filter _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Set
open scoped _root_.ENNReal _root_.Topology
namespace DifferentialGeometry.Analysis.Parabolic.TimeSobolev

variable {X S : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [SeminormedAddCommGroup S] [NormedSpace ℝ S]

theorem extend_scalar_weak_deriv_of_denseRange_on
    {a b : ℝ} (ι : S →L[ℝ] X) (hdense : DenseRange ι)
    {p q : ℝ → X →L[ℝ] ℝ}
    (hp : _root_.MeasureTheory.MemLp p 2 (volume.restrict (_root_.Set.Icc a b)))
    (hq : _root_.MeasureTheory.MemLp q 2 (volume.restrict (_root_.Set.Icc a b)))
    (hweak : ∀ (x : S) (φ : ℝ → ℝ), ContDiff ℝ (⊤ : ℕ∞) φ →
      HasCompactSupport φ → tsupport φ ⊆ _root_.Set.Ioo a b →
      (∫ t in _root_.Set.Ioo a b, deriv φ t * p t (ι x)) =
        -∫ t in _root_.Set.Ioo a b, φ t * q t (ι x)) :
    ∀ (x : X) (φ : ℝ → ℝ), ContDiff ℝ (⊤ : ℕ∞) φ →
      HasCompactSupport φ → tsupport φ ⊆ _root_.Set.Ioo a b →
      (∫ t in _root_.Set.Ioo a b, deriv φ t * p t x) =
        -∫ t in _root_.Set.Ioo a b, φ t * q t x := by
  intro x φ hφ hφc hφs
  let μ := volume.restrict (_root_.Set.Ioo a b)
  have hpI : _root_.MeasureTheory.Integrable p μ := (hp.integrable (by norm_num)).mono_measure
    (Measure.restrict_mono _root_.Set.Ioo_subset_Icc_self le_rfl)
  have hqI : _root_.MeasureTheory.Integrable q μ := (hq.integrable (by norm_num)).mono_measure
    (Measure.restrict_mono _root_.Set.Ioo_subset_Icc_self le_rfl)
  have hdp : _root_.MeasureTheory.Integrable (fun t => deriv φ t • p t) μ :=
    hpI.locallyIntegrable.integrable_smul_left_of_hasCompactSupport
      (hφ.continuous_deriv (by norm_cast)) hφc.deriv
  have hqφ : _root_.MeasureTheory.Integrable (fun t => φ t • q t) μ :=
    hqI.locallyIntegrable.integrable_smul_left_of_hasCompactSupport hφ.continuous hφc
  let A : X →L[ℝ] ℝ := ∫ t, deriv φ t • p t ∂μ
  let B : X →L[ℝ] ℝ := ∫ t, φ t • q t ∂μ
  have hABfun : (A : X → ℝ) = (-B : X → ℝ) := by
    apply DenseRange.equalizer hdense A.continuous (-B).continuous
    funext s
    dsimp [A, B]
    rw [ContinuousLinearMap.integral_apply hdp]
    change (∫ x, (deriv φ x • p x) (ι s) ∂μ) = -((∫ t, φ t • q t ∂μ) (ι s))
    rw [ContinuousLinearMap.integral_apply hqφ]
    convert hweak s φ hφ hφc hφs using 1 <;> simp [μ, smul_eq_mul]
  have hAB : A = -B := ContinuousLinearMap.ext (fun s => congrFun hABfun s)
  have hx := congrArg (fun L : X →L[ℝ] ℝ => L x) hAB
  dsimp [A, B] at hx
  rw [ContinuousLinearMap.integral_apply hdp] at hx
  change (∫ t, (deriv φ t • p t) x ∂μ) = -((∫ t, φ t • q t ∂μ) x) at hx
  rw [ContinuousLinearMap.integral_apply hqφ] at hx
  convert hx using 1 <;> simp [μ, smul_eq_mul]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.extend_scalar_weak_deriv_of_denseRange_on then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TimeSobolev.extend_scalar_weak_deriv_of_denseRange_on"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.extend_scalar_weak_deriv_of_denseRange_on ``Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.extend_scalar_weak_deriv_of_denseRange_on

theorem extend_scalar_weak_deriv_of_denseRange
    {T : ℝ} (ι : S →L[ℝ] X) (hdense : DenseRange ι)
    {p q : ℝ → X →L[ℝ] ℝ} (hp : _root_.MeasureTheory.MemLp p 2 (timeMeasure T))
    (hq : _root_.MeasureTheory.MemLp q 2 (timeMeasure T))
    (hweak : ∀ (x : S) (φ : ℝ → ℝ), ContDiff ℝ (⊤ : ℕ∞) φ →
      HasCompactSupport φ → tsupport φ ⊆ _root_.Set.Ioo (0 : ℝ) T →
      (∫ t in _root_.Set.Ioo (0 : ℝ) T, deriv φ t * p t (ι x)) =
        -∫ t in _root_.Set.Ioo (0 : ℝ) T, φ t * q t (ι x)) :
    ∀ (x : X) (φ : ℝ → ℝ), ContDiff ℝ (⊤ : ℕ∞) φ →
      HasCompactSupport φ → tsupport φ ⊆ _root_.Set.Ioo (0 : ℝ) T →
      (∫ t in _root_.Set.Ioo (0 : ℝ) T, deriv φ t * p t x) =
        -∫ t in _root_.Set.Ioo (0 : ℝ) T, φ t * q t x := by
  exact extend_scalar_weak_deriv_of_denseRange_on ι hdense hp hq hweak

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.extend_scalar_weak_deriv_of_denseRange then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TimeSobolev.extend_scalar_weak_deriv_of_denseRange"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.extend_scalar_weak_deriv_of_denseRange ``Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.extend_scalar_weak_deriv_of_denseRange

end DifferentialGeometry.Analysis.Parabolic.TimeSobolev
