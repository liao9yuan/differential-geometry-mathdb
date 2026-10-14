import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.MeasureTheory.Measure.Prod

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission



noncomputable section

open _root_.Set _root_.MeasureTheory

namespace DifferentialGeometry.Analysis

theorem volume_complex_re_eq (a : ℝ) : _root_.MeasureTheory.MeasureSpace.volume {z : ℂ | z.re = a} = 0 := by
  have h := Complex.volume_preserving_equiv_real_prod.measure_preimage
    ((_root_.MeasurableSingletonClass.measurableSet_singleton a).prod (MeasurableSet.univ (α := ℝ))).nullMeasurableSet
  have he : Complex.measurableEquivRealProd ⁻¹' ({a} ×ˢ (_root_.Set.univ : Set ℝ)) = {z : ℂ | z.re = a} := by
    ext z
    simp
  rw [he] at h
  simpa only [Measure.volume_eq_prod, Measure.prod_prod, _root_.MeasureTheory.NullSingletonClass.measure_singleton, _root_.MulZeroClass.zero_mul] using h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.volume_complex_re_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.volume_complex_re_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.volume_complex_re_eq ``Submission.DifferentialGeometry.Analysis.volume_complex_re_eq

theorem volume_complex_im_eq (a : ℝ) : _root_.MeasureTheory.MeasureSpace.volume {z : ℂ | z.im = a} = 0 := by
  have h := Complex.volume_preserving_equiv_real_prod.measure_preimage
    ((MeasurableSet.univ (α := ℝ)).prod (_root_.MeasurableSingletonClass.measurableSet_singleton a)).nullMeasurableSet
  have he : Complex.measurableEquivRealProd ⁻¹' ((_root_.Set.univ : Set ℝ) ×ˢ {a}) = {z : ℂ | z.im = a} := by
    ext z
    simp
  rw [he] at h
  simpa only [Measure.volume_eq_prod, Measure.prod_prod, _root_.MeasureTheory.NullSingletonClass.measure_singleton, _root_.MulZeroClass.mul_zero] using h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.volume_complex_im_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.volume_complex_im_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.volume_complex_im_eq ``Submission.DifferentialGeometry.Analysis.volume_complex_im_eq

theorem ae_complex_re_ne (a : ℝ) : ∀ᵐ z : ℂ, z.re ≠ a := by
  rw [_root_.MeasureTheory.ae_iff]
  convert volume_complex_re_eq a using 1
  congr 1
  ext z
  simp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.ae_complex_re_ne then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.ae_complex_re_ne"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.ae_complex_re_ne ``Submission.DifferentialGeometry.Analysis.ae_complex_re_ne

theorem ae_complex_im_ne (a : ℝ) : ∀ᵐ z : ℂ, z.im ≠ a := by
  rw [_root_.MeasureTheory.ae_iff]
  convert volume_complex_im_eq a using 1
  congr 1
  ext z
  simp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.ae_complex_im_ne then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.ae_complex_im_ne"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.ae_complex_im_ne ``Submission.DifferentialGeometry.Analysis.ae_complex_im_ne

end DifferentialGeometry.Analysis
