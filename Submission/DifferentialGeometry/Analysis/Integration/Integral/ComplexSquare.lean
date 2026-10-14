import Submission.DifferentialGeometry.Analysis.Elliptic.ComplexPlane.Strip
import Mathlib.MeasureTheory.Integral.Prod

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission



noncomputable section

open _root_.Set _root_.MeasureTheory

namespace DifferentialGeometry.Analysis


theorem integrable_unitSquare_coordinates {f : ℂ → ℝ} (hf : _root_.MeasureTheory.IntegrableOn f unitSquare) :
    _root_.MeasureTheory.IntegrableOn (fun p : ℝ × ℝ => f (Complex.measurableEquivRealProd.symm p))
      (_root_.Set.Icc (0 : ℝ) 1 ×ˢ _root_.Set.Icc (0 : ℝ) 1) (volume.prod _root_.MeasureTheory.MeasureSpace.volume) := by
  have h := (Complex.volume_preserving_equiv_real_prod.symm.integrableOn_comp_preimage
    Complex.measurableEquivRealProd.symm.measurableEmbedding).mpr hf
  exact h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.integrable_unitSquare_coordinates then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.integrable_unitSquare_coordinates"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.integrable_unitSquare_coordinates ``Submission.DifferentialGeometry.Analysis.integrable_unitSquare_coordinates



theorem integral_unitSquare_eq_iterated {f : ℂ → ℝ} (hf : _root_.MeasureTheory.IntegrableOn f unitSquare) :
    ∫ z in unitSquare, f z =
      ∫ v in _root_.Set.Icc (0 : ℝ) 1, ∫ θ in _root_.Set.Icc (0 : ℝ) 1, f (Complex.measurableEquivRealProd.symm (v, θ)) := by
  have h := Complex.volume_preserving_equiv_real_prod.symm.integral_comp' (unitSquare.indicator f)
  change (∫ p : ℝ × ℝ, (_root_.Set.Icc (0 : ℝ) 1 ×ˢ _root_.Set.Icc (0 : ℝ) 1).indicator
    (fun q => f (Complex.measurableEquivRealProd.symm q)) p) = _ at h
  rw [_root_.MeasureTheory.integral_indicator (measurableSet_Icc.prod measurableSet_Icc),
    _root_.MeasureTheory.integral_indicator isCompact_unitSquare.measurableSet] at h
  exact h.symm.trans (_root_.MeasureTheory.setIntegral_prod _ (integrable_unitSquare_coordinates hf))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.integral_unitSquare_eq_iterated then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.integral_unitSquare_eq_iterated"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.integral_unitSquare_eq_iterated ``Submission.DifferentialGeometry.Analysis.integral_unitSquare_eq_iterated

end DifferentialGeometry.Analysis
