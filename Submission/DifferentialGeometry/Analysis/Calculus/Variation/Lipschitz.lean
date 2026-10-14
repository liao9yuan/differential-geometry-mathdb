import Mathlib.Analysis.BoundedVariation
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission








noncomputable section

open _root_.Set _root_.MeasureTheory
open scoped _root_.ENNReal _root_.NNReal

namespace DifferentialGeometry.Analysis

section

variable {X : Type*} [PseudoEMetricSpace X] {f : ℝ → X} {C : ℝ≥0}

theorem eVariationOn_Icc_le_of_lipschitz (hf : LipschitzWith C f) (a b : ℝ) :
    eVariationOn f (_root_.Set.Icc a b) ≤ (C : ℝ≥0∞) * ENNReal.ofReal (b - a) := by
  simpa only [Function.comp_id, eVariationOn_id_Icc] using
    hf.lipschitzOnWith.comp_eVariationOn_le (g := id) (s := _root_.Set.Icc a b) (_root_.Set.mapsTo_univ _ _)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.eVariationOn_Icc_le_of_lipschitz then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.eVariationOn_Icc_le_of_lipschitz"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.eVariationOn_Icc_le_of_lipschitz ``Submission.DifferentialGeometry.Analysis.eVariationOn_Icc_le_of_lipschitz

theorem eVariationOn_Icc_ne_top_of_lipschitz (hf : LipschitzWith C f) (a b : ℝ) :
    eVariationOn f (_root_.Set.Icc a b) ≠ ⊤ :=
  ne_top_of_le_ne_top (by finiteness) (eVariationOn_Icc_le_of_lipschitz hf a b)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.eVariationOn_Icc_ne_top_of_lipschitz then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.eVariationOn_Icc_ne_top_of_lipschitz"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.eVariationOn_Icc_ne_top_of_lipschitz ``Submission.DifferentialGeometry.Analysis.eVariationOn_Icc_ne_top_of_lipschitz


theorem lipschitz_variationOnFromTo (hf : LipschitzWith C f) (a : ℝ) :
    LipschitzWith C (variationOnFromTo f _root_.Set.univ a) := by
  have hloc : LocallyBoundedVariationOn f univ := hf.locallyBoundedVariationOn _root_.Set.univ
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [Real.dist_eq, variationOnFromTo.sub_right hloc (_root_.Set.mem_univ _) (_root_.Set.mem_univ _) (_root_.Set.mem_univ _)]
  wlog hxy : y ≤ x generalizing x y
  · rw [variationOnFromTo.eq_neg_swap, abs_neg, dist_comm]
    exact this y x (le_of_not_ge hxy)
  rw [variationOnFromTo.eq_of_le f _root_.Set.univ hxy, _root_.Set.univ_inter, ENNReal.abs_toReal]
  have h := ENNReal.toReal_mono (by finiteness)
    (eVariationOn_Icc_le_of_lipschitz hf y x)
  simpa only [ENNReal.toReal_mul, ENNReal.coe_toReal,
    ENNReal.toReal_ofReal (sub_nonneg.mpr hxy), Real.dist_eq,
    abs_of_nonneg (sub_nonneg.mpr hxy)] using h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.lipschitz_variationOnFromTo then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.lipschitz_variationOnFromTo"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.lipschitz_variationOnFromTo ``Submission.DifferentialGeometry.Analysis.lipschitz_variationOnFromTo

theorem edist_le_ofReal_variationOnFromTo (hf : LipschitzWith C f) (a : ℝ) (x y : ℝ) :
    _root_.EDist.edist (f x) (f y) ≤
      ENNReal.ofReal |variationOnFromTo f _root_.Set.univ a x - variationOnFromTo f _root_.Set.univ a y| := by
  have hloc : LocallyBoundedVariationOn f univ := hf.locallyBoundedVariationOn _root_.Set.univ
  wlog hxy : y ≤ x generalizing x y
  · rw [_root_.PseudoEMetricSpace.edist_comm, abs_sub_comm]
    exact this y x (le_of_not_ge hxy)
  have hV : variationOnFromTo f _root_.Set.univ a x - variationOnFromTo f _root_.Set.univ a y =
      (eVariationOn f (_root_.Set.Icc y x)).toReal := by
    rw [variationOnFromTo.sub_right hloc (_root_.Set.mem_univ _) (_root_.Set.mem_univ _) (_root_.Set.mem_univ _),
      variationOnFromTo.eq_of_le f _root_.Set.univ hxy, _root_.Set.univ_inter]
  calc _root_.EDist.edist (f x) (f y)
      = _root_.EDist.edist (f y) (f x) := _root_.PseudoEMetricSpace.edist_comm _ _
    _ ≤ eVariationOn f (_root_.Set.Icc y x) := eVariationOn.edist_le f ⟨le_rfl, hxy⟩ ⟨hxy, le_rfl⟩
    _ = ENNReal.ofReal ((eVariationOn f (_root_.Set.Icc y x)).toReal) :=
        (ENNReal.ofReal_toReal (eVariationOn_Icc_ne_top_of_lipschitz hf y x)).symm
    _ = ENNReal.ofReal (variationOnFromTo f _root_.Set.univ a x - variationOnFromTo f _root_.Set.univ a y) := by
        rw [hV]
    _ = ENNReal.ofReal |variationOnFromTo f _root_.Set.univ a x - variationOnFromTo f _root_.Set.univ a y| := by
        rw [abs_of_nonneg (by rw [hV]; exact ENNReal.toReal_nonneg)]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.edist_le_ofReal_variationOnFromTo then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.edist_le_ofReal_variationOnFromTo"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.edist_le_ofReal_variationOnFromTo ``Submission.DifferentialGeometry.Analysis.edist_le_ofReal_variationOnFromTo

end

section

variable {X : Type*} [PseudoMetricSpace X] {f : ℝ → X} {C : ℝ≥0}

theorem dist_le_variationOnFromTo_dist (hf : LipschitzWith C f) (a x y : ℝ) :
    dist (f x) (f y) ≤ _root_.Dist.dist (variationOnFromTo f _root_.Set.univ a x) (variationOnFromTo f _root_.Set.univ a y) := by
  have hloc : LocallyBoundedVariationOn f univ := hf.locallyBoundedVariationOn _root_.Set.univ
  rw [Real.dist_eq, variationOnFromTo.sub_right hloc (_root_.Set.mem_univ _) (_root_.Set.mem_univ _) (_root_.Set.mem_univ _)]
  wlog hxy : y ≤ x generalizing x y
  · rw [variationOnFromTo.eq_neg_swap, abs_neg, dist_comm]
    exact this y x (le_of_not_ge hxy)
  rw [variationOnFromTo.eq_of_le f _root_.Set.univ hxy, _root_.Set.univ_inter, ENNReal.abs_toReal]
  exact BoundedVariationOn.dist_le (eVariationOn_Icc_ne_top_of_lipschitz hf y x)
    ⟨hxy, le_rfl⟩ ⟨le_rfl, hxy⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.dist_le_variationOnFromTo_dist then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.dist_le_variationOnFromTo_dist"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.dist_le_variationOnFromTo_dist ``Submission.DifferentialGeometry.Analysis.dist_le_variationOnFromTo_dist



theorem deriv_variationOnFromTo_nonneg (hf : LipschitzWith C f) (a x : ℝ) :
    0 ≤ deriv (variationOnFromTo f _root_.Set.univ a) x := by
  have hm : Monotone (variationOnFromTo f _root_.Set.univ a) :=
    fun _ _ h => variationOnFromTo.monotoneOn (hf.locallyBoundedVariationOn _root_.Set.univ)
      (_root_.Set.mem_univ a) (_root_.Set.mem_univ _) (_root_.Set.mem_univ _) h
  exact hm.deriv_nonneg

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.deriv_variationOnFromTo_nonneg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.deriv_variationOnFromTo_nonneg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.deriv_variationOnFromTo_nonneg ``Submission.DifferentialGeometry.Analysis.deriv_variationOnFromTo_nonneg

end

end DifferentialGeometry.Analysis
