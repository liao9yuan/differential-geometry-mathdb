/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith, Codex
-/
import Mathlib.Analysis.Calculus.FDeriv.Equiv
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.Analysis.Normed.Module.FiniteDimension

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

namespace MeasureTheory
open _root_.MeasureTheory

open _root_.Function _root_.MeasureTheory.Measure _root_.Set

open _root_.MeasureTheory in
/-- **Sard's lemma in equal dimensions.** Let `E` and `F` be finite-dimensional real normed
spaces of equal dimension. If `f` is differentiable along `s` with derivative `f'`, and `f'` is
nowhere surjective on `s`, then `f '' s` has additive Haar measure zero in `F`.

Unlike the endomorphism version in Mathlib, the domain and codomain need not be the same normed
space and may carry unrelated norms and Haar measure normalizations. -/
theorem addHaar_image_eq_zero_of_not_surjective_fderivWithin
    {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [MeasurableSpace F] [BorelSpace F]
    {s : Set E} {f : E → F} {f' : E → E →L[ℝ] F}
    (ν : _root_.MeasureTheory.Measure F) [_root_.MeasureTheory.Measure.IsAddHaarMeasure ν]
    (hdim : Module.finrank ℝ E = Module.finrank ℝ F)
    (hf' : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x)
    (hcrit : ∀ x ∈ s, ¬ _root_.Function.Surjective (f' x)) : ν (f '' s) = 0 := by
  borelize E
  let e : F ≃L[ℝ] E := ContinuousLinearEquiv.ofFinrankEq hdim.symm
  let g : E → E := fun x => e (f x)
  let g' : E → E →L[ℝ] E := fun x => (e : F →L[ℝ] E).comp (f' x)
  have hg' : ∀ x ∈ s, HasFDerivWithinAt g (g' x) s x := by
    intro x hx
    exact e.hasFDerivAt.comp_hasFDerivWithinAt x (hf' x hx)
  have hdet : ∀ x ∈ s, (g' x).det = 0 := by
    intro x hx
    rw [LinearMap.det_eq_zero_iff_ker_ne_bot, ne_eq, LinearMap.ker_eq_bot]
    intro hinj
    apply hcrit x hx
    intro y
    obtain ⟨z, hz⟩ := LinearMap.injective_iff_surjective.mp hinj (e y)
    refine ⟨z, e.injective ?_⟩
    simpa only [g', ContinuousLinearMap.coe_coe, ContinuousLinearMap.comp_apply,
      ContinuousLinearEquiv.coe_coe] using hz
  have hnull : (_root_.MeasureTheory.Measure.addHaar : _root_.MeasureTheory.Measure E) (g '' s) = 0 :=
    _root_.MeasureTheory.addHaar_image_eq_zero_of_det_fderivWithin_eq_zero _root_.MeasureTheory.Measure.addHaar hg' hdet
  have hqm : _root_.MeasureTheory.Measure.QuasiMeasurePreserving e ν (_root_.MeasureTheory.Measure.addHaar : _root_.MeasureTheory.Measure E) :=
    ⟨e.continuous.measurable, _root_.MeasureTheory.Measure.absolutelyContinuous_isAddHaarMeasure (ν.map e) addHaar⟩
  have hpreimage : ν (e ⁻¹' (g '' s)) = 0 := hqm.preimage_null hnull
  have himage : g '' s = e '' (f '' s) := by rw [_root_.Set.image_image]
  rw [himage, Set.preimage_image_eq _ e.injective] at hpreimage
  exact hpreimage

run_cmd do
  let env ← Lean.getEnv
  if env.contains `MeasureTheory.addHaar_image_eq_zero_of_not_surjective_fderivWithin then
    throwError "Refusing to shadow existing declaration MeasureTheory.addHaar_image_eq_zero_of_not_surjective_fderivWithin"
  Lean.modifyEnv fun env => Lean.addAlias env `MeasureTheory.addHaar_image_eq_zero_of_not_surjective_fderivWithin ``Submission.MeasureTheory.addHaar_image_eq_zero_of_not_surjective_fderivWithin

end MeasureTheory
