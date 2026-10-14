import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary
import Mathlib.Analysis.Calculus.LocalExtr.Basic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set
open scoped _root_.Manifold _root_.Topology _root_.Convex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

open _root_.IsLocalMin in
theorem IsLocalMin.mvfderiv_eq_zero {f : M → ℝ} {x : M}
    (hmin : IsLocalMin f x) (hx : I.IsInteriorPoint x) : mvfderiv I f x = 0 := by
  by_cases hf : MDifferentiableAt I 𝓘(ℝ, ℝ) f x
  swap
  · simp only [mvfderiv, mfderiv_zero_of_not_mdifferentiableAt hf,
      ContinuousLinearMap.comp_zero]
  have hmin_chart : IsLocalMin (f ∘ (extChartAt I x).symm) (extChartAt I x x) := by
    have hmin' : IsLocalMin f ((extChartAt I x).symm (extChartAt I x x)) := by
      simpa only [mfld_simps] using hmin
    exact hmin'.comp_continuous (continuousAt_extChartAt_symm (I := I) x)
  rw [hf.mvfderiv, fderivWithin_of_mem_nhds (range_mem_nhds_isInteriorPoint hx)]
  have heq : writtenInExtChartAt I 𝓘(ℝ, ℝ) x f = f ∘ (extChartAt I x).symm := by
    rw [writtenInExtChartAt, extChartAt_model_space_eq_id]
    rfl
  rw [heq]
  exact hmin_chart.fderiv_eq_zero

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.IsLocalMin
  let env ← Lean.getEnv
  if env.contains `IsLocalMin.mvfderiv_eq_zero then
    throwError "Refusing to shadow existing declaration IsLocalMin.mvfderiv_eq_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `IsLocalMin.mvfderiv_eq_zero ``Submission.IsLocalMin.mvfderiv_eq_zero

open _root_.IsLocalMax in
theorem IsLocalMax.mvfderiv_eq_zero {f : M → ℝ} {x : M}
    (hmax : IsLocalMax f x) (hx : I.IsInteriorPoint x) : mvfderiv I f x = 0 := by
  have h := hmax.neg.mvfderiv_eq_zero hx
  change mvfderiv I (-f) x = 0 at h
  simpa only [mvfderiv_neg, neg_eq_zero] using h

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.IsLocalMax
  let env ← Lean.getEnv
  if env.contains `IsLocalMax.mvfderiv_eq_zero then
    throwError "Refusing to shadow existing declaration IsLocalMax.mvfderiv_eq_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `IsLocalMax.mvfderiv_eq_zero ``Submission.IsLocalMax.mvfderiv_eq_zero

open _root_.IsLocalMax in
theorem IsLocalMax.mvfderiv_nonpos {f : M → ℝ} {x : M} (hmax : IsLocalMax f x)
    {v : E} (hv : v ∈ posTangentConeAt (Set.range I) (extChartAt I x x)) :
    mvfderiv I f x v ≤ 0 := by
  by_cases hf : MDifferentiableAt I 𝓘(ℝ, ℝ) f x
  swap
  · rw [mvfderiv, mfderiv_zero_of_not_mdifferentiableAt hf, ContinuousLinearMap.comp_zero]
    exact le_refl 0
  have hmax_chart : IsLocalMax (f ∘ (extChartAt I x).symm) (extChartAt I x x) := by
    have hmax' : IsLocalMax f ((extChartAt I x).symm (extChartAt I x x)) := by
      simpa only [mfld_simps] using hmax
    exact hmax'.comp_continuous (continuousAt_extChartAt_symm (I := I) x)
  rw [hf.mvfderiv]
  have heq : writtenInExtChartAt I 𝓘(ℝ, ℝ) x f = f ∘ (extChartAt I x).symm := by
    rw [writtenInExtChartAt, extChartAt_model_space_eq_id]
    rfl
  rw [heq]
  exact (hmax_chart.on (Set.range I)).fderivWithin_nonpos hv

run_cmd do
  let env ← Lean.getEnv
  if env.contains `IsLocalMax.mvfderiv_nonpos then
    throwError "Refusing to shadow existing declaration IsLocalMax.mvfderiv_nonpos"
  Lean.modifyEnv fun env => Lean.addAlias env `IsLocalMax.mvfderiv_nonpos ``Submission.IsLocalMax.mvfderiv_nonpos

open _root_.IsLocalMin in
theorem IsLocalMin.mvfderiv_nonneg {f : M → ℝ} {x : M} (hmin : IsLocalMin f x)
    {v : E} (hv : v ∈ posTangentConeAt (Set.range I) (extChartAt I x x)) :
    0 ≤ mvfderiv I f x v := by
  have h := hmin.neg.mvfderiv_nonpos hv
  change mvfderiv I (-f) x v ≤ 0 at h
  rw [mvfderiv_neg] at h
  exact neg_nonpos.mp h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `IsLocalMin.mvfderiv_nonneg then
    throwError "Refusing to shadow existing declaration IsLocalMin.mvfderiv_nonneg"
  Lean.modifyEnv fun env => Lean.addAlias env `IsLocalMin.mvfderiv_nonneg ``Submission.IsLocalMin.mvfderiv_nonneg
