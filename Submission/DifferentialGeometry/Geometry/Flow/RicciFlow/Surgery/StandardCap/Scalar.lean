import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.Curvature
import Submission.DifferentialGeometry.Geometry.Curvature.ScalarSectional
import Submission.DifferentialGeometry.Geometry.Metric.RadialFrame

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Bundle _root_.Submission.Bundle _root_.Submission.DifferentialGeometry _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian
open scoped _root_.Manifold _root_.Submission.Manifold _root_.InnerProductSpace
namespace DifferentialGeometry.PDE.RicciFlow.StandardCap
private abbrev E3 := EuclideanSpace ℝ (Fin 3)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.E3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.E3 target :: scope.openDecls } }
private abbrev E4 := EuclideanSpace ℝ (Fin 4)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.E4
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.E4 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.instFactEqNatFinrankRealE4HAddOfNat : Fact (Module.finrank ℝ E4 = 3 + 1) := ⟨by simp⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.instFactEqNatFinrankRealE4HAddOfNat
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.instFactEqNatFinrankRealE4HAddOfNat target :: scope.openDecls } }

theorem metricScalarAt_tip (p : Metric.sphere (0 : E4) 1) {x : E3}
    (hxr : ‖x‖ < roundNormalRadius p) (hxa : ‖x‖ < transitionStart) :
    metricScalarAt metric x = 3 := by
  have h := metricScalarAt_of_constant_sectional metric x (1 / 2)
    (fun u v => metricRm04_tip p hxr hxa u v)
  norm_num at h
  exact h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.metricScalarAt_tip then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.metricScalarAt_tip"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.metricScalarAt_tip ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.metricScalarAt_tip

theorem metricScalarAt_zero : metricScalarAt metric (0 : E3) = 3 := by
  let p : Metric.sphere (0 : E4) 1 := ⟨EuclideanSpace.single 0 1, by simp⟩
  exact metricScalarAt_tip p (by simpa using roundNormalRadius_pos p)
    (by simpa using transitionStart_pos)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.metricScalarAt_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.metricScalarAt_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.metricScalarAt_zero ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.metricScalarAt_zero

theorem metricScalarAt_eq_warping {x : E3} (hx : x ≠ 0) :
    metricScalarAt metric x =
      4 * (-deriv (deriv warpingFunction) ‖x‖ / warpingFunction ‖x‖) +
      2 * ((1 - deriv warpingFunction ‖x‖ ^ 2) / warpingFunction ‖x‖ ^ 2) := by
  classical
  have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  have ha : warpingFunction ‖x‖ ≠ 0 := (warpingFunction_pos (norm_pos_iff.mpr hx)).ne'
  obtain ⟨b, hb⟩ := exists_radial_orthonormalBasis hx
  let B := radialMetricBasis warpingFunction hx ha b
  have hB : ∀ i j : Fin 3, metric.inner x (B i) (B j) = if i = j then (1 : ℝ) else 0 :=
    metric_inner_radialMetricBasis metric (metric_eventually_radial hx).eq_of_nhds hx ha b hb
  have haux (n : ℕ) (hd : Module.finrank ℝ E3 = n)
      (C : Fin n → TangentSpace (𝓡 3) x)
      (hC : ∀ i j, metric.inner x (C i) (C j) = if i = j then (1 : ℝ) else 0) :
      metricScalarAt metric x = ∑ i, ∑ j, metricRm04StandardAt metric x (C j) (C i) (C i) (C j) := by
    subst n
    exact metricScalarAt_eq_sum_metricRm04StandardAt metric x C hC
  have htrace := haux 3 (by simp) B hB
  have hterm (i j : Fin 3) : metricRm04StandardAt metric x (B j) (B i) (B i) (B j) =
      if i = j then 0 else if i = 0 ∨ j = 0 then
        -deriv (deriv warpingFunction) ‖x‖ / warpingFunction ‖x‖ else
        (1 - deriv warpingFunction ‖x‖ ^ 2) / warpingFunction ‖x‖ ^ 2 := by
    change metricRm04StandardAt metric x
      (radialMetricBasis warpingFunction hx ha b j) (radialMetricBasis warpingFunction hx ha b i)
      (radialMetricBasis warpingFunction hx ha b i) (radialMetricBasis warpingFunction hx ha b j) = _
    simp only [radialMetricBasis_apply]
    rw [metricRm04StdAt_radialBilinearField metric
      (metric_eventually_radial hx) contDiff_warpingFunction hx ha]
    simp only [real_inner_smul_left, real_inner_smul_right, b.inner_eq_ite,
      inner_radial_orthonormalBasis b hb]
    fin_cases i <;> fin_cases j <;> norm_num <;> field_simp <;> ring
  rw [htrace]
  simp only [hterm]
  simp [Fin.sum_univ_succ]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.metricScalarAt_eq_warping then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.metricScalarAt_eq_warping"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.metricScalarAt_eq_warping ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.metricScalarAt_eq_warping

theorem one_le_metricScalarAt (x : E3) : 1 ≤ metricScalarAt metric x := by
  by_cases hx : x = 0
  · subst x
    rw [metricScalarAt_zero]
    norm_num
  · rw [metricScalarAt_eq_warping hx]
    exact one_le_warpingFunction_derivative_combination (norm_pos_iff.mpr hx)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.one_le_metricScalarAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.one_le_metricScalarAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.one_le_metricScalarAt ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.one_le_metricScalarAt

theorem metricScalarAt_cylindrical {x : E3} (hx : transitionEnd ≤ ‖x‖) :
    metricScalarAt metric x = 1 := by
  rw [metricScalarAt_eq_warping (norm_pos_iff.mp (transitionEnd_pos.trans_le hx)),
    deriv_warpingFunction_eq_zero_of_transitionEnd_le hx,
    deriv_deriv_warpingFunction_eq_zero_of_transitionEnd_le hx,
    warpingFunction_eq_sqrt_two hx]
  norm_num

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.metricScalarAt_cylindrical then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.metricScalarAt_cylindrical"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.metricScalarAt_cylindrical ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.metricScalarAt_cylindrical

end DifferentialGeometry.PDE.RicciFlow.StandardCap
