import Submission.DifferentialGeometry.Topology.Manifold.ContMDiff.Interior
import Submission.DifferentialGeometry.Topology.Morse.InteriorRestriction
import Submission.DifferentialGeometry.Topology.Morse.CriticalPoint
import Submission.DifferentialGeometry.Topology.Morse.HessianNaturality
import Mathlib.LinearAlgebra.QuadraticForm.Signature

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Filter _root_.Function
open scoped _root_.Manifold _root_.ContDiff _root_.Topology
open _root_.Submission.DifferentialGeometry.Topology.Morse
namespace DifferentialGeometry.Morse
variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {H M : Type} [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
  (I : ModelWithCorners ℝ E H) [IsManifold I ∞ M]
  (e : E ≃L[ℝ] F)


theorem chartHessianAt_transContinuousLinearEquiv {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {x : M} (hx : I.IsInteriorPoint x)
    (hc : IsCriticalPointAt I f x) :
    chartHessianAt (fun y => f ((extChartAt (I.transContinuousLinearEquiv e) x).symm y))
      (extChartAt (I.transContinuousLinearEquiv e) x x) =
      (chartHessianAt (fun y => f ((extChartAt I x).symm y)) (extChartAt I x x)).comp
        e.symm.toLinearEquiv.toLinearMap := by
  let g : E → ℝ := fun y => f ((extChartAt I x).symm y)
  let z := extChartAt I x x
  have hg : ContDiffAt ℝ 2 g (e.symm (e z)) := by
    simpa only [e.symm_apply_apply] using
      (DifferentialGeometry.Manifold.contDiffAt_comp_extChartAt_symm_of_isInteriorPoint I hf hx).of_le (show (2 : ℕ∞ω) ≤ ∞ from WithTop.coe_le_coe.mpr le_top)
  have hz : fderiv ℝ g (e.symm (e z)) = 0 := by
    rw [e.symm_apply_apply]
    have hd := DifferentialGeometry.Manifold.mfderiv_eq_fderiv_extChartAt_of_isInteriorPoint
      I (hf.mdifferentiableAt (by simp)) hx
    exact hd.symm.trans hc
  have hd := fderiv_fderiv_comp_at_critical hg e.symm.contDiff.contDiffAt hz
  ext v
  change (fderiv ℝ (fderiv ℝ (g ∘ e.symm)) (e z)) v v =
    (fderiv ℝ (fderiv ℝ g) z) (e.symm v) (e.symm v)
  rw [hd, e.symm.fderiv, e.symm_apply_apply]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Morse.chartHessianAt_transContinuousLinearEquiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Morse.chartHessianAt_transContinuousLinearEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Morse.chartHessianAt_transContinuousLinearEquiv ``Submission.DifferentialGeometry.Morse.chartHessianAt_transContinuousLinearEquiv


theorem chartHessianAt_equivalent_transContinuousLinearEquiv {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {x : M} (hx : I.IsInteriorPoint x)
    (hc : IsCriticalPointAt I f x) :
    (chartHessianAt (fun y => f ((extChartAt (I.transContinuousLinearEquiv e) x).symm y))
      (extChartAt (I.transContinuousLinearEquiv e) x x)).Equivalent
      (chartHessianAt (fun y => f ((extChartAt I x).symm y)) (extChartAt I x x)) := by
  rw [chartHessianAt_transContinuousLinearEquiv I e hf hx hc]
  exact ⟨(QuadraticMap.isometryEquivOfCompLinearEquiv _ e.symm.toLinearEquiv).symm⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Morse.chartHessianAt_equivalent_transContinuousLinearEquiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Morse.chartHessianAt_equivalent_transContinuousLinearEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Morse.chartHessianAt_equivalent_transContinuousLinearEquiv ``Submission.DifferentialGeometry.Morse.chartHessianAt_equivalent_transContinuousLinearEquiv


theorem sigNeg_chartHessianAt_transContinuousLinearEquiv {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {x : M} (hx : I.IsInteriorPoint x)
    (hc : IsCriticalPointAt I f x) :
    sigNeg (chartHessianAt (fun y => f ((extChartAt (I.transContinuousLinearEquiv e) x).symm y))
      (extChartAt (I.transContinuousLinearEquiv e) x x)) =
      sigNeg (chartHessianAt (fun y => f ((extChartAt I x).symm y)) (extChartAt I x x)) :=
  (chartHessianAt_equivalent_transContinuousLinearEquiv I e hf hx hc).sigNeg_eq

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Morse.sigNeg_chartHessianAt_transContinuousLinearEquiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Morse.sigNeg_chartHessianAt_transContinuousLinearEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Morse.sigNeg_chartHessianAt_transContinuousLinearEquiv ``Submission.DifferentialGeometry.Morse.sigNeg_chartHessianAt_transContinuousLinearEquiv


theorem isNondegenerateCriticalPointAt_transContinuousLinearEquiv_iff {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {x : M} (hx : I.IsInteriorPoint x) :
    IsNondegenerateCriticalPointAt (I.transContinuousLinearEquiv e) f x ↔
      IsNondegenerateCriticalPointAt I f x := by
  unfold IsNondegenerateCriticalPointAt
  rw [isCriticalPointAt_transContinuousLinearEquiv_iff I e f x]
  by_cases hc : IsCriticalPointAt I f x
  · simp only [hc, true_and]
    rw [chartHessianAt_transContinuousLinearEquiv I e hf hx hc, QuadraticMap.associated_comp]
    convert! LinearMap.separatingLeft_congr_iff
      (B := QuadraticMap.associated (R := ℝ)
        (chartHessianAt (fun y => f ((extChartAt I x).symm y)) (extChartAt I x x)))
      e.toLinearEquiv e.toLinearEquiv using 1
  · simp only [hc, false_and]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Morse.isNondegenerateCriticalPointAt_transContinuousLinearEquiv_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Morse.isNondegenerateCriticalPointAt_transContinuousLinearEquiv_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Morse.isNondegenerateCriticalPointAt_transContinuousLinearEquiv_iff ``Submission.DifferentialGeometry.Morse.isNondegenerateCriticalPointAt_transContinuousLinearEquiv_iff
end DifferentialGeometry.Morse
