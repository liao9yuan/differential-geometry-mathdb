import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.AbstractChartPullCutoff
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.ChartPartial.UniformBound
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.Estimates.ChristoffelCorrection.CovL2BoundFromH1
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.Estimates.ChristoffelCorrection.ChristoffelBound
import Submission.DifferentialGeometry.Analysis.Elliptic.TensorRegularity.CovDeriv.ChartFormLowerOrder
import Submission.DifferentialGeometry.Analysis.Elliptic.Regularity.SmoothFChartResidual.BilinearBound

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Geometry.Curvature

noncomputable section


open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.MeasureTheory _root_.Set _root_.Filter _root_.Submission.DifferentialGeometry.Tensor0SBundle
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.ENNReal _root_.NNReal _root_.BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.DivergenceTheorem
open _root_.Submission.DifferentialGeometry.Integral.L2

open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.Chart
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.TensorRegularity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

private local instance _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instMeasurableSpace_differentialGeometry : MeasurableSpace E := borel E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instMeasurableSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instMeasurableSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instBorelSpace_differentialGeometry : BorelSpace E := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instBorelSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instBorelSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instMeasurableSpace_differentialGeometry_1 : MeasurableSpace M := borel M

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instMeasurableSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instMeasurableSpace_differentialGeometry_1 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instBorelSpace_differentialGeometry_1 : BorelSpace M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instBorelSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instBorelSpace_differentialGeometry_1 target :: scope.openDecls } }

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

lemma eLpNorm_add_add_sub_le
    {β : Type*} [MeasurableSpace β] {ν : _root_.MeasureTheory.Measure β} {a b c : β → ℝ}
    (ha : _root_.MeasureTheory.AEStronglyMeasurable a ν) (hb : _root_.MeasureTheory.AEStronglyMeasurable b ν)
    (hc : _root_.MeasureTheory.AEStronglyMeasurable c ν) :
    _root_.MeasureTheory.eLpNorm (fun y => a y + b y - c y) 2 ν ≤
      eLpNorm a 2 ν + _root_.MeasureTheory.eLpNorm b 2 ν + _root_.MeasureTheory.eLpNorm c 2 ν := by
  have h_ab : _root_.MeasureTheory.eLpNorm (fun y => a y + b y) 2 ν ≤
      eLpNorm a 2 ν + _root_.MeasureTheory.eLpNorm b 2 ν :=
    _root_.MeasureTheory.eLpNorm_add_le ha hb (by norm_num)
  have h_full : _root_.MeasureTheory.eLpNorm (fun y => (a y + b y) - c y) 2 ν ≤
      eLpNorm (fun y => a y + b y) 2 ν + _root_.MeasureTheory.eLpNorm c 2 ν :=
    _root_.MeasureTheory.eLpNorm_sub_le (ha.add hb) hc (by norm_num)
  exact h_full.trans (by gcongr)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eLpNorm_add_add_sub_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eLpNorm_add_add_sub_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eLpNorm_add_add_sub_le ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eLpNorm_add_add_sub_le

lemma abs_prod_kronecker_le_one
    {ι : Type*} (t : Finset ι) (f : ι → Prop) [DecidablePred f] :
    |∏ i ∈ t, (if f i then (1 : ℝ) else 0)| ≤ 1 := by
  classical
  induction t using Finset.induction with
  | empty => simp
  | insert i t hi ih =>
      rw [Finset.prod_insert hi, abs_mul]
      by_cases hf : f i
      · rw [if_pos hf, abs_one, one_mul]; exact ih
      · rw [if_neg hf, abs_zero, _root_.MulZeroClass.zero_mul]; exact zero_le_one

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.abs_prod_kronecker_le_one then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.abs_prod_kronecker_le_one"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.abs_prod_kronecker_le_one ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.abs_prod_kronecker_le_one

private lemma abs_kronecker_le_one' {P : Prop} [Decidable P] :
    |if P then (1 : ℝ) else 0| ≤ 1 := by
  by_cases h : P
  · rw [if_pos h, abs_one]
  · rw [if_neg h, abs_zero]; exact zero_le_one

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.abs_kronecker_le_one'
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.abs_kronecker_le_one' target :: scope.openDecls } }

lemma abs_sum_coeff_kronecker_le
    {ι : Type*} (t : Finset ι) (f : ι → ℝ) (P : ι → Prop) [DecidablePred P]
    {Cχ : ℝ} (hCχ_nn : 0 ≤ Cχ) (hf : ∀ i ∈ t, |f i| ≤ Cχ) :
    |∑ i ∈ t, f i * (if P i then (1 : ℝ) else 0)| ≤ t.card * Cχ := by
  classical
  have hbound : ∀ i ∈ t,
      |f i * (if P i then (1 : ℝ) else 0)| ≤ Cχ := by
    intro i hi
    rw [abs_mul]
    calc |f i| * |if P i then (1 : ℝ) else 0|
        ≤ Cχ * 1 :=
          mul_le_mul (hf i hi) abs_kronecker_le_one' (abs_nonneg _) hCχ_nn
      _ = Cχ := mul_one _
  calc |∑ i ∈ t, f i * (if P i then (1 : ℝ) else 0)|
      ≤ ∑ i ∈ t, |f i * (if P i then (1 : ℝ) else 0)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i ∈ t, Cχ := Finset.sum_le_sum hbound
    _ = t.card * Cχ := by rw [Finset.sum_const, nsmul_eq_mul]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.abs_sum_coeff_kronecker_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.abs_sum_coeff_kronecker_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.abs_sum_coeff_kronecker_le ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.abs_sum_coeff_kronecker_le

lemma le_rpow_half_of_sq_le {x y : ℝ≥0∞} (h : x ^ 2 ≤ y) :
    x ≤ y ^ ((1 : ℝ) / 2) := by
  have h_xpow : x = (x ^ 2) ^ ((1 : ℝ) / 2) := by
    rw [← ENNReal.rpow_natCast x 2, ← ENNReal.rpow_mul]
    norm_num
  conv_lhs => rw [h_xpow]
  exact ENNReal.rpow_le_rpow h (by norm_num)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.le_rpow_half_of_sq_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.le_rpow_half_of_sq_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.le_rpow_half_of_sq_le ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.le_rpow_half_of_sq_le

lemma ofReal_rpow_half_eq_ofReal_sqrt {a : ℝ} (ha : 0 ≤ a) :
    (ENNReal.ofReal a) ^ ((1 : ℝ) / 2) = ENNReal.ofReal (Real.sqrt a) := by
  rw [show a = Real.sqrt a * Real.sqrt a from (Real.mul_self_sqrt ha).symm,
    ENNReal.ofReal_mul (Real.sqrt_nonneg _),
    show (ENNReal.ofReal (Real.sqrt a)) * (ENNReal.ofReal (Real.sqrt a)) =
      (ENNReal.ofReal (Real.sqrt a)) ^ 2 from by ring,
    ← ENNReal.rpow_natCast _ 2, ← ENNReal.rpow_mul]
  norm_num

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ofReal_rpow_half_eq_ofReal_sqrt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ofReal_rpow_half_eq_ofReal_sqrt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ofReal_rpow_half_eq_ofReal_sqrt ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ofReal_rpow_half_eq_ofReal_sqrt

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
