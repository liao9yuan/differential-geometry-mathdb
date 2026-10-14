import Submission.DifferentialGeometry.Analysis.Heat.Smoothing.Scalar.HeatFlow
import Submission.DifferentialGeometry.Analysis.Sobolev.TensorHilbert.OperatorField.Parametric.ScalarSmulJet
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Jet.Bounds.IteratedCovariantDerivative
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.MeasureTheory _root_.Submission.MeasureTheory
open scoped _root_.ENNReal _root_.Manifold _root_.Submission.Manifold _root_.ContDiff

namespace DifferentialGeometry.Analysis.Spectral

open _root_.Submission.DifferentialGeometry.Analysis.HeatEquation
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open _root_.Submission.DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (∞ : WithTop ℕ∞) M]
  [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]

private local instance _root_.Submission.DifferentialGeometry.Analysis.Spectral.instMeasurableSpace_differentialGeometry : MeasurableSpace M := borel M

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Spectral.instMeasurableSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Spectral.instMeasurableSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Spectral.instBorelSpace_differentialGeometry : BorelSpace M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Spectral.instBorelSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Spectral.instBorelSpace_differentialGeometry target :: scope.openDecls } }

private local instance _root_.Submission.DifferentialGeometry.Analysis.Spectral.instIsFiniteMeasureRiemannianVolumeMeasure (g : SmoothRiemannianMetric I M) :
    IsFiniteMeasure (riemannianVolumeMeasure I M g) :=
  riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace g

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Spectral.instIsFiniteMeasureRiemannianVolumeMeasure
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Spectral.instIsFiniteMeasureRiemannianVolumeMeasure target :: scope.openDecls } }

def scalarH0EquivLp (g : SmoothRiemannianMetric I M) :
    TensorHs g 0 0 0 ≃ₗᵢ[ℝ] _root_.MeasureTheory.Lp ℝ 2 (riemannianVolumeMeasure I M g) :=
  (tensorHsZeroEquivL2 (tensorResolventL2_isCompactOperator g 0 0)).trans
    (tensor00ScalarL2Equiv g)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.scalarH0EquivLp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.scalarH0EquivLp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.scalarH0EquivLp ``Submission.DifferentialGeometry.Analysis.Spectral.scalarH0EquivLp

def scalarH0ContinuousMul (g : SmoothRiemannianMetric I M) :
    C(M, ℝ) →L[ℝ] TensorHs g 0 0 0 →L[ℝ] TensorHs g 0 0 0 :=
  let e := (scalarH0EquivLp g).symm.toContinuousLinearEquiv
  (ContinuousLinearEquiv.arrowCongr e e).toContinuousLinearMap.comp
    ((ContinuousLinearMap.holderL (riemannianVolumeMeasure I M g) ∞ 2 2 (ContinuousLinearMap.mul ℝ ℝ)).comp
      (ContinuousMap.toLp ∞ (riemannianVolumeMeasure I M g) ℝ))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.scalarH0ContinuousMul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.scalarH0ContinuousMul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.scalarH0ContinuousMul ``Submission.DifferentialGeometry.Analysis.Spectral.scalarH0ContinuousMul

theorem scalarH0EquivLp_scalarH0ContinuousMul (g : SmoothRiemannianMetric I M)
    (a : C(M, ℝ)) (u : TensorHs g 0 0 0) :
    scalarH0EquivLp g (scalarH0ContinuousMul g a u) =ᵐ[riemannianVolumeMeasure I M g]
      fun x => a x * scalarH0EquivLp g u x := by
  change (scalarH0EquivLp g)
    ((scalarH0EquivLp g).symm
      ((ContinuousLinearMap.mul ℝ ℝ).holder 2
        (ContinuousMap.toLp ∞ (riemannianVolumeMeasure I M g) ℝ a)
        (scalarH0EquivLp g u))) =ᵐ[_] _
  rw [LinearIsometryEquiv.apply_symm_apply]
  filter_upwards [(ContinuousLinearMap.coeFn_holder (μ := riemannianVolumeMeasure I M g) (p := ∞) (q := 2) (r := 2) (ContinuousLinearMap.mul ℝ ℝ)
    (ContinuousMap.toLp ∞ (riemannianVolumeMeasure I M g) ℝ a) (scalarH0EquivLp g u)),
    ContinuousMap.coeFn_toLp (𝕜 := ℝ) (p := ∞) (riemannianVolumeMeasure I M g) a] with x hx ha
  simpa only [ContinuousLinearMap.mul_apply', ha] using hx

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.scalarH0EquivLp_scalarH0ContinuousMul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.scalarH0EquivLp_scalarH0ContinuousMul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.scalarH0EquivLp_scalarH0ContinuousMul ``Submission.DifferentialGeometry.Analysis.Spectral.scalarH0EquivLp_scalarH0ContinuousMul

theorem norm_scalarH0ContinuousMul_apply_le (g : SmoothRiemannianMetric I M)
    (a : C(M, ℝ)) (u : TensorHs g 0 0 0) :
    ‖scalarH0ContinuousMul g a u‖ ≤ ‖a‖ * ‖u‖ := by
  rw [← (scalarH0EquivLp g).norm_map (scalarH0ContinuousMul g a u),
    ← (scalarH0EquivLp g).norm_map u]
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [scalarH0EquivLp_scalarH0ContinuousMul g a u] with x hx
  rw [hx, norm_mul]
  exact mul_le_mul_of_nonneg_right (ContinuousMap.norm_coe_le_norm a x) (norm_nonneg _)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.norm_scalarH0ContinuousMul_apply_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.norm_scalarH0ContinuousMul_apply_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.norm_scalarH0ContinuousMul_apply_le ``Submission.DifferentialGeometry.Analysis.Spectral.norm_scalarH0ContinuousMul_apply_le

theorem norm_scalarH0ContinuousMul_le (g : SmoothRiemannianMetric I M) :
    ‖scalarH0ContinuousMul g‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro a
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro u
  simpa only [one_mul] using norm_scalarH0ContinuousMul_apply_le g a u

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.norm_scalarH0ContinuousMul_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.norm_scalarH0ContinuousMul_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.norm_scalarH0ContinuousMul_le ``Submission.DifferentialGeometry.Analysis.Spectral.norm_scalarH0ContinuousMul_le

theorem scalarH0EquivLp_ccTensorToHs (g : SmoothRiemannianMetric I M)
    (S : DifferentialGeometry.Integral.L2.SmoothCcTensor g 0 0) :
    scalarH0EquivLp g (ccTensorToHs g 0 0 S) =ᵐ[riemannianVolumeMeasure I M g]
      DifferentialGeometry.Tensor0SBundle.TensorRSField.scalar0 S.toSection := by
  have h : tensorHsZeroEquivL2 (tensorResolventL2_isCompactOperator g 0 0)
      (ccTensorToHs g 0 0 S) = DifferentialGeometry.Integral.L2.SmoothCcTensor.toL2 S := by
    apply (tensorHsZeroEquivL2 (tensorResolventL2_isCompactOperator g 0 0)).symm.injective
    rw [LinearIsometryEquiv.symm_apply_apply]
    apply TensorHs.ext
    funext i
    rw [tensorHsZeroEquivL2_symm_coeff, ccTensorToHs_coeff]
  change (tensor00ScalarL2Equiv g
    (tensorHsZeroEquivL2 (tensorResolventL2_isCompactOperator g 0 0)
      (ccTensorToHs g 0 0 S)) : M → ℝ) =ᵐ[_] _
  rw [h]
  change (tensor00ToScalarL2 g
    (DifferentialGeometry.Integral.L2.SmoothCcTensor.toL2 S) : M → ℝ) =ᵐ[_] _
  rw [tensor00ToScalarL2_toL2]
  exact (scalar0Cc g S).memLp_two.coeFn_toLp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.scalarH0EquivLp_ccTensorToHs then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.scalarH0EquivLp_ccTensorToHs"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.scalarH0EquivLp_ccTensorToHs ``Submission.DifferentialGeometry.Analysis.Spectral.scalarH0EquivLp_ccTensorToHs

theorem scalarH0ContinuousMul_ccTensorToHs (g : SmoothRiemannianMetric I M)
    (a : C^∞⟮I, M; ℝ⟯) (S : DifferentialGeometry.Integral.L2.SmoothCcTensor g 0 0) :
    scalarH0ContinuousMul g ⟨a, a.2.continuous⟩ (ccTensorToHs g 0 0 S) =
      ccTensorToHs g 0 0
        (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.scalarSmul g 0 0 a S) := by
  apply (scalarH0EquivLp g).injective
  apply Lp.ext
  filter_upwards [scalarH0EquivLp_scalarH0ContinuousMul g ⟨a, a.2.continuous⟩
      (ccTensorToHs g 0 0 S), scalarH0EquivLp_ccTensorToHs g S,
    scalarH0EquivLp_ccTensorToHs g
      (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.scalarSmul g 0 0 a S)]
      with x hx hu hv
  rw [hx, hu, hv]
  exact (DifferentialGeometry.Analysis.Sobolev.scalar0_smul_cc g a S x).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.scalarH0ContinuousMul_ccTensorToHs then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.scalarH0ContinuousMul_ccTensorToHs"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.scalarH0ContinuousMul_ccTensorToHs ``Submission.DifferentialGeometry.Analysis.Spectral.scalarH0ContinuousMul_ccTensorToHs

end DifferentialGeometry.Analysis.Spectral
end

noncomputable section
open _root_.MeasureTheory _root_.Submission.MeasureTheory
open scoped _root_.ENNReal _root_.Manifold _root_.Submission.Manifold _root_.ContDiff
namespace DifferentialGeometry.Analysis.Spectral
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open _root_.Submission.DifferentialGeometry.Integral.Measure
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (∞ : WithTop ℕ∞) M]
  [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
private local instance _root_.Submission.DifferentialGeometry.Analysis.Spectral.instMeasurableSpace_differentialGeometry_1 : MeasurableSpace M := borel M

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Spectral.instMeasurableSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Spectral.instMeasurableSpace_differentialGeometry_1 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Spectral.instBorelSpace_differentialGeometry_1 : BorelSpace M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Spectral.instBorelSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Spectral.instBorelSpace_differentialGeometry_1 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Spectral.instIsFiniteMeasureRiemannianVolumeMeasure_1 (g : SmoothRiemannianMetric I M) :
    IsFiniteMeasure (riemannianVolumeMeasure I M g) :=
  riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace g

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Spectral.instIsFiniteMeasureRiemannianVolumeMeasure_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Spectral.instIsFiniteMeasureRiemannianVolumeMeasure_1 target :: scope.openDecls } }

theorem scalarH0ContinuousMul_const (g : SmoothRiemannianMetric I M)
    (c : ℝ) (u : TensorHs g 0 0 0) :
    scalarH0ContinuousMul g (ContinuousMap.const M c) u = c • u := by
  apply (scalarH0EquivLp g).injective
  rw [map_smul]
  apply Lp.ext
  filter_upwards [scalarH0EquivLp_scalarH0ContinuousMul g (ContinuousMap.const M c) u,
    Lp.coeFn_smul c (scalarH0EquivLp g u)] with x hx hs
  simpa only [ContinuousMap.const_apply, Pi.smul_apply, smul_eq_mul] using hx.trans hs.symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.scalarH0ContinuousMul_const then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.scalarH0ContinuousMul_const"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.scalarH0ContinuousMul_const ``Submission.DifferentialGeometry.Analysis.Spectral.scalarH0ContinuousMul_const

end DifferentialGeometry.Analysis.Spectral
end
