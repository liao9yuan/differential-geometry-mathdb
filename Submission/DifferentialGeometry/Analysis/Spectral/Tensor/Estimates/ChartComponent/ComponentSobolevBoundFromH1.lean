import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.Estimates.ChartComponent.ComponentL2BoundUniform
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.ChartTensor.ChartGeometry.IntrinsicL2Bridge
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.Variational.H1Compl
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.Variational.PreHilbert
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.Estimates.ChartComponent.ComponentSobolevBound
import Submission.DifferentialGeometry.Analysis.Integration.L2.SmoothSections.PreHilbert
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission


noncomputable section


open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.MeasureTheory _root_.Set _root_.Filter _root_.Submission.DifferentialGeometry.Tensor0SBundle
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.ENNReal _root_.NNReal _root_.BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.L2
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.Chart

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
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

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
private lemma abs_pou_mul_le_abs_local
    (β : M) (u : M → ℝ) (x : M) :
    |((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M β
        : C^∞⟮I, M; ℝ⟯) : M → ℝ) x * u x| ≤ |u x| := by
  rw [abs_mul]
  have hρ_nn : 0 ≤ ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M β
      : C^∞⟮I, M; ℝ⟯) : M → ℝ) x :=
    (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M).nonneg β x
  have hρ_le : ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M β
      : C^∞⟮I, M; ℝ⟯) : M → ℝ) x ≤ 1 :=
    (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M).le_one β x
  have hρ_abs_le_one : |((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M β
      : C^∞⟮I, M; ℝ⟯) : M → ℝ) x| ≤ 1 := by
    rw [abs_of_nonneg hρ_nn]; exact hρ_le
  calc |((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M β
            : C^∞⟮I, M; ℝ⟯) : M → ℝ) x| * |u x|
      ≤ 1 * |u x| := by gcongr
    _ = |u x| := one_mul _

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.abs_pou_mul_le_abs_local
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.abs_pou_mul_le_abs_local target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem eLpNorm_chartPushed_le_const_mul_eLpNorm_riemannianVolumeMeasure_uniform
    (g : SmoothRiemannianMetric I M) (β : M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (u : M → ℝ) (_hu_meas : Measurable u),
        _root_.MeasureTheory.eLpNorm
            (chartPushed (I := I) (M := M) (chartAtlasPOU I M) β u) 2
            ((_root_.MeasureTheory.MeasureSpace.volume :
                _root_.MeasureTheory.Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))).restrict
              (chartTargetEuclid (I := I) (M := M) β)) ≤
          ENNReal.ofReal C *
            eLpNorm u 2 (riemannianVolumeMeasure (I := I) (M := M) g) := by
  classical
  set ρ : C^∞⟮I, M; ℝ⟯ :=
    DifferentialGeometry.Integral.Measure.chartAtlasPOU I M β with hρ_def
  set Kβ : Set M := tsupport ((ρ : C^∞⟮I, M; ℝ⟯) : M → ℝ) with hKβ_def
  have hKβ_compact : IsCompact Kβ := (isClosed_tsupport _).isCompact
  have hKβ_sub : Kβ ⊆ (chartAt H β).source :=
    DifferentialGeometry.Integral.Measure.chartAtlasPOU_isSubordinate I M β
  have hp_one : (1 : ℝ≥0∞) ≤ 2 := by norm_num
  have hp_top : (2 : ℝ≥0∞) ≠ ⊤ := by decide
  obtain ⟨C, hC_pos, hC_bound⟩ :=
    eLpNorm_chartPushedRaw_le_const_mul_eLpNorm_riemannianMeasure_uniform_of_subset
      (I := I) (M := M) g β hKβ_compact hKβ_sub hp_one hp_top
  refine ⟨C, hC_pos.le, ?_⟩
  intro u hu_meas
  set f : M → ℝ := fun x : M => ((ρ : C^∞⟮I, M; ℝ⟯) : M → ℝ) x * u x with hf_def
  have hρ_cont : Continuous ((ρ : C^∞⟮I, M; ℝ⟯) : M → ℝ) :=
    (ρ.contMDiff).continuous
  have hf_meas : Measurable f := hρ_cont.measurable.mul hu_meas
  have hf_support : tsupport f ⊆ Kβ := by
    have h_eq : f = (fun x : M => ((ρ : C^∞⟮I, M; ℝ⟯) : M → ℝ) x • u x) := by
      funext x; rfl
    rw [h_eq]
    exact tsupport_smul_subset_left
      (f := fun x : M => ((ρ : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) (g := u)
  have h_raw_bound := hC_bound (u := f) hf_meas hf_support
  rw [show DifferentialGeometry.Integral.Measure.riemannianMeasure (I := I) g
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M)
        = DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure I M g from rfl]
    at h_raw_bound
  have h_ae :=
    DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed_eq_chartPushedRaw_pou_ae
      (I := I) (M := M)
      (ρ := DifferentialGeometry.Integral.Measure.chartAtlasPOU I M)
      β u
  rw [_root_.MeasureTheory.eLpNorm_congr_ae h_ae]
  refine h_raw_bound.trans ?_
  gcongr
  refine _root_.MeasureTheory.eLpNorm_mono (f := f) (g := u) ?_
  intro x
  have h_norm_f : ‖f x‖ = |((ρ : C^∞⟮I, M; ℝ⟯) : M → ℝ) x * u x| := Real.norm_eq_abs _
  have h_norm_u : ‖u x‖ = |u x| := Real.norm_eq_abs _
  rw [h_norm_f, h_norm_u]
  exact abs_pou_mul_le_abs_local (I := I) (M := M) β u x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eLpNorm_chartPushed_le_const_mul_eLpNorm_riemannianVolumeMeasure_uniform then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eLpNorm_chartPushed_le_const_mul_eLpNorm_riemannianVolumeMeasure_uniform"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eLpNorm_chartPushed_le_const_mul_eLpNorm_riemannianVolumeMeasure_uniform ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eLpNorm_chartPushed_le_const_mul_eLpNorm_riemannianVolumeMeasure_uniform

private lemma coe_nnnorm_eq_ofReal_norm {X : Type*} [SeminormedAddCommGroup X]
    (x : X) :
    (‖x‖₊ : ℝ≥0∞) = ENNReal.ofReal ‖x‖ := by
  rw [show ((‖x‖₊ : ℝ≥0∞)) = ‖x‖ₑ from (enorm_eq_nnnorm x).symm,
    ← ofReal_norm x]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.coe_nnnorm_eq_ofReal_norm
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.coe_nnnorm_eq_ofReal_norm target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
private lemma ofReal_tensorL2Norm_toFun_eq_nnnorm_toCcTensor
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensorH1 g r s) :
    ENNReal.ofReal (tensorL2Norm (I := I) (M := M) g r s S.toCcTensor.toFun) =
      (‖S.toCcTensor‖₊ : ℝ≥0∞) := by
  have h_norm_eq :
      ‖S.toCcTensor‖ = tensorL2Norm (I := I) (M := M) g r s S.toCcTensor.toFun :=
    SmoothCcTensor.norm_def (I := I) (M := M) S.toCcTensor
  rw [← h_norm_eq, ← coe_nnnorm_eq_ofReal_norm]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ofReal_tensorL2Norm_toFun_eq_nnnorm_toCcTensor
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ofReal_tensorL2Norm_toFun_eq_nnnorm_toCcTensor target :: scope.openDecls } }

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma nnnorm_toCcTensor_le_nnnorm
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensorH1 g r s) :
    (‖S.toCcTensor‖₊ : ℝ≥0∞) ≤ (‖S‖₊ : ℝ≥0∞) := by
  have h_real : ‖S.toCcTensor‖ ≤ ‖S‖ :=
    SmoothCcTensorH1.l2Norm_le_h1Norm (I := I) (M := M) S
  rw [coe_nnnorm_eq_ofReal_norm, coe_nnnorm_eq_ofReal_norm]
  exact ENNReal.ofReal_le_ofReal h_real

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.nnnorm_toCcTensor_le_nnnorm
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.nnnorm_toCcTensor_le_nnnorm target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] in
theorem eLpNorm_chartPushed_tensorChartComponentScalar_le_const_mul_h1Norm
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α β : M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (S : SmoothCcTensorH1 g r s)
        (Idx : Fin r → Fin (Module.finrank ℝ E))
        (Jdx : Fin s → Fin (Module.finrank ℝ E)),
        _root_.MeasureTheory.eLpNorm
            (chartPushed (I := I) (M := M) (chartAtlasPOU I M) β
              (tensorChartComponentScalar (I := I) (M := M)
                g r s S.toCcTensor α Idx Jdx)) 2
            ((_root_.MeasureTheory.MeasureSpace.volume :
                _root_.MeasureTheory.Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))).restrict
              (chartTargetEuclid (I := I) (M := M) β)) ≤
          ENNReal.ofReal C * (‖S‖₊ : ℝ≥0∞) := by
  classical
  obtain ⟨C₁, hC₁_nn, hC₁_uniform⟩ :=
    eLpNorm_chartPushed_le_const_mul_eLpNorm_riemannianVolumeMeasure_uniform
      (I := I) (M := M) g β
  obtain ⟨C₂, hC₂_nn, h_man⟩ :=
    tensorChartComponentScalar_eLpNorm_le_uniform
      (I := I) (M := M) (E := E) g r s α
  refine ⟨C₁ * C₂, mul_nonneg hC₁_nn hC₂_nn, ?_⟩
  intro S Idx Jdx
  set u : M → ℝ :=
    tensorChartComponentScalar (I := I) (M := M) g r s S.toCcTensor α Idx Jdx
    with hu_def
  have hu_meas : Measurable u :=
    (tensorChartComponentScalar_contMDiff (I := I) (M := M)
      g r s S.toCcTensor α Idx Jdx).continuous.measurable
  have hA :
      _root_.MeasureTheory.eLpNorm
          (chartPushed (I := I) (M := M) (chartAtlasPOU I M) β u) 2
          ((_root_.MeasureTheory.MeasureSpace.volume :
              _root_.MeasureTheory.Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))).restrict
            (chartTargetEuclid (I := I) (M := M) β)) ≤
        ENNReal.ofReal C₁ *
          eLpNorm u 2 (riemannianVolumeMeasure (I := I) (M := M) g) :=
    hC₁_uniform u hu_meas
  have hB :
      eLpNorm u 2 (riemannianVolumeMeasure (I := I) (M := M) g) ≤
        ENNReal.ofReal C₂ *
          ENNReal.ofReal
            (tensorL2Norm (I := I) (M := M) g r s S.toCcTensor.toFun) := by
    rw [hu_def]
    exact h_man S.toCcTensor Idx Jdx
  have hAB :
      _root_.MeasureTheory.eLpNorm
          (chartPushed (I := I) (M := M) (chartAtlasPOU I M) β u) 2
          ((_root_.MeasureTheory.MeasureSpace.volume :
              _root_.MeasureTheory.Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))).restrict
            (chartTargetEuclid (I := I) (M := M) β)) ≤
        ENNReal.ofReal C₁ *
          (ENNReal.ofReal C₂ *
            ENNReal.ofReal
              (tensorL2Norm (I := I) (M := M) g r s S.toCcTensor.toFun)) := by
    calc _root_.MeasureTheory.eLpNorm
            (chartPushed (I := I) (M := M) (chartAtlasPOU I M) β u) 2
            ((_root_.MeasureTheory.MeasureSpace.volume :
                _root_.MeasureTheory.Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))).restrict
              (chartTargetEuclid (I := I) (M := M) β))
        ≤ ENNReal.ofReal C₁ *
            eLpNorm u 2 (riemannianVolumeMeasure (I := I) (M := M) g) := hA
      _ ≤ ENNReal.ofReal C₁ *
            (ENNReal.ofReal C₂ *
              ENNReal.ofReal
                (tensorL2Norm (I := I) (M := M) g r s S.toCcTensor.toFun)) :=
          mul_le_mul_of_nonneg_left hB (by exact zero_le)
  have h_eq :
      ENNReal.ofReal
          (tensorL2Norm (I := I) (M := M) g r s S.toCcTensor.toFun) =
        (‖S.toCcTensor‖₊ : ℝ≥0∞) :=
    ofReal_tensorL2Norm_toFun_eq_nnnorm_toCcTensor
      (I := I) (M := M) g r s S
  have h_le :
      (‖S.toCcTensor‖₊ : ℝ≥0∞) ≤ (‖S‖₊ : ℝ≥0∞) :=
    nnnorm_toCcTensor_le_nnnorm (I := I) (M := M) g r s S
  refine hAB.trans ?_
  rw [h_eq]
  calc ENNReal.ofReal C₁ *
          (ENNReal.ofReal C₂ * (‖S.toCcTensor‖₊ : ℝ≥0∞))
      = (ENNReal.ofReal C₁ * ENNReal.ofReal C₂) *
            (‖S.toCcTensor‖₊ : ℝ≥0∞) := by
        rw [mul_assoc]
    _ = ENNReal.ofReal (C₁ * C₂) * (‖S.toCcTensor‖₊ : ℝ≥0∞) := by
        rw [(ENNReal.ofReal_mul hC₁_nn).symm]
    _ ≤ ENNReal.ofReal (C₁ * C₂) * (‖S‖₊ : ℝ≥0∞) :=
        mul_le_mul_of_nonneg_left h_le (by exact zero_le)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eLpNorm_chartPushed_tensorChartComponentScalar_le_const_mul_h1Norm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eLpNorm_chartPushed_tensorChartComponentScalar_le_const_mul_h1Norm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eLpNorm_chartPushed_tensorChartComponentScalar_le_const_mul_h1Norm ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eLpNorm_chartPushed_tensorChartComponentScalar_le_const_mul_h1Norm

omit [NeZero (Module.finrank ℝ E)] in
theorem eLpNorm_chartPushed_tensorChartComponentScalar_le_const_mul_h1Norm_forall
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α β : M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ S : SmoothCcTensorH1 g r s,
        ∀ (Idx : Fin r → Fin (Module.finrank ℝ E))
          (Jdx : Fin s → Fin (Module.finrank ℝ E)),
          _root_.MeasureTheory.eLpNorm
              (chartPushed (I := I) (M := M) (chartAtlasPOU I M) β
                (tensorChartComponentScalar (I := I) (M := M)
                  g r s S.toCcTensor α Idx Jdx)) 2
              ((_root_.MeasureTheory.MeasureSpace.volume :
                  _root_.MeasureTheory.Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))).restrict
                (chartTargetEuclid (I := I) (M := M) β)) ≤
            ENNReal.ofReal C * (‖S‖₊ : ℝ≥0∞) :=
  eLpNorm_chartPushed_tensorChartComponentScalar_le_const_mul_h1Norm
    (I := I) (M := M) g r s α β

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eLpNorm_chartPushed_tensorChartComponentScalar_le_const_mul_h1Norm_forall then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eLpNorm_chartPushed_tensorChartComponentScalar_le_const_mul_h1Norm_forall"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eLpNorm_chartPushed_tensorChartComponentScalar_le_const_mul_h1Norm_forall ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eLpNorm_chartPushed_tensorChartComponentScalar_le_const_mul_h1Norm_forall

omit [NeZero (Module.finrank ℝ E)] in
theorem eLpNorm_chartPushed_tensorChartComponentScalar_le_const_mul_h1Norm_single_chart
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (S : SmoothCcTensorH1 g r s)
        (Idx : Fin r → Fin (Module.finrank ℝ E))
        (Jdx : Fin s → Fin (Module.finrank ℝ E)),
        _root_.MeasureTheory.eLpNorm
            (chartPushed (I := I) (M := M) (chartAtlasPOU I M) α
              (tensorChartComponentScalar (I := I) (M := M)
                g r s S.toCcTensor α Idx Jdx)) 2
            ((_root_.MeasureTheory.MeasureSpace.volume :
                _root_.MeasureTheory.Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))).restrict
              (chartTargetEuclid (I := I) (M := M) α)) ≤
          ENNReal.ofReal C * (‖S‖₊ : ℝ≥0∞) :=
  eLpNorm_chartPushed_tensorChartComponentScalar_le_const_mul_h1Norm
    (I := I) (M := M) g r s α α

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eLpNorm_chartPushed_tensorChartComponentScalar_le_const_mul_h1Norm_single_chart then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eLpNorm_chartPushed_tensorChartComponentScalar_le_const_mul_h1Norm_single_chart"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eLpNorm_chartPushed_tensorChartComponentScalar_le_const_mul_h1Norm_single_chart ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eLpNorm_chartPushed_tensorChartComponentScalar_le_const_mul_h1Norm_single_chart

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
