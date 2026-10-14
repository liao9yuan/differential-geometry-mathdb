import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.Estimates.ChartComponent.ComponentSobolevBound
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.Estimates.WeakPartial.ComponentSobolevBoundDerivBridge
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.Estimates.WeakPartial.PartialL2Transfer
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.Estimates.ChartComponent.ComponentL2BoundUniform
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.ChartTensor.ChartGeometry.IntrinsicL2Bridge

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
open _root_.Submission.DifferentialGeometry.Integral.L2
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.Chart

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
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

private lemma le_sum_of_mem_finset_nonneg
    {ι : Type*} [Fintype ι]
    (f : ι → ℝ) (hf_nn : ∀ i, 0 ≤ f i) (i : ι) :
    f i ≤ ∑ j, f j := by
  classical
  have hmem : i ∈ (Finset.univ : Finset ι) := Finset.mem_univ _
  have h_split :
      ∑ j, f j = f i + ∑ j ∈ Finset.univ.erase i, f j := by
    rw [← Finset.sum_erase_add _ _ hmem, add_comm]
  have h_rest_nn :
      0 ≤ ∑ j ∈ Finset.univ.erase i, f j :=
    Finset.sum_nonneg (fun j _ => hf_nn j)
  linarith

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.le_sum_of_mem_finset_nonneg
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.le_sum_of_mem_finset_nonneg target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] in
theorem tensorChartComponentScalar_wkpNormChart_le_per_section_improved
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (S : SmoothCcTensorH1 g r s) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (Idx : Fin r → Fin (Module.finrank ℝ E))
        (Jdx : Fin s → Fin (Module.finrank ℝ E)),
        wkpNormChart (I := I) (M := M) 1 2
            (tensorChartComponentScalar (I := I) (M := M)
              g r s S.toCcTensor α Idx Jdx) ≤
          ENNReal.ofReal C * (‖S‖₊ + 1) := by
  classical
  have hper : ∀ (IJ : (Fin r → Fin (Module.finrank ℝ E)) ×
                      (Fin s → Fin (Module.finrank ℝ E))),
      ∃ C : ℝ, 0 ≤ C ∧
        wkpNormChart (I := I) (M := M) 1 2
            (tensorChartComponentScalar (I := I) (M := M)
              g r s S.toCcTensor α IJ.1 IJ.2) ≤
          ENNReal.ofReal C * (‖S‖₊ + 1) := fun IJ =>
    tensorChartComponent_wkpNormChart_le_per_section
      (I := I) (M := M) g r s S α IJ.1 IJ.2
  choose CIJ hCIJ_nn hCIJ_le using hper
  set Csum : ℝ := ∑ IJ : (Fin r → Fin (Module.finrank ℝ E)) ×
                          (Fin s → Fin (Module.finrank ℝ E)),
    CIJ IJ with hCsum_def
  have hCsum_nn : 0 ≤ Csum :=
    Finset.sum_nonneg (fun IJ _ => hCIJ_nn IJ)
  refine ⟨Csum, hCsum_nn, ?_⟩
  intro Idx Jdx
  have hsmd : CIJ (Idx, Jdx) ≤ Csum :=
    le_sum_of_mem_finset_nonneg
      (f := fun IJ : (Fin r → Fin (Module.finrank ℝ E)) ×
                    (Fin s → Fin (Module.finrank ℝ E)) => CIJ IJ)
      (fun IJ => hCIJ_nn IJ) (Idx, Jdx)
  have h_ofReal_le : ENNReal.ofReal (CIJ (Idx, Jdx)) ≤
      ENNReal.ofReal Csum := ENNReal.ofReal_le_ofReal hsmd
  have h_envelope_le :
      ENNReal.ofReal (CIJ (Idx, Jdx)) * (‖S‖₊ + 1) ≤
        ENNReal.ofReal Csum * (‖S‖₊ + 1) :=
    mul_le_mul_of_nonneg_right h_ofReal_le (by exact zero_le)
  exact (hCIJ_le (Idx, Jdx)).trans h_envelope_le

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponentScalar_wkpNormChart_le_per_section_improved then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponentScalar_wkpNormChart_le_per_section_improved"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponentScalar_wkpNormChart_le_per_section_improved ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponentScalar_wkpNormChart_le_per_section_improved

omit [NeZero (Module.finrank ℝ E)] in
theorem tensorChartComponentScalar_wkpNormChart_le_per_section_improved_forall
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M) :
    ∀ S : SmoothCcTensorH1 g r s,
      ∃ C : ℝ, 0 ≤ C ∧
        ∀ (Idx : Fin r → Fin (Module.finrank ℝ E))
          (Jdx : Fin s → Fin (Module.finrank ℝ E)),
          wkpNormChart (I := I) (M := M) 1 2
              (tensorChartComponentScalar (I := I) (M := M)
                g r s S.toCcTensor α Idx Jdx) ≤
            ENNReal.ofReal C * (‖S‖₊ + 1) := fun S =>
  tensorChartComponentScalar_wkpNormChart_le_per_section_improved
    (I := I) (M := M) g r s α S

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponentScalar_wkpNormChart_le_per_section_improved_forall then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponentScalar_wkpNormChart_le_per_section_improved_forall"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponentScalar_wkpNormChart_le_per_section_improved_forall ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponentScalar_wkpNormChart_le_per_section_improved_forall

omit [NeZero (Module.finrank ℝ E)] in
theorem sum_tensorChartComponentScalar_wkpNormChart_le_per_section
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (S : SmoothCcTensorH1 g r s) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∑ IJ : (Fin r → Fin (Module.finrank ℝ E)) ×
              (Fin s → Fin (Module.finrank ℝ E)),
        wkpNormChart (I := I) (M := M) 1 2
            (tensorChartComponentScalar (I := I) (M := M)
              g r s S.toCcTensor α IJ.1 IJ.2) ≤
        ENNReal.ofReal C * (‖S‖₊ + 1) := by
  classical
  obtain ⟨C, hC_nn, hC_le⟩ :=
    tensorChartComponentScalar_wkpNormChart_le_per_section_improved
      (I := I) (M := M) g r s α S
  set N : ℕ := Fintype.card ((Fin r → Fin (Module.finrank ℝ E)) ×
                              (Fin s → Fin (Module.finrank ℝ E))) with hN_def
  refine ⟨(N : ℝ) * C, mul_nonneg (Nat.cast_nonneg _) hC_nn, ?_⟩
  have h_sum_le :
      ∑ IJ : (Fin r → Fin (Module.finrank ℝ E)) ×
              (Fin s → Fin (Module.finrank ℝ E)),
        wkpNormChart (I := I) (M := M) 1 2
            (tensorChartComponentScalar (I := I) (M := M)
              g r s S.toCcTensor α IJ.1 IJ.2) ≤
      ∑ _IJ : (Fin r → Fin (Module.finrank ℝ E)) ×
              (Fin s → Fin (Module.finrank ℝ E)),
        ENNReal.ofReal C * (‖S‖₊ + 1) :=
    Finset.sum_le_sum (fun IJ _ => hC_le IJ.1 IJ.2)
  refine h_sum_le.trans ?_
  rw [Finset.sum_const, Finset.card_univ]
  change (N : ℕ) • (ENNReal.ofReal C * (‖S‖₊ + 1)) ≤
      ENNReal.ofReal ((N : ℝ) * C) * (‖S‖₊ + 1)
  rw [nsmul_eq_mul]
  have hN_ofReal : (N : ℝ≥0∞) = ENNReal.ofReal (N : ℝ) := by
    rw [ENNReal.ofReal_natCast]
  rw [hN_ofReal]
  rw [show ENNReal.ofReal (N : ℝ) * (ENNReal.ofReal C * (‖S‖₊ + 1)) =
        (ENNReal.ofReal (N : ℝ) * ENNReal.ofReal C) * (‖S‖₊ + 1) from
      (mul_assoc _ _ _).symm]
  rw [show ENNReal.ofReal (N : ℝ) * ENNReal.ofReal C =
        ENNReal.ofReal ((N : ℝ) * C) from
      (ENNReal.ofReal_mul (Nat.cast_nonneg _)).symm]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.sum_tensorChartComponentScalar_wkpNormChart_le_per_section then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.sum_tensorChartComponentScalar_wkpNormChart_le_per_section"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.sum_tensorChartComponentScalar_wkpNormChart_le_per_section ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.sum_tensorChartComponentScalar_wkpNormChart_le_per_section

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
