import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.Estimates.ChartComponent.ComponentSobolevPointwise
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.Estimates.WeakPartial.ComponentSobolevBoundDerivBridge
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
theorem exists_const_eLpNorm_chosenWeakPartialOrZero_chartPushed_le_uniform_indices
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensorH1 g r s) (α β : M)
    (k : Fin (Module.finrank ℝ E)) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (Idx : Fin r → Fin (Module.finrank ℝ E))
        (Jdx : Fin s → Fin (Module.finrank ℝ E)),
        _root_.MeasureTheory.eLpNorm
            (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartialOrZero
              (d := Module.finrank ℝ E) 2 k
              (chartPushed (I := I) (M := M) (chartAtlasPOU I M) β
                (tensorChartComponentScalar (I := I) (M := M)
                  g r s S.toCcTensor α Idx Jdx))
              (chartTargetEuclid (I := I) (M := M) β)) 2
            (volume.restrict (chartTargetEuclid (I := I) (M := M) β)) ≤
          ENNReal.ofReal C * (‖S‖₊ + 1) := by
  classical
  have hper : ∀ (IJ : (Fin r → Fin (Module.finrank ℝ E)) ×
                      (Fin s → Fin (Module.finrank ℝ E))),
      ∃ C : ℝ, 0 ≤ C ∧
        _root_.MeasureTheory.eLpNorm
            (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartialOrZero
              (d := Module.finrank ℝ E) 2 k
              (chartPushed (I := I) (M := M) (chartAtlasPOU I M) β
                (tensorChartComponentScalar (I := I) (M := M)
                  g r s S.toCcTensor α IJ.1 IJ.2))
              (chartTargetEuclid (I := I) (M := M) β)) 2
            (volume.restrict (chartTargetEuclid (I := I) (M := M) β)) ≤
          ENNReal.ofReal C * (‖S‖₊ + 1) := fun IJ =>
    eLpNorm_chosenWeakPartialOrZero_chartPushed_tensorChartComponentScalar_le_per_section
      (I := I) (M := M) g r s S α β IJ.1 IJ.2 k
  choose CIJ hCIJ_nn hCIJ_le using hper
  set Csum : ℝ := ∑ IJ : (Fin r → Fin (Module.finrank ℝ E)) ×
                          (Fin s → Fin (Module.finrank ℝ E)),
    CIJ IJ with hCsum_def
  refine ⟨Csum, Finset.sum_nonneg (fun IJ _ => hCIJ_nn IJ), ?_⟩
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
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.exists_const_eLpNorm_chosenWeakPartialOrZero_chartPushed_le_uniform_indices then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.exists_const_eLpNorm_chosenWeakPartialOrZero_chartPushed_le_uniform_indices"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.exists_const_eLpNorm_chosenWeakPartialOrZero_chartPushed_le_uniform_indices ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.exists_const_eLpNorm_chosenWeakPartialOrZero_chartPushed_le_uniform_indices

omit [NeZero (Module.finrank ℝ E)] in
theorem exists_const_sum_eLpNorm_chosenWeakPartialOrZero_chartPushed_le_uniform_indices
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensorH1 g r s) (α β : M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (Idx : Fin r → Fin (Module.finrank ℝ E))
        (Jdx : Fin s → Fin (Module.finrank ℝ E)),
        ∑ k : Fin (Module.finrank ℝ E),
          _root_.MeasureTheory.eLpNorm
              (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartialOrZero
                (d := Module.finrank ℝ E) 2 k
                (chartPushed (I := I) (M := M) (chartAtlasPOU I M) β
                  (tensorChartComponentScalar (I := I) (M := M)
                    g r s S.toCcTensor α Idx Jdx))
                (chartTargetEuclid (I := I) (M := M) β)) 2
              (volume.restrict (chartTargetEuclid (I := I) (M := M) β)) ≤
          ENNReal.ofReal C * (‖S‖₊ + 1) := by
  classical
  have hper : ∀ k : Fin (Module.finrank ℝ E),
      ∃ C : ℝ, 0 ≤ C ∧
        ∀ (Idx : Fin r → Fin (Module.finrank ℝ E))
          (Jdx : Fin s → Fin (Module.finrank ℝ E)),
          _root_.MeasureTheory.eLpNorm
              (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartialOrZero
                (d := Module.finrank ℝ E) 2 k
                (chartPushed (I := I) (M := M) (chartAtlasPOU I M) β
                  (tensorChartComponentScalar (I := I) (M := M)
                    g r s S.toCcTensor α Idx Jdx))
                (chartTargetEuclid (I := I) (M := M) β)) 2
              (volume.restrict (chartTargetEuclid (I := I) (M := M) β)) ≤
            ENNReal.ofReal C * (‖S‖₊ + 1) := fun k =>
    exists_const_eLpNorm_chosenWeakPartialOrZero_chartPushed_le_uniform_indices
      (I := I) (M := M) g r s S α β k
  choose Ck hCk_nn hCk_le using hper
  set Ctot : ℝ := ∑ k : Fin (Module.finrank ℝ E), Ck k with hCtot_def
  refine ⟨Ctot, Finset.sum_nonneg (fun k _ => hCk_nn k), ?_⟩
  intro Idx Jdx
  have h_sum_le :
      ∑ k : Fin (Module.finrank ℝ E),
        _root_.MeasureTheory.eLpNorm
            (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartialOrZero
              (d := Module.finrank ℝ E) 2 k
              (chartPushed (I := I) (M := M) (chartAtlasPOU I M) β
                (tensorChartComponentScalar (I := I) (M := M)
                  g r s S.toCcTensor α Idx Jdx))
              (chartTargetEuclid (I := I) (M := M) β)) 2
            (volume.restrict (chartTargetEuclid (I := I) (M := M) β)) ≤
        ∑ k : Fin (Module.finrank ℝ E),
          ENNReal.ofReal (Ck k) * (‖S‖₊ + 1) :=
    Finset.sum_le_sum (fun k _ => hCk_le k Idx Jdx)
  refine h_sum_le.trans ?_
  rw [show
        ∑ k : Fin (Module.finrank ℝ E),
          ENNReal.ofReal (Ck k) * (‖S‖₊ + 1) =
        (∑ k : Fin (Module.finrank ℝ E), ENNReal.ofReal (Ck k)) *
          (‖S‖₊ + 1) from
      (Finset.sum_mul (s := Finset.univ)
        (f := fun k : Fin (Module.finrank ℝ E) => ENNReal.ofReal (Ck k))
        (a := (‖S‖₊ + 1))).symm]
  have h_ofReal_sum :
      ∑ k : Fin (Module.finrank ℝ E), ENNReal.ofReal (Ck k) ≤
        ENNReal.ofReal (∑ k : Fin (Module.finrank ℝ E), Ck k) := by
    rw [ENNReal.ofReal_sum_of_nonneg (fun k _ => hCk_nn k)]
  exact mul_le_mul_of_nonneg_right h_ofReal_sum (by exact zero_le)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.exists_const_sum_eLpNorm_chosenWeakPartialOrZero_chartPushed_le_uniform_indices then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.exists_const_sum_eLpNorm_chosenWeakPartialOrZero_chartPushed_le_uniform_indices"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.exists_const_sum_eLpNorm_chosenWeakPartialOrZero_chartPushed_le_uniform_indices ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.exists_const_sum_eLpNorm_chosenWeakPartialOrZero_chartPushed_le_uniform_indices

omit [NeZero (Module.finrank ℝ E)] in
theorem exists_const_eLpNorm_chosenWeakPartialOrZero_chartPushed_le_uniform_indices_S
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α β : M)
    (k : Fin (Module.finrank ℝ E)) :
    ∀ S : SmoothCcTensorH1 g r s,
      ∃ C : ℝ, 0 ≤ C ∧
        ∀ (Idx : Fin r → Fin (Module.finrank ℝ E))
          (Jdx : Fin s → Fin (Module.finrank ℝ E)),
          _root_.MeasureTheory.eLpNorm
              (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartialOrZero
                (d := Module.finrank ℝ E) 2 k
                (chartPushed (I := I) (M := M) (chartAtlasPOU I M) β
                  (tensorChartComponentScalar (I := I) (M := M)
                    g r s S.toCcTensor α Idx Jdx))
                (chartTargetEuclid (I := I) (M := M) β)) 2
              (volume.restrict (chartTargetEuclid (I := I) (M := M) β)) ≤
            ENNReal.ofReal C * (‖S‖₊ + 1) := fun S =>
  exists_const_eLpNorm_chosenWeakPartialOrZero_chartPushed_le_uniform_indices
    (I := I) (M := M) g r s S α β k

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.exists_const_eLpNorm_chosenWeakPartialOrZero_chartPushed_le_uniform_indices_S then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.exists_const_eLpNorm_chosenWeakPartialOrZero_chartPushed_le_uniform_indices_S"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.exists_const_eLpNorm_chosenWeakPartialOrZero_chartPushed_le_uniform_indices_S ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.exists_const_eLpNorm_chosenWeakPartialOrZero_chartPushed_le_uniform_indices_S

omit [NeZero (Module.finrank ℝ E)] in
theorem exists_const_sum_eLpNorm_chosenWeakPartialOrZero_chartPushed_le_uniform_indices_S
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α β : M) :
    ∀ S : SmoothCcTensorH1 g r s,
      ∃ C : ℝ, 0 ≤ C ∧
        ∀ (Idx : Fin r → Fin (Module.finrank ℝ E))
          (Jdx : Fin s → Fin (Module.finrank ℝ E)),
          ∑ k : Fin (Module.finrank ℝ E),
            _root_.MeasureTheory.eLpNorm
                (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartialOrZero
                  (d := Module.finrank ℝ E) 2 k
                  (chartPushed (I := I) (M := M) (chartAtlasPOU I M) β
                    (tensorChartComponentScalar (I := I) (M := M)
                      g r s S.toCcTensor α Idx Jdx))
                  (chartTargetEuclid (I := I) (M := M) β)) 2
                (volume.restrict (chartTargetEuclid (I := I) (M := M) β)) ≤
            ENNReal.ofReal C * (‖S‖₊ + 1) := fun S =>
  exists_const_sum_eLpNorm_chosenWeakPartialOrZero_chartPushed_le_uniform_indices
    (I := I) (M := M) g r s S α β

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.exists_const_sum_eLpNorm_chosenWeakPartialOrZero_chartPushed_le_uniform_indices_S then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.exists_const_sum_eLpNorm_chosenWeakPartialOrZero_chartPushed_le_uniform_indices_S"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.exists_const_sum_eLpNorm_chosenWeakPartialOrZero_chartPushed_le_uniform_indices_S ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.exists_const_sum_eLpNorm_chosenWeakPartialOrZero_chartPushed_le_uniform_indices_S

omit [NeZero (Module.finrank ℝ E)] in
theorem exists_const_eLpNorm_chosenWeakPartialOrZero_chartPushed_le_uniform_indices_single_chart
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensorH1 g r s) (α : M)
    (k : Fin (Module.finrank ℝ E)) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (Idx : Fin r → Fin (Module.finrank ℝ E))
        (Jdx : Fin s → Fin (Module.finrank ℝ E)),
        _root_.MeasureTheory.eLpNorm
            (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartialOrZero
              (d := Module.finrank ℝ E) 2 k
              (chartPushed (I := I) (M := M) (chartAtlasPOU I M) α
                (tensorChartComponentScalar (I := I) (M := M)
                  g r s S.toCcTensor α Idx Jdx))
              (chartTargetEuclid (I := I) (M := M) α)) 2
            (volume.restrict (chartTargetEuclid (I := I) (M := M) α)) ≤
          ENNReal.ofReal C * (‖S‖₊ + 1) :=
  exists_const_eLpNorm_chosenWeakPartialOrZero_chartPushed_le_uniform_indices
    (I := I) (M := M) g r s S α α k

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.exists_const_eLpNorm_chosenWeakPartialOrZero_chartPushed_le_uniform_indices_single_chart then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.exists_const_eLpNorm_chosenWeakPartialOrZero_chartPushed_le_uniform_indices_single_chart"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.exists_const_eLpNorm_chosenWeakPartialOrZero_chartPushed_le_uniform_indices_single_chart ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.exists_const_eLpNorm_chosenWeakPartialOrZero_chartPushed_le_uniform_indices_single_chart

omit [NeZero (Module.finrank ℝ E)] in
theorem exists_const_sum_eLpNorm_chosenWeakPartialOrZero_chartPushed_le_uniform_indices_single_chart
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensorH1 g r s) (α : M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (Idx : Fin r → Fin (Module.finrank ℝ E))
        (Jdx : Fin s → Fin (Module.finrank ℝ E)),
        ∑ k : Fin (Module.finrank ℝ E),
          _root_.MeasureTheory.eLpNorm
              (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartialOrZero
                (d := Module.finrank ℝ E) 2 k
                (chartPushed (I := I) (M := M) (chartAtlasPOU I M) α
                  (tensorChartComponentScalar (I := I) (M := M)
                    g r s S.toCcTensor α Idx Jdx))
                (chartTargetEuclid (I := I) (M := M) α)) 2
              (volume.restrict (chartTargetEuclid (I := I) (M := M) α)) ≤
          ENNReal.ofReal C * (‖S‖₊ + 1) :=
  exists_const_sum_eLpNorm_chosenWeakPartialOrZero_chartPushed_le_uniform_indices
    (I := I) (M := M) g r s S α α

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.exists_const_sum_eLpNorm_chosenWeakPartialOrZero_chartPushed_le_uniform_indices_single_chart then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.exists_const_sum_eLpNorm_chosenWeakPartialOrZero_chartPushed_le_uniform_indices_single_chart"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.exists_const_sum_eLpNorm_chosenWeakPartialOrZero_chartPushed_le_uniform_indices_single_chart ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.exists_const_sum_eLpNorm_chosenWeakPartialOrZero_chartPushed_le_uniform_indices_single_chart

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
