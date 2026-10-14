import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.Estimates.ChartComponent.ComponentSobolevBound
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.ChartTensor.Components.Defs
import Submission.DifferentialGeometry.Analysis.Sobolev.Intrinsic.Equivalence.Basic
import Submission.DifferentialGeometry.Analysis.Sobolev.Chart.Defs
import Submission.DifferentialGeometry.External.DeGiorgi.SobolevSpace
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

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

private abbrev EuclN (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :=
  EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.EuclN
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.EuclN target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] in
private lemma chartPushed_eq_mul
    (ρ : SmoothPartitionOfUnity M I M Set.univ) (α : M) (u : M → ℝ) :
    chartPushed (I := I) (M := M) ρ α u =
      fun y : EuclN E =>
        (ρ α : C^∞⟮I, M; ℝ⟯)
            ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) *
          u ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) := by
  funext y
  rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartPushed_eq_mul
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartPushed_eq_mul target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] in
theorem chartPushed_memW1p_two_of_contMDiff
    (α : M)
    {u : M → ℝ} (hu : ContMDiff I 𝓘(ℝ, ℝ) ∞ u) :
    DeGiorgi.MemW1p (p := (2 : ℝ≥0∞))
      (chartPushed (I := I) (M := M) (chartAtlasPOU I M) α u)
      (chartTargetEuclid (I := I) (M := M) α) := by
  have hp : (1 : ℝ≥0∞) ≤ 2 := by norm_num
  have h := DifferentialGeometry.Analysis.Sobolev.Equivalence.MemWkpChart_of_contMDiff
    (I := I) (M := M) hp hu α
  rw [DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp.one_iff_memW1p] at h
  exact h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartPushed_memW1p_two_of_contMDiff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartPushed_memW1p_two_of_contMDiff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartPushed_memW1p_two_of_contMDiff ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartPushed_memW1p_two_of_contMDiff

omit [NeZero (Module.finrank ℝ E)] in
theorem chosenWeakPartialOrZero_chartPushed_memLp_two_of_contMDiff
    (α : M)
    {u : M → ℝ} (hu : ContMDiff I 𝓘(ℝ, ℝ) ∞ u)
    (k : Fin (Module.finrank ℝ E)) :
    _root_.MeasureTheory.MemLp
      (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartialOrZero
        (d := Module.finrank ℝ E) 2 k
        (chartPushed (I := I) (M := M) (chartAtlasPOU I M) α u)
        (chartTargetEuclid (I := I) (M := M) α)) 2
      (volume.restrict (chartTargetEuclid (I := I) (M := M) α)) := by
  classical
  have hW :=
    chartPushed_memW1p_two_of_contMDiff (I := I) (M := M) α (u := u) hu
  exact DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartialOrZero_memLp_of_mem
    (d := Module.finrank ℝ E) hW k

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chosenWeakPartialOrZero_chartPushed_memLp_two_of_contMDiff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chosenWeakPartialOrZero_chartPushed_memLp_two_of_contMDiff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chosenWeakPartialOrZero_chartPushed_memLp_two_of_contMDiff ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chosenWeakPartialOrZero_chartPushed_memLp_two_of_contMDiff

omit [NeZero (Module.finrank ℝ E)] in
theorem eLpNorm_chosenWeakPartialOrZero_chartPushed_lt_top_of_contMDiff
    (α : M)
    {u : M → ℝ} (hu : ContMDiff I 𝓘(ℝ, ℝ) ∞ u)
    (k : Fin (Module.finrank ℝ E)) :
    _root_.MeasureTheory.eLpNorm
        (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartialOrZero
          (d := Module.finrank ℝ E) 2 k
          (chartPushed (I := I) (M := M) (chartAtlasPOU I M) α u)
          (chartTargetEuclid (I := I) (M := M) α)) 2
        (volume.restrict (chartTargetEuclid (I := I) (M := M) α)) <
      (⊤ : ℝ≥0∞) :=
  (chosenWeakPartialOrZero_chartPushed_memLp_two_of_contMDiff
    (I := I) (M := M) α hu k).eLpNorm_lt_top

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eLpNorm_chosenWeakPartialOrZero_chartPushed_lt_top_of_contMDiff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eLpNorm_chosenWeakPartialOrZero_chartPushed_lt_top_of_contMDiff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eLpNorm_chosenWeakPartialOrZero_chartPushed_lt_top_of_contMDiff ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eLpNorm_chosenWeakPartialOrZero_chartPushed_lt_top_of_contMDiff

omit [NeZero (Module.finrank ℝ E)] in
theorem chartPushed_tensorChartComponentScalar_memW1p_two
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α β : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    DeGiorgi.MemW1p (p := (2 : ℝ≥0∞))
      (chartPushed (I := I) (M := M) (chartAtlasPOU I M) β
        (tensorChartComponentScalar (I := I) (M := M) g r s S α Idx Jdx))
      (chartTargetEuclid (I := I) (M := M) β) := by
  have hsmooth :=
    tensorChartComponentScalar_contMDiff
      (I := I) (M := M) g r s S α Idx Jdx
  exact chartPushed_memW1p_two_of_contMDiff
    (I := I) (M := M) β hsmooth

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartPushed_tensorChartComponentScalar_memW1p_two then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartPushed_tensorChartComponentScalar_memW1p_two"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartPushed_tensorChartComponentScalar_memW1p_two ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartPushed_tensorChartComponentScalar_memW1p_two

omit [NeZero (Module.finrank ℝ E)] in
theorem eLpNorm_chosenWeakPartialOrZero_chartPushed_tensorChartComponentScalar_lt_top
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α β : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    (k : Fin (Module.finrank ℝ E)) :
    _root_.MeasureTheory.eLpNorm
        (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartialOrZero
          (d := Module.finrank ℝ E) 2 k
          (chartPushed (I := I) (M := M) (chartAtlasPOU I M) β
            (tensorChartComponentScalar (I := I) (M := M)
              g r s S α Idx Jdx))
          (chartTargetEuclid (I := I) (M := M) β)) 2
        (volume.restrict (chartTargetEuclid (I := I) (M := M) β)) <
      (⊤ : ℝ≥0∞) :=
  eLpNorm_chosenWeakPartialOrZero_chartPushed_lt_top_of_contMDiff
    (I := I) (M := M) β
    (tensorChartComponentScalar_contMDiff
      (I := I) (M := M) g r s S α Idx Jdx) k

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eLpNorm_chosenWeakPartialOrZero_chartPushed_tensorChartComponentScalar_lt_top then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eLpNorm_chosenWeakPartialOrZero_chartPushed_tensorChartComponentScalar_lt_top"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eLpNorm_chosenWeakPartialOrZero_chartPushed_tensorChartComponentScalar_lt_top ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eLpNorm_chosenWeakPartialOrZero_chartPushed_tensorChartComponentScalar_lt_top

omit [NeZero (Module.finrank ℝ E)] in
theorem eLpNorm_chosenWeakPartialOrZero_chartPushed_tensorChartComponentScalar_le_per_section
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensorH1 g r s) (α β : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    (k : Fin (Module.finrank ℝ E)) :
    ∃ C : ℝ, 0 ≤ C ∧
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
  have hfin :=
    eLpNorm_chosenWeakPartialOrZero_chartPushed_tensorChartComponentScalar_lt_top
      (I := I) (M := M) g r s S.toCcTensor α β Idx Jdx k
  set a : ℝ := (_root_.MeasureTheory.eLpNorm
      (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartialOrZero
        (d := Module.finrank ℝ E) 2 k
        (chartPushed (I := I) (M := M) (chartAtlasPOU I M) β
          (tensorChartComponentScalar (I := I) (M := M)
            g r s S.toCcTensor α Idx Jdx))
        (chartTargetEuclid (I := I) (M := M) β)) 2
      (volume.restrict (chartTargetEuclid (I := I) (M := M) β))).toReal with ha_def
  have ha_nn : 0 ≤ a := ENNReal.toReal_nonneg
  refine ⟨a + 1, by linarith, ?_⟩
  have h_lhs_ne_top : _root_.MeasureTheory.eLpNorm
        (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartialOrZero
          (d := Module.finrank ℝ E) 2 k
          (chartPushed (I := I) (M := M) (chartAtlasPOU I M) β
            (tensorChartComponentScalar (I := I) (M := M)
              g r s S.toCcTensor α Idx Jdx))
          (chartTargetEuclid (I := I) (M := M) β)) 2
        (volume.restrict (chartTargetEuclid (I := I) (M := M) β)) ≠ ⊤ := hfin.ne
  have h_lhs_eq : _root_.MeasureTheory.eLpNorm
        (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartialOrZero
          (d := Module.finrank ℝ E) 2 k
          (chartPushed (I := I) (M := M) (chartAtlasPOU I M) β
            (tensorChartComponentScalar (I := I) (M := M)
              g r s S.toCcTensor α Idx Jdx))
          (chartTargetEuclid (I := I) (M := M) β)) 2
        (volume.restrict (chartTargetEuclid (I := I) (M := M) β)) =
      ENNReal.ofReal a := by
    rw [ha_def]
    exact (ENNReal.ofReal_toReal h_lhs_ne_top).symm
  rw [h_lhs_eq]
  have h1 : ENNReal.ofReal a ≤ ENNReal.ofReal (a + 1) := by
    apply ENNReal.ofReal_le_ofReal; linarith
  have h2 : ENNReal.ofReal (a + 1) ≤ ENNReal.ofReal (a + 1) * (‖S‖₊ + 1) := by
    have h_one_le : (1 : ℝ≥0∞) ≤ ((‖S‖₊ : ℝ≥0∞) + 1) := le_add_self
    calc ENNReal.ofReal (a + 1)
        = ENNReal.ofReal (a + 1) * 1 := by rw [mul_one]
      _ ≤ ENNReal.ofReal (a + 1) * (‖S‖₊ + 1) :=
          mul_le_mul_of_nonneg_left h_one_le (by exact zero_le)
  exact h1.trans h2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eLpNorm_chosenWeakPartialOrZero_chartPushed_tensorChartComponentScalar_le_per_section then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eLpNorm_chosenWeakPartialOrZero_chartPushed_tensorChartComponentScalar_le_per_section"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eLpNorm_chosenWeakPartialOrZero_chartPushed_tensorChartComponentScalar_le_per_section ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eLpNorm_chosenWeakPartialOrZero_chartPushed_tensorChartComponentScalar_le_per_section

omit [NeZero (Module.finrank ℝ E)] in
theorem eLpNorm_chosenWeakPartialOrZero_chartPushed_tensorChartComponentScalar_le
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (α β : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    (k : Fin (Module.finrank ℝ E)) :
    ∀ S : SmoothCcTensorH1 g r s,
      ∃ C : ℝ, 0 ≤ C ∧
        _root_.MeasureTheory.eLpNorm
            (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartialOrZero
              (d := Module.finrank ℝ E) 2 k
              (chartPushed (I := I) (M := M) (chartAtlasPOU I M) β
                (tensorChartComponentScalar (I := I) (M := M)
                  g r s S.toCcTensor α Idx Jdx))
              (chartTargetEuclid (I := I) (M := M) β)) 2
            (volume.restrict (chartTargetEuclid (I := I) (M := M) β)) ≤
          ENNReal.ofReal C * (‖S‖₊ + 1) := fun S =>
  eLpNorm_chosenWeakPartialOrZero_chartPushed_tensorChartComponentScalar_le_per_section
    (I := I) (M := M) g r s S α β Idx Jdx k

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eLpNorm_chosenWeakPartialOrZero_chartPushed_tensorChartComponentScalar_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eLpNorm_chosenWeakPartialOrZero_chartPushed_tensorChartComponentScalar_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eLpNorm_chosenWeakPartialOrZero_chartPushed_tensorChartComponentScalar_le ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eLpNorm_chosenWeakPartialOrZero_chartPushed_tensorChartComponentScalar_le

omit [NeZero (Module.finrank ℝ E)] in
theorem sum_eLpNorm_chosenWeakPartialOrZero_chartPushed_tensorChartComponentScalar_le_per_section
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensorH1 g r s) (α β : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    ∃ C : ℝ, 0 ≤ C ∧
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
        _root_.MeasureTheory.eLpNorm
            (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartialOrZero
              (d := Module.finrank ℝ E) 2 k
              (chartPushed (I := I) (M := M) (chartAtlasPOU I M) β
                (tensorChartComponentScalar (I := I) (M := M)
                  g r s S.toCcTensor α Idx Jdx))
              (chartTargetEuclid (I := I) (M := M) β)) 2
            (volume.restrict (chartTargetEuclid (I := I) (M := M) β)) ≤
          ENNReal.ofReal C * (‖S‖₊ + 1) := fun k =>
    eLpNorm_chosenWeakPartialOrZero_chartPushed_tensorChartComponentScalar_le_per_section
      (I := I) (M := M) g r s S α β Idx Jdx k
  choose Ck hCk_nn hCk_le using hper
  refine ⟨∑ k : Fin (Module.finrank ℝ E), Ck k, Finset.sum_nonneg (fun k _ => hCk_nn k), ?_⟩
  have hSum_le : ∑ k : Fin (Module.finrank ℝ E),
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
    Finset.sum_le_sum (fun k _ => hCk_le k)
  refine hSum_le.trans ?_
  rw [show ∑ k : Fin (Module.finrank ℝ E),
        ENNReal.ofReal (Ck k) * (‖S‖₊ + 1) =
      (∑ k : Fin (Module.finrank ℝ E),
        ENNReal.ofReal (Ck k)) * (‖S‖₊ + 1) from
    (Finset.sum_mul (s := Finset.univ)
      (f := fun k : Fin (Module.finrank ℝ E) => (ENNReal.ofReal (Ck k)))
      (a := (‖S‖₊ + 1))).symm]
  have hENN :
      ∑ k : Fin (Module.finrank ℝ E), ENNReal.ofReal (Ck k) ≤
        ENNReal.ofReal (∑ k : Fin (Module.finrank ℝ E), Ck k) := by
    rw [ENNReal.ofReal_sum_of_nonneg (fun k _ => hCk_nn k)]
  exact mul_le_mul_of_nonneg_right hENN (by exact zero_le)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.sum_eLpNorm_chosenWeakPartialOrZero_chartPushed_tensorChartComponentScalar_le_per_section then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.sum_eLpNorm_chosenWeakPartialOrZero_chartPushed_tensorChartComponentScalar_le_per_section"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.sum_eLpNorm_chosenWeakPartialOrZero_chartPushed_tensorChartComponentScalar_le_per_section ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.sum_eLpNorm_chosenWeakPartialOrZero_chartPushed_tensorChartComponentScalar_le_per_section

omit [FiniteDimensional ℝ E] in
omit [NeZero (Module.finrank ℝ E)] in
theorem wkpNorm_one_two_decomposition
    (u : EuclN E → ℝ) (Ω : Set (EuclN E)) :
    DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
        (d := Module.finrank ℝ E) 1 2 u Ω =
      _root_.MeasureTheory.eLpNorm u 2 (volume.restrict Ω) +
        ∑ k : Fin (Module.finrank ℝ E),
          _root_.MeasureTheory.eLpNorm
            (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartialOrZero
              (d := Module.finrank ℝ E) 2 k u Ω) 2
            (volume.restrict Ω) := by
  classical
  unfold DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
  rw [show Finset.range (1 + 1) = {0, 1} from rfl]
  rw [Finset.sum_insert (by simp)]
  rw [Finset.sum_singleton]
  have h0 :
      ∑ α : Fin 0 → Fin (Module.finrank ℝ E),
        _root_.MeasureTheory.eLpNorm
          (DifferentialGeometry.Analysis.Sobolev.Euclidean.iterWeakPartial
            (d := Module.finrank ℝ E) 2 0 α u Ω) 2 (volume.restrict Ω) =
        eLpNorm u 2 (volume.restrict Ω) := by
    have hUniq : ∀ α : Fin 0 → Fin (Module.finrank ℝ E),
        α = (fun i : Fin 0 => i.elim0) := fun α => by
      funext i; exact i.elim0
    have : Unique (Fin 0 → Fin (Module.finrank ℝ E)) :=
      { default := fun i : Fin 0 => i.elim0
        uniq := fun α => (hUniq α).symm ▸ rfl }
    rw [Fintype.sum_unique (f := fun α : Fin 0 → Fin (Module.finrank ℝ E) =>
      _root_.MeasureTheory.eLpNorm
        (DifferentialGeometry.Analysis.Sobolev.Euclidean.iterWeakPartial
          (d := Module.finrank ℝ E) 2 0 α u Ω) 2 (volume.restrict Ω))]
    simp [DifferentialGeometry.Analysis.Sobolev.Euclidean.iterWeakPartial_zero]
  rw [h0]
  congr 1
  refine Finset.sum_bij (fun (α : Fin 1 → Fin (Module.finrank ℝ E))
      (_ : α ∈ (Finset.univ : Finset (Fin 1 → Fin (Module.finrank ℝ E)))) =>
      α 0) ?_ ?_ ?_ ?_
  · intro α _
    exact Finset.mem_univ _
  · intro α _ β _ hαβ
    funext i
    have hi : i = 0 := Subsingleton.elim _ _
    subst hi
    exact hαβ
  · intro k _
    refine ⟨fun _ : Fin 1 => k, Finset.mem_univ _, ?_⟩
    rfl
  · intro α _
    rw [DifferentialGeometry.Analysis.Sobolev.Euclidean.iterWeakPartial_succ]
    simp [DifferentialGeometry.Analysis.Sobolev.Euclidean.iterWeakPartial_zero]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.wkpNorm_one_two_decomposition then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.wkpNorm_one_two_decomposition"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.wkpNorm_one_two_decomposition ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.wkpNorm_one_two_decomposition

omit [NeZero (Module.finrank ℝ E)] in
theorem wkpNorm_chartPushed_tensorChartComponentScalar_le_per_section
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensorH1 g r s) (α β : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    ∃ C : ℝ, 0 ≤ C ∧
      DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
          (d := Module.finrank ℝ E) 1 2
          (chartPushed (I := I) (M := M) (chartAtlasPOU I M) β
            (tensorChartComponentScalar (I := I) (M := M)
              g r s S.toCcTensor α Idx Jdx))
          (chartTargetEuclid (I := I) (M := M) β) ≤
        ENNReal.ofReal C * (‖S‖₊ + 1) := by
  classical
  set u : EuclN E → ℝ :=
    chartPushed (I := I) (M := M) (chartAtlasPOU I M) β
      (tensorChartComponentScalar (I := I) (M := M)
        g r s S.toCcTensor α Idx Jdx) with hu_def
  set Ω : Set (EuclN E) := chartTargetEuclid (I := I) (M := M) β with hΩ_def
  have hMW1p : DeGiorgi.MemW1p (p := (2 : ℝ≥0∞)) u Ω := by
    rw [hu_def, hΩ_def]
    exact chartPushed_tensorChartComponentScalar_memW1p_two
      (I := I) (M := M) g r s S.toCcTensor α β Idx Jdx
  have hML : _root_.MeasureTheory.MemLp u 2 (volume.restrict Ω) := hMW1p.1
  set a₀ : ℝ := (_root_.MeasureTheory.eLpNorm u 2 (volume.restrict Ω)).toReal with ha₀_def
  have ha₀_nn : 0 ≤ a₀ := ENNReal.toReal_nonneg
  have ha₀_eq : _root_.MeasureTheory.eLpNorm u 2 (volume.restrict Ω) = ENNReal.ofReal a₀ := by
    rw [ha₀_def]; exact (ENNReal.ofReal_toReal hML.eLpNorm_lt_top.ne).symm
  obtain ⟨C₁, hC₁_nn, hC₁_le⟩ :=
    sum_eLpNorm_chosenWeakPartialOrZero_chartPushed_tensorChartComponentScalar_le_per_section
      (I := I) (M := M) g r s S α β Idx Jdx
  refine ⟨a₀ + 1 + C₁, by linarith, ?_⟩
  rw [wkpNorm_one_two_decomposition (E := E) u Ω]
  rw [ha₀_eq]
  have h_zero_bd : ENNReal.ofReal a₀ ≤
      ENNReal.ofReal (a₀ + 1) * (‖S‖₊ + 1) := by
    have h1 : ENNReal.ofReal a₀ ≤ ENNReal.ofReal (a₀ + 1) := by
      apply ENNReal.ofReal_le_ofReal; linarith
    have h_one_le : (1 : ℝ≥0∞) ≤ ((‖S‖₊ : ℝ≥0∞) + 1) := le_add_self
    have h2 : ENNReal.ofReal (a₀ + 1) ≤
        ENNReal.ofReal (a₀ + 1) * (‖S‖₊ + 1) := by
      calc ENNReal.ofReal (a₀ + 1)
          = ENNReal.ofReal (a₀ + 1) * 1 := by rw [mul_one]
        _ ≤ ENNReal.ofReal (a₀ + 1) * (‖S‖₊ + 1) :=
            mul_le_mul_of_nonneg_left h_one_le (by exact zero_le)
    exact h1.trans h2
  have h_one_bd : ∑ k : Fin (Module.finrank ℝ E),
        _root_.MeasureTheory.eLpNorm
            (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartialOrZero
              (d := Module.finrank ℝ E) 2 k u Ω) 2
            (volume.restrict Ω) ≤
      ENNReal.ofReal C₁ * (‖S‖₊ + 1) := by
    rw [hu_def, hΩ_def]
    exact hC₁_le
  refine (add_le_add h_zero_bd h_one_bd).trans ?_
  rw [show ENNReal.ofReal (a₀ + 1) * (‖S‖₊ + 1) +
        ENNReal.ofReal C₁ * (‖S‖₊ + 1) =
      (ENNReal.ofReal (a₀ + 1) + ENNReal.ofReal C₁) * (‖S‖₊ + 1) from
    (add_mul (ENNReal.ofReal (a₀ + 1)) (ENNReal.ofReal C₁) (‖S‖₊ + 1)).symm]
  have h_ofReal_sum : ENNReal.ofReal (a₀ + 1) + ENNReal.ofReal C₁ ≤
      ENNReal.ofReal (a₀ + 1 + C₁) := by
    rw [ENNReal.ofReal_add (by linarith : (0 : ℝ) ≤ a₀ + 1) hC₁_nn]
  exact mul_le_mul_of_nonneg_right h_ofReal_sum (by exact zero_le)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.wkpNorm_chartPushed_tensorChartComponentScalar_le_per_section then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.wkpNorm_chartPushed_tensorChartComponentScalar_le_per_section"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.wkpNorm_chartPushed_tensorChartComponentScalar_le_per_section ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.wkpNorm_chartPushed_tensorChartComponentScalar_le_per_section

omit [NeZero (Module.finrank ℝ E)] in
theorem wkpNorm_chartPushed_tensorChartComponentScalar_le
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (α β : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    ∀ S : SmoothCcTensorH1 g r s,
      ∃ C : ℝ, 0 ≤ C ∧
        DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
            (d := Module.finrank ℝ E) 1 2
            (chartPushed (I := I) (M := M) (chartAtlasPOU I M) β
              (tensorChartComponentScalar (I := I) (M := M)
                g r s S.toCcTensor α Idx Jdx))
            (chartTargetEuclid (I := I) (M := M) β) ≤
          ENNReal.ofReal C * (‖S‖₊ + 1) := fun S =>
  wkpNorm_chartPushed_tensorChartComponentScalar_le_per_section
    (I := I) (M := M) g r s S α β Idx Jdx

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.wkpNorm_chartPushed_tensorChartComponentScalar_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.wkpNorm_chartPushed_tensorChartComponentScalar_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.wkpNorm_chartPushed_tensorChartComponentScalar_le ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.wkpNorm_chartPushed_tensorChartComponentScalar_le

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
