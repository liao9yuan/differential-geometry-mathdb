import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.ChartTensor.Components.ChristoffelDecomp
import Submission.DifferentialGeometry.Geometry.Connection.LeviCivita.Chart.Local

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Geometry.Operator


noncomputable section


open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Set _root_.Filter _root_.Submission.DifferentialGeometry.Tensor0SBundle
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.BigOperators

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.L2

open _root_.Submission.DifferentialGeometry.Integral.DivergenceTheorem

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

noncomputable def chartChristoffelBilin
    (g : SmoothRiemannianMetric I M) (α : M) (b : M) :
    E →L[ℝ] E →L[ℝ] E :=
  ∑ i : Fin (Module.finrank ℝ E),
    ∑ j : Fin (Module.finrank ℝ E),
      ∑ k : Fin (Module.finrank ℝ E),
        ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).coord i).toContinuousLinearMap.smulRight
          (((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).coord j).toContinuousLinearMap.smulRight
            (chartChristoffel (I := I) g α i j k (extChartAt I α b) •
              (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) k))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartChristoffelBilin then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartChristoffelBilin"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartChristoffelBilin ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartChristoffelBilin

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] in
lemma chartChristoffelBilin_apply
    (g : SmoothRiemannianMetric I M) (α : M) (b : M) (v w : E) :
    chartChristoffelBilin (I := I) (M := M) g α b v w =
      ∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          ∑ k : Fin (Module.finrank ℝ E),
            (((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr v) i *
                ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr w) j *
                chartChristoffel (I := I) g α i j k (extChartAt I α b)) •
              (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) k := by
  classical
  unfold chartChristoffelBilin
  rw [sum_apply]
  rw [sum_apply]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [sum_apply]
  rw [sum_apply]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [sum_apply]
  rw [sum_apply]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [ContinuousLinearMap.smulRight_apply]
  rw [smul_apply]
  rw [ContinuousLinearMap.smulRight_apply]
  have hcoord_i : ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).coord i).toContinuousLinearMap v =
      ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr v) i := rfl
  have hcoord_j : ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).coord j).toContinuousLinearMap w =
      ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr w) j := rfl
  rw [hcoord_i, hcoord_j]
  rw [smul_smul, smul_smul]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartChristoffelBilin_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartChristoffelBilin_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartChristoffelBilin_apply ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartChristoffelBilin_apply

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] in
lemma chartChristoffelBilin_add_first
    (g : SmoothRiemannianMetric I M) (α : M) (b : M) (v₁ v₂ w : E) :
    chartChristoffelBilin (I := I) (M := M) g α b (v₁ + v₂) w =
      chartChristoffelBilin (I := I) (M := M) g α b v₁ w +
        chartChristoffelBilin (I := I) (M := M) g α b v₂ w := by
  rw [show chartChristoffelBilin (I := I) (M := M) g α b (v₁ + v₂) =
        chartChristoffelBilin (I := I) (M := M) g α b v₁ +
          chartChristoffelBilin (I := I) (M := M) g α b v₂ from map_add _ _ _,
      add_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartChristoffelBilin_add_first then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartChristoffelBilin_add_first"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartChristoffelBilin_add_first ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartChristoffelBilin_add_first

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] in
lemma chartChristoffelBilin_smul_first
    (g : SmoothRiemannianMetric I M) (α : M) (b : M) (c : ℝ) (v w : E) :
    chartChristoffelBilin (I := I) (M := M) g α b (c • v) w =
      c • chartChristoffelBilin (I := I) (M := M) g α b v w := by
  rw [show chartChristoffelBilin (I := I) (M := M) g α b (c • v) =
        c • chartChristoffelBilin (I := I) (M := M) g α b v from map_smul _ _ _,
      smul_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartChristoffelBilin_smul_first then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartChristoffelBilin_smul_first"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartChristoffelBilin_smul_first ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartChristoffelBilin_smul_first

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] in
lemma chartChristoffelBilin_add_second
    (g : SmoothRiemannianMetric I M) (α : M) (b : M) (v w₁ w₂ : E) :
    chartChristoffelBilin (I := I) (M := M) g α b v (w₁ + w₂) =
      chartChristoffelBilin (I := I) (M := M) g α b v w₁ +
        chartChristoffelBilin (I := I) (M := M) g α b v w₂ :=
  map_add _ _ _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartChristoffelBilin_add_second then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartChristoffelBilin_add_second"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartChristoffelBilin_add_second ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartChristoffelBilin_add_second

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] in
lemma chartChristoffelBilin_smul_second
    (g : SmoothRiemannianMetric I M) (α : M) (b : M) (v : E) (c : ℝ) (w : E) :
    chartChristoffelBilin (I := I) (M := M) g α b v (c • w) =
      c • chartChristoffelBilin (I := I) (M := M) g α b v w :=
  map_smul _ _ _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartChristoffelBilin_smul_second then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartChristoffelBilin_smul_second"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartChristoffelBilin_smul_second ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartChristoffelBilin_smul_second

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
