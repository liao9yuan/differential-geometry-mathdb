import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.Spectrum.Resolvent
import Mathlib.Analysis.Normed.Operator.Compact.Basic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.MeasureTheory _root_.Set _root_.Filter
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.ENNReal _root_.BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.L2

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E]
  [NeZero (Module.finrank ℝ E)]
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

omit [NeZero (Module.finrank ℝ E)] in
lemma tensorResolventL2_eq_comp (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    tensorResolventL2 (I := I) (M := M) g r s =
      (TensorH1ComplToTensorL2 (I := I) (M := M) g r s).comp
        (tensorResolvent (I := I) (M := M) g r s) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorResolventL2_eq_comp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorResolventL2_eq_comp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorResolventL2_eq_comp ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorResolventL2_eq_comp

omit [NeZero (Module.finrank ℝ E)] in
lemma tensorResolventL2_apply_eq_comp
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (f : TensorL2 r s g) :
    (tensorResolventL2 (I := I) (M := M) g r s) f =
      (TensorH1ComplToTensorL2 (I := I) (M := M) g r s)
        ((tensorResolvent (I := I) (M := M) g r s) f) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorResolventL2_apply_eq_comp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorResolventL2_apply_eq_comp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorResolventL2_apply_eq_comp ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorResolventL2_apply_eq_comp

omit [NeZero (Module.finrank ℝ E)] in
theorem tensorResolventL2_isCompactOperator_of_isCompactOperator
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_H1L2 :
      IsCompactOperator
        (TensorH1ComplToTensorL2 (I := I) (M := M) g r s)) :
    IsCompactOperator (tensorResolventL2 (I := I) (M := M) g r s) := by
  have h_comp : IsCompactOperator
      ((fun v : TensorH1Compl g r s =>
          TensorH1ComplToTensorL2 (I := I) (M := M) g r s v) ∘
        (fun f : TensorL2 r s g =>
          tensorResolvent (I := I) (M := M) g r s f)) :=
    h_H1L2.comp_clm (tensorResolvent (I := I) (M := M) g r s)
  exact h_comp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorResolventL2_isCompactOperator_of_isCompactOperator then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorResolventL2_isCompactOperator_of_isCompactOperator"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorResolventL2_isCompactOperator_of_isCompactOperator ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorResolventL2_isCompactOperator_of_isCompactOperator

omit [NeZero (Module.finrank ℝ E)] in
theorem tensorResolventL2_isCompactOperator_and_isSelfAdjoint
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_H1L2 :
      IsCompactOperator
        (TensorH1ComplToTensorL2 (I := I) (M := M) g r s)) :
    IsCompactOperator (tensorResolventL2 (I := I) (M := M) g r s) ∧
      IsSelfAdjoint (tensorResolventL2 (I := I) (M := M) g r s) :=
  ⟨tensorResolventL2_isCompactOperator_of_isCompactOperator
    (I := I) (M := M) g r s h_H1L2,
   tensorResolventL2_isSelfAdjoint (I := I) (M := M) g r s⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorResolventL2_isCompactOperator_and_isSelfAdjoint then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorResolventL2_isCompactOperator_and_isSelfAdjoint"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorResolventL2_isCompactOperator_and_isSelfAdjoint ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorResolventL2_isCompactOperator_and_isSelfAdjoint

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
