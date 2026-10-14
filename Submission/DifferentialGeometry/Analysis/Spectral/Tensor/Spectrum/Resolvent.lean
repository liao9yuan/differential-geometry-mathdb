import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.Variational.Defs
import Mathlib.Analysis.Normed.Operator.Compact.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint

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

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.L2

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

variable [I.Boundaryless] [T2Space M] [CompactSpace M]

noncomputable def tensorResolventL2 (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    TensorL2 r s g →L[ℝ] TensorL2 r s g :=
  (TensorH1ComplToTensorL2 (I := I) (M := M) g r s).comp
    (tensorResolvent (I := I) (M := M) g r s)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorResolventL2 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorResolventL2"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorResolventL2 ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorResolventL2


omit [NeZero (Module.finrank ℝ E)] in
@[simp] lemma tensorResolventL2_apply (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (f : TensorL2 r s g) :
    tensorResolventL2 (I := I) (M := M) g r s f =
      TensorH1ComplToTensorL2 (I := I) (M := M) g r s
        (tensorResolvent (I := I) (M := M) g r s f) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorResolventL2_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorResolventL2_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorResolventL2_apply ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorResolventL2_apply


omit [NeZero (Module.finrank ℝ E)] in
private lemma inner_tensorResolventL2_eq_inner_tensorResolvent
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (f h : TensorL2 r s g) :
    ⟪tensorResolventL2 (I := I) (M := M) g r s f, h⟫_ℝ =
      ⟪tensorResolvent (I := I) (M := M) g r s f,
        tensorResolvent (I := I) (M := M) g r s h⟫_ℝ := by
  rw [tensorResolventL2_apply]
  have hvar := tensorResolvent_inner_eq_lpFunctional (I := I) (M := M) g r s h
    (tensorResolvent (I := I) (M := M) g r s f)
  rw [← hvar]
  exact real_inner_comm _ _

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.inner_tensorResolventL2_eq_inner_tensorResolvent
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.inner_tensorResolventL2_eq_inner_tensorResolvent target :: scope.openDecls } }


omit [NeZero (Module.finrank ℝ E)] in
theorem tensorResolventL2_symm
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (f h : TensorL2 r s g) :
    ⟪tensorResolventL2 (I := I) (M := M) g r s f, h⟫_ℝ =
      ⟪f, tensorResolventL2 (I := I) (M := M) g r s h⟫_ℝ := by
  rw [inner_tensorResolventL2_eq_inner_tensorResolvent (I := I) (M := M) g r s f h]
  rw [show ⟪f, tensorResolventL2 (I := I) (M := M) g r s h⟫_ℝ =
      ⟪tensorResolventL2 (I := I) (M := M) g r s h, f⟫_ℝ from real_inner_comm _ _]
  rw [inner_tensorResolventL2_eq_inner_tensorResolvent (I := I) (M := M) g r s h f]
  exact real_inner_comm _ _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorResolventL2_symm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorResolventL2_symm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorResolventL2_symm ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorResolventL2_symm


omit [NeZero (Module.finrank ℝ E)] in
theorem tensorResolventL2_isSelfAdjoint
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    IsSelfAdjoint (tensorResolventL2 (I := I) (M := M) g r s) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
  intro f h
  exact tensorResolventL2_symm (I := I) (M := M) g r s f h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorResolventL2_isSelfAdjoint then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorResolventL2_isSelfAdjoint"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorResolventL2_isSelfAdjoint ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorResolventL2_isSelfAdjoint

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
