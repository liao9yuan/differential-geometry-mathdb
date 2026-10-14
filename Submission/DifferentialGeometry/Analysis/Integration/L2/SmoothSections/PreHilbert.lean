import Submission.DifferentialGeometry.Analysis.Integration.L2.SmoothSections.Defs
import Submission.DifferentialGeometry.Analysis.Integration.L2.SmoothSections.Integrability
import Submission.DifferentialGeometry.Analysis.Integration.L2.Pairing.CauchySchwarz
import Submission.DifferentialGeometry.Geometry.Metric.PointwiseInner.Algebra
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.Geometry.Manifold.Metrizable
import Mathlib.Geometry.Manifold.VectorBundle.Basic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission


noncomputable section


open _root_.Manifold _root_.MeasureTheory _root_.Set _root_.Filter _root_.Bundle _root_.Submission.Bundle _root_.Submission.DifferentialGeometry.Tensor0SBundle
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.ENNReal _root_.BigOperators _root_.Matrix
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Integral
namespace L2

open _root_.Submission.DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private local instance _root_.Submission.DifferentialGeometry.Integral.L2.instMeasurableSpace_differentialGeometry : MeasurableSpace E := borel E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Integral.L2.instMeasurableSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Integral.L2.instMeasurableSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Integral.L2.instBorelSpace_differentialGeometry : BorelSpace E := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Integral.L2.instBorelSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Integral.L2.instBorelSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Integral.L2.instMeasurableSpace_differentialGeometry_1 : MeasurableSpace M := borel M

run_cmd do
  let target := ``Submission.DifferentialGeometry.Integral.L2.instMeasurableSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Integral.L2.instMeasurableSpace_differentialGeometry_1 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Integral.L2.instBorelSpace_differentialGeometry_1 : BorelSpace M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Integral.L2.instBorelSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Integral.L2.instBorelSpace_differentialGeometry_1 target :: scope.openDecls } }

section PreHilbert

variable [T2Space M] [SigmaCompactSpace M]
variable {g : SmoothRiemannianMetric I M} {r s : ℕ}


noncomputable instance instPreInnerProductSpaceCore :
    PreInnerProductSpace.Core ℝ (SmoothCcTensor g r s) where
  inner S T := tensorL2Inner (I := I) (M := M) g r s S.toFun T.toFun
  conj_inner_symm S T := by
    change (tensorL2Inner (I := I) (M := M) g r s T.toFun S.toFun : ℝ) =
      tensorL2Inner (I := I) (M := M) g r s S.toFun T.toFun
    exact tensorL2Inner_symm (I := I) (M := M) g r s T.toFun S.toFun
  re_inner_nonneg S := by
    change (0 : ℝ) ≤ tensorL2Inner (I := I) (M := M) g r s S.toFun S.toFun
    exact tensorL2Inner_nonneg (I := I) (M := M) g r s S.toFun
  add_left S₁ S₂ T := by
    change tensorL2Inner (I := I) (M := M) g r s (S₁ + S₂).toFun T.toFun =
      tensorL2Inner (I := I) (M := M) g r s S₁.toFun T.toFun +
        tensorL2Inner (I := I) (M := M) g r s S₂.toFun T.toFun
    rw [SmoothCcTensor.toFun_add]
    exact tensorL2Inner_add_left (I := I) (M := M) g r s S₁.toFun S₂.toFun T.toFun
      (SmoothCcTensor.integrable_inner_cross (I := I) (M := M) S₁ T)
      (SmoothCcTensor.integrable_inner_cross (I := I) (M := M) S₂ T)
  smul_left S T c := by
    change tensorL2Inner (I := I) (M := M) g r s (c • S).toFun T.toFun =
      c * tensorL2Inner (I := I) (M := M) g r s S.toFun T.toFun
    rw [SmoothCcTensor.toFun_smul]
    exact tensorL2Inner_smul_left (I := I) (M := M) g r s c S.toFun T.toFun

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.L2.instPreInnerProductSpaceCore then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.L2.instPreInnerProductSpaceCore"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.L2.instPreInnerProductSpaceCore ``Submission.DifferentialGeometry.Integral.L2.instPreInnerProductSpaceCore


noncomputable instance instSeminormedAddCommGroup :
    SeminormedAddCommGroup (SmoothCcTensor g r s) :=
  InnerProductSpace.Core.toSeminormedAddCommGroup (𝕜 := ℝ)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.L2.instSeminormedAddCommGroup then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.L2.instSeminormedAddCommGroup"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.L2.instSeminormedAddCommGroup ``Submission.DifferentialGeometry.Integral.L2.instSeminormedAddCommGroup


noncomputable instance instInnerProductSpace :
    InnerProductSpace ℝ (SmoothCcTensor g r s) :=
  InnerProductSpace.ofCore _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.L2.instInnerProductSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.L2.instInnerProductSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.L2.instInnerProductSpace ``Submission.DifferentialGeometry.Integral.L2.instInnerProductSpace


@[simp] theorem SmoothCcTensor.inner_def (S T : SmoothCcTensor g r s) :
    ⟪S, T⟫_ℝ = tensorL2Inner (I := I) (M := M) g r s S.toFun T.toFun := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.L2.SmoothCcTensor.inner_def then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.L2.SmoothCcTensor.inner_def"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.L2.SmoothCcTensor.inner_def ``Submission.DifferentialGeometry.Integral.L2.SmoothCcTensor.inner_def


theorem SmoothCcTensor.norm_def (S : SmoothCcTensor g r s) :
    ‖S‖ = tensorL2Norm (I := I) (M := M) g r s S.toFun := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.L2.SmoothCcTensor.norm_def then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.L2.SmoothCcTensor.norm_def"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.L2.SmoothCcTensor.norm_def ``Submission.DifferentialGeometry.Integral.L2.SmoothCcTensor.norm_def

theorem tensorL2Inner_sub_left_smoothCc
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S₁ S₂ T : SmoothCcTensor g r s) :
    tensorL2Inner (I := I) (M := M) g r s
        (S₁.toFun - S₂.toFun) T.toFun =
      tensorL2Inner (I := I) (M := M) g r s S₁.toFun T.toFun -
        tensorL2Inner (I := I) (M := M) g r s S₂.toFun T.toFun := by
  rw [← SmoothCcTensor.toFun_sub]
  change ⟪S₁ - S₂, T⟫_ℝ = ⟪S₁, T⟫_ℝ - ⟪S₂, T⟫_ℝ
  exact inner_sub_left S₁ S₂ T

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.L2.tensorL2Inner_sub_left_smoothCc then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.L2.tensorL2Inner_sub_left_smoothCc"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.L2.tensorL2Inner_sub_left_smoothCc ``Submission.DifferentialGeometry.Integral.L2.tensorL2Inner_sub_left_smoothCc

theorem tensorL2Inner_sub_right_smoothCc
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S T₁ T₂ : SmoothCcTensor g r s) :
    tensorL2Inner (I := I) (M := M) g r s
        S.toFun (T₁.toFun - T₂.toFun) =
      tensorL2Inner (I := I) (M := M) g r s S.toFun T₁.toFun -
        tensorL2Inner (I := I) (M := M) g r s S.toFun T₂.toFun := by
  rw [← SmoothCcTensor.toFun_sub]
  change ⟪S, T₁ - T₂⟫_ℝ = ⟪S, T₁⟫_ℝ - ⟪S, T₂⟫_ℝ
  exact inner_sub_right S T₁ T₂

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.L2.tensorL2Inner_sub_right_smoothCc then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.L2.tensorL2Inner_sub_right_smoothCc"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.L2.tensorL2Inner_sub_right_smoothCc ``Submission.DifferentialGeometry.Integral.L2.tensorL2Inner_sub_right_smoothCc

end PreHilbert

end L2
end Integral
end DifferentialGeometry

end
