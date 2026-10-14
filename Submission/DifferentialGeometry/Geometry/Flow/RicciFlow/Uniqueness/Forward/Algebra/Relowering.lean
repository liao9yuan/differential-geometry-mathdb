import Submission.DifferentialGeometry.Geometry.Connection.MetricTrace.Relowering
import Submission.DifferentialGeometry.Geometry.Connection.TensorNabla.Tensor0S.Relowering
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Uniqueness.Forward.Curvature.AlgebraicBridge
import Submission.DifferentialGeometry.Geometry.Connection.TensorNabla.Naturality.SlotPermutation
import Submission.DifferentialGeometry.Geometry.Connection.TensorNabla.Tensor0S.Algebra.ContractionLeibniz

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open _root_.Bundle _root_.Submission.Bundle _root_.Submission.DifferentialGeometry.Tensor0SBundle
open _root_.Submission.DifferentialGeometry.Integral.Connection
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Connection
open _root_.Submission.DifferentialGeometry.Geometry.Operator
open _root_.Submission.DifferentialGeometry.Tensor.RSTensor
open scoped _root_.Manifold _root_.ContDiff _root_.BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

variable [SigmaCompactSpace M] [T2Space M] [I.Boundaryless]

section ReLower

omit [SigmaCompactSpace M] in
theorem reLower_rm04 (g₁ g₂ : SmoothRiemannianMetric I M)
    (Rm2 : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 4)
    (x : M) (hRm : Rm2 x = metricRm04At (I := I) g₂ x)
    (X Y Z W : TangentSpace I x) :
    Tensor0SSpace.eval (reLower (I := I) g₁ g₂ Rm2 x)
        (vec4 (I := I) X Y Z W) =
      g₁.inner x (riemannOp (metricCov (I := I) g₂) x X Y Z) W := by
  classical
  have hlast : (vec4 (I := I) X Y Z W) (Fin.last 3) = W := by
    simp [vec4]
  have hupd : Function.update (vec4 (I := I) X Y Z W) (Fin.last 3)
      (sharpFlat (I := I) g₁ g₂ x W) =
      vec4 (I := I) X Y Z (sharpFlat (I := I) g₁ g₂ x W) := by
    funext i
    fin_cases i <;> simp [vec4, Function.update]
  rw [reLower_apply (I := I) g₁ g₂ Rm2 x, hlast, hupd, hRm]
  exact mixLow_eq_rm04 (I := I) g₁ g₂ x X Y Z W

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.reLower_rm04 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.reLower_rm04"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.reLower_rm04 ``Submission.DifferentialGeometry.PDE.RicciFlow.reLower_rm04

end ReLower

section Defect

omit [SigmaCompactSpace M] [T2Space M] [I.Boundaryless] in
private theorem metricCov_one (g : SmoothRiemannianMetric I M) :
    CovariantDerivative.ContMDiffCovariantDerivativeLocally
      (I := I) (E := E) (M := M) (metricCov (I := I) g) (1 : WithTop ℕ∞) := by
  simpa [metricCov] using
    (DifferentialGeometry.Geometry.Connection.leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally_one
      (I := I) (M := M) g)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.metricCov_one
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.metricCov_one target :: scope.openDecls } }

end Defect

section Payoff

def reLowerOp (g₁ g₂ : SmoothRiemannianMetric I M) :
    ∀ k : ℕ, Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        (n := (∞ : WithTop ℕ∞)) k ->
      Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        (n := (∞ : WithTop ℕ∞)) k
  | 0 => id
  | (_ + 1) => fun T => reLower (I := I) g₁ g₂ T

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.reLowerOp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.reLowerOp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.reLowerOp ``Submission.DifferentialGeometry.PDE.RicciFlow.reLowerOp

omit [SigmaCompactSpace M] [T2Space M] [I.Boundaryless] in
@[simp] theorem reLowerOp_succ (g₁ g₂ : SmoothRiemannianMetric I M) {k : ℕ}
    (T : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (k + 1)) :
    reLowerOp (I := I) g₁ g₂ (k + 1) T = reLower (I := I) g₁ g₂ T := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.reLowerOp_succ then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.reLowerOp_succ"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.reLowerOp_succ ``Submission.DifferentialGeometry.PDE.RicciFlow.reLowerOp_succ

omit [I.Boundaryless] [SigmaCompactSpace M] in
theorem lapCommFlux_reLower (g₁ g₂ : SmoothRiemannianMetric I M) {k : ℕ}
    (T : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (k + 1)) :
    lapCommFlux (I := I) g₂ (reLowerOp (I := I) g₁ g₂) T =
      reLowerPair (I := I) g₂ T
        (metricNabla0S (I := I) g₂ (metricTensorField (I := I) g₁)) := by
  rw [lapCommFlux, reLowerOp_succ, reLowerOp_succ, nabla_reLower]
  abel

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.lapCommFlux_reLower then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.lapCommFlux_reLower"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.lapCommFlux_reLower ``Submission.DifferentialGeometry.PDE.RicciFlow.lapCommFlux_reLower

omit [I.Boundaryless] [SigmaCompactSpace M] in
theorem lapComm_reLower (g₁ g₂ : SmoothRiemannianMetric I M) {k : ℕ}
    (T : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (k + 1)) :
    roughLap0SField (I := I) g₂ (reLower (I := I) g₁ g₂ T) -
        reLower (I := I) g₁ g₂ (roughLap0SField (I := I) g₂ T) =
      covDiv0SField (I := I) g₂
          (reLowerPair (I := I) g₂ T
            (metricNabla0S (I := I) g₂ (metricTensorField (I := I) g₁))) +
        lapCommRem (I := I) g₂ (reLowerOp (I := I) g₁ g₂) T := by
  have h := lapComm_eq_div_flux (I := I) g₂ (reLowerOp (I := I) g₁ g₂) T
  rw [lapCommFlux_reLower (I := I) g₁ g₂ T] at h
  simpa using h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.lapComm_reLower then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.lapComm_reLower"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.lapComm_reLower ``Submission.DifferentialGeometry.PDE.RicciFlow.lapComm_reLower

omit [I.Boundaryless] [SigmaCompactSpace M] in
theorem lapCommRem_reLower (g₁ g₂ : SmoothRiemannianMetric I M) {k : ℕ}
    (T : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (k + 1)) :
    lapCommRem (I := I) g₂ (reLowerOp (I := I) g₁ g₂) T =
      metricTraceFirstTwoField (I := I) (M := M) (s := k + 1) g₂
        (reLowerPair (I := I) g₂ (metricNabla0S (I := I) g₂ T)
          (metricNabla0S (I := I) g₂ (metricTensorField (I := I) g₁))) := by
  rw [lapCommRem, reLowerOp_succ, reLowerOp_succ, covDiv0SField, covDiv0SField,
    nabla_reLower, metricTraceFirstTwoField_add, trace_reLower]
  abel

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.lapCommRem_reLower then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.lapCommRem_reLower"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.lapCommRem_reLower ``Submission.DifferentialGeometry.PDE.RicciFlow.lapCommRem_reLower

omit [I.Boundaryless] [SigmaCompactSpace M] in
theorem lapComm_reLower_eq (g₁ g₂ : SmoothRiemannianMetric I M) {k : ℕ}
    (T : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (k + 1)) :
    roughLap0SField (I := I) g₂ (reLower (I := I) g₁ g₂ T) -
        reLower (I := I) g₁ g₂ (roughLap0SField (I := I) g₂ T) =
      covDiv0SField (I := I) g₂
          (reLowerPair (I := I) g₂ T
            (metricNabla0S (I := I) g₂ (metricTensorField (I := I) g₁))) +
        metricTraceFirstTwoField (I := I) (M := M) (s := k + 1) g₂
          (reLowerPair (I := I) g₂ (metricNabla0S (I := I) g₂ T)
            (metricNabla0S (I := I) g₂ (metricTensorField (I := I) g₁))) := by
  rw [lapComm_reLower (I := I) g₁ g₂ T, lapCommRem_reLower (I := I) g₁ g₂ T]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.lapComm_reLower_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.lapComm_reLower_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.lapComm_reLower_eq ``Submission.DifferentialGeometry.PDE.RicciFlow.lapComm_reLower_eq

omit [I.Boundaryless] [SigmaCompactSpace M] in
theorem lapComm_reLower_flux (g₁ g₂ : SmoothRiemannianMetric I M) {k : ℕ}
    (T : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (k + 1)) :
    roughLap0SField (I := I) g₂ (reLower (I := I) g₁ g₂ T) -
        reLower (I := I) g₁ g₂ (roughLap0SField (I := I) g₂ T) =
      covDiv0SField (I := I) g₂
          (reLowerPair (I := I) g₂ T
            (-lapDiffFlux (I := I) g₁ g₂ (metricTensorField (I := I) g₁))) +
        metricTraceFirstTwoField (I := I) (M := M) (s := k + 1) g₂
          (reLowerPair (I := I) g₂ (metricNabla0S (I := I) g₂ T)
            (-lapDiffFlux (I := I) g₁ g₂ (metricTensorField (I := I) g₁))) := by
  rw [lapComm_reLower_eq (I := I) g₁ g₂ T, nabla2_metric1 (I := I) g₁ g₂]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.lapComm_reLower_flux then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.lapComm_reLower_flux"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.lapComm_reLower_flux ``Submission.DifferentialGeometry.PDE.RicciFlow.lapComm_reLower_flux

end Payoff

end DifferentialGeometry.PDE.RicciFlow

end
