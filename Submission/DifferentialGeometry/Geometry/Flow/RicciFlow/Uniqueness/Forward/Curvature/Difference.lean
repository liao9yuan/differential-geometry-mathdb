import Submission.DifferentialGeometry.Geometry.Connection.TensorNabla.Tensor0S.MetricConnectionDifference
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Uniqueness.Forward.Data.DifferenceFields
import Submission.DifferentialGeometry.Geometry.Operator.CovariantTensor

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
open _root_.Submission.DifferentialGeometry.Geometry.Operator
open _root_.Submission.DifferentialGeometry.Tensor.RSTensor
open scoped _root_.Manifold _root_.ContDiff _root_.BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

variable [SigmaCompactSpace M] [T2Space M]


section DivergenceForm

variable {s : ℕ}

def lapDiffRem (g₁ g₂ : SmoothRiemannianMetric I M)
    (T : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s) :
    Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s :=
  metricTraceFirstTwoField (I := I) (M := M) g₁
      (lapDiffFlux (I := I) g₁ g₂ (metricNabla0S (I := I) g₂ T)) +
    (metricTraceFirstTwoField (I := I) (M := M) g₁
        (metricNabla0S (I := I) g₂ (metricNabla0S (I := I) g₂ T)) -
      metricTraceFirstTwoField (I := I) (M := M) g₂
        (metricNabla0S (I := I) g₂ (metricNabla0S (I := I) g₂ T)))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.lapDiffRem then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.lapDiffRem"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.lapDiffRem ``Submission.DifferentialGeometry.PDE.RicciFlow.lapDiffRem

omit [SigmaCompactSpace M] in
@[simp] theorem lapDiffRem_self (g : SmoothRiemannianMetric I M)
    (T : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s) :
    lapDiffRem (I := I) g g T = 0 := by
  rw [lapDiffRem, lapDiffFlux_self, traceFirstTwo_zero, sub_self, add_zero]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.lapDiffRem_self then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.lapDiffRem_self"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.lapDiffRem_self ``Submission.DifferentialGeometry.PDE.RicciFlow.lapDiffRem_self

omit [SigmaCompactSpace M] in
theorem lapDiff_eq_div_flux (g₁ g₂ : SmoothRiemannianMetric I M)
    (T : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s) :
    roughLap0SField (I := I) g₁ T - roughLap0SField (I := I) g₂ T =
      covDiv0SField (I := I) g₁ (lapDiffFlux (I := I) g₁ g₂ T) +
        lapDiffRem (I := I) g₁ g₂ T := by
  have hdiv :
      covDiv0SField (I := I) g₁ (lapDiffFlux (I := I) g₁ g₂ T) =
        roughLap0SField (I := I) g₁ T -
          covDiv0SField (I := I) g₁ (metricNabla0S (I := I) g₂ T) := by
    rw [lapDiffFlux, covDiv0SField_sub, roughLap0SField]
  have hrem :
      lapDiffRem (I := I) g₁ g₂ T =
        (covDiv0SField (I := I) g₁ (metricNabla0S (I := I) g₂ T) -
            metricTraceFirstTwoField (I := I) (M := M) g₁
              (metricNabla0S (I := I) g₂ (metricNabla0S (I := I) g₂ T))) +
          (metricTraceFirstTwoField (I := I) (M := M) g₁
              (metricNabla0S (I := I) g₂ (metricNabla0S (I := I) g₂ T)) -
            roughLap0SField (I := I) g₂ T) := by
    rw [lapDiffRem, lapDiffFlux, traceFirstTwo_sub, roughLap0SField, covDiv0SField,
      covDiv0SField]
  rw [hdiv, hrem]
  abel

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.lapDiff_eq_div_flux then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.lapDiff_eq_div_flux"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.lapDiff_eq_div_flux ``Submission.DifferentialGeometry.PDE.RicciFlow.lapDiff_eq_div_flux

end DivergenceForm

section Curvature

def rmDiffFlux (g₁ g₂ : SmoothRiemannianMetric I M)
    (Rm2 : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 4) (x : M) :
    Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 5 x :=
  lapDiffFlux (I := I) g₁ g₂ Rm2 x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.rmDiffFlux then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.rmDiffFlux"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.rmDiffFlux ``Submission.DifferentialGeometry.PDE.RicciFlow.rmDiffFlux

omit [SigmaCompactSpace M] in
theorem rmDiffFlux_apply (g₁ g₂ : SmoothRiemannianMetric I M)
    (Rm2 : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 4) (x : M) :
    rmDiffFlux (I := I) g₁ g₂ Rm2 x =
      totalNabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 4
          (metricCov (I := I) g₁) Rm2 x -
        totalNabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 4
          (metricCov (I := I) g₂) Rm2 x := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.rmDiffFlux_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.rmDiffFlux_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.rmDiffFlux_apply ``Submission.DifferentialGeometry.PDE.RicciFlow.rmDiffFlux_apply

omit [SigmaCompactSpace M] [T2Space M] in
theorem rm2Low_eq_sub (g₁ g₂ : SmoothRiemannianMetric I M) (x : M) :
    DifferentialGeometry.Geometry.Curvature.CovariantDerivative.riemannCurvature04At
        (I := I) g₁ (metricCov (I := I) g₂) (metricCov_smooth (I := I) g₂) x =
      metricRm04At (I := I) g₁ x - rmDiffLowAt (I := I) g₁ g₂ x :=
  (sub_sub_cancel _ _).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.rm2Low_eq_sub then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.rm2Low_eq_sub"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.rm2Low_eq_sub ``Submission.DifferentialGeometry.PDE.RicciFlow.rm2Low_eq_sub

omit [SigmaCompactSpace M] in
theorem rmLapDiff_div_flux (g₁ g₂ : SmoothRiemannianMetric I M)
    (Rm2 : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 4) (x : M) :
    roughLap0SField (I := I) g₁ Rm2 x - roughLap0SField (I := I) g₂ Rm2 x =
      covDiv0SField (I := I) g₁ (lapDiffFlux (I := I) g₁ g₂ Rm2) x +
        lapDiffRem (I := I) g₁ g₂ Rm2 x := by
  have h := lapDiff_eq_div_flux (I := I) g₁ g₂ Rm2
  have hsub :
      (roughLap0SField (I := I) g₁ Rm2 - roughLap0SField (I := I) g₂ Rm2) x =
        roughLap0SField (I := I) g₁ Rm2 x - roughLap0SField (I := I) g₂ Rm2 x := rfl
  have hadd :
      (covDiv0SField (I := I) g₁ (lapDiffFlux (I := I) g₁ g₂ Rm2) +
          lapDiffRem (I := I) g₁ g₂ Rm2) x =
        covDiv0SField (I := I) g₁ (lapDiffFlux (I := I) g₁ g₂ Rm2) x +
          lapDiffRem (I := I) g₁ g₂ Rm2 x := rfl
  rw [← hsub, ← hadd, h]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.rmLapDiff_div_flux then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.rmLapDiff_div_flux"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.rmLapDiff_div_flux ``Submission.DifferentialGeometry.PDE.RicciFlow.rmLapDiff_div_flux

end Curvature

end DifferentialGeometry.PDE.RicciFlow

end
