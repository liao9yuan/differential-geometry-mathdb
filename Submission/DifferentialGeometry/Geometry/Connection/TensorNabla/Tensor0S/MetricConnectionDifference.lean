import Submission.DifferentialGeometry.Geometry.Operator.CovariantTensor
import Submission.DifferentialGeometry.Geometry.Connection.MetricCompatibility.Tensor.Metric

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

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


section Flux

variable {s : ℕ}

def lapDiffFlux (g₁ g₂ : SmoothRiemannianMetric I M)
    (T : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s) :
    Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (s + 1) :=
  metricNabla0S (I := I) g₁ T - metricNabla0S (I := I) g₂ T

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.lapDiffFlux then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.lapDiffFlux"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.lapDiffFlux ``Submission.DifferentialGeometry.PDE.RicciFlow.lapDiffFlux

omit [SigmaCompactSpace M] in
theorem lapDiffFlux_apply (g₁ g₂ : SmoothRiemannianMetric I M)
    (T : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s) (x : M) :
    lapDiffFlux (I := I) g₁ g₂ T x =
      totalNabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s
          (metricCov (I := I) g₁) T x -
        totalNabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s
          (metricCov (I := I) g₂) T x := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.lapDiffFlux_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.lapDiffFlux_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.lapDiffFlux_apply ``Submission.DifferentialGeometry.PDE.RicciFlow.lapDiffFlux_apply

omit [SigmaCompactSpace M] in
@[simp] theorem lapDiffFlux_self (g : SmoothRiemannianMetric I M)
    (T : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s) :
    lapDiffFlux (I := I) g g T = 0 :=
  sub_self _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.lapDiffFlux_self then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.lapDiffFlux_self"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.lapDiffFlux_self ``Submission.DifferentialGeometry.PDE.RicciFlow.lapDiffFlux_self

end Flux

variable [BoundarylessManifold I M]

section Parallel

omit [SigmaCompactSpace M] [BoundarylessManifold I M] in
theorem metricNabla0S_self (g : SmoothRiemannianMetric I M) :
    metricNabla0S (I := I) g (metricTensorField (I := I) g) =
      (0 : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        (n := (∞ : WithTop ℕ∞)) 3) := by
  classical
  have hmc : DifferentialGeometry.Geometry.Connection.IsMetricCompatible
      (I := I) (metricCov (I := I) g) g :=
    DifferentialGeometry.Geometry.Connection.leviCivitaConnectionOfMetric_isMetricCompatible
      (I := I) g
  refine DFunLike.ext _ _ fun x => ?_
  have hfib : metricNabla0S (I := I) g (metricTensorField (I := I) g) x = 0 := by
    refine ContinuousMultilinearMap.ext fun v => ?_
    obtain ⟨Xsec, hXx⟩ :=
      ContMDiffSection.exists_eq_at
        (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞)) x (v 0)
    have hv : Fin.cons (Xsec x) (Fin.tail v) = v := by
      rw [hXx]
      exact Fin.cons_self_tail v
    have hsec := totalNabla0SFun_apply_section (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) 2 (metricCov (I := I) g) Xsec (metricTensorField (I := I) g) x
      (Fin.tail v)
    rw [hv] at hsec
    have hzero := nabla_metric_zero (I := I) (metricCov (I := I) g) g hmc Xsec x
    rw [metricNabla0S_apply]
    exact hsec.trans (by
      rw [hzero]
      rfl)
  rw [hfib]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.metricNabla0S_self then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.metricNabla0S_self"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.metricNabla0S_self ``Submission.DifferentialGeometry.PDE.RicciFlow.metricNabla0S_self

omit [SigmaCompactSpace M] [BoundarylessManifold I M] in
theorem nabla2_metric1 (g₁ g₂ : SmoothRiemannianMetric I M) :
    metricNabla0S (I := I) g₂ (metricTensorField (I := I) g₁) =
      -lapDiffFlux (I := I) g₁ g₂ (metricTensorField (I := I) g₁) := by
  rw [lapDiffFlux, metricNabla0S_self]
  abel

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.nabla2_metric1 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.nabla2_metric1"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.nabla2_metric1 ``Submission.DifferentialGeometry.PDE.RicciFlow.nabla2_metric1

end Parallel


end DifferentialGeometry.PDE.RicciFlow

end
