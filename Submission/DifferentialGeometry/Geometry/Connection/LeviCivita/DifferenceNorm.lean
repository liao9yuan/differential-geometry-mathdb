import Submission.DifferentialGeometry.Geometry.Curvature.Metric.Defs
import Submission.DifferentialGeometry.Geometry.Connection.TensorNabla.Tensor0S.ConnectionDifference
import Submission.DifferentialGeometry.Geometry.Metric.TensorInner.FiberMetric.Tensor0SMetric
import Submission.DifferentialGeometry.Geometry.Metric.PointwiseInner.DualMetric

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open _root_.Bundle _root_.Submission.Bundle _root_.Submission.DifferentialGeometry.Tensor0SBundle
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Connection
open scoped _root_.Manifold _root_.ContDiff _root_.BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

variable [SigmaCompactSpace M] [T2Space M]

omit [SigmaCompactSpace M] in
private theorem covDiff_self
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _)) (x : M) :
    CovariantDerivative.difference cov cov x = 0 := by
  classical
  refine ContinuousLinearMap.ext fun w => ?_
  obtain ⟨σ, hσx⟩ := ContMDiffSection.exists_eq_at (I := I) (n := (⊤ : ℕ∞))
    (F := E) (V := (TangentSpace I : M -> Type _)) x w
  have hσ : MDiffAt (T% fun y => σ y) x := σ.mdifferentiableAt
  have h := IsCovariantDerivativeOn.difference_apply
    cov.isCovariantDerivativeOnUniv cov.isCovariantDerivativeOnUniv
    (x := x) (Set.mem_univ x) (σ := fun y => σ y) hσ
  rw [sub_self] at h
  rw [← hσx]
  simpa [CovariantDerivative.difference] using h

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.covDiff_self
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.covDiff_self target :: scope.openDecls } }

private def connectionDifferenceOutAt (g : SmoothRiemannianMetric I M)
    (cov cov' : CovariantDerivative I E (TangentSpace I : M -> Type _)) (x : M) :
    Tensor0SSpace 3 I x :=
  Tensor0SSpace.ofModel (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
    (DifferentialGeometry.Integral.L2.lowerAllUpperIndices (I := I) (M := M) g 1 2 x
      (TensorRSSpace.toModel (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        (connectionDifferenceTensorAt (I := I) cov cov' x)))

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.connectionDifferenceOutAt
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.connectionDifferenceOutAt target :: scope.openDecls } }

private def connectionDifferenceStandardPerm : Equiv.Perm (Fin 3) where
  toFun i := if i = 0 then 2 else if i = 1 then 0 else 1
  invFun i := if i = 0 then 1 else if i = 1 then 2 else 0
  left_inv i := by fin_cases i <;> simp
  right_inv i := by fin_cases i <;> simp

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.connectionDifferenceStandardPerm
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.connectionDifferenceStandardPerm target :: scope.openDecls } }

omit [SigmaCompactSpace M] [T2Space M] in
private theorem connectionDifferenceOutAt_apply (g : SmoothRiemannianMetric I M)
    (cov cov' : CovariantDerivative I E (TangentSpace I : M -> Type _)) (x : M)
    (w : Fin 3 -> TangentSpace I x) :
    connectionDifferenceOutAt (I := I) g cov cov' x w =
      g.inner x (w 0) (CovariantDerivative.difference cov cov' x (w 2) (w 1)) := by
  change
    DifferentialGeometry.Integral.L2.lowerAllUpperIndices (I := I) (M := M) g 1 2 x
        (TensorRSSpace.toModel (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
          (connectionDifferenceTensorAt (I := I) cov cov' x))
        (fun i => tangentSpaceModelContinuousLinearEquiv (I := I) x (w i)) = _
  rw [DifferentialGeometry.Integral.L2.lowerAllUpperIndices_apply]
  change
    Tensor0SSpace.eval
      (connectionDifferenceOutput (I := I) (CovariantDerivative.difference cov cov' x)
        (Tensor0SSpace.ofModel (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
          (DifferentialGeometry.Integral.L2.separableFormAt (I := I) (M := M) g x 1
            (fun i : Fin 1 =>
              tangentSpaceModelContinuousLinearEquiv (I := I) x (w (Fin.castAdd 2 i))))))
        (fun j : Fin 2 => w (Fin.natAdd 1 j)) = _
  rw [connectionDifferenceOutput_apply]
  change
    DifferentialGeometry.Integral.L2.separableFormAt (I := I) (M := M) g x 1
        (fun i : Fin 1 =>
          tangentSpaceModelContinuousLinearEquiv (I := I) x (w (Fin.castAdd 2 i)))
        (fun _ : Fin 1 =>
          tangentSpaceModelContinuousLinearEquiv (I := I) x
            (CovariantDerivative.difference cov cov' x
              (w (Fin.natAdd 1 (1 : Fin 2))) (w (Fin.natAdd 1 (0 : Fin 2))))) = _
  rw [DifferentialGeometry.Integral.L2.separableFormAt_apply]
  simp only [DifferentialGeometry.Integral.L2.modelInnerAt_apply,
    ContinuousLinearEquiv.symm_apply_apply]
  simp

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.connectionDifferenceOutAt_apply
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.connectionDifferenceOutAt_apply target :: scope.openDecls } }

def connectionDifferenceLowAt (g₁ g₂ : SmoothRiemannianMetric I M) (x : M) :
    Tensor0SSpace 3 I x :=
  ContinuousMultilinearMap.domDomCongr connectionDifferenceStandardPerm
    (connectionDifferenceOutAt (I := I) g₁ (metricCov (I := I) g₁) (metricCov (I := I) g₂) x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.connectionDifferenceLowAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.connectionDifferenceLowAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.connectionDifferenceLowAt ``Submission.DifferentialGeometry.PDE.RicciFlow.connectionDifferenceLowAt

omit [SigmaCompactSpace M] [T2Space M] in
theorem connectionDifferenceLowAt_apply (g₁ g₂ : SmoothRiemannianMetric I M) (x : M)
    (v : Fin 3 -> TangentSpace I x) :
    Tensor0SSpace.eval (connectionDifferenceLowAt (I := I) g₁ g₂ x) v =
      g₁.inner x
        (CovariantDerivative.difference (metricCov (I := I) g₁) (metricCov (I := I) g₂) x
          (v 1) (v 0))
        (v 2) := by
  have h : Tensor0SSpace.eval (connectionDifferenceLowAt (I := I) g₁ g₂ x) v =
      g₁.inner x (v 2)
        (CovariantDerivative.difference (metricCov (I := I) g₁) (metricCov (I := I) g₂) x
          (v 1) (v 0)) :=
    connectionDifferenceOutAt_apply (I := I) g₁ (metricCov (I := I) g₁) (metricCov (I := I) g₂) x
      (fun i : Fin 3 => v (connectionDifferenceStandardPerm i))
  rw [h]
  exact g₁.symm x (v 2)
    (CovariantDerivative.difference (metricCov (I := I) g₁) (metricCov (I := I) g₂) x
      (v 1) (v 0))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.connectionDifferenceLowAt_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.connectionDifferenceLowAt_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.connectionDifferenceLowAt_apply ``Submission.DifferentialGeometry.PDE.RicciFlow.connectionDifferenceLowAt_apply

omit [SigmaCompactSpace M] in
@[simp]
theorem connectionDifferenceLowAt_self (g : SmoothRiemannianMetric I M) (x : M) :
    connectionDifferenceLowAt (I := I) g g x = 0 := by
  refine ContinuousMultilinearMap.ext fun v => ?_
  change Tensor0SSpace.eval (connectionDifferenceLowAt (I := I) g g x) v =
    Tensor0SSpace.eval 0 v
  rw [connectionDifferenceLowAt_apply, covDiff_self]
  change g.inner x 0 (v 2) = 0
  rw [map_zero (g.inner x), zero_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.connectionDifferenceLowAt_self then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.connectionDifferenceLowAt_self"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.connectionDifferenceLowAt_self ``Submission.DifferentialGeometry.PDE.RicciFlow.connectionDifferenceLowAt_self

def connectionDifferenceSq (g₁ g₂ : SmoothRiemannianMetric I M) (x : M) : Real :=
  normSq0S (I := I) g₁ x 3 (connectionDifferenceLowAt (I := I) g₁ g₂ x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.connectionDifferenceSq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.connectionDifferenceSq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.connectionDifferenceSq ``Submission.DifferentialGeometry.PDE.RicciFlow.connectionDifferenceSq

omit [SigmaCompactSpace M] [T2Space M] in
theorem connectionDifferenceSq_def (g₁ g₂ : SmoothRiemannianMetric I M) (x : M) :
    connectionDifferenceSq (I := I) g₁ g₂ x =
      normSq0S (I := I) g₁ x 3 (connectionDifferenceLowAt (I := I) g₁ g₂ x) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.connectionDifferenceSq_def then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.connectionDifferenceSq_def"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.connectionDifferenceSq_def ``Submission.DifferentialGeometry.PDE.RicciFlow.connectionDifferenceSq_def


end DifferentialGeometry.PDE.RicciFlow

end
