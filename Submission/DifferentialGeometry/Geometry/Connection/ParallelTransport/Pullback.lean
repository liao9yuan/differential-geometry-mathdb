import Submission.DifferentialGeometry.Geometry.Connection.ParallelTransport.Construction.Endpoint
import Submission.DifferentialGeometry.Tensor.Alternating.Composition

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

namespace CovariantDerivative

open _root_.Submission.DifferentialGeometry
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian.Variation
open scoped _root_.Manifold _root_.ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M]

noncomputable def pullbackParallelTransportLinearEquivBetween
    [I.Boundaryless]
    (phi : ∀ x : M, TangentSpace I x ≃ₗ[Real] TangentSpace I x)
    (g : SmoothRiemannianMetric I M) (gamma : Real → M)
    (hgamma : ContMDiff 𝓘(Real, Real) I (2 : ℕ∞) gamma)
    {a b : Real} (hab : a < b) :
    TangentSpace I (gamma a) ≃ₗ[Real] TangentSpace I (gamma b) :=
  (phi (gamma a)).trans
    ((parallelTransportLinearEquivBetween (I := I) g gamma hgamma hab).trans
      (phi (gamma b)).symm)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `CovariantDerivative.pullbackParallelTransportLinearEquivBetween then
    throwError "Refusing to shadow existing declaration CovariantDerivative.pullbackParallelTransportLinearEquivBetween"
  Lean.modifyEnv fun env => Lean.addAlias env `CovariantDerivative.pullbackParallelTransportLinearEquivBetween ``Submission.CovariantDerivative.pullbackParallelTransportLinearEquivBetween

@[simp] theorem pullbackParallelTransportLinearEquivBetween_apply
    [I.Boundaryless]
    (phi : ∀ x : M, TangentSpace I x ≃ₗ[Real] TangentSpace I x)
    (g : SmoothRiemannianMetric I M) (gamma : Real → M)
    (hgamma : ContMDiff 𝓘(Real, Real) I (2 : ℕ∞) gamma)
    {a b : Real} (hab : a < b) (v : TangentSpace I (gamma a)) :
    pullbackParallelTransportLinearEquivBetween phi g gamma hgamma hab v =
      (phi (gamma b)).symm
        (parallelTransportLinearEquivBetween (I := I) g gamma hgamma hab
          (phi (gamma a) v)) :=
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `CovariantDerivative.pullbackParallelTransportLinearEquivBetween_apply then
    throwError "Refusing to shadow existing declaration CovariantDerivative.pullbackParallelTransportLinearEquivBetween_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `CovariantDerivative.pullbackParallelTransportLinearEquivBetween_apply ``Submission.CovariantDerivative.pullbackParallelTransportLinearEquivBetween_apply

theorem pullbackParallelTransportLinearEquivBetween_intertwining
    [I.Boundaryless]
    (phi : ∀ x : M, TangentSpace I x ≃ₗ[Real] TangentSpace I x)
    (g : SmoothRiemannianMetric I M) (gamma : Real → M)
    (hgamma : ContMDiff 𝓘(Real, Real) I (2 : ℕ∞) gamma)
    {a b : Real} (hab : a < b) :
    (phi (gamma b)).toLinearMap.comp
        (pullbackParallelTransportLinearEquivBetween
          phi g gamma hgamma hab).toLinearMap =
      (parallelTransportLinearEquivBetween (I := I) g gamma hgamma hab).toLinearMap.comp
        (phi (gamma a)).toLinearMap := by
  ext v
  simp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `CovariantDerivative.pullbackParallelTransportLinearEquivBetween_intertwining then
    throwError "Refusing to shadow existing declaration CovariantDerivative.pullbackParallelTransportLinearEquivBetween_intertwining"
  Lean.modifyEnv fun env => Lean.addAlias env `CovariantDerivative.pullbackParallelTransportLinearEquivBetween_intertwining ``Submission.CovariantDerivative.pullbackParallelTransportLinearEquivBetween_intertwining

theorem pullbackParallelTransportContinuousAlternatingMap_intertwining
    [I.Boundaryless]
    (phi : ∀ x : M, TangentSpace I x ≃ₗ[Real] TangentSpace I x)
    (g : SmoothRiemannianMetric I M) (gamma : Real → M)
    (hgamma : ContMDiff 𝓘(Real, Real) I (2 : ℕ∞) gamma)
    {a b : Real} (hab : a < b) :
    let PSource := (pullbackParallelTransportLinearEquivBetween
      phi g gamma hgamma hab).toContinuousLinearEquiv
    let PTarget :=
      (parallelTransportLinearEquivBetween
        (I := I) g gamma hgamma hab).toContinuousLinearEquiv
    let FSource := (phi (gamma a)).toContinuousLinearEquiv
      |>.continuousAlternatingMapCongrLeft (ι := Fin 2) (F := Real)
    let FTarget := (phi (gamma b)).toContinuousLinearEquiv
      |>.continuousAlternatingMapCongrLeft (ι := Fin 2) (F := Real)
    FTarget.toLinearMap.comp
        (PSource.continuousAlternatingMapCongrLeft
          (ι := Fin 2) (F := Real)).toLinearMap =
      (PTarget.continuousAlternatingMapCongrLeft
        (ι := Fin 2) (F := Real)).toLinearMap.comp FSource.toLinearMap := by
  dsimp only
  apply LinearMap.ext
  intro alpha
  apply ContinuousAlternatingMap.ext
  intro v
  change alpha (fun i =>
      (phi (gamma a)).symm
        ((parallelTransportLinearEquivBetween
          (I := I) g gamma hgamma hab).symm
          (phi (gamma b) ((phi (gamma b)).symm (v i))))) =
    alpha (fun i =>
      (phi (gamma a)).symm
        ((parallelTransportLinearEquivBetween
          (I := I) g gamma hgamma hab).symm (v i)))
  simp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `CovariantDerivative.pullbackParallelTransportContinuousAlternatingMap_intertwining then
    throwError "Refusing to shadow existing declaration CovariantDerivative.pullbackParallelTransportContinuousAlternatingMap_intertwining"
  Lean.modifyEnv fun env => Lean.addAlias env `CovariantDerivative.pullbackParallelTransportContinuousAlternatingMap_intertwining ``Submission.CovariantDerivative.pullbackParallelTransportContinuousAlternatingMap_intertwining

end CovariantDerivative
