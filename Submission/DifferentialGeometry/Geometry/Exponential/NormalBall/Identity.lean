import Submission.DifferentialGeometry.Geometry.Exponential.NormalBall.Chart

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section
open _root_.Set
open scoped _root_.ContDiff _root_.Manifold _root_.Topology

namespace DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.NormalBallChart

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

def identity {r : ℝ} (hr : 0 < r) : NormalBallChart (I := 𝓘(ℝ, E)) (0 : E) where
  radius := r
  radius_pos := hr
  hom :=
    { toPartialEquiv := PartialEquiv.refl E
      open_source := isOpen_univ
      open_target := isOpen_univ
      contMDiffOn_toFun := contMDiffOn_id
      contMDiffOn_invFun := contMDiffOn_id }
  ball_subset := _root_.Set.subset_univ _
  map_zero := rfl
  smooth_to := contMDiffOn_id
  smooth_inv := contMDiffOn_id

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.NormalBallChart.identity then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.NormalBallChart.identity"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.NormalBallChart.identity ``Submission.DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.NormalBallChart.identity

@[simp] theorem identity_radius {r : ℝ} (hr : 0 < r) :
    (identity (E := E) hr).radius = r := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.NormalBallChart.identity_radius then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.NormalBallChart.identity_radius"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.NormalBallChart.identity_radius ``Submission.DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.NormalBallChart.identity_radius

@[simp] theorem identity_apply {r : ℝ} (hr : 0 < r) (z : E) :
    (identity (E := E) hr).hom z = z := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.NormalBallChart.identity_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.NormalBallChart.identity_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.NormalBallChart.identity_apply ``Submission.DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.NormalBallChart.identity_apply

@[simp] theorem identity_inv {r : ℝ} (hr : 0 < r) (z : E) :
    (identity (E := E) hr).inv z = z := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.NormalBallChart.identity_inv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.NormalBallChart.identity_inv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.NormalBallChart.identity_inv ``Submission.DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.NormalBallChart.identity_inv

@[simp] theorem metric_identity (g : SmoothRiemannianMetric 𝓘(ℝ, E) E)
    {r : ℝ} (hr : 0 < r) :
    (identity (E := E) hr).metric g = fun z => g.inner z := by
  funext z
  apply ContinuousLinearMap.ext
  intro v
  apply ContinuousLinearMap.ext
  intro w
  rw [metric_apply]
  change g.inner z (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) id z v)
    (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) id z w) = g.inner z v w
  rw [mfderiv_id]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.NormalBallChart.metric_identity then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.NormalBallChart.metric_identity"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.NormalBallChart.metric_identity ``Submission.DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.NormalBallChart.metric_identity


end DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.NormalBallChart

end
