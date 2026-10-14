import Submission.DifferentialGeometry.Geometry.Curvature.Algebraic.CurvatureOperatorConeMetric
import Submission.DifferentialGeometry.Geometry.Curvature.Naturality.Pullback.Cross
import Submission.DifferentialGeometry.Geometry.Curvature.Naturality.OpenRestriction
import Submission.DifferentialGeometry.Geometry.Metric.OpenEmbeddingPullback

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Set _root_.TopologicalSpace _root_.Submission.DifferentialGeometry
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Metric _root_.Submission.DifferentialGeometry.Topology.Manifold
open scoped _root_.Manifold _root_.Submission.DifferentialGeometry.Manifold _root_.ContDiff _root_.BigOperators
namespace DifferentialGeometry.Geometry.Curvature

variable {E F H H' M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace H] [TopologicalSpace H']
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F H'}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N] [T2Space N]
private local instance _root_.Submission.DifferentialGeometry.Geometry.Curvature.instCompleteSpace_differentialGeometry : CompleteSpace E := FiniteDimensional.complete ℝ E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Curvature.instCompleteSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Curvature.instCompleteSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Geometry.Curvature.instCompleteSpace_differentialGeometry_1 : CompleteSpace F := FiniteDimensional.complete ℝ F

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Curvature.instCompleteSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Curvature.instCompleteSpace_differentialGeometry_1 target :: scope.openDecls } }

theorem curvatureOperatorLowerBoundAt_iff_of_metricRm04StdAt_equiv
    (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric J N)
    (x : M) (y : N) (e : TangentSpace I x ≃ₗ[ℝ] TangentSpace J y)
    (hmetric : ∀ u v : TangentSpace I x, g.inner x u v = h.inner y (e u) (e v))
    (hRm : ∀ u v w z : TangentSpace I x,
      metricRm04StandardAt g x u v w z = metricRm04StandardAt h y (e u) (e v) (e w) (e z))
    (K : ℝ) :
    curvatureOperatorLowerBoundAt g x (metricAlgebraicCurvatureTensorAt g x) K ↔
      curvatureOperatorLowerBoundAt h y (metricAlgebraicCurvatureTensorAt h y) K := by
  have hquad (n : ℕ) (c : Fin n → ℝ) (v w : Fin n → TangentSpace I x) :
      algebraicCurvatureOperatorQuadraticEval (metricAlgebraicCurvatureTensorAt g x) c v w +
          K * algebraicCurvatureIdentityQuadraticEval g c v w =
        algebraicCurvatureOperatorQuadraticEval (metricAlgebraicCurvatureTensorAt h y) c
            (fun i => e (v i)) (fun i => e (w i)) +
          K * algebraicCurvatureIdentityQuadraticEval h c
            (fun i => e (v i)) (fun i => e (w i)) := by
    change (∑ i, ∑ j, c i * c j * metricRm04StandardAt g x (v i) (w i) (w j) (v j)) +
        K * (∑ i, ∑ j, c i * c j *
          (g.inner x (v i) (v j) * g.inner x (w i) (w j) -
            g.inner x (v i) (w j) * g.inner x (w i) (v j))) =
      (∑ i, ∑ j, c i * c j * metricRm04StandardAt h y (e (v i)) (e (w i)) (e (w j)) (e (v j))) +
        K * (∑ i, ∑ j, c i * c j *
          (h.inner y (e (v i)) (e (v j)) * h.inner y (e (w i)) (e (w j)) -
            h.inner y (e (v i)) (e (w j)) * h.inner y (e (w i)) (e (v j))))
    simp_rw [hRm, hmetric]
  constructor
  · intro hg n c v w
    have ht := hg n c (fun i => e.symm (v i)) (fun i => e.symm (w i))
    rw [hquad] at ht
    simpa only [LinearEquiv.apply_symm_apply] using ht
  · intro hh n c v w
    rw [hquad]
    exact hh n c (fun i => e (v i)) (fun i => e (w i))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.curvatureOperatorLowerBoundAt_iff_of_metricRm04StdAt_equiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.curvatureOperatorLowerBoundAt_iff_of_metricRm04StdAt_equiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.curvatureOperatorLowerBoundAt_iff_of_metricRm04StdAt_equiv ``Submission.DifferentialGeometry.Geometry.Curvature.curvatureOperatorLowerBoundAt_iff_of_metricRm04StdAt_equiv

theorem leastCurvatureOperatorEigenvalueAt_eq_of_metricRm04StdAt_equiv
    (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric J N)
    (x : M) (y : N) (e : TangentSpace I x ≃ₗ[ℝ] TangentSpace J y)
    (hmetric : ∀ u v : TangentSpace I x, g.inner x u v = h.inner y (e u) (e v))
    (hRm : ∀ u v w z : TangentSpace I x,
      metricRm04StandardAt g x u v w z = metricRm04StandardAt h y (e u) (e v) (e w) (e z)) :
    leastCurvatureOperatorEigenvalueAt g x (metricAlgebraicCurvatureTensorAt g x) =
      leastCurvatureOperatorEigenvalueAt h y (metricAlgebraicCurvatureTensorAt h y) := by
  have hsets : {K : ℝ | curvatureOperatorLowerBoundAt g x (metricAlgebraicCurvatureTensorAt g x) K} =
      {K : ℝ | curvatureOperatorLowerBoundAt h y (metricAlgebraicCurvatureTensorAt h y) K} := by
    ext K
    exact curvatureOperatorLowerBoundAt_iff_of_metricRm04StdAt_equiv g h x y e hmetric hRm K
  exact congrArg (fun s : Set ℝ => -_root_.InfSet.sInf s) hsets

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.leastCurvatureOperatorEigenvalueAt_eq_of_metricRm04StdAt_equiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.leastCurvatureOperatorEigenvalueAt_eq_of_metricRm04StdAt_equiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.leastCurvatureOperatorEigenvalueAt_eq_of_metricRm04StdAt_equiv ``Submission.DifferentialGeometry.Geometry.Curvature.leastCurvatureOperatorEigenvalueAt_eq_of_metricRm04StdAt_equiv

theorem leastCurvatureOperatorEigenvalueAt_pullbackMetricCross
    (g : SmoothRiemannianMetric J N) (Φ : M ≃ₘ⟮I, J⟯ N) (x : M) :
    leastCurvatureOperatorEigenvalueAt (Diffeomorph.pullbackMetricCross g Φ) x
        (metricAlgebraicCurvatureTensorAt (Diffeomorph.pullbackMetricCross g Φ) x) =
      leastCurvatureOperatorEigenvalueAt g (Φ x) (metricAlgebraicCurvatureTensorAt g (Φ x)) := by
  let e := (Φ.mfderivToContinuousLinearEquiv (by decide : (∞ : ℕ∞ω) ≠ 0) x).toLinearEquiv
  have he (v : TangentSpace I x) : e v = mfderiv I J Φ x v := by
    exact congrArg (fun D : TangentSpace I x →L[ℝ] TangentSpace J (Φ x) => D v)
      (Diffeomorph.mfderivToContinuousLinearEquiv_coe (Φ := Φ) (x := x) (by decide))
  apply leastCurvatureOperatorEigenvalueAt_eq_of_metricRm04StdAt_equiv
    (Diffeomorph.pullbackMetricCross g Φ) g x (Φ x) e
  · intro u v
    simpa only [he] using Diffeomorph.pullbackMetricCross_inner g Φ x u v
  · intro u v w z
    simpa only [he] using metricRm04Standard_pullbackCross g Φ x u v w z

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.leastCurvatureOperatorEigenvalueAt_pullbackMetricCross then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.leastCurvatureOperatorEigenvalueAt_pullbackMetricCross"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.leastCurvatureOperatorEigenvalueAt_pullbackMetricCross ``Submission.DifferentialGeometry.Geometry.Curvature.leastCurvatureOperatorEigenvalueAt_pullbackMetricCross

theorem leastCurvatureOperatorEigenvalueAt_restrictOpen
    (g : SmoothRiemannianMetric I M) (U : _root_.TopologicalSpace.Opens M) [SigmaCompactSpace U] (x : U) :
    leastCurvatureOperatorEigenvalueAt (g.restrictOpen U) x
        (metricAlgebraicCurvatureTensorAt (g.restrictOpen U) x) =
      leastCurvatureOperatorEigenvalueAt g (x : M) (metricAlgebraicCurvatureTensorAt g (x : M)) := by
  apply leastCurvatureOperatorEigenvalueAt_eq_of_metricRm04StdAt_equiv
    (g.restrictOpen U) g x (x : M) (LinearEquiv.refl ℝ E)
  · intro u v
    rfl
  · intro u v w z
    change metricRm04StandardAt (g.restrictOpen U) x u v w z = metricRm04StandardAt g (x : M) u v w z
    simpa only [mfderiv_subtype_val_apply] using
      metricRm04StandardAt_restrictOpen g U x u v w z

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.leastCurvatureOperatorEigenvalueAt_restrictOpen then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.leastCurvatureOperatorEigenvalueAt_restrictOpen"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.leastCurvatureOperatorEigenvalueAt_restrictOpen ``Submission.DifferentialGeometry.Geometry.Curvature.leastCurvatureOperatorEigenvalueAt_restrictOpen

theorem leastCurvatureOperatorEigenvalueAt_pullbackMetricOfInjectiveLocalDiffeomorph
    [SigmaCompactSpace M] (g : SmoothRiemannianMetric J N) (f : M → N)
    (hf : IsLocalDiffeomorph I J ∞ f) (hinj : Function.Injective f) (x : M) :
    leastCurvatureOperatorEigenvalueAt (pullbackMetricOfInjectiveLocalDiffeomorph g f hf hinj) x
        (metricAlgebraicCurvatureTensorAt (pullbackMetricOfInjectiveLocalDiffeomorph g f hf hinj) x) =
      leastCurvatureOperatorEigenvalueAt g (f x) (metricAlgebraicCurvatureTensorAt g (f x)) := by
  let Φ := diffeomorphOntoImage f hf hinj
  have hrange : Set.range Φ = Set.univ := Φ.surjective.range_eq
  let : SigmaCompactSpace hf.image := isSigmaCompact_univ_iff.mp
    (hrange ▸ isSigmaCompact_range Φ.continuous)
  rw [pullbackMetricOfInjectiveLocalDiffeomorph,
    leastCurvatureOperatorEigenvalueAt_pullbackMetricCross,
    leastCurvatureOperatorEigenvalueAt_restrictOpen, diffeomorphOntoImage_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.leastCurvatureOperatorEigenvalueAt_pullbackMetricOfInjectiveLocalDiffeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.leastCurvatureOperatorEigenvalueAt_pullbackMetricOfInjectiveLocalDiffeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.leastCurvatureOperatorEigenvalueAt_pullbackMetricOfInjectiveLocalDiffeomorph ``Submission.DifferentialGeometry.Geometry.Curvature.leastCurvatureOperatorEigenvalueAt_pullbackMetricOfInjectiveLocalDiffeomorph

end DifferentialGeometry.Geometry.Curvature
