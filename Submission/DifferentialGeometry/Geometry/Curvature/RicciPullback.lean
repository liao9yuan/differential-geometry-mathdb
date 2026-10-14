import Submission.DifferentialGeometry.Geometry.Curvature.Naturality.Pullback.Cross
import Submission.DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivative.Pullback
import Submission.DifferentialGeometry.Geometry.Curvature.CurvatureOperator.Identities.Ricci
import Submission.DifferentialGeometry.Geometry.Metric.TensorInner.Tangent.MetricData

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section
open scoped _root_.Manifold _root_.ContDiff
open _root_.Submission.DifferentialGeometry _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Connection _root_.Submission.DifferentialGeometry.Tensor0SBundle
open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness

namespace DifferentialGeometry.Geometry.Curvature

variable {E F H H' M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace H] [TopologicalSpace H']
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F H'}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N] [T2Space N]
  [BoundarylessManifold I M] [BoundarylessManifold J N]

theorem riemannOp_pullbackMetricCross
    (g : SmoothRiemannianMetric J N) (Φ : M ≃ₘ⟮I, J⟯ N)
    (x : M) (u v w : TangentSpace I x) :
    mfderiv I J Φ x (riemannOp (LeviCivita (Diffeomorph.pullbackMetricCross g Φ)) x u v w) =
      riemannOp (LeviCivita g) (Φ x) (mfderiv I J Φ x u) (mfderiv I J Φ x v)
        (mfderiv I J Φ x w) := by
  let : CompleteSpace E := FiniteDimensional.complete ℝ E
  let : CompleteSpace F := FiniteDimensional.complete ℝ F
  let e := Φ.mfderivToContinuousLinearEquiv (by decide : (∞ : WithTop ℕ∞) ≠ 0) x
  have he (z : TangentSpace I x) : e z = mfderiv I J Φ x z :=
    congrArg (fun A : TangentSpace I x →L[ℝ] TangentSpace J (Φ x) ↦ A z)
      (Φ.mfderivToContinuousLinearEquiv_coe (by decide))
  apply tangentFlatLinear_injective_gen (I := J) g (Φ x)
  ext z
  simp only [tangentFlatLinear_apply_gen]
  obtain ⟨q, rfl⟩ := e.surjective z
  rw [he]
  have h := metricRm04Standard_pullbackCross g Φ x u v w q
  rw [metricRm04StandardAt_eq_inner_riemannOp, metricRm04StandardAt_eq_inner_riemannOp,
    Diffeomorph.pullbackMetricCross_inner] at h
  exact (g.symm (Φ x) _ _).trans (h.trans (g.symm (Φ x) _ _))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.riemannOp_pullbackMetricCross then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.riemannOp_pullbackMetricCross"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.riemannOp_pullbackMetricCross ``Submission.DifferentialGeometry.Geometry.Curvature.riemannOp_pullbackMetricCross

theorem ricciTensor_pullbackMetricCross
    (g : SmoothRiemannianMetric J N) (Φ : M ≃ₘ⟮I, J⟯ N)
    (x : M) (v w : TangentSpace I x) :
    ricciTensor (Diffeomorph.pullbackMetricCross g Φ) x v w =
      ricciTensor g (Φ x) (mfderiv I J Φ x v) (mfderiv I J Φ x w) := by
  let e := Φ.mfderivToContinuousLinearEquiv (by decide : (∞ : WithTop ℕ∞) ≠ 0) x
  have he (z : TangentSpace I x) : e z = mfderiv I J Φ x z :=
    congrArg (fun A : TangentSpace I x →L[ℝ] TangentSpace J (Φ x) ↦ A z)
      (Φ.mfderivToContinuousLinearEquiv_coe (by decide))
  let A := ricciEndo g (Φ x) (mfderiv I J Φ x v) (mfderiv I J Φ x w)
  have hconj : ricciEndo (Diffeomorph.pullbackMetricCross g Φ) x v w =
      e.toLinearEquiv.symm.conj A := by
    apply LinearMap.ext
    intro z
    apply e.injective
    change e (riemannOp (LeviCivita (Diffeomorph.pullbackMetricCross g Φ)) x z v w) =
      e (e.symm (A (e z)))
    rw [e.apply_symm_apply, he, he]
    exact riemannOp_pullbackMetricCross g Φ x z v w
  rw [ricciTensor_apply, ricciTensor_apply, hconj]
  exact LinearMap.trace_conj' A e.toLinearEquiv.symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.ricciTensor_pullbackMetricCross then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.ricciTensor_pullbackMetricCross"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.ricciTensor_pullbackMetricCross ``Submission.DifferentialGeometry.Geometry.Curvature.ricciTensor_pullbackMetricCross

theorem ricciSharp_pullbackMetricCross
    (g : SmoothRiemannianMetric J N) (Φ : M ≃ₘ⟮I, J⟯ N)
    (x : M) (v : TangentSpace I x) :
    mfderiv I J Φ x (ricciSharp (Diffeomorph.pullbackMetricCross g Φ) x v) =
      ricciSharp g (Φ x) (mfderiv I J Φ x v) := by
  let e := Φ.mfderivToContinuousLinearEquiv (by decide : (∞ : WithTop ℕ∞) ≠ 0) x
  have he (z : TangentSpace I x) : e z = mfderiv I J Φ x z :=
    congrArg (fun A : TangentSpace I x →L[ℝ] TangentSpace J (Φ x) ↦ A z)
      (Φ.mfderivToContinuousLinearEquiv_coe (by decide))
  apply tangentFlatLinear_injective_gen (I := J) g (Φ x)
  ext z
  simp only [tangentFlatLinear_apply_gen]
  obtain ⟨w, rfl⟩ := e.surjective z
  rw [he, ← Diffeomorph.pullbackMetricCross_inner, inner_ricciSharp, inner_ricciSharp]
  exact ricciTensor_pullbackMetricCross g Φ x v w

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.ricciSharp_pullbackMetricCross then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.ricciSharp_pullbackMetricCross"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.ricciSharp_pullbackMetricCross ``Submission.DifferentialGeometry.Geometry.Curvature.ricciSharp_pullbackMetricCross

end DifferentialGeometry.Geometry.Curvature
