import Submission.DifferentialGeometry.Geometry.Curvature.Bochner.Scalar.CoordinateFormula
import Submission.DifferentialGeometry.Geometry.Connection.ChartBridge.Scalar.HessianNorm
import Submission.DifferentialGeometry.Geometry.Operator.Laplacian.LeviCivitaIdentification
import Submission.DifferentialGeometry.Geometry.Curvature.Metric.LeviCivita

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.Geometry.Curvature

open _root_.Submission.DifferentialGeometry.Geometry.Operator
open _root_.Submission.DifferentialGeometry.Geometry.Connection
open _root_.Submission.DifferentialGeometry.Tensor0SBundle
open scoped _root_.Manifold _root_.ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

theorem laplacian_gradient_norm_sq_eq
    (g : SmoothRiemannianMetric I M) {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (x : M) :
    laplacian (metricCov g) g
      (fun y => g.inner y (gradientFun g f y) (gradientFun g f y)) x =
      2 * normSq0S g x 2 (hessianSec (metricCov g) (metricCov_smooth g) f hf x) +
        2 * metricRicciAt g x (vec2 (gradientFun g f x) (gradientFun g f x)) +
        2 * g.inner x (gradientFun g f x)
          (gradientFun g (fun y => laplacian (metricCov g) g f y) x) := by
  by_cases hdim : Module.finrank ℝ E = 0
  · let : Subsingleton E := Module.finrank_zero_iff.mp hdim
    let : Subsingleton (TangentSpace I x) := inferInstanceAs (Subsingleton E)
    have hLap : ∀ F : M → ℝ, laplacian (metricCov g) g F x = 0 := by
      intro F
      rw [laplacian_eq, divergence_eq]
      rw [Subsingleton.elim ((metricCov g) (gradientFun g F) x).toLinearMap 0]
      exact map_zero _
    have hHessZero : hessianSec (metricCov g) (metricCov_smooth g) f hf x = 0 := by
      apply ContinuousMultilinearMap.ext
      intro v
      exact (hessianSec (metricCov g) (metricCov_smooth g) f hf x).map_coord_zero
        (i := 0) (Subsingleton.elim _ _)
    have hRicZero : metricRicciAt g x (vec2 (gradientFun g f x) (gradientFun g f x)) = 0 :=
      (metricRicciAt g x).map_coord_zero (i := 0) (Subsingleton.elim _ _)
    rw [hLap, hHessZero, hRicZero, Subsingleton.elim (gradientFun g f x) 0]
    simp [normSq0S, inner0S]
  let : NeZero (Module.finrank ℝ E) := ⟨hdim⟩
  have hHess : normSq0S g x 2
      (hessianSec (metricCov g) (metricCov_smooth g) f hf x) =
      chartHessFrobeniusSq g f x := by
    simpa only [leviHessSec, metricCov] using hessSec_normSq g hf x
  have hRic : metricRicciAt g x (vec2 (gradientFun g f x) (gradientFun g f x)) =
      ricciTensor g x (gradFun g f x) (gradFun g f x) := by
    simpa only [gradient_eq_gradFun] using
      metricRicciAt_apply_eq_ricciTensor g x (gradientFun g f x) (gradientFun g f x)
  have hgrad : (fun y => g.inner y (gradientFun g f y) (gradientFun g f y)) =
      normGradSqFun g f := by
    funext y
    rw [normGradSqFun_def, gradient_eq_gradFun]
  have hL : (fun y => laplacian (metricCov g) g f y) = ΔG g ⟨f, hf⟩ := by
    funext y
    exact laplacian_levi_eq g hf y
  rw [hgrad, hL]
  have hLap := laplacian_levi_eq g (normGradSqFun_contMDiff g hf) x
  change laplacian (metricCov g) g (normGradSqFun g f) x = _ at hLap
  rw [hLap]
  rw [hHess, hRic, gradient_eq_gradFun, gradient_eq_gradFun]
  exact bochner_pointwise_concrete_metric g hf x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.laplacian_gradient_norm_sq_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.laplacian_gradient_norm_sq_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.laplacian_gradient_norm_sq_eq ``Submission.DifferentialGeometry.Geometry.Curvature.laplacian_gradient_norm_sq_eq

end DifferentialGeometry.Geometry.Curvature
