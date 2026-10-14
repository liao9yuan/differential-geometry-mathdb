import Submission.DifferentialGeometry.Geometry.Comparison.Variation.Jacobi.Basic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Filter
open scoped _root_.Manifold _root_.ContDiff _root_.Topology

namespace DifferentialGeometry.Geometry.Riemannian.Variation

open _root_.Submission.DifferentialGeometry.Geometry.Riemannian.AlongCurve _root_.Submission.DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

theorem isJacobiAt_variationField_of_covDerivAlong_velocity_eq_zero
    (g : SmoothRiemannianMetric I M) (F : ℝ → ℝ → M)
    (hF : IsSmoothVariation (I := I) F) (t₀ : ℝ)
    (hzero : ∀ s : ℝ,
      covDerivAlong (I := I) g (fun v : ℝ => F s v)
        (fun v : ℝ => mfderiv (𝓘(ℝ, ℝ)) I
          (fun u : ℝ => F s u) v (1 : ℝ)) t₀ = 0) :
    IsJacobiAt (I := I) g (fun v : ℝ => F 0 v)
      (fun v : ℝ => mfderiv (𝓘(ℝ, ℝ)) I
        (fun s : ℝ => F s v) 0 (1 : ℝ)) t₀ := by
  have houterL : DifferentiableAt ℝ
      (chartRepAt (I := I) (fun s : ℝ => F s t₀)
        (fun s : ℝ => covDerivAlong (I := I) g (fun v : ℝ => F s v)
          (fun v : ℝ => mfderiv (𝓘(ℝ, ℝ)) I
            (fun u : ℝ => F s u) v (1 : ℝ)) t₀) 0) 0 := by
    have hev : (chartRepAt (I := I) (fun s : ℝ => F s t₀)
        (fun s : ℝ => covDerivAlong (I := I) g (fun v : ℝ => F s v)
          (fun v : ℝ => mfderiv (𝓘(ℝ, ℝ)) I
            (fun u : ℝ => F s u) v (1 : ℝ)) t₀) 0)
        =ᶠ[𝓝 (0 : ℝ)] (fun _ : ℝ => (0 : E)) := by
      filter_upwards with s
      rw [chartRepAt_apply, hzero s]
      exact map_zero _
    exact (hev.differentiableAt_iff).mpr (differentiableAt_const _)
  have hsymm : ∀ v : ℝ,
      covDerivAlong (I := I) g (fun u : ℝ => F u v)
        (fun u : ℝ => mfderiv (𝓘(ℝ, ℝ)) I
          (fun u' : ℝ => F u u') v (1 : ℝ)) 0
      = covDerivAlong (I := I) g (fun v' : ℝ => F 0 v')
        (fun v' : ℝ => mfderiv (𝓘(ℝ, ℝ)) I
          (fun u : ℝ => F u v') 0 (1 : ℝ)) v :=
    fun v => commute_ds_dt_intrinsic (I := I) g F hF v
  have hfields : (fun v : ℝ =>
      covDerivAlong (I := I) g (fun u : ℝ => F u v)
        (fun u : ℝ => mfderiv (𝓘(ℝ, ℝ)) I
          (fun u' : ℝ => F u u') v (1 : ℝ)) 0)
      = (fun v : ℝ =>
        covDerivAlong (I := I) g (fun v' : ℝ => F 0 v')
          (fun v' : ℝ => mfderiv (𝓘(ℝ, ℝ)) I
            (fun u : ℝ => F u v') 0 (1 : ℝ)) v) :=
    funext hsymm
  have houterR : DifferentiableAt ℝ
      (chartRepAt (I := I) (fun v : ℝ => F 0 v)
        (fun v : ℝ => covDerivAlong (I := I) g (fun u : ℝ => F u v)
          (fun u : ℝ => mfderiv (𝓘(ℝ, ℝ)) I
            (fun u' : ℝ => F u u') v (1 : ℝ)) 0) t₀) t₀ := by
    rw [hfields]
    exact variationField_covDeriv_chartRep_differentiableAt (I := I) g F hF t₀
  have hcomm := commute_ds_dt_curvature (I := I) g F hF t₀ houterL houterR
  have hT1 : covDerivAlong (I := I) g (fun s : ℝ => F s t₀)
      (fun s : ℝ => covDerivAlong (I := I) g (fun v : ℝ => F s v)
        (fun v : ℝ => mfderiv (𝓘(ℝ, ℝ)) I
          (fun u : ℝ => F s u) v (1 : ℝ)) t₀) 0 = 0 := by
    have hfun : (fun s : ℝ =>
        covDerivAlong (I := I) g (fun v : ℝ => F s v)
          (fun v : ℝ => mfderiv (𝓘(ℝ, ℝ)) I
            (fun u : ℝ => F s u) v (1 : ℝ)) t₀)
        = (fun s : ℝ => (0 : TangentSpace I (F s t₀))) :=
      funext hzero
    rw [hfun]
    exact covDerivAlong_zero (I := I) g (fun s : ℝ => F s t₀) 0
  rw [hT1, hfields, zero_sub, neg_eq_iff_eq_neg] at hcomm
  change covDerivAlong (I := I) g (fun v : ℝ => F 0 v)
      (fun v : ℝ => covDerivAlong (I := I) g (fun v' : ℝ => F 0 v')
        (fun v' : ℝ => mfderiv (𝓘(ℝ, ℝ)) I
          (fun u : ℝ => F u v') 0 (1 : ℝ)) v) t₀
    + (DifferentialGeometry.Geometry.Curvature.riemannOp
        (DifferentialGeometry.Geometry.Connection.LeviCivita (I := I) g) (F 0 t₀))
        (mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => F u t₀) 0 (1 : ℝ))
        (mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => F 0 u) t₀ (1 : ℝ))
        (mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => F 0 u) t₀ (1 : ℝ)) = 0
  linear_combination (norm := module) hcomm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.Variation.isJacobiAt_variationField_of_covDerivAlong_velocity_eq_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.Variation.isJacobiAt_variationField_of_covDerivAlong_velocity_eq_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.Variation.isJacobiAt_variationField_of_covDerivAlong_velocity_eq_zero ``Submission.DifferentialGeometry.Geometry.Riemannian.Variation.isJacobiAt_variationField_of_covDerivAlong_velocity_eq_zero

end DifferentialGeometry.Geometry.Riemannian.Variation
