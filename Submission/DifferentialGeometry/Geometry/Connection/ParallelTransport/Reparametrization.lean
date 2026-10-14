import Submission.DifferentialGeometry.Geometry.Connection.ParallelTransport.Derivative.CovariantDerivativeAlong

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section
open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Set _root_.Filter
open scoped _root_.Manifold _root_.ContDiff _root_.Topology

namespace DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem covDerivAlong_smul_reparam_geodesic_velocity
    (g : SmoothRiemannianMetric I M) {γ : ℝ → M} {φ f : ℝ → ℝ} {t : ℝ}
    (hγ : ContMDiffAt 𝓘(ℝ, ℝ) I 2 γ (φ t))
    (hgeo : Geodesic.HasGeodesicEquationAt g γ (φ t))
    (hφ : DifferentiableAt ℝ φ t) (hf : DifferentiableAt ℝ f t) :
    covDerivAlong g (fun s => γ (φ s))
        (fun s => f s • mfderiv 𝓘(ℝ, ℝ) I γ (φ s) (1 : ℝ)) t =
      deriv f t • mfderiv 𝓘(ℝ, ℝ) I γ (φ t) (1 : ℝ) := by
  have hV := differentiableAt_chartRepAt_curveVelocity hγ
  have hVφ : DifferentiableAt ℝ
      (chartRepAt (I := I) (fun s => γ (φ s))
        (fun s => mfderiv 𝓘(ℝ, ℝ) I γ (φ s) (1 : ℝ)) t) t :=
    hV.comp t hφ
  rw [covDerivAlong_smulFun g _ f _ t hf hVφ,
    covDerivAlong_comp g γ _ φ t (hγ.mdifferentiableAt (by norm_num)) hV hφ,
    covDerivAlong_velocity_eq_zero_of_hasGeodesicEquationAt_C2 g γ (φ t) hγ hgeo,
    smul_zero, smul_zero, add_zero]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong.covDerivAlong_smul_reparam_geodesic_velocity then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong.covDerivAlong_smul_reparam_geodesic_velocity"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong.covDerivAlong_smul_reparam_geodesic_velocity ``Submission.DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong.covDerivAlong_smul_reparam_geodesic_velocity

end DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
