import Submission.DifferentialGeometry.Geometry.Metric.RicciSoliton.Models
import Submission.DifferentialGeometry.Geometry.Operator.Laplacian.Minimum

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission


noncomputable section

open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff

namespace DifferentialGeometry.Geometry

open _root_.Submission.DifferentialGeometry.Geometry.Curvature _root_.Submission.DifferentialGeometry.Geometry.Operator

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M]

theorem isGaussianGradientRicciSoliton_exists_diffeomorph_of_hamiltonNormalized
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; ℝ⟯} {sigma : ℝ}
    (hgaussian : isGaussianGradientRicciSoliton (E := E) g f sigma)
    (hnormal : hamiltonNormalized (I := I) g f sigma) :
    ∃ hsigma : 0 < sigma, ∃ Psi : M ≃ₘ⟮I, 𝓘(ℝ, E)⟯ E,
      Diffeomorph.pullbackMetricCross euclideanMetric Psi =
          scaleMetric (I := I) sigma hsigma g ∧
        f = gaussianPotential.comp Psi.toContMDiffMap := by
  obtain ⟨hsigma, Psi, c, hmetric, hpotential⟩ := hgaussian
  have hvalue (x : M) : f x + c = gaussianPotential (Psi x) :=
    congrArg (fun q : C^∞⟮I, M; ℝ⟯ => q x) hpotential
  have hzero : f (Psi.symm 0) + c = 0 := by
    simpa only [Psi.apply_symm_apply, gaussianPotential_apply, norm_zero,
      zero_pow (by decide : 2 ≠ 0), zero_div] using hvalue (Psi.symm 0)
  have hmin : IsLocalMin (f : M → ℝ) (Psi.symm 0) := by
    apply Filter.Eventually.of_forall
    intro x
    have hnonneg : 0 ≤ gaussianPotential (Psi x) := by
      rw [gaussianPotential_apply]
      positivity
    linarith [hvalue x]
  have hgrad : gradFun (I := I) g f (Psi.symm 0) = 0 :=
    gradientFun_eq_zero_at_spatial_min (I := I) g hmin
      (f.contMDiff.mdifferentiableAt (by simp))
  have hscalar : metricScalarAt (I := I) g (Psi.symm 0) = 0 :=
    isGaussianGradientRicciSoliton_scalarCurvature_eq_zero
      ⟨hsigma, Psi, c, hmetric, hpotential⟩ (Psi.symm 0)
  have hnormalAt := hnormal (Psi.symm 0)
  rw [hscalar, hgrad] at hnormalAt
  have hfzero : f (Psi.symm 0) = 0 := by
    have hmul : sigma * f (Psi.symm 0) = 0 := by
      simpa using hnormalAt.symm
    exact (mul_eq_zero.mp hmul).resolve_left hsigma.ne'
  have hc : c = 0 := by linarith
  refine ⟨hsigma, Psi, hmetric, ?_⟩
  apply ContMDiffMap.ext
  intro x
  change f x = gaussianPotential (Psi x)
  simpa only [hc, add_zero] using hvalue x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.isGaussianGradientRicciSoliton_exists_diffeomorph_of_hamiltonNormalized then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.isGaussianGradientRicciSoliton_exists_diffeomorph_of_hamiltonNormalized"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.isGaussianGradientRicciSoliton_exists_diffeomorph_of_hamiltonNormalized ``Submission.DifferentialGeometry.Geometry.isGaussianGradientRicciSoliton_exists_diffeomorph_of_hamiltonNormalized

end DifferentialGeometry.Geometry

end
