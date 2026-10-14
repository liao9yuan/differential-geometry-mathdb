import Submission.DifferentialGeometry.Geometry.Operator.Laplacian.Minimum
import Submission.DifferentialGeometry.Geometry.Operator.Gradient.Regularity

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

open _root_.Filter
open scoped _root_.Manifold _root_.ContDiff _root_.Topology

namespace DifferentialGeometry.Geometry.Operator

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem laplacian_le_of_isLocalMin_sub
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (g : SmoothRiemannianMetric I M)
    (hcov : DifferentialGeometry.Geometry.Connection.IsMetricCompatible (I := I) cov g)
    {f h : M → ℝ} {x : M} (hx : I.IsInteriorPoint x)
    (hf : ContMDiffAt I 𝓘(ℝ, ℝ) 2 f x)
    (hh : ContMDiffAt I 𝓘(ℝ, ℝ) 2 h x)
    (hmin : IsLocalMin (fun y => f y - h y) x) :
    laplacian (I := I) cov g h x ≤ laplacian (I := I) cov g f x := by
  have hfd : ∀ᶠ y in 𝓝 x, MDifferentiableAt I 𝓘(ℝ, ℝ) f y :=
    ((contMDiffAt_iff_contMDiffAt_nhds (n := 2) (by decide)).mp hf).mono
      fun _ hy => hy.mdifferentiableAt (by norm_num)
  have hhd : ∀ᶠ y in 𝓝 x, MDifferentiableAt I 𝓘(ℝ, ℝ) h y :=
    ((contMDiffAt_iff_contMDiffAt_nhds (n := 2) (by decide)).mp hh).mono
      fun _ hy => hy.mdifferentiableAt (by norm_num)
  have hgradf := (gradientFun_contMDiffAt_one g hf).mdifferentiableAt (by norm_num)
  have hgradh := (gradientFun_contMDiffAt_one g hh).mdifferentiableAt (by norm_num)
  have hgradsub := (gradientFun_contMDiffAt_one g (hf.sub hh)).mdifferentiableAt (by norm_num)
  have hnonneg := laplacian_nonneg_at_spatial_min_of_metricCompatible_of_isInteriorPoint
    cov g hcov hmin hx ((hf.sub hh).mdifferentiableAt (by norm_num))
      ((hfd.and hhd).mono fun _ hy => hy.1.sub hy.2) hgradsub
  rw [laplacian_sub_at cov g hfd hhd hgradf hgradh] at hnonneg
  exact sub_nonneg.mp hnonneg

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Operator.laplacian_le_of_isLocalMin_sub then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Operator.laplacian_le_of_isLocalMin_sub"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Operator.laplacian_le_of_isLocalMin_sub ``Submission.DifferentialGeometry.Geometry.Operator.laplacian_le_of_isLocalMin_sub

end DifferentialGeometry.Geometry.Operator
