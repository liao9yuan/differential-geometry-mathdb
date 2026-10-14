import Submission.DifferentialGeometry.Geometry.Curvature.Curve
import Submission.DifferentialGeometry.Geometry.Metric.CurveUnitReparametrization

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission



noncomputable section

open _root_.Set _root_.Function _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.Submission.DifferentialGeometry _root_.Filter
open scoped _root_.Topology _root_.ContDiff _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold

namespace DifferentialGeometry.Geometry

open _root_.Submission.DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian.Variation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]




theorem riemannianCurveCurvature_reparam_pos (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    {γ : ℝ → M} (hγ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ γ)
    (hi : ∀ t, mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) γ t 1 ≠ 0)
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ) {t : ℝ} (hpos : 0 < deriv φ t) :
    riemannianCurveCurvature g (γ ∘ φ) t = riemannianCurveCurvature g γ (φ t) := by
  have hgd (s : ℝ) := hγ.mdifferentiable (by simp) s
  have hpd (s : ℝ) := hφ.differentiable (by simp) s
  have hevent : ∀ᶠ s in 𝓝 t, 0 < deriv φ s :=
    (hφ.continuous_deriv (by simp)).continuousAt.eventually (lt_mem_nhds hpos)
  have hT : ∀ᶠ s in 𝓝 t,
      riemannianCurveUnitTangent g (γ ∘ φ) s = riemannianCurveUnitTangent g γ (φ s) := by
    filter_upwards [hevent] with s hs
    exact riemannianCurveUnitTangent_reparam g (hgd _) (hpd _) hs
  have hcov := covDerivAlong_congr_of_eventuallyEq g (γ ∘ φ) hT
  have hrep := (contDiffAt_chartRepAt_of_section
    ((contMDiff_riemannianCurveUnitTangent g hγ hi).contMDiffAt (x := φ t))).differentiableAt
      (by simp : (∞ : WithTop ℕ∞) ≠ 0)
  have hcomp := covDerivAlong_comp g γ (riemannianCurveUnitTangent g γ) φ t
    (hgd _) hrep (hpd _)
  unfold riemannianCurveCurvature
  rw [riemannianCurveSpeed_reparam g (hgd _) (hpd _), abs_of_pos hpos]
  erw [hcov, hcomp]
  rw [smul_smul]
  congr 1
  field_simp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.riemannianCurveCurvature_reparam_pos then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.riemannianCurveCurvature_reparam_pos"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.riemannianCurveCurvature_reparam_pos ``Submission.DifferentialGeometry.Geometry.riemannianCurveCurvature_reparam_pos

end DifferentialGeometry.Geometry
