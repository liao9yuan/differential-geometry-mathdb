import Submission.DifferentialGeometry.Geometry.Metric.CurveUnitTangent
import Submission.DifferentialGeometry.Geometry.Connection.SectionAlongRegularity
import Submission.DifferentialGeometry.Geometry.Connection.SectionAlongSmooth
import Submission.DifferentialGeometry.Geometry.Comparison.Variation.FirstVariation.Basic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission



noncomputable section

open _root_.Set _root_.Function _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.Submission.DifferentialGeometry
open scoped _root_.Topology _root_.ContDiff _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold

namespace DifferentialGeometry.Geometry

open _root_.Submission.DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian.Variation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]



def riemannianCurveCurvature (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (γ : ℝ → M) (t : ℝ) : TangentSpace 𝓘(ℝ, E) (γ t) :=
  (riemannianCurveSpeed g γ t)⁻¹ •
    covDerivAlong g γ (riemannianCurveUnitTangent g γ) t

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.riemannianCurveCurvature then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.riemannianCurveCurvature"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.riemannianCurveCurvature ``Submission.DifferentialGeometry.Geometry.riemannianCurveCurvature



theorem contMDiff_riemannianCurveCurvature (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    {γ : ℝ → M} (hγ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ γ)
    (hi : ∀ t, mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) γ t 1 ≠ 0) :
    ContMDiff 𝓘(ℝ, ℝ) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) ∞
      (fun t => TotalSpace.mk' E (γ t) (riemannianCurveCurvature g γ t)) := by
  have hD := contMDiff_covDerivAlong g (contMDiff_riemannianCurveUnitTangent g hγ hi)
  have hs := (contDiff_riemannianCurveSpeed g hγ hi).inv
    (fun t => ne_of_gt (riemannianCurveSpeed_pos g (hi t)))
  intro t
  exact contMDiffAt_tangent_smul hs.contMDiff.contMDiffAt hD.contMDiffAt

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.contMDiff_riemannianCurveCurvature then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.contMDiff_riemannianCurveCurvature"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.contMDiff_riemannianCurveCurvature ``Submission.DifferentialGeometry.Geometry.contMDiff_riemannianCurveCurvature



theorem riemannianCurveCurvature_orthogonal (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    {γ : ℝ → M} (hγ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ γ)
    (hi : ∀ t, mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) γ t 1 ≠ 0) (t : ℝ) :
    g.inner (γ t) (riemannianCurveCurvature g γ t) (riemannianCurveUnitTangent g γ t) = 0 := by
  have hT := contMDiff_riemannianCurveUnitTangent g hγ hi
  have hr := (contDiffAt_chartRepAt_of_section (hT.contMDiffAt (x := t))).differentiableAt
    (by simp : (∞ : WithTop ℕ∞) ≠ 0)
  have hd := inner_deriv_at (by simp : (1 : WithTop ℕ∞) ≤ ∞) g γ
    (riemannianCurveUnitTangent g γ) (riemannianCurveUnitTangent g γ) t hγ.contMDiffAt hr hr
  have heq : (fun s => g.inner (γ s) (riemannianCurveUnitTangent g γ s)
      (riemannianCurveUnitTangent g γ s)) = fun _ => (1 : ℝ) :=
    funext (fun s => riemannianCurveUnitTangent_inner_self g (hi s))
  rw [heq] at hd
  have hz := hd.unique (hasDerivAt_const t (1 : ℝ))
  rw [g.symm (γ t) (riemannianCurveUnitTangent g γ t)] at hz
  have hzero : g.inner (γ t)
      (covDerivAlong g γ (riemannianCurveUnitTangent g γ) t)
      (riemannianCurveUnitTangent g γ t) = 0 := by linarith
  simp only [riemannianCurveCurvature, map_smul, smul_apply, smul_eq_mul, hzero, _root_.MulZeroClass.mul_zero]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.riemannianCurveCurvature_orthogonal then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.riemannianCurveCurvature_orthogonal"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.riemannianCurveCurvature_orthogonal ``Submission.DifferentialGeometry.Geometry.riemannianCurveCurvature_orthogonal




theorem riemannianCurveCurvature_inner_normal (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    {γ : ℝ → M} (hγ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ γ)
    {t : ℝ} (ht : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) γ t 1 ≠ 0)
    (N : TangentSpace 𝓘(ℝ, E) (γ t))
    (hN : g.inner (γ t) (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) γ t 1) N = 0) :
    g.inner (γ t) (riemannianCurveCurvature g γ t) N =
      g.inner (γ t) (covDerivAlong g γ (fun s => mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) γ s 1) t) N /
        riemannianCurveSpeed g γ t ^ 2 := by
  have hV := contMDiffOn_univ.mp
    (contMDiffOn_source_partial isOpen_univ hγ.contMDiffOn (m := ∞) (by simp) 1)
  have hr := (contDiffAt_chartRepAt_of_section (hV.contMDiffAt (x := t))).differentiableAt
    (by simp : (∞ : WithTop ℕ∞) ≠ 0)
  have hs := (contDiffAt_riemannianCurveSpeed g hγ ht).inv
    (ne_of_gt (riemannianCurveSpeed_pos g ht))
  unfold riemannianCurveCurvature riemannianCurveUnitTangent
  erw [covDerivAlong_smulFun g γ (fun s => (riemannianCurveSpeed g γ s)⁻¹)
    (fun s => mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) γ s 1) t (hs.differentiableAt (by simp)) hr]
  simp only [map_smul, smul_apply, smul_eq_mul, map_add, add_apply, hN, _root_.MulZeroClass.mul_zero, zero_add]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.riemannianCurveCurvature_inner_normal then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.riemannianCurveCurvature_inner_normal"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.riemannianCurveCurvature_inner_normal ``Submission.DifferentialGeometry.Geometry.riemannianCurveCurvature_inner_normal

end DifferentialGeometry.Geometry
