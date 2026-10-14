import Submission.DifferentialGeometry.Geometry.Comparison.Variation.Covariant.TwoParameterFields

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission



noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.DifferentialGeometry
open scoped _root_.Topology _root_.ContDiff _root_.Bundle _root_.Submission.Bundle _root_.Manifold

namespace DifferentialGeometry.Geometry

open _root_.Submission.DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian.Variation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]



theorem contMDiff_covDerivAlong (g : SmoothRiemannianMetric I M)
    {γ : ℝ → M} {V : ∀ t, TangentSpace I (γ t)}
    (hV : ContMDiff 𝓘(ℝ, ℝ) I.tangent ∞
      (fun t => TotalSpace.mk' E (γ t) (V t))) :
    ContMDiff 𝓘(ℝ, ℝ) I.tangent ∞
      (fun t => TotalSpace.mk' E (γ t) (covDerivAlong g γ V t)) := by
  have h := cov_snd_smooth g (fun _ t : ℝ => γ t) (fun _ t => V t)
    (hV.comp contMDiff_snd)
  exact h.comp (contMDiff_const.prodMk contMDiff_id :
    ContMDiff 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) ∞ (fun t : ℝ => ((0 : ℝ), t)))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.contMDiff_covDerivAlong then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.contMDiff_covDerivAlong"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.contMDiff_covDerivAlong ``Submission.DifferentialGeometry.Geometry.contMDiff_covDerivAlong

end DifferentialGeometry.Geometry
