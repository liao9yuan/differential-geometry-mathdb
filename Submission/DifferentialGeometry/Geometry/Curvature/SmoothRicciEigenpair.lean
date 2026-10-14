import Submission.DifferentialGeometry.Bundle.SmoothMetricEigenpair
import Submission.DifferentialGeometry.Geometry.Curvature.RicciSharpSmooth

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section
open _root_.Set _root_.Bundle _root_.Submission.Bundle
open scoped _root_.ContDiff _root_.Manifold
open _root_.Submission.DifferentialGeometry _root_.Submission.DifferentialGeometry.Geometry.Curvature

namespace DifferentialGeometry.Geometry.Curvature

theorem exists_smooth_ricci_eigenpair_near_simple
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
    (g : SmoothRiemannianMetric I M) {U : Set M} (hU : IsOpen U)
    {x₀ : M} (hx₀ : x₀ ∈ U) (μ₀ : ℝ) (w₀ : TangentSpace I x₀)
    (hw₀ : g.inner x₀ w₀ w₀ = 1) (heigen : ricciSharp g x₀ w₀ = μ₀ • w₀)
    (hsimple : Module.End.eigenspace (ricciSharp g x₀).toLinearMap μ₀ = Submodule.span ℝ {w₀}) :
    ∃ V : Set M, IsOpen V ∧ x₀ ∈ V ∧ V ⊆ U ∧
      ∃ (μ : M → ℝ) (w : ∀ x : M, TangentSpace I x),
        ContMDiffOn I 𝓘(ℝ) ∞ μ V ∧
        ContMDiffOn I I.tangent ∞ (fun x ↦ (⟨x, w x⟩ : TangentBundle I M)) V ∧
        μ x₀ = μ₀ ∧ w x₀ = w₀ ∧ ∀ x ∈ V,
          g.inner x (w x) (w x) = 1 ∧ ricciSharp g x (w x) = μ x • w x := by
  apply DifferentialGeometry.Geometry.VectorBundle.exists_smooth_metric_normalized_eigenpair g (ricciSharp g)
    hU (ricciSharp_contMDiff g).contMDiffOn hx₀ _ μ₀ w₀ hw₀ heigen hsimple
  intro u v
  rw [inner_ricciSharp, inner_ricciSharp_right, ricciTensor_symm g x₀ u v]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.exists_smooth_ricci_eigenpair_near_simple then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.exists_smooth_ricci_eigenpair_near_simple"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.exists_smooth_ricci_eigenpair_near_simple ``Submission.DifferentialGeometry.Geometry.Curvature.exists_smooth_ricci_eigenpair_near_simple

end DifferentialGeometry.Geometry.Curvature
