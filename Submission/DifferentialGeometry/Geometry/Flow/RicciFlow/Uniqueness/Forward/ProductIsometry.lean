import Submission.DifferentialGeometry.Geometry.Metric.ProductIsometry
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Uniqueness.Forward.Isometry

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section
open _root_.Bundle _root_.Submission.Bundle _root_.Set _root_.Submission.Set
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff

namespace DifferentialGeometry.PDE.RicciFlow

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [T2Space M] [ConnectedSpace M]

theorem ricci_flow_prod_real_pullback_eq_of_initial_isometry
    (g : ℝ → SmoothRiemannianMetric I M) {a b : ℝ} (hab : a < b)
    (hdim : Module.finrank ℝ E = 2)
    (hscalar : ∀ x, metricScalarAt (g a) x ≠ 0)
    (hjoint : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun p : ℝ × M => (⟨p.2, (g p.1).inner p.2⟩ :
        _root_.Bundle.TotalSpace (E →L[ℝ] E →L[ℝ] ℝ)
          (fun x => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)))
      (_root_.Set.Ico a b ×ˢ (Set.univ : Set M)))
    (hpde : ∀ t ∈ _root_.Set.Ico a b, ∀ x : M, ∀ v w : TangentSpace I x,
      HasDerivWithinAt (fun s : ℝ => (g s).inner x v w)
        (-2 * ricciTensor (g t) x v w) (_root_.Set.Ici a) t)
    (Φ : (M × ℝ) ≃ₘ⟮I.prod 𝓘(ℝ, ℝ), I.prod 𝓘(ℝ, ℝ)⟯ (M × ℝ))
    (hinit : Diffeomorph.pullbackMetricCross ((g a).prod (euclideanMetric (E := ℝ))) Φ =
      (g a).prod (euclideanMetric (E := ℝ))) :
    ∀ t ∈ _root_.Set.Ico a b,
      Diffeomorph.pullbackMetricCross ((g t).prod (euclideanMetric (E := ℝ))) Φ =
        (g t).prod (euclideanMetric (E := ℝ)) := by
  let _ : NeZero (Module.finrank ℝ E) := ⟨by omega⟩
  obtain ⟨φ, ψ, rfl, hφ, hψ⟩ :=
    exists_prod_isometries_of_scalar_ne_zero (g a) hdim hscalar Φ hinit
  intro t ht
  rw [Diffeomorph.pullbackMetricCross_eq_pullbackMetric,
    Diffeomorph.pullbackMetric_prodCongr, hψ,
    ricci_flow_pullback_eq_of_initial_isometry g hab hjoint hpde φ hφ t ht]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.ricci_flow_prod_real_pullback_eq_of_initial_isometry then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.ricci_flow_prod_real_pullback_eq_of_initial_isometry"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.ricci_flow_prod_real_pullback_eq_of_initial_isometry ``Submission.DifferentialGeometry.PDE.RicciFlow.ricci_flow_prod_real_pullback_eq_of_initial_isometry

end DifferentialGeometry.PDE.RicciFlow
