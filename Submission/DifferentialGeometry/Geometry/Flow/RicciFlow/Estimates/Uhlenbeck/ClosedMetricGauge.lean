import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.Uhlenbeck.MetricGauge
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Metric.ClosedRegularity
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Metric.ClosedIntervalDerivative

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Set _root_.Submission.Set
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff

namespace DifferentialGeometry.PDE.RicciFlow

open _root_.Submission.DifferentialGeometry.Geometry.Curvature

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M]

theorem exists_uhlenbeck_isometry_on_closed_interval [I.Boundaryless] [SigmaCompactSpace M]
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {V : M → Type*} [∀ x, NormedAddCommGroup (V x)] [∀ x, NormedSpace ℝ (V x)]
    [TopologicalSpace (_root_.Bundle.TotalSpace F V)] [FiberBundle F V] [VectorBundle ℝ F V]
    {a c b : ℝ} (hac : a < c) (hcb : c < b)
    (hslab : _root_.Set.Icc a b ⊆ D.carrier) (hreg : _root_.Set.Ioo a b ⊆ D.regular)
    {t₀ : ℝ} (ht₀ : t₀ ∈ _root_.Set.Icc c b)
    (h : _root_.Bundle.RiemannianMetric V) (ι₀ : ∀ x, V x ≃L[ℝ] TangentSpace I x)
    (hι₀ : ContMDiff I (I.prod 𝓘(ℝ, F →L[ℝ] E)) ∞
      (fun x => (⟨x, (ι₀ x).toContinuousLinearMap⟩ : _root_.Bundle.TotalSpace (F →L[ℝ] E)
        (fun x => V x →L[ℝ] TangentSpace I x))))
    (h₀ : ∀ x v w, (S.family.metric t₀).inner x (ι₀ x v) (ι₀ x w) = h.inner x v w) :
    ∃ ι : ℝ → ∀ x, V x ≃L[ℝ] TangentSpace I x,
      (∀ x, ι t₀ x = ι₀ x) ∧
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, F →L[ℝ] E)) ∞
        (fun p : ℝ × M => (⟨p.2, (ι p.1 p.2).toContinuousLinearMap⟩ :
          _root_.Bundle.TotalSpace (F →L[ℝ] E) (fun x => V x →L[ℝ] TangentSpace I x)))
        (_root_.Set.Icc c b ×ˢ (_root_.Set.univ : Set M)) ∧
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] F)) ∞
        (fun p : ℝ × M => (⟨p.2, (ι p.1 p.2).symm.toContinuousLinearMap⟩ :
          _root_.Bundle.TotalSpace (E →L[ℝ] F) (fun x => TangentSpace I x →L[ℝ] V x)))
        (_root_.Set.Icc c b ×ˢ (_root_.Set.univ : Set M)) ∧
      (∀ x v, ∀ t ∈ _root_.Set.Icc c b, HasDerivWithinAt (fun s => ι s x v)
        (ricciSharp (I := I) (S.family.metric t) x (ι t x v)) (_root_.Set.Icc c b) t) ∧
      ∀ t ∈ _root_.Set.Icc c b, ∀ x v w,
        (S.family.metric t).inner x (ι t x v) (ι t x w) = h.inner x v w := by
  apply exists_uhlenbeck_isometry_on_interval_of_hasDerivWithinAt _root_.Set.ordConnected_Icc ht₀
    S.family.metric (solution_metricCLMSection_contMDiffOn_closed S hS hac hcb hslab hreg)
    (h := h) (ι₀ := ι₀) (hι₀ := hι₀) (h₀ := h₀)
  intro t ht x v w
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  simpa only [SolutionOn.ricciAt, SolutionFamily.ricciAt,
    metricRicciAt_apply_eq_ricciTensor, SolutionOn.family_metric] using
    metric_inner_hasDerivWithinAt_on_closed_interval S hS hcb
      (fun r hr => hslab ⟨hac.le.trans hr.1, hr.2⟩)
      (fun r hr => hreg ⟨hac.trans hr.1, hr.2⟩) ht x v w

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.exists_uhlenbeck_isometry_on_closed_interval then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.exists_uhlenbeck_isometry_on_closed_interval"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.exists_uhlenbeck_isometry_on_closed_interval ``Submission.DifferentialGeometry.PDE.RicciFlow.exists_uhlenbeck_isometry_on_closed_interval

end DifferentialGeometry.PDE.RicciFlow
