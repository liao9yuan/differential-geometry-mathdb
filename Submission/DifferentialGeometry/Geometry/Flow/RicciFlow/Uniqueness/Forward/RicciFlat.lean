import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.NoncompactRicciFlat

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.Set _root_.Submission.DifferentialGeometry.Tensor0SBundle
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.BigOperators
open _root_.Submission.DifferentialGeometry.Geometry.Curvature

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

theorem metric_eq_initial_of_ricci_flat_of_complete_forward_uniqueness
    {a b : ℝ} (hab : a < b)
    (S : CompleteBoundedCurvatureSolutionOn (I := I) (M := M)
      (D := RealTimeInterval.closedOpen a b hab))
    (hbound : ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ _root_.Set.Ico a b, ∀ x : M,
      normSq0S (I := I) (S.solution.base.metric t) x 4
        (metricRm04At (I := I) (S.solution.base.metric t) x) ≤ C)
    (hunique : ∀ S₁ S₂ : CompleteBoundedCurvatureSolutionOn (I := I) (M := M)
        (D := RealTimeInterval.closedOpen a b hab),
      (∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ _root_.Set.Ico a b, ∀ x : M,
        normSq0S (I := I) (S₁.solution.base.metric t) x 4
          (metricRm04At (I := I) (S₁.solution.base.metric t) x) ≤ C) →
      (∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ _root_.Set.Ico a b, ∀ x : M,
        normSq0S (I := I) (S₂.solution.base.metric t) x 4
          (metricRm04At (I := I) (S₂.solution.base.metric t) x) ≤ C) →
      S₁.solution.base.metric a = S₂.solution.base.metric a →
      ∀ t ∈ _root_.Set.Ico a b, S₁.solution.base.metric t = S₂.solution.base.metric t)
    (hRicci : ∀ (x : M) (v w : TangentSpace I x),
      ricciTensor (I := I) (S.solution.base.metric a) x v w = 0) :
    ∀ t ∈ _root_.Set.Ico a b, S.solution.base.metric t = S.solution.base.metric a := by
  let g₀ := S.solution.base.metric a
  let g : ℝ → SmoothRiemannianMetric I M := fun _ => g₀
  have hjoint : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) ∞
        (fun p : ℝ × M => Tensor.Coordinates.chartGramMatrix (I := I) (g p.1) x₀ p.2 i j)
        (_root_.Set.Ico a b ×ˢ (_root_.FiberBundle.trivializationAt E (TangentSpace I) x₀).baseSet) := by
    intro x₀ i j
    exact (Tensor.Coordinates.chartGramMatrix_entry_contMDiffOn
      (I := I) g₀ x₀ i j).comp contMDiffOn_snd (fun p hp => hp.2)
  have hpde : ∀ t ∈ _root_.Set.Ico a b, ∀ (x : M) (v w : TangentSpace I x),
      HasDerivWithinAt (fun s : ℝ => (g s).inner x v w)
        ((-2 : ℝ) * ricciTensor (I := I) (g t) x v w) (_root_.Set.Ici a) t := by
    intro t ht x v w
    simpa only [g, g₀, hRicci, _root_.MulZeroClass.mul_zero] using
      hasDerivWithinAt_const t (_root_.Set.Ici a) (g₀.inner x v w)
  have hcomplete : ∀ t ∈ _root_.Set.Ico a b, RiemannianMetricComplete (I := I) (g t) := by
    intro t ht
    exact S.complete a ⟨le_rfl, hab⟩
  have hcurv := S.curvatureBound a ⟨le_rfl, hab⟩
  let S₀ := completeBoundedCurvatureSolutionOfJointRicciFlow hab g hjoint hpde hcomplete
    (fun t ht => hcurv)
  have hbound₀ : ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ _root_.Set.Ico a b, ∀ x : M,
      normSq0S (I := I) (S₀.solution.base.metric t) x 4
        (metricRm04At (I := I) (S₀.solution.base.metric t) x) ≤ C := by
    obtain ⟨C, hC, hCb⟩ := hcurv
    exact ⟨C, hC, fun t ht x => hCb x⟩
  exact hunique S S₀ hbound hbound₀ rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.metric_eq_initial_of_ricci_flat_of_complete_forward_uniqueness then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.metric_eq_initial_of_ricci_flat_of_complete_forward_uniqueness"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.metric_eq_initial_of_ricci_flat_of_complete_forward_uniqueness ``Submission.DifferentialGeometry.PDE.RicciFlow.metric_eq_initial_of_ricci_flat_of_complete_forward_uniqueness

end DifferentialGeometry.PDE.RicciFlow
