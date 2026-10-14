import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.Restriction

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open _root_.Set _root_.Submission.DifferentialGeometry.Tensor0SBundle
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open scoped _root_.Manifold _root_.ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]

theorem metric_eq_on_closedOpen_of_complete_forward_uniqueness_on_closed
    {a b : ℝ} (hab : a < b)
    (S₁ S₂ : CompleteBoundedCurvatureSolutionOn (I := I) (M := M)
      (D := RealTimeInterval.closedOpen a b hab))
    (hbound₁ : ∀ c ∈ _root_.Set.Ioo a b, ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ _root_.Set.Icc a c, ∀ x : M,
      normSq0S (S₁.solution.base.metric t) x 4
        (metricRm04At (S₁.solution.base.metric t) x) ≤ C)
    (hbound₂ : ∀ c ∈ _root_.Set.Ioo a b, ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ _root_.Set.Icc a c, ∀ x : M,
      normSq0S (S₂.solution.base.metric t) x 4
        (metricRm04At (S₂.solution.base.metric t) x) ≤ C)
    (hunique : ∀ c, (hac : a < c) → c < b →
      ∀ T₁ T₂ : CompleteBoundedCurvatureSolutionOn (I := I) (M := M)
        (D := RealTimeInterval.closed a c hac.le),
      (∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ _root_.Set.Icc a c, ∀ x : M,
        normSq0S (T₁.solution.base.metric t) x 4
          (metricRm04At (T₁.solution.base.metric t) x) ≤ C) →
      (∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ _root_.Set.Icc a c, ∀ x : M,
        normSq0S (T₂.solution.base.metric t) x 4
          (metricRm04At (T₂.solution.base.metric t) x) ≤ C) →
      T₁.solution.base.metric a = T₂.solution.base.metric a →
      ∀ t ∈ _root_.Set.Icc a c, T₁.solution.base.metric t = T₂.solution.base.metric t)
    (hinitial : S₁.solution.base.metric a = S₂.solution.base.metric a) :
    ∀ t ∈ _root_.Set.Ico a b, S₁.solution.base.metric t = S₂.solution.base.metric t := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  intro t ht
  obtain ⟨c, htc, hcb⟩ := exists_between ht.2
  have hac : a < c := ht.1.trans_lt htc
  let D' := RealTimeInterval.closed a c hac.le
  let restrict (S : CompleteBoundedCurvatureSolutionOn (I := I) (M := M)
      (D := RealTimeInterval.closedOpen a b hab)) :
      CompleteBoundedCurvatureSolutionOn (I := I) (M := M) (D := D') := {
    solution := S.solution.timeRestrict D'
    isSolution := isSolutionOn_timeRestrict S.isSolution
      (fun r hr => ⟨hr.1, hr.2.trans_lt hcb⟩)
      (fun r hr => ⟨hr.1, hr.2.trans hcb⟩)
    complete := fun r hr => S.complete r ⟨hr.1, hr.2.trans_lt hcb⟩
    curvatureBound := fun r hr => S.curvatureBound r ⟨hr.1, hr.2.trans_lt hcb⟩ }
  exact hunique c hac hcb (restrict S₁) (restrict S₂)
    (hbound₁ c ⟨hac, hcb⟩) (hbound₂ c ⟨hac, hcb⟩) hinitial t ⟨ht.1, htc.le⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.metric_eq_on_closedOpen_of_complete_forward_uniqueness_on_closed then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.metric_eq_on_closedOpen_of_complete_forward_uniqueness_on_closed"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.metric_eq_on_closedOpen_of_complete_forward_uniqueness_on_closed ``Submission.DifferentialGeometry.PDE.RicciFlow.metric_eq_on_closedOpen_of_complete_forward_uniqueness_on_closed

end DifferentialGeometry.PDE.RicciFlow
