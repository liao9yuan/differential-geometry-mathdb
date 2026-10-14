import Submission.DifferentialGeometry.Geometry.Connection.LeviCivita.Christoffel.Bounds
import Submission.DifferentialGeometry.Geometry.Operator.Hessian.Trace.ChartGramRegularity
import Mathlib.Topology.Order.Compact

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission


noncomputable section

open _root_.Manifold _root_.Set
open scoped _root_.ContDiff _root_.Manifold _root_.BigOperators

namespace DifferentialGeometry.Geometry.Connection

open _root_.Submission.DifferentialGeometry.Geometry.Operator

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem exists_norm_chartChristoffel_le_of_isCompact
    (g : SmoothRiemannianMetric I M) (p : M) {K : Set E}
    (hK : IsCompact K) (hKt : K ⊆ interior (extChartAt I p).target) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ K, ∀ i j k,
      ‖chartChristoffel g p i j k x‖ ≤ C := by
  classical
  let F : E → ℝ := fun x => ∑ i, ∑ j, ∑ k, ‖chartChristoffel g p i j k x‖
  have hF : ContinuousOn F K := by
    apply continuousOn_finsetSum
    intro i _
    apply continuousOn_finsetSum
    intro j _
    apply continuousOn_finsetSum
    intro k _
    exact ((chartChristoffel_contDiffOn_interior g p i j k).continuousOn.mono hKt).norm
  obtain ⟨B, hB⟩ := hK.bddAbove_image hF
  refine ⟨max B 0, le_max_right _ _, ?_⟩
  intro x hx i j k
  have hk : ‖chartChristoffel g p i j k x‖ ≤
      ∑ c, ‖chartChristoffel g p i j c x‖ :=
    Finset.single_le_sum (f := fun c => ‖chartChristoffel g p i j c x‖)
      (fun _ _ => norm_nonneg _) (Finset.mem_univ k)
  have hj : (∑ c, ‖chartChristoffel g p i j c x‖) ≤
      ∑ b, ∑ c, ‖chartChristoffel g p i b c x‖ :=
    Finset.single_le_sum (f := fun b => ∑ c, ‖chartChristoffel g p i b c x‖)
      (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _)
      (Finset.mem_univ j)
  have hi : (∑ b, ∑ c, ‖chartChristoffel g p i b c x‖) ≤ F x :=
    Finset.single_le_sum (f := fun a => ∑ b, ∑ c, ‖chartChristoffel g p a b c x‖)
      (fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _)
      (Finset.mem_univ i)
  exact (hk.trans (hj.trans hi)).trans ((hB (_root_.Set.mem_image_of_mem F hx)).trans (le_max_left _ _))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.exists_norm_chartChristoffel_le_of_isCompact then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.exists_norm_chartChristoffel_le_of_isCompact"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.exists_norm_chartChristoffel_le_of_isCompact ``Submission.DifferentialGeometry.Geometry.Connection.exists_norm_chartChristoffel_le_of_isCompact

end DifferentialGeometry.Geometry.Connection
