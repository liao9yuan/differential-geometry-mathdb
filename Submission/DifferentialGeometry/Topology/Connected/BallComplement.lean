import Mathlib.Analysis.Normed.Module.Connected

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Metric

namespace DifferentialGeometry.Topology

theorem isPathConnected_compl_closedBall {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (hd : 1 < Module.rank ℝ E) (x : E) (r : ℝ) :
    IsPathConnected (_root_.Metric.closedBall x r)ᶜ := by
  by_cases hr : r < 0
  · rw [closedBall_eq_empty.mpr hr, _root_.Set.compl_empty]
    exact isPathConnected_univ
  have hr₀ : 0 ≤ r := le_of_not_gt hr
  let F : E × ℝ → E := fun p ↦ x + p.2 • p.1
  have heq : F '' (_root_.Metric.sphere (0 : E) 1 ×ˢ _root_.Set.Ioi r) = (_root_.Metric.closedBall x r)ᶜ := by
    apply Subset.antisymm
    · rintro _ ⟨⟨v, t⟩, ⟨hv, ht⟩, rfl⟩
      have ht₀ : 0 < t := hr₀.trans_lt ht
      have hvn : ‖v‖ = 1 := by simpa [mem_sphere_iff_norm] using hv
      simpa [F, _root_.Metric.mem_closedBall, dist_eq_norm, norm_smul, abs_of_pos ht₀, hvn] using ht
    · intro y hy
      have hnr : r < ‖y - x‖ := by simpa [_root_.Metric.mem_closedBall, dist_eq_norm] using hy
      have hn : 0 < ‖y - x‖ := hr₀.trans_lt hnr
      refine ⟨(‖y - x‖⁻¹ • (y - x), ‖y - x‖), ⟨?_, hnr⟩, ?_⟩
      · simp [mem_sphere_iff_norm, norm_smul, hn.ne']
      · dsimp only [F]
        rw [smul_smul, mul_inv_cancel₀ hn.ne', one_smul]
        exact add_sub_cancel _ _
  rw [← heq]
  exact ((isPathConnected_sphere hd (0 : E) zero_le_one).prod
    ((convex_Ioi r).isPathConnected ⟨r + 1, by simp⟩)).image (by fun_prop)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.isPathConnected_compl_closedBall then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.isPathConnected_compl_closedBall"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.isPathConnected_compl_closedBall ``Submission.DifferentialGeometry.Topology.isPathConnected_compl_closedBall

end DifferentialGeometry.Topology
