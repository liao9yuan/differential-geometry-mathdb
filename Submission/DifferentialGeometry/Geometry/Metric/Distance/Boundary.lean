import Submission.DifferentialGeometry.Geometry.Metric.Distance.Basic
import Submission.DifferentialGeometry.Topology.FirstExit
import Mathlib.Geometry.Manifold.Riemannian.Basic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Bundle _root_.Manifold _root_.Set
open scoped _root_.ContDiff _root_.ENNReal _root_.Manifold _root_.Topology

namespace DifferentialGeometry.Geometry.Metric

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem riemannianEDistOf_ball_subset_of_le_frontier_distance
    (g : SmoothRiemannianMetric I M) {A : Set M} {p : M}
    (hp : p ∈ interior A) {r : ℝ≥0∞}
    (hfront : ∀ q ∈ frontier A, r ≤ riemannianEDistOf g p q) :
    {y | riemannianEDistOf g p y < r} ⊆ interior A := by
  let : _root_.Bundle.RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
  intro y hy
  obtain ⟨γ, hγ0, hγ1, hγ, hlength⟩ := _root_.Manifold.exists_lt_of_riemannianEDist_lt hy
  by_contra hyA
  obtain ⟨t, ht, _, hboundary⟩ :=
    exists_first_exit_frontier_of_not_mem_interior zero_lt_one hγ.continuousOn
      (hγ0 ▸ hp) (hγ1 ▸ hyA)
  have hprefix : riemannianEDistOf g p (γ t) ≤ _root_.Manifold.pathELength I γ 0 t :=
    _root_.Manifold.riemannianEDist_le_pathELength (hγ.mono (_root_.Set.Icc_subset_Icc le_rfl ht.2))
      hγ0 rfl ht.1.le
  exact (not_lt_of_ge (hfront (γ t) hboundary))
    (hprefix.trans_lt ((_root_.Manifold.pathELength_mono le_rfl ht.2).trans_lt hlength))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Metric.riemannianEDistOf_ball_subset_of_le_frontier_distance then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Metric.riemannianEDistOf_ball_subset_of_le_frontier_distance"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Metric.riemannianEDistOf_ball_subset_of_le_frontier_distance ``Submission.DifferentialGeometry.Geometry.Metric.riemannianEDistOf_ball_subset_of_le_frontier_distance

theorem riemannianEDistOf_closedBall_subset_of_le_frontier_distance [RegularSpace M]
    (g : SmoothRiemannianMetric I M) {A : Set M} (hA : IsClosed A) {p : M}
    (hp : p ∈ interior A) {r : ℝ≥0∞} (hr : r ≠ ⊤)
    (hfront : ∀ q ∈ frontier A, r ≤ riemannianEDistOf g p q) :
    {y | riemannianEDistOf g p y ≤ r} ⊆ A := by
  let : _root_.Bundle.RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (TangentSpace I : M → Type _) :=
    ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
  intro y hy
  by_contra hyA
  obtain ⟨c, hc, hball⟩ :=
    setOfPred_riemannianEDist_lt_subset_nhds I (hA.isOpen_compl.mem_nhds hyA)
  have hshort : _root_.Manifold.riemannianEDist I p y < r + c :=
    hy.trans_lt (ENNReal.lt_add_right hr (by exact_mod_cast hc.ne'))
  obtain ⟨γ, hγ0, hγ1, hγ, hlength⟩ := _root_.Manifold.exists_lt_of_riemannianEDist_lt hshort
  obtain ⟨t, ht, _, hboundary⟩ :=
    exists_first_exit_frontier hA zero_lt_one hγ.continuousOn
      (hγ0 ▸ hp) (hγ1 ▸ hyA)
  have hleft : r ≤ _root_.Manifold.pathELength I γ 0 t :=
    (hfront (γ t) hboundary).trans
      (_root_.Manifold.riemannianEDist_le_pathELength (hγ.mono (_root_.Set.Icc_subset_Icc le_rfl ht.2))
        hγ0 rfl ht.1.le)
  have hright : (c : ℝ≥0∞) ≤ _root_.Manifold.pathELength I γ t 1 := by
    have hfar : (c : ℝ≥0∞) ≤ _root_.Manifold.riemannianEDist I y (γ t) := by
      apply le_of_not_gt
      intro hlt
      exact hball hlt (hA.closure_eq ▸ frontier_subset_closure hboundary)
    rw [_root_.Manifold.riemannianEDist_comm] at hfar
    exact hfar.trans
      (_root_.Manifold.riemannianEDist_le_pathELength (hγ.mono (_root_.Set.Icc_subset_Icc ht.1.le le_rfl))
        rfl hγ1 ht.2)
  have htotal := add_le_add hleft hright
  rw [_root_.Manifold.pathELength_add ht.1.le ht.2] at htotal
  exact (not_lt_of_ge htotal) hlength

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Metric.riemannianEDistOf_closedBall_subset_of_le_frontier_distance then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Metric.riemannianEDistOf_closedBall_subset_of_le_frontier_distance"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Metric.riemannianEDistOf_closedBall_subset_of_le_frontier_distance ``Submission.DifferentialGeometry.Geometry.Metric.riemannianEDistOf_closedBall_subset_of_le_frontier_distance

end DifferentialGeometry.Geometry.Metric
