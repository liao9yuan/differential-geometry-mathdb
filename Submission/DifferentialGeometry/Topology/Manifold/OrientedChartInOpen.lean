import Submission.DifferentialGeometry.Topology.Manifold.BallChartSupportedTransport
import Submission.DifferentialGeometry.Topology.Manifold.BallChartAffine

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Function _root_.Filter
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology

namespace DifferentialGeometry.Topology

universe u
private abbrev E3 := EuclideanSpace ℝ (Fin 3)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.E3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.E3 target :: scope.openDecls } }

variable (M : ConnectedClosedOrientedManifold.{u} 3)

theorem exists_orientedBallChart_closedBall_subset_open {U : Set M.Carrier}
    (hU : IsOpen U) (hne : U.Nonempty) :
    ∃ c : OrientedBallChart M.toClosedOrientedManifold, c.chart '' Metric.closedBall 0 2 ⊆ U := by
  obtain ⟨p, hp⟩ := hne
  let c := orientedBallChart M
  obtain ⟨F, hF, hFp⟩ := exists_preservesOrientation_diffeomorph_apply_eq M.orientation (c.chart (0 : E3)) p
  let d := c.pushforward F hF
  have hdp : d.chart (0 : E3) = p := hFp
  have hnhds : U ∈ 𝓝 (d.chart (0 : E3)) := hdp.symm ▸ hU.mem_nhds hp
  obtain ⟨ε, hε, hsmall⟩ := exists_pos_forall_image_smul_closedBall_subset d.toBallChart hnhds
  let r := _root_.Min.min (ε / 2) (1 / 2)
  have hr : 0 < r := lt_min (by positivity) (by norm_num)
  have hrε : r < ε := (min_le_left _ _).trans_lt (by linarith)
  have hrbound : ‖(0 : E3)‖ + 2 * r ≤ 2 := by
    have h := min_le_right (ε / 2) (1 / 2 : ℝ)
    change r ≤ 1 / 2 at h
    norm_num
    linarith
  refine ⟨d.affine 0 r hr hrbound, ?_⟩
  rintro y ⟨x, hx, rfl⟩
  apply hsmall r hr hrε
  exact ⟨r • x, ⟨x, hx, rfl⟩, by simp only [OrientedBallChart.affine_apply, zero_add]⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.exists_orientedBallChart_closedBall_subset_open then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.exists_orientedBallChart_closedBall_subset_open"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.exists_orientedBallChart_closedBall_subset_open ``Submission.DifferentialGeometry.Topology.exists_orientedBallChart_closedBall_subset_open

theorem exists_orientedBallChart_disjoint_pair
    (c d : OrientedBallChart M.toClosedOrientedManifold)
    (hcd : Disjoint (c.chart '' Metric.closedBall 0 2) (d.chart '' Metric.closedBall 0 2)) :
    ∃ e : OrientedBallChart M.toClosedOrientedManifold,
      Disjoint (e.chart '' Metric.closedBall 0 2) (c.chart '' Metric.closedBall 0 2) ∧
      Disjoint (e.chart '' Metric.closedBall 0 2) (d.chart '' Metric.closedBall 0 2) := by
  let C := c.chart '' Metric.closedBall (0 : E3) 2
  let D := d.chart '' Metric.closedBall (0 : E3) 2
  have hC : IsClosed C := ((_root_.ProperSpace.isCompact_closedBall (0 : E3) 2).image_of_continuousOn
    (c.chart.contMDiffOn_toFun.continuousOn.mono c.closedBall_subset_source)).isClosed
  have hD : IsClosed D := ((_root_.ProperSpace.isCompact_closedBall (0 : E3) 2).image_of_continuousOn
    (d.chart.contMDiffOn_toFun.continuousOn.mono d.closedBall_subset_source)).isClosed
  have hCne : C.Nonempty := ⟨c.chart 0, ⟨0, Metric.mem_closedBall_self (by norm_num), rfl⟩⟩
  have hDne : D.Nonempty := ⟨d.chart 0, ⟨0, Metric.mem_closedBall_self (by norm_num), rfl⟩⟩
  have hne : (C ∪ D)ᶜ.Nonempty := by
    by_contra hn
    have hcover : C ∪ D = univ := by
      apply Set.eq_univ_of_forall
      intro x
      by_contra hx
      exact hn ⟨x, hx⟩
    have heq : C = Dᶜ := by
      ext x
      constructor
      · intro hx hd
        exact Set.disjoint_left.mp hcd hx hd
      · intro hx
        have hmem : x ∈ C ∪ D := hcover ▸ _root_.Set.mem_univ x
        exact hmem.resolve_right hx
    have hCop : IsOpen C := heq ▸ hD.isOpen_compl
    have hCu : C = univ := IsClopen.eq_univ ⟨hC, hCop⟩ hCne
    obtain ⟨x, hx⟩ := hDne
    have hxC : x ∈ C := hCu ▸ _root_.Set.mem_univ x
    exact Set.disjoint_left.mp hcd hxC hx
  obtain ⟨e, he⟩ := exists_orientedBallChart_closedBall_subset_open M (hC.union hD).isOpen_compl hne
  refine ⟨e, Set.disjoint_left.mpr (fun x hx hc => he hx (Or.inl hc)),
    Set.disjoint_left.mpr (fun x hx hd => he hx (Or.inr hd))⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.exists_orientedBallChart_disjoint_pair then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.exists_orientedBallChart_disjoint_pair"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.exists_orientedBallChart_disjoint_pair ``Submission.DifferentialGeometry.Topology.exists_orientedBallChart_disjoint_pair

end DifferentialGeometry.Topology
