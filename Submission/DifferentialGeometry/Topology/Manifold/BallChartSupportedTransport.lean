import Submission.DifferentialGeometry.Topology.Manifold.SupportedPointMotion
import Submission.DifferentialGeometry.Topology.Manifold.BallChartSupportedIsotopy
import Submission.DifferentialGeometry.Topology.ClosedBallComplement

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

namespace OrientedBallChart

variable {M : ClosedOrientedManifold.{u} 3}

def pushforward (c : OrientedBallChart M) (F : M.Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯ M.Carrier)
    (hF : F.preservesOrientation M.orientation M.orientation) : OrientedBallChart M where
  toBallChart := BallChart.pullback c.toBallChart F.symm
  preserves_orientation := OrientationAssembly.ballChart_pullback_preserves_orientation c F.symm
    (Diffeomorph.preservesOrientation_symm hF)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.OrientedBallChart.pushforward then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.OrientedBallChart.pushforward"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.OrientedBallChart.pushforward ``Submission.DifferentialGeometry.Topology.OrientedBallChart.pushforward

theorem pushforward_apply (c : OrientedBallChart M) (F : M.Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯ M.Carrier)
    (hF : F.preservesOrientation M.orientation M.orientation) (x : E3) :
    (c.pushforward F hF).chart x = F (c.chart x) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.OrientedBallChart.pushforward_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.OrientedBallChart.pushforward_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.OrientedBallChart.pushforward_apply ``Submission.DifferentialGeometry.Topology.OrientedBallChart.pushforward_apply

variable [PreconnectedSpace M.Carrier]

theorem exists_compact_diffeomorph_of_isPreconnected
    (c d : OrientedBallChart M) (U : Set M.Carrier) (hU : IsOpen U) (hUc : IsPreconnected U)
    (hcU : c.chart '' Metric.closedBall 0 2 ⊆ U) (hdU : d.chart '' Metric.closedBall 0 2 ⊆ U) :
    ∃ F : M.Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯ M.Carrier,
      F.preservesOrientation M.orientation M.orientation ∧
      (∀ x ∈ Metric.closedBall (0 : E3) 2, F (c.chart x) = d.chart x) ∧
      ∃ K : Set M.Carrier, IsCompact K ∧ K ⊆ U ∧
        ∀ x ∉ K, F x = x ∧ F.symm x = x := by
  have h02 : (0 : E3) ∈ Metric.closedBall (0 : E3) 2 := Metric.mem_closedBall_self (by norm_num)
  obtain ⟨F, K, hK, hKU, hFo, hF0, hFfix⟩ :=
    exists_supported_diffeomorph_apply_eq_of_isPreconnected M.orientation U hU hUc
      (c.chart 0) (d.chart 0) (hcU ⟨0, h02, rfl⟩) (hdU ⟨0, h02, rfl⟩)
  let c' := c.pushforward F hFo
  have hc' : c'.chart (0 : E3) = d.chart (0 : E3) := hF0
  have hc'U : c'.chart '' Metric.closedBall 0 2 ⊆ U := by
    rintro y ⟨x, hx, rfl⟩
    change F (c.chart x) ∈ U
    by_contra hnot
    have hfix := (hFfix (F (c.chart x)) (fun h => hnot (hKU h))).1
    have he := F.injective hfix
    exact hnot (he.symm ▸ hcU ⟨x, hx, rfl⟩)
  obtain ⟨G, hGo, hG, L, hL, hLU, hGfix⟩ := c'.exists_compact_diffeomorph_of_center_eq d hc' hU hc'U hdU
  refine ⟨F.trans G, Diffeomorph.preservesOrientation_trans hFo hGo, ?_, K ∪ L,
    hK.union hL, _root_.Set.union_subset hKU hLU, ?_⟩
  · intro x hx
    exact hG x hx
  · intro x hx
    have hxK : x ∉ K := fun h => hx (Or.inl h)
    have hxL : x ∉ L := fun h => hx (Or.inr h)
    constructor
    · change G (F x) = x
      rw [(hFfix x hxK).1, (hGfix x hxL).1]
    · change F.symm (G.symm x) = x
      rw [(hGfix x hxL).2, (hFfix x hxK).2]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.OrientedBallChart.exists_compact_diffeomorph_of_isPreconnected then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.OrientedBallChart.exists_compact_diffeomorph_of_isPreconnected"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.OrientedBallChart.exists_compact_diffeomorph_of_isPreconnected ``Submission.DifferentialGeometry.Topology.OrientedBallChart.exists_compact_diffeomorph_of_isPreconnected

end OrientedBallChart

namespace BallChart

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E3 M] [T2Space M]
  [PreconnectedSpace M]

theorem isPathConnected_compl_image_closedBall_two (c : BallChart 3 (𝓡 3) M) :
    IsPathConnected ((c.chart '' Metric.closedBall 0 2)ᶜ : Set M) := by
  let _ := ChartedSpace.locallyPathConnectedSpace E3 M
  exact isPathConnected_compl_image_closedBall c.chart.toOpenPartialHomeomorph
    (Module.one_lt_rank_of_one_lt_finrank (by simp)) (by norm_num) c.closedBall_subset_source

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.BallChart.isPathConnected_compl_image_closedBall_two then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.BallChart.isPathConnected_compl_image_closedBall_two"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.BallChart.isPathConnected_compl_image_closedBall_two ``Submission.DifferentialGeometry.Topology.BallChart.isPathConnected_compl_image_closedBall_two

end BallChart

end DifferentialGeometry.Topology
