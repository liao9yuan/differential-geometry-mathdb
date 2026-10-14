import Submission.DifferentialGeometry.Topology.Manifold.BallChartSupportedTransport

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Function
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology

namespace DifferentialGeometry.Topology

universe u
private abbrev E3 := EuclideanSpace ℝ (Fin 3)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.E3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.E3 target :: scope.openDecls } }

variable {M : ConnectedClosedOrientedManifold.{u} 3}

theorem exists_oriented_diffeomorph_ballPair
    (c d c' d' : OrientedBallChart M.toClosedOrientedManifold)
    (hcd : Disjoint (c.chart '' Metric.closedBall 0 2) (d.chart '' Metric.closedBall 0 2))
    (hcd' : Disjoint (c'.chart '' Metric.closedBall 0 2) (d'.chart '' Metric.closedBall 0 2)) :
    ∃ F : M.Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯ M.Carrier,
      F.preservesOrientation M.orientation M.orientation ∧
      (∀ x ∈ Metric.closedBall (0 : E3) 2, F (c.chart x) = c'.chart x) ∧
      ∀ x ∈ Metric.closedBall (0 : E3) 2, F (d.chart x) = d'.chart x := by
  obtain ⟨F, hFo, hFc, _, _, _, _⟩ := c.exists_compact_diffeomorph_of_isPreconnected c' _root_.Set.univ
    isOpen_univ _root_.PreconnectedSpace.isPreconnected_univ (_root_.Set.subset_univ _) (_root_.Set.subset_univ _)
  let d₀ := d.pushforward F hFo
  let U : Set M.Carrier := (c'.chart '' Metric.closedBall 0 2)ᶜ
  have hcompact : IsCompact (c'.chart '' Metric.closedBall 0 2) :=
    (_root_.ProperSpace.isCompact_closedBall (0 : E3) 2).image_of_continuousOn
      (c'.chart.contMDiffOn_toFun.continuousOn.mono c'.closedBall_subset_source)
  have hU : IsOpen U := hcompact.isClosed.isOpen_compl
  have hUc : IsPreconnected U := (c'.toBallChart.isPathConnected_compl_image_closedBall_two).isConnected.isPreconnected
  have hd₀U : d₀.chart '' Metric.closedBall 0 2 ⊆ U := by
    rintro y ⟨x, hx, rfl⟩ ⟨z, hz, he⟩
    change c'.chart z = F (d.chart x) at he
    rw [← hFc z hz] at he
    have hzx := F.injective he
    exact Set.disjoint_left.mp hcd ⟨z, hz, rfl⟩ ⟨x, hx, hzx.symm⟩
  have hd'U : d'.chart '' Metric.closedBall 0 2 ⊆ U := by
    intro x hx hc'
    exact Set.disjoint_left.mp hcd' hc' hx
  obtain ⟨G, hGo, hGd, K, _, hKU, hGfix⟩ :=
    d₀.exists_compact_diffeomorph_of_isPreconnected d' U hU hUc hd₀U hd'U
  refine ⟨F.trans G, Diffeomorph.preservesOrientation_trans hFo hGo, ?_, ?_⟩
  · intro x hx
    change G (F (c.chart x)) = c'.chart x
    rw [hFc x hx]
    exact (hGfix _ (fun h => hKU h ⟨x, hx, rfl⟩)).1
  · intro x hx
    exact hGd x hx

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.exists_oriented_diffeomorph_ballPair then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.exists_oriented_diffeomorph_ballPair"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.exists_oriented_diffeomorph_ballPair ``Submission.DifferentialGeometry.Topology.exists_oriented_diffeomorph_ballPair

theorem exists_oriented_diffeomorph_ballPair_retaining_charts
    (c d c' d' : OrientedBallChart M.toClosedOrientedManifold)
    (hcd : Disjoint (c.chart '' Metric.closedBall 0 2) (d.chart '' Metric.closedBall 0 2))
    (hcd' : Disjoint (c'.chart '' Metric.closedBall 0 2) (d'.chart '' Metric.closedBall 0 2)) :
    ∃ F : M.Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯ M.Carrier,
      F.preservesOrientation M.orientation M.orientation ∧
      (∀ x ∈ Metric.closedBall (0 : E3) 2, F (c.chart x) = c'.chart x) ∧
      (∀ x ∈ Metric.closedBall (0 : E3) 2, F (d.chart x) = d'.chart x) ∧
      ∀ e : OrientedBallChart M.toClosedOrientedManifold, ∃ e' : OrientedBallChart M.toClosedOrientedManifold,
        (∀ x, e'.chart x = F (e.chart x)) ∧
        (∀ r : ℝ, e'.chart '' Metric.ball 0 r = F '' (e.chart '' Metric.ball 0 r)) ∧
        ∀ r : ℝ, e'.chart '' Metric.closedBall 0 r = F '' (e.chart '' Metric.closedBall 0 r) := by
  obtain ⟨F, hF, hc, hd⟩ := exists_oriented_diffeomorph_ballPair c d c' d' hcd hcd'
  refine ⟨F, hF, hc, hd, ?_⟩
  intro e
  exact ⟨e.pushforward F hF, fun _ => rfl, fun r => Set.image_comp (F : M.Carrier → M.Carrier) (e.chart : E3 → M.Carrier) _,
    fun r => Set.image_comp (F : M.Carrier → M.Carrier) (e.chart : E3 → M.Carrier) _⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.exists_oriented_diffeomorph_ballPair_retaining_charts then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.exists_oriented_diffeomorph_ballPair_retaining_charts"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.exists_oriented_diffeomorph_ballPair_retaining_charts ``Submission.DifferentialGeometry.Topology.exists_oriented_diffeomorph_ballPair_retaining_charts

end DifferentialGeometry.Topology
