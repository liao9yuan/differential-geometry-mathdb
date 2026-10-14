import Submission.DifferentialGeometry.Topology.Attachment.Restriction
import Submission.DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.TriplePunctured
import Submission.DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.FactorBallPair

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Function
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology

namespace DifferentialGeometry.Topology.ConnectedSumQuotient

universe u v
private abbrev E3 := EuclideanSpace ℝ (Fin 3)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ConnectedSumQuotient.E3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ConnectedSumQuotient.E3 target :: scope.openDecls } }
private abbrev S2 := Metric.sphere (0 : E3) 1

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ConnectedSumQuotient.S2
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ConnectedSumQuotient.S2 target :: scope.openDecls } }

variable {M : ConnectedClosedOrientedManifold.{u} 3} {N : ConnectedClosedOrientedManifold.{v} 3}
  (m : OrientedBallChart M.toClosedOrientedManifold) (e c d : OrientedBallChart N.toClosedOrientedManifold)
  (a : BoundaryAttachment)
  (hec : Disjoint (e.chart '' Metric.closedBall 0 2) (c.chart '' Metric.closedBall 0 2))
  (hed : Disjoint (e.chart '' Metric.closedBall 0 2) (d.chart '' Metric.closedBall 0 2))
  (c' d' : OrientedBallChart (smoothConnectedSum M N m e a).toConnectedClosedOrientedManifold.toClosedOrientedManifold)
  (hc' : ∀ x ∈ Metric.closedBall (0 : E3) 2, ∃ hx,
    c'.chart x = inr m.toBallChart e.toBallChart a.val.toHomeomorph ⟨c.chart x, hx⟩)
  (hd' : ∀ x ∈ Metric.closedBall (0 : E3) 2, ∃ hx,
    d'.chart x = inr m.toBallChart e.toBallChart a.val.toHomeomorph ⟨d.chart x, hx⟩)

include hec hed in
private theorem boundary_mem_firstRestriction (z : S2) :
    e.boundaryMap (a.val z) ∈ e.toBallChart.firstRestriction c.toBallChart d.toBallChart := by
  rintro (h | h)
  · exact e.toBallChart.chart_sphere_not_mem_other_ball c.toBallChart hec (a.val z) h
  · exact e.toBallChart.chart_sphere_not_mem_other_ball d.toBallChart hed (a.val z) h

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ConnectedSumQuotient.boundary_mem_firstRestriction
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ConnectedSumQuotient.boundary_mem_firstRestriction target :: scope.openDecls } }

include hc' hd' in
private theorem retained_pair_holes :
    adjunctionLower (i := m.toBallChart.boundaryMap) (e.toBallChart.boundaryMap ∘ a.val.toHomeomorph) ''
      (e.toBallChart.firstRestriction c.toBallChart d.toBallChart)ᶜ =
        c'.chart '' Metric.ball 0 1 ∪ d'.chart '' Metric.ball 0 1 := by
  rw [chart_image_ball_eq_inr_image m e a c c' hc', chart_image_ball_eq_inr_image m e a d d' hd']
  erw [← Set.image_union]
  congr 1
  ext x
  simp only [BallChart.firstRestriction, _root_.Set.mem_compl_iff, _root_.Set.mem_ofPred_eq, _root_.Classical.not_not, _root_.Set.mem_union]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ConnectedSumQuotient.retained_pair_holes
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ConnectedSumQuotient.retained_pair_holes target :: scope.openDecls } }

def puncturedPairHomeomorph :
    AdjunctionSpace m.toBallChart.boundaryMap
      (e.toBallChart.tripleBoundaryFirst c.toBallChart d.toBallChart hec hed ∘ a.val.toHomeomorph) ≃ₜ
        c'.toBallChart.DoublePunctured d'.toBallChart := by
  let T := e.toBallChart.firstRestriction c.toBallChart d.toBallChart
  let φ := e.toBallChart.boundaryMap ∘ a.val.toHomeomorph
  let hT : IsClosed T := e.toBallChart.isClosed_firstRestriction c.toBallChart d.toBallChart
  let hφT : ∀ z, φ z ∈ T := boundary_mem_firstRestriction e c d a hec hed
  let H := adjunctionClosedRestrictionHomeomorph m.toBallChart.boundaryMap φ
    m.toBallChart.boundaryMap_injective (e.toBallChart.boundaryMap_injective.comp a.val.injective)
    m.toBallChart.continuous_boundaryMap (e.toBallChart.continuous_boundaryMap.comp a.val.continuous) T hT hφT
  let E := adjunctionSpaceHomeomorphOfHomeomorph
    m.toBallChart.boundaryMap (fun z => (⟨φ z, hφT z⟩ : T))
    m.toBallChart.boundaryMap
    (e.toBallChart.tripleBoundaryFirst c.toBallChart d.toBallChart hec hed ∘ a.val.toHomeomorph)
    (Homeomorph.refl _) (Homeomorph.refl _)
    (e.toBallChart.firstRestrictionHomeomorph c.toBallChart d.toBallChart)
    (fun _ => rfl) (fun _ => rfl)
  let C : {q : ConnectedSumQuotient m.toBallChart e.toBallChart a.val.toHomeomorph //
      q ∉ adjunctionLower (i := m.toBallChart.boundaryMap) φ '' Tᶜ} ≃ₜ
      c'.toBallChart.DoublePunctured d'.toBallChart := Homeomorph.setCongr (by
    rw [retained_pair_holes m e c d a c' d' hc' hd']
    rfl)
  exact (E.symm.trans H).trans C

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ConnectedSumQuotient.puncturedPairHomeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ConnectedSumQuotient.puncturedPairHomeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ConnectedSumQuotient.puncturedPairHomeomorph ``Submission.DifferentialGeometry.Topology.ConnectedSumQuotient.puncturedPairHomeomorph

theorem puncturedPairHomeomorph_cell (x : m.Punctured) :
    (puncturedPairHomeomorph m e c d a hec hed c' d' hc' hd'
      (adjunctionCell m.toBallChart.boundaryMap
        (e.toBallChart.tripleBoundaryFirst c.toBallChart d.toBallChart hec hed ∘ a.val.toHomeomorph) x)).val =
      inl m.toBallChart e.toBallChart a.val.toHomeomorph x := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ConnectedSumQuotient.puncturedPairHomeomorph_cell then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ConnectedSumQuotient.puncturedPairHomeomorph_cell"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ConnectedSumQuotient.puncturedPairHomeomorph_cell ``Submission.DifferentialGeometry.Topology.ConnectedSumQuotient.puncturedPairHomeomorph_cell

theorem puncturedPairHomeomorph_lower (x : e.toBallChart.TriplePunctured c.toBallChart d.toBallChart) :
    (puncturedPairHomeomorph m e c d a hec hed c' d' hc' hd'
      (adjunctionLower (i := m.toBallChart.boundaryMap)
        (e.toBallChart.tripleBoundaryFirst c.toBallChart d.toBallChart hec hed ∘ a.val.toHomeomorph) x)).val =
      inr m.toBallChart e.toBallChart a.val.toHomeomorph (e.toBallChart.tripleToFirst c.toBallChart d.toBallChart x) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ConnectedSumQuotient.puncturedPairHomeomorph_lower then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ConnectedSumQuotient.puncturedPairHomeomorph_lower"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ConnectedSumQuotient.puncturedPairHomeomorph_lower ``Submission.DifferentialGeometry.Topology.ConnectedSumQuotient.puncturedPairHomeomorph_lower

end DifferentialGeometry.Topology.ConnectedSumQuotient
