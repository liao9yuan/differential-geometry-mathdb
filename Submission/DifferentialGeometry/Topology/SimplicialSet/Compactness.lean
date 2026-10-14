import Submission.DifferentialGeometry.Topology.SimplicialSet.FiniteCellInduction
import Submission.DifferentialGeometry.Topology.Category.TopCat.PushoutClosedEmbedding
import Mathlib.AlgebraicTopology.SimplicialSet.TopAdj
import Mathlib.Topology.Compactness.Compact

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Simplicial

universe u

namespace DifferentialGeometry.SSet

private theorem compactSpace_pushout {A D X P : TopCat.{u}} {f : A ⟶ D} {g : A ⟶ X}
    {r : D ⟶ P} {b : X ⟶ P} (h : _root_.CategoryTheory.IsPushout f g r b)
    [CompactSpace D] [CompactSpace X] : CompactSpace P := by
  have hc : Continuous (Sum.elim r b) :=
    continuous_sum_dom.mpr ⟨r.hom.continuous, b.hom.continuous⟩
  apply Function.Surjective.compactSpace hc
  intro p
  rcases DifferentialGeometry.TopCat.Pushout.jointly_surjective h p with ⟨d, hd⟩ | ⟨x, hx⟩
  · exact ⟨Sum.inl d, hd⟩
  · exact ⟨Sum.inr x, hx⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.SSet.compactSpace_pushout
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.SSet.compactSpace_pushout target :: scope.openDecls } }


instance compactSpace_realization (X : _root_.SSet.{u}) [X.Finite] :
    CompactSpace (_root_.SSet.toTop.obj X) := by
  apply finite_cell_induction (fun Y ↦ CompactSpace (_root_.SSet.toTop.obj Y)) ?_ ?_ X
  · intro Y hY
    let h : _root_.CategoryTheory.Limits.IsInitial (_root_.SSet.toTop.obj Y) := hY.isInitialObj _root_.SSet.toTop
    let : IsEmpty (_root_.SSet.toTop.obj Y) :=
      ⟨fun y ↦ PEmpty.elim (h.to (TopCat.of PEmpty.{u + 1}) y)⟩
    infer_instance
  · intro n Y Z g r b h _ hY
    let : CompactSpace (_root_.SSet.toTop.obj Y) := hY
    let : CompactSpace (_root_.SSet.toTop.obj (Δ[n] : _root_.SSet.{u})) :=
      (SimplexCategory.toTopHomeo ⦋n⦌).symm.compactSpace
    exact compactSpace_pushout (h.map _root_.SSet.toTop)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.SSet.compactSpace_realization then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.SSet.compactSpace_realization"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.SSet.compactSpace_realization ``Submission.DifferentialGeometry.SSet.compactSpace_realization

end DifferentialGeometry.SSet
